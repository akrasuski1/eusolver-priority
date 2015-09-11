#!/usr/bin/env python3
# solvers.py ---
#
# Filename: solvers.py
# Author: Abhishek Udupa
# Created: Wed Aug 26 09:34:54 2015 (-0400)
#
#
# Copyright (c) 2015, Abhishek Udupa, University of Pennsylvania
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
# 3. All advertising materials mentioning features or use of this software
#    must display the following acknowledgement:
#    This product includes software developed by The University of Pennsylvania
# 4. Neither the name of the University of Pennsylvania nor the
#    names of its contributors may be used to endorse or promote products
#    derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
# EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#

# Code:

import basetypes
import evaluation
import functools
import hashcache
import exprtypes
import exprs
import expr_transforms
import z3
import z3smt
import semantics_types

def model_to_point(model, var_smt_expr_list, var_info_list):
    num_vars = len(var_smt_expr_list)
    point = [None] * num_vars
    for i in range(num_vars):
        eval_value = model.evaluate(var_smt_expr_list[i], True)
        if (var_info_list[i].variable_type == exprtypes.BoolType):
            point[i] = bool(str(eval_value))
        else:
            point[i] = int(str(eval_value))
    return tuple(point)


class TermSolver(object):
    def __init__(self):
        self.points = []
        self.point_set = set()
        self.reset()

    def reset(self):
        self.spec = None
        self.var_info_list = None
        self.var_smt_expr_list = None
        self.fun_list = None
        self.smt_ctx = None
        self.eval_ctx = None
        self.solver = None
        self.sat_point_set = None
        self.sat_expr_list = None

    def add_point(self, point):
        print('Adding point: %s' % str(point))
        if point in self.point_set:
            raise basetypes.ArgumentError('Duplicate point added: %s' % str(point))
        self.point_set.add(point)
        self.points.append(point)

    def add_point_from_model(self, model):
        point = model_to_point(model, self.var_smt_expr_list, self.var_info_list)
        self.add_point(point)

    def test_expr(self, expr):
        num_points = len(self.points)
        if (num_points == 0):
            return True
        eval_ctx = self.eval_ctx
        points = self.points
        eval_ctx.set_interpretation_map([expr])

        points_satisfied = set()
        for i in range(num_points):
            eval_ctx.set_valuation_map(points[i])
            res = evaluation.evaluate_expression_raw(self.spec, eval_ctx)
            if (res):
                self.sat_point_set.add(i)
                points_satisfied.add(i)

        if (len(points_satisfied) > 0):
            self.sat_expr_list.append((expr, points_satisfied))
            if (len(self.sat_point_set) == num_points):
                return True

        return False

    def get_next_term_from_sat_expr_list(self, covered_points):
        index = 0
        num_points = len(self.points)
        while (self.sat_expr_list[index][1].issubset(covered_points) and index < num_points):
            index += 1
        if (index >= num_points):
            return None
        else:
            (expr, points_covered_by_expr) = self.sat_expr_list[index]
            newly_covered_points = points_covered_by_expr - covered_points
            for i in range(num_points):
                (old_expr, old_points) = self.sat_expr_list[i]
                self.sat_expr_list[i] = (old_expr, old_points - newly_covered_points)
            self.sat_expr_list.sort(key=lambda x: len(x[1]))
            return (expr, newly_covered_points, (set(range(num_points)) -
                                                 covered_points -
                                                 newly_covered_points))

    def test_guard(self, guard, term, smt_uncovered_region):
        self.smt_ctx.set_interpretation_map([term])
        guard_smt = semantics_types.expression_to_smt(guard, self.smt_ctx)
        test_formula = z3.And(smt_uncovered_region, guard_smt, smt_uncovered_region.ctx)
        test_formula = z3.Implies(test_formula,
                                  semantics_types.expression_to_smt(self.spec, self.smt_ctx),
                                  test_formula.ctx)
        self.solver.push()
        print('Testing guard %s' % exprs.expression_to_string(guard))
        print(z3.Not(test_formula))
        self.solver.add(z3.Not(test_formula))
        res = self.solver.check()
        self.solver.pop()
        if (res == z3.sat):
            self.add_point_from_model(self.solver.model())
            return False
        else:
            return True


    def learn_guard(self, term, pos_pt_indices, neg_pt_indices,
                    smt_uncovered_region, pred_generator):
        print('Synthesizing guard for term %s' % exprs.expression_to_string(term))
        print('With positive points: %s' % str([self.points[i] for i in pos_pt_indices]))
        print('With negative points: %s' % str([self.points[i] for i in neg_pt_indices]))
        covered_neg_pts = set()
        num_pos_pts = len(pos_pt_indices)
        num_neg_pts = len(neg_pt_indices)
        exprs_covering_pos_pts = [set() for x in range(num_pos_pts)]
        exprs_covering_neg_pts = [set() for x in range(num_neg_pts)]
        eval_ctx = self.eval_ctx

        pred_generator.set_size(3)
        for expr in pred_generator.generate():
            pos_pts_covered_by_expr = set()
            neg_pts_covered_by_expr = set()
            print('Trying guard: %s' % exprs.expression_to_string(expr))
            for pos_pt_index in pos_pt_indices:
                eval_ctx.set_valuation_map(self.points[pos_pt_index])
                if(evaluation.evaluate_expression_raw(expr, eval_ctx)):
                    pos_pts_covered_by_expr.add(pos_pt_index)
            for neg_pt_index in neg_pt_indices:
                eval_ctx.set_valuation_map(self.points[neg_pt_index])
                if (evaluation.evaluate_expression_raw(expr, eval_ctx)):
                    neg_pts_covered_by_expr.add(neg_pt_index)

            if (len(pos_pts_covered_by_expr) > 0 and len(neg_pts_covered_by_expr) > 0):
                continue

            if (len(pos_pts_covered_by_expr) > 0):
                for point_idx in pos_pts_covered_by_expr:
                    exprs_covering_pos_pts[point_idx].add(expr)
            if (len(neg_pts_covered_by_expr) > 0):
                for point_idx in neg_pts_covered_by_expr:
                    exprs_covering_neg_pts[point_idx].add(expr)
                    covered_neg_pts.add(point_idx)

            # termination checks
            common_pos = functools.reduce(lambda x, y: x.intersection(y), exprs_covering_pos_pts)
            if (len(common_pos) > 0):
                guard = self.syn_ctx.make_function_expr('and', *common_pos)
                if (self.test_guard(guard, term, smt_uncovered_region)):
                    return guard
                else:
                    return None

            if (len(covered_neg_pts) == num_neg_pts):
                witnesses = set([expr_set.pop() for expr_set in exprs_covering_neg_pts])
                neg_witnesses = [self.syn_ctx.make_function_expr('not', witness)
                                 for witness in witnesses]
                guard = self.syn_ctx.make_ac_function_expr('and', *neg_witnesses)
                if (self.test_guard(guard, term, smt_uncovered_region)):
                    return guard
                else:
                    return None


    def try_unification(self, pred_generator):
        num_points = len(self.points)
        self.sat_expr_list.sort(key=lambda x: len(x[1]))

        print('Trying to unify terms:')
        for i in range(len(self.sat_expr_list)):
            print('%s which satisfies %s' % (exprs.expression_to_string(self.sat_expr_list[i][0]),
                                             str([self.points[j] for j in self.sat_expr_list[i][1]])))

        smt_uncovered_region = z3.BoolVal(True, self.smt_ctx.ctx())
        index_in_sat_expr_list = 0
        term_guard_list = []
        expr_to_smt = semantics_types.expression_to_smt
        covered_points = set()
        while (len(covered_points) != num_points):
            cur_term, pos_pts, neg_pts = self.get_next_term_from_sat_expr_list(covered_points)
            covered_points = covered_points | pos_pts
            if (len(covered_points) == num_points):
                # last point, no pred required
                term_guard_list.append((cur_term, None))
                return term_guard_list
            # learn a guard for the point
            guard = self.learn_guard(cur_term, pos_pts, neg_pts,
                                     smt_uncovered_region, pred_generator)
            if (guard != None):
                # we've learnt a new guard
                print('Learned guard %s for term %s' % (exprs.expression_to_string(guard),
                                                        exprs.expression_to_string(cur_term)))
                term_guard_list.append(cur_term, guard)
                smt_uncovered_region = z3.And(smt_uncovered_region,
                                              z3.Not(expr_to_smt(guard, self.smt_ctx)))
            else:
                # we've added a point that's not covered
                return None

    def prove_expr(self, expr):
        print(('Attempting to prove expression: %s' +
               ' which passes on points %s') % (exprs.expression_to_string(expr),
                                                str(self.points)))
        self.smt_ctx.set_interpretation_map([expr])
        formula = semantics_types.expression_to_smt(self.spec, self.smt_ctx)
        formula = z3.Not(formula)
        self.solver.push()
        self.solver.add(formula)
        res = self.solver.check()
        self.solver.pop()
        if (res == z3.sat):
            self.add_point_from_model(self.solver.model())
            return False
        else:
            return True

    def make_expr_from_term_guard_list(self, term_guard_list):
        num_terms = len(term_guard_list)
        if (num_terms == 1):
            return term_guard_list[0][0]
        else:
            expr = term_guard_list[num_terms - 1]
            for i in reversed(range(num_terms - 1)):
                expr = self.syn_ctx.make_function_expr('ite', term_guard_list[i][1],
                                                       term_guard_list[i][0], expr)
            return expr

    def solve(self, syn_ctx, generator, predicate_generator):
        self.spec, self.var_info_list, self.fun_list = syn_ctx.get_synthesis_spec()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.eval_ctx = evaluation.EvaluationContext()
        self.syn_ctx = syn_ctx
        var_expr_list = [exprs.VariableExpression(var_info)
                         for var_info in self.var_info_list]
        self.var_smt_expr_list = [semantics_types.expression_to_smt(expr, self.smt_ctx)
                                  for expr in var_expr_list]
        self.solver = z3.Solver(ctx=self.smt_ctx.ctx())

        while (True):
            print('Restarting...')
            self.sat_point_set = set()
            self.sat_expr_list = []
            generator.set_size(3)
            predicate_generator.set_size(3)
            for expr in generator.generate():
                print('Trying: %s' % exprs.expression_to_string(expr))
                done = self.test_expr(expr)
                if (done):
                    if (len(self.points) > 0):
                        term_guard_list = self.try_unification(predicate_generator)
                        if (term_guard_list == None):
                            break
                        else:
                            final_expr = self.make_expr_from_term_guard_list(term_guard_list)
                    else:
                        final_expr = expr
                    if (self.prove_expr(final_expr)):
                        return final_expr
                    else:
                        break


########################################################################
# TEST CASES
########################################################################

def test_solver_max(num_vars):
    import synthesis_context
    import semantics_core
    import semantics_lia
    import enumerators

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_lia.LIAInstantiator())
    max_fun = syn_ctx.make_unknown_function('max', [exprtypes.IntType()] * num_vars,
                                            exprtypes.IntType())
    add_fun = syn_ctx.make_function('add', exprtypes.IntType(), exprtypes.IntType())
    sub_fun = syn_ctx.make_function('sub', exprtypes.IntType(), exprtypes.IntType())
    le_fun = syn_ctx.make_function('le', exprtypes.IntType(), exprtypes.IntType())
    ge_fun = syn_ctx.make_function('ge', exprtypes.IntType(), exprtypes.IntType())
    eq_fun = syn_ctx.make_function('eq', exprtypes.IntType(), exprtypes.IntType())

    param_infos = [syn_ctx.make_variable(exprtypes.IntType(), 'arg%d' % x, x)
                   for x in range(num_vars)]

    param_exprs = [exprs.VariableExpression(var_info) for var_info in param_infos]
    param_generator = enumerators.LeafGenerator(param_exprs, 'Variable Generator')
    zero_value = exprs.Value(0, exprtypes.IntType())
    one_value = exprs.Value(1, exprtypes.IntType())
    const_generator = enumerators.LeafGenerator([exprs.ConstantExpression(zero_value),
                                                 exprs.ConstantExpression(one_value)])
    leaf_generator = enumerators.AlternativesGenerator([param_generator, const_generator],
                                                       'Leaf Term Generator')

    generator_factory = enumerators.RecursiveGeneratorFactory()
    term_generator_ph = generator_factory.make_placeholder('TermGenerator')
    pred_bool_generator_ph = generator_factory.make_placeholder('PredGenerator')
    term_generator = \
    generator_factory.make_generator('TermGenerator',
                                     enumerators.AlternativesGenerator,
                                     ([leaf_generator] +
                                      [enumerators.FunctionalGenerator(add_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(sub_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph])],))

    pred_generator = \
    generator_factory.make_generator('PredGenerator',
                                     enumerators.AlternativesGenerator,
                                     ([enumerators.FunctionalGenerator(le_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(eq_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(ge_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph])],))

    # construct the spec
    uvar_infos = [syn_ctx.make_variable(exprtypes.IntType(), 'x%d' % x, x)
                  for x in range(num_vars)]
    uvar_exprs = [exprs.VariableExpression(var_info) for var_info in uvar_infos]
    max_app = syn_ctx.make_function_expr(max_fun, *uvar_exprs)
    ge_constraints = []
    eq_constraints = []
    for i in range(num_vars):
        c = syn_ctx.make_function_expr('ge', max_app, uvar_exprs[i])
        ge_constraints.append(c)
        c = syn_ctx.make_function_expr('eq', max_app, uvar_exprs[i])
        eq_constraints.append(c)

    constraint = syn_ctx.make_function_expr('and', *ge_constraints)
    constraint = syn_ctx.make_function_expr('and', constraint,
                                            syn_ctx.make_function_expr('or',
                                                                       *eq_constraints))
    syn_ctx.assert_spec(constraint)

    solver = TermSolver()
    expr = solver.solve(syn_ctx, term_generator, pred_generator)
    print(exprs.expression_to_string(expr))


if __name__ == '__main__':
    test_solver_max(2)

#
# solvers.py ends here
