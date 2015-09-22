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
import bitset
from bitset import BitSet
import evaluation
import functools
import hashcache
import exprtypes
import exprs
import expr_transforms
import z3
import z3smt
import semantics_types
from enum import IntEnum

_expr_to_str = exprs.expression_to_string
_expr_to_smt = semantics_types.expression_to_smt

class GuardProofStatus(IntEnum):
    proved_ok = 1
    unproved_continue = 2
    unproved_restart = 3

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
        """Resets the solver."""
        self.spec = None
        self.var_info_list = None
        self.var_smt_expr_list = None
        self.fun_list = None
        self.smt_ctx = None
        self.eval_ctx = None
        self.solver = None
        self.sat_point_set = None
        self.sat_term_list = None

    def add_point(self, point):
        """Adds a point, which is really just a tuple of values."""
        print('Adding point: %s' % str(point))
        if point in self.point_set:
            raise basetypes.ArgumentError('Duplicate point added: %s' % str(point))
        self.point_set.add(point)
        self.points.append(point)
        print('Current point set = %s' % [str(point) for point in self.points])

    def add_point_from_model(self, model):
        """Adds a point from a Z3 model object."""
        point = model_to_point(model, self.var_smt_expr_list, self.var_info_list)
        self.add_point(point)

    def test_term_on_points(self, term, term_signature_set):
        """Tests a term over the points accumulated so far.
        Effects: if the expression satisfies the specification at one or more of the points,
                 then the expression is "remembered", along with the points at which it satisfies
                 the specification.
        Return Value: If ALL points are covered by some set of expressions "remembered" so far,
                      then return True, otherwise, return False
        """
        num_points = len(self.points)
        if (num_points == 0):
            return True
        eval_ctx = self.eval_ctx
        points = self.points
        eval_ctx.set_interpretation_map([term])

        points_satisfied = BitSet(num_points)
        for i in range(num_points):
            eval_ctx.set_valuation_map(points[i])
            res = evaluation.evaluate_expression_raw(self.spec, eval_ctx)
            if (res):
                print('pass: %s' % str(points[i]))
                self.sat_point_idx_set.add(i)
                points_satisfied.add(i)

        if (len(points_satisfied) > 0):
            self.sat_term_list.append((term, points_satisfied))
            if (len(self.sat_point_idx_set) == num_points):
                return True

        return False

    def check_if_any_term_covers_point(self, point):
        self.eval_ctx.set_valuation_map(point)
        point_idx = len(self.points)
        self.add_point(point)
        retval = False

        for i in range(len(self.sat_term_list)):
            (term, set_of_point_indices_satisfied) = self.sat_term_list[i]
            self.eval_ctx.set_interpretation_map([term])
            res = evaluation.evaluate_expression_raw(self.spec, self.eval_ctx)
            if (res):
                self.sat_term_list[i][1].add(point_idx)
                retval = True
        return retval

    def prove_guard(self, guard, term, uncovered_region):
        num_clauses = len(self.neg_clauses)
        print(('Trying to prove guard %s correct for term %s with uncovered region ' +
               '%s') % (_expr_to_str(guard), _expr_to_str(term),
                        _expr_to_str(uncovered_region)))
        self.smt_ctx.set_interpretation_map([term])
        for i in range(num_clauses):
            guard_smt = _expr_to_smt(guard, self.smt_ctx, self.smt_mapping_list[i])
            neg_smt_clause = _expr_to_smt(self.neg_clauses[i], self.smt_ctx)
            smt_uncovered_region = _expr_to_smt(uncovered_region, self.smt_ctx, self.smt_mapping_list[i])
            query = z3.And(smt_uncovered_region, guard_smt, neg_smt_clause, self.smt_ctx.ctx())
            self.solver.push()
            self.solver.add(query)
            sat_res = self.solver.check()
            self.solver.pop()
            if (sat_res == z3.sat):
                model = self.solver.model()
                point = model_to_point(model, self.var_smt_expr_list, self.var_info_list)
                if (self.check_if_any_term_covers_point(point)):
                    return GuardProofStatus.unproved_continue
                else:
                    return GuardProofStatus.unproved_restart
            else:
                continue
        return GuardProofStatus.proved_ok

    def learn_guard(self, term, pos_pt_indices, neg_pt_indices,
                    uncovered_region, pred_generator):
        print('Synthesizing guard for term %s' % _expr_to_str(term))
        print('With positive points: %s' % str([self.points[i] for i in pos_pt_indices]))
        print('With negative points: %s' % str([self.points[i] for i in neg_pt_indices]))
        covered_neg_pts = set()
        covered_pos_pts = set()
        num_pos_pts = len(pos_pt_indices)
        num_neg_pts = len(neg_pt_indices)
        num_points = len(self.points)
        exprs_covering_pos_pts = [set() for x in range(num_points)]
        exprs_covering_neg_pts = [set() for x in range(num_points)]
        eval_ctx = self.eval_ctx

        pred_generator.set_size(3)
        for expr in pred_generator.generate():
            pos_pts_covered_by_expr = set()
            neg_pts_covered_by_expr = set()
            print('Trying guard: %s' % _expr_to_str(expr))
            for i in range(num_points):
                if (i not in pos_pt_indices and i not in neg_pt_indices):
                    continue
                if (i in pos_pt_indices):
                    eval_ctx.set_valuation_map(self.points[i])
                    if(evaluation.evaluate_expression_raw(expr, eval_ctx)):
                        print('Covers positive point %s' % str(self.points[i]))
                        pos_pts_covered_by_expr.add(i)

                if (i in neg_pt_indices):
                    eval_ctx.set_valuation_map(self.points[i])
                    if (evaluation.evaluate_expression_raw(expr, eval_ctx)):
                        print('Covers negative point %s' % str(self.points[i]))
                        neg_pts_covered_by_expr.add(i)

            if (len(pos_pts_covered_by_expr) > 0 and len(neg_pts_covered_by_expr) > 0):
                continue

            if (len(pos_pts_covered_by_expr) > 0):
                for point_idx in pos_pts_covered_by_expr:
                    exprs_covering_pos_pts[point_idx].add(expr)
                    covered_pos_pts.add(point_idx)
            if (len(neg_pts_covered_by_expr) > 0):
                for point_idx in neg_pts_covered_by_expr:
                    exprs_covering_neg_pts[point_idx].add(expr)
                    covered_neg_pts.add(point_idx)

            # termination checks
            if (len(covered_neg_pts) == num_neg_pts):
                witnesses = set()
                for i in range(num_points):
                    if (i in neg_pt_indices):
                        witnesses.add(exprs_covering_neg_pts[i].pop())
                neg_witnesses = [self.syn_ctx.make_function_expr('not', witness)
                                 for witness in witnesses]
                guard = self.syn_ctx.make_ac_function_expr('and', *neg_witnesses)
                prove_stat = self.prove_guard(guard, term, uncovered_region)
                if (prove_stat == GuardProofStatus.proved_ok):
                    return guard
                else:
                    return None

            if (len(covered_pos_pts) == num_pos_pts):
                witnesses = set()
                for i in range(num_points):
                    if (i in pos_pt_indices):
                        witnesses.add(exprs_covering_pos_pts[i].pop())
                guard = self.syn_ctx.make_ac_function_expr('or', *witnesses)
                prove_stat = self.prove_guard(guard, term, uncovered_region)
                if (prove_stat == GuardProofStatus.proved_ok):
                    return guard
                else:
                    return None

    def pop_maximally_covering_sat_term(self, already_covered_points):
        max_new_points_covered = -1
        max_idx = -1
        num_terms = len(self.sat_term_list)
        best_term = None
        best_set_of_point_indices_satisfied = None
        for i in range(num_terms):
            (term, set_of_point_indices_satisfied) = self.sat_term_list[i]
            new_points_covered = set_of_point_indices_satisfied - already_covered_points
            num_new_points_covered = len(new_points_covered)
            if (num_new_points_covered > max_new_points_covered):
                max_idx = i
                max_new_points_covered = num_new_points_covered
                best_term = term
                best_set_of_points_satisfied = new_points_covered

        if (max_idx >= 0):
            print('max_idx = %d' % max_idx)
            self.sat_term_list.remove(self.sat_term_list[max_idx])
            return (best_term,
                    best_set_of_points_satisfied,
                    self.all_point_idx_set -
                    already_covered_points -
                    best_set_of_points_satisfied)
        else:
            return None

    def unify_terms(self, pred_generator):
        num_points = len(self.points)

        print('Trying to unify terms:')
        _format_str = '%s which satisfies points: %s'
        for i in range(len(self.sat_term_list)):
            print(_format_str % (_expr_to_str(self.sat_term_list[i][0]),
                                 str([self.points[j] for j in self.sat_term_list[i][1]])))

        uncovered_region = self.syn_ctx.make_true_expr()
        term_guard_list = []
        expr_to_smt = semantics_types.expression_to_smt
        covered_points = set()
        while (len(covered_points) != num_points):
            cur_term, pos_pts, neg_pts = self.pop_maximally_covering_sat_term(covered_points)
            covered_points = covered_points | pos_pts
            if (len(covered_points) == num_points):
                # last point, no pred required
                term_guard_list.append((cur_term, None))
                return term_guard_list
            # learn a guard for the point
            guard = self.learn_guard(cur_term, pos_pts, neg_pts,
                                     uncovered_region, pred_generator)
            if (guard != None):
                # we've learnt a new guard
                print('Learned guard %s for term %s' % (exprs.expression_to_string(guard),
                                                        exprs.expression_to_string(cur_term)))
                term_guard_list.append((cur_term, guard))
                neg_guard = self.syn_ctx.make_function_expr('not', guard);
                uncovered_region = self.syn_ctx.make_ac_function_expr('and',
                                                                      uncovered_region,
                                                                      neg_guard)
            else:
                # we've added a point that's not covered
                return None

    def prove_solution(self, expr):
        print(('Attempting to prove solution: %s' +
               ' which passes on points %s') % (exprs.expression_to_string(expr),
                                                str(self.points)))
        self.smt_ctx.set_interpretation_map([expr])
        formula = semantics_types.expression_to_smt(self.spec, self.smt_ctx)
        formula = z3.Not(formula)
        print('Formula: %s' % formula)
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
            expr = term_guard_list[num_terms - 1][0]
            for i in reversed(range(num_terms - 1)):
                expr = self.syn_ctx.make_function_expr('ite', term_guard_list[i][1],
                                                       term_guard_list[i][0], expr)
            return expr

    def synthesize_terms_for_points(self, term_generator, size_limit):
        num_points = len(self.points)

        # no points available: any term will do!
        if (num_points == 0):
            term_generator.set_size(1)
            for term in term_generator.generate():
                return [(term, None)]

        # the more interesting case when we actually need
        # to satisfy the spec at some points
        covered_point_idx_set = BitSet(num_points)
        term_signature_set = set()
        for current_size in range(1, size_limit + 1):
            term_generator.set_size(current_size)
            for term in term_generator.generate():



    def solve(self, syn_ctx, term_generator, pred_generator):
        (self.spec, self.var_info_list, self.fun_list,
         self.clauses, self.neg_clauses, self.mapping_list) = syn_ctx.get_synthesis_spec()
        print([str(x) for x in self.var_info_list])

        for mapping in self.mapping_list:
            print([_expr_to_str(x) for x in mapping])

        self.smt_ctx = z3smt.Z3SMTContext()
        self.eval_ctx = evaluation.EvaluationContext()
        self.smt_mapping_list = []
        for mapping in self.mapping_list:
            self.smt_mapping_list.append([_expr_to_smt(x, self.smt_ctx) for x in mapping])

        self.syn_ctx = syn_ctx
        var_expr_list = [exprs.VariableExpression(var_info)
                         for var_info in self.var_info_list]
        self.var_smt_expr_list = [semantics_types.expression_to_smt(expr, self.smt_ctx)
                                  for expr in var_expr_list]
        self.smt_solver = z3.Solver(ctx=self.smt_ctx.ctx())

        max_term_size = 1
        while (True):
            print('Restarting...')
            term_pointidx_set_list = self.synthesize_terms_for_points(term_generator,
                                                                      max_term_size)
            if (term_pointidx_set_list == None):
                # could not synthesize terms, bump up the max term size
                max_term_size += 1


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

    param_exprs = [exprs.FormalParameterExpression(max_fun, exprtypes.IntType(), i)
                   for i in range(num_vars)]
    param_generator = enumerators.LeafGenerator(param_exprs, 'Argument Generator')
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
    return expr


if __name__ == '__main__':
    import time
    import sys
    if (len(sys.argv) < 3):
        print('Usage: %s <num args to max function> <log file name>' % sys.argv[0])
        exit(1)
    max_cardinality = int(sys.argv[1])
    log_file = open(sys.argv[2], 'a')
    start_time = time.clock()
    sol = test_solver_max(max_cardinality)
    end_time = time.clock()
    total_time = end_time - start_time
    log_file.write('max of %d arguments:\n%s\ncomputed in %s seconds\n' % (max_cardinality,
                                                                           exprs.expression_to_string(sol),
                                                                           str(total_time)))



#
# solvers.py ends here
