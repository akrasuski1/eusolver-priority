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
import eusolver
from eusolver import BitSet
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
_is_expr = exprs.is_expression

_term_id_point_id_to_sat = {}
_pred_id_point_id_to_sat = {}

def _cached_evaluate(term_id_point_id_tuple, eval_dict, not_found_factory):
    try:
        return eval_dict[term_id_point_id_tuple]
    except KeyError:
        r = not_found_factory()
        eval_dict[term_id_point_id_tuple] = r
        return r

def _cached_evaluate_term(term_id_point_id_tuple, not_found_factory):
    return _cached_evaluate(term_id_point_id_tuple, _term_id_point_id_to_sat, not_found_factory)

def _cached_evaluate_pred(pred_id_point_id_tuple, not_found_factory):
    return _cached_evaluate(pred_id_point_id_tuple, _pred_id_point_id_to_sat, not_found_factory)

def model_to_point(model, var_smt_expr_list, var_info_list):
    num_vars = len(var_smt_expr_list)
    point = [None] * num_vars
    for i in range(num_vars):
        eval_value = model.evaluate(var_smt_expr_list[i], True)
        if (var_info_list[i].variable_type == exprtypes.BoolType()):
            point[i] = exprs.Value(bool(str(eval_value)), exprtypes.BoolType())
        elif (var_info_list[i].variable_type == exprtypes.IntType()):
            point[i] = exprs.Value(int(str(eval_value)), exprtypes.IntType())
        elif (var_info_list[i].variable_type.type_code == exprtypes.TypeCodes.bit_vector_type):
            point[i] = expr.Value(int(str(eval_value)), var_info_list.variable_type)
        else:
            raise basetypes.UnhandledCaseError('solvers.In model_to_point')
    return tuple(point)

def _decision_tree_to_guard_term_list_internal(decision_tree, pred_list, term_list,
                                               syn_ctx, retval, guard_stack):
    if (decision_tree.is_leaf()):
        retval.append((syn_ctx.make_ac_function_expr('and', *guard_stack),
                       term_list[decision_tree.get_label_id()]))
    else:
        # split node
        attr_id = decision_tree.get_split_attribute_id()
        guard_stack.append(pred_list[attr_id])
        _decision_tree_to_guard_term_list_internal(decision_tree.get_positive_child(),
                                                   pred_list, term_list, syn_ctx,
                                                   retval, guard_stack)
        guard_stack.pop()
        guard_stack.append(syn_ctx.make_function_expr('not', pred_list[attr_id]))
        _decision_tree_to_guard_term_list_internal(decision_tree.get_negative_child(),
                                                   pred_list, term_list, syn_ctx,
                                                   retval, guard_stack)
        guard_stack.pop()

def _decision_tree_to_expr_internal(decision_tree, pred_list, term_list, syn_ctx):
    if (decision_tree.is_leaf()):
        return term_list[decision_tree.get_label_id()]
    else:
        if_term = _decision_tree_to_expr_internal(decision_tree.get_positive_child(),
                                                  pred_list, term_list, syn_ctx)
        else_term = _decision_tree_to_expr_internal(decision_tree.get_negative_child(),
                                                    pred_list, term_list, syn_ctx)
        return syn_ctx.make_function_expr('ite', pred_list[decision_tree.get_split_attribute_id()],
                                          if_term, else_term)

def decision_tree_to_guard_term_list(decision_tree, pred_list, term_list, syn_ctx):
    retval = []
    _decision_tree_to_guard_term_list_internal(decision_tree, pred_list,
                                               term_list, syn_ctx, retval, [])
    return retval

def guard_term_list_to_expr(guard_term_list, syn_ctx):
    num_segments = len(guard_term_list)
    retval = guard_term_list[num_segments - 1][1]
    for i in reversed(range(num_segments - 1)):
        retval = syn_ctx.make_function_expr('ite', guard_term_list[i][0],
                                            guard_term_list[i][1], retval)
    return retval

# def decision_tree_to_expr(decision_tree, pred_list, term_list, syn_ctx):
#     guard_term_list = decision_tree_to_guard_term_list(decision_tree,
#                                                        pred_list,
#                                                        term_list,
#                                                        syn_ctx)
#     return guard_term_list_to_expr(guard_term_list, syn_ctx)

def decision_tree_to_expr(decision_tree, pred_list, term_list, syn_ctx):
    return _decision_tree_to_expr_internal(decision_tree, pred_list, term_list, syn_ctx)


class DuplicatePointException(Exception):
    def __init__(self, point):
        self.point = point

    def __str__(self):
        return 'Duplicate Point: %s' % str(self.point)


class TermSolver(object):
    def __init__(self, spec, term_generator):
        self.spec = spec
        self.term_generator = term_generator

    def _compute_term_signature(self, term, spec, eval_ctx):
        points = self.points
        num_points = len(points)
        retval = self.signature_factory()
        eval_ctx.set_interpretation_map([term])

        for i in range(num_points):
            eval_ctx.set_valuation_map(points[i])
            res = evaluation.evaluate_term_raw(spec, eval_ctx)
            if (res):
                retval.add(i)
        return retval

    def _trivial_solve(self):
        for term in self.term_generator.generate():
            retval = (True, {None : term})
            # print('Term Solve complete!')
            # print({str(x) : _expr_to_str(y) for (x, y) in retval[1].items()})
            return retval

        # print('Term Solve failed!')
        return (False, None)

    def continue_solve(self):
        self.current_term_size += 1
        generator = self.term_generator
        generator.set_size(self.current_term_size)

        num_points = self.num_points
        if (num_points == 0):
            return self._trivial_solve()

        signature_to_term = self.signature_to_term
        spec_satisfied_at_points = self.spec_satisfied_at_points

        for term in generator.generate():
            # print('Generated term %s' % _expr_to_str(term))
            sig = self._compute_term_signature(term, self.spec, self.eval_ctx)
            if (sig in signature_to_term or sig.is_empty()):
                continue
            signature_to_term[sig] = term
            spec_satisfied_at_points |= sig
            # print('Cumulative specification satisfaction: %s' % str(spec_satisfied_at_points))
            if (spec_satisfied_at_points.is_full()):
                # print('Term Solve complete!')
                # print({str(x) : _expr_to_str(y) for (x, y) in signature_to_term.items()})
                return (True, signature_to_term)

        return (False, None)


    def solve(self, term_size, points):
        global _term_id_point_id_to_sat
        global _pred_id_point_id_to_sat

        _term_id_point_id_to_sat = {}
        _pred_id_point_id_to_sat = {}

        self.points = points
        self.signature_to_term = {}
        self.num_points = len(points)
        num_points = self.num_points
        if (num_points > 0):
            self.signature_factory = BitSet.make_factory(num_points)
            self.spec_satisfied_at_points = self.signature_factory()
        else:
            self.signature_factory = None
            self.spec_satisfied_at_points = None

        self.current_term_size = term_size - 1
        self.eval_ctx = evaluation.EvaluationContext()

        return self.continue_solve()

class Unifier(object):
    def __init__(self, syn_ctx, points, pred_generator):
        self.pred_generator = pred_generator
        self.syn_ctx = syn_ctx
        self.true_expr = exprs.ConstantExpression(exprs.Value(True, exprtypes.BoolType()))
        self.false_expr = exprs.ConstantExpression(exprs.Value(False, exprtypes.BoolType()))
        spec_tuple = syn_ctx.get_synthesis_spec()
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = spec_tuple
        self.var_list = var_list
        self.canon_spec = canon_spec
        self.clauses = clauses
        self.neg_clauses = neg_clauses
        self.intro_vars = intro_vars
        self.points = points
        self.eval_ctx = evaluation.EvaluationContext()

    def _compute_pred_signature(self, pred):
        points = self.points
        num_points = len(points)
        retval = self.signature_factory()
        intro_vars = self.intro_vars
        eval_ctx = self.eval_ctx

        for i in range(num_points):
            eval_ctx.set_valuation_map(points[i])
            res = evaluation.evaluate_pred_raw(pred, eval_ctx)
            if (res):
                retval.add(i)
        return retval

    def _verify_expr(self, term):
        smt_ctx = z3smt.Z3SMTContext()
        syn_ctx = self.syn_ctx
        smt_ctx.set_interpretation_map([term])
        neg_canon_spec = self.syn_ctx.make_function_expr('not', self.canon_spec)
        cnstr = _expr_to_smt(neg_canon_spec, smt_ctx)
        smt_solver = z3.Solver(ctx=smt_ctx.ctx())
        smt_solver.add(cnstr)
        r = smt_solver.check()
        var_info_list = self.var_list
        var_expr_list = [exprs.VariableExpression(e) for e in var_info_list]
        var_smt_expr_list = [_expr_to_smt(e, smt_ctx) for e in var_expr_list]
        if (r == z3.sat):
            model = smt_solver.model()
            return model_to_point(model, var_smt_expr_list, var_info_list)
        else:
            return term

    def _try_trivial_unification(self, signature_to_term):
        # we can trivially unify if there exists a term
        # which satisfies the spec at all points
        trivial_term = None
        for (sig, term) in signature_to_term.items():
            if (sig is None or sig.is_full()):
                trivial_term = term
                break

        if (trivial_term == None):
            return None

        # try to verify the trivial term
        return self._verify_expr(trivial_term)

    def _try_decision_tree_learning(self, signature_to_term, signature_to_pred):
        term_list = []
        term_sig_list = []
        pred_list = []
        pred_sig_list = []
        for (term_sig, term) in signature_to_term.items():
            term_list.append(term)
            term_sig_list.append(term_sig)
        for (pred_sig, pred) in signature_to_pred.items():
            pred_list.append(pred)
            pred_sig_list.append(pred_sig)

        # print('pred_sig_list: %s' % [str(x) for x in pred_sig_list])
        # print('pred_list: %s' % [_expr_to_str(x) for x in pred_list], flush=True)
        # print('term_sig_list: %s' % [str(x) for x in term_sig_list], flush=True)
        dt = eusolver.eus_learn_decision_tree_for_ml_data(pred_sig_list,
                                                          term_sig_list)
        # print('Obtained decision tree:\n%s' % str(dt))
        if (dt == None):
            return None
        else:
            return (term_list, term_sig_list, pred_list, pred_sig_list, dt)

    def unify(self, signature_to_term):
        triv = self._try_trivial_unification(signature_to_term)
        if (triv != None):
            return triv

        num_points = len(self.points)
        self.signature_factory = BitSet.make_factory(num_points)
        pred_size = 0
        # cannot be trivially unified
        pred_generator = self.pred_generator
        signature_to_pred = {}
        while (True):
            pred_size += 1
            pred_generator.set_size(pred_size)
            new_preds_generated = False
            for pred in pred_generator.generate():
                sig = self._compute_pred_signature(pred)
                # if the predicate evaluates universally to true or false
                # at all points, then it isn't worth considering it.
                if (not sig.is_empty() and not sig.is_full() and sig not in signature_to_pred):
                    # print('Generated pred %s' % _expr_to_str(pred))
                    signature_to_pred[sig] = pred
                    new_preds_generated = True

            if (not new_preds_generated):
                # print(('Unifier.unify(): no new predicates generated at size %d, ' +
                #       'continuing...') % pred_size)
                continue

            # we've generated a bunch of (new) predicates
            # try to learn a decision tree
            # print('Unifier.unify(): Attempting to learn decision tree...', flush=True)
            dt_tuple = self._try_decision_tree_learning(signature_to_term,
                                                        signature_to_pred)
            if (dt_tuple == None):
                # print('Unifier.unify(): Could not learn decision tree!')
                continue
            # print('Unifier.unify(): Learned a decision tree!')
            (term_list, term_sig_list, pred_list, pred_sig_list, dt) = dt_tuple
            expr = decision_tree_to_expr(dt, pred_list, term_list, self.syn_ctx)
            # print('Obtained expr: %s' % _expr_to_str(expr))
            return self._verify_expr(expr)

class Solver(object):
    def __init__(self, syn_ctx):
        self.syn_ctx = syn_ctx
        self.spec_tuple = syn_ctx.get_synthesis_spec()
        self.reset()

    def reset(self):
        self.spec = None
        self.eval_ctx = evaluation.EvaluationContext()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.points = []
        self.point_set = set()

    def add_point(self, point):
        if (point in self.point_set):
            raise DuplicatePointException(point)
        self.point_set.add(point)
        self.points.append(point)

    def add_point_from_model(self, model):
        point = model_to_point

    def add_specification(self, specification):
        syn_ctx = self.syn_ctx
        if (self.spec == None):
            self.spec = specification
        else:
            self.spec = syn_ctx.make_ac_function_expr('and', self.spec,
                                                      specification)

    def solve(self, term_generator, pred_generator):
        act_spec, var_list, uf_list, clauses, neg_clauses, canon_spec, intro_vars = self.spec_tuple
        self.var_info_list = var_list
        var_expr_list = [exprs.VariableExpression(x) for x in var_list]
        self.var_smt_expr_list = [_expr_to_smt(x, self.smt_ctx) for x in var_expr_list]

        # print('Solver.solve(), variable infos:\n%s' % [str(x) for x in self.var_info_list])

        while (True):
            term_solver = TermSolver(canon_spec, term_generator)
            # iterate until we have terms that are "sufficient"
            (terms_done, sig_to_term) = term_solver.solve(1, self.points)
            while (not terms_done):
                (terms_done, sig_to_term) = term_solver.continue_solve()
            # we now have a sufficient set of terms
            unifier = Unifier(self.syn_ctx, self.points, pred_generator)
            r = unifier.unify(sig_to_term)
            if (exprs.is_expression(r)):
                return r
            else:
                # this is a counterexample
                self.add_point(r)
                # print('Solver: Added point %s' % str([c.value_object for c in r]))
                continue

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
                                            syn_ctx.make_function_expr('or', *eq_constraints))
    syn_ctx.assert_spec(constraint)

    solver = Solver(syn_ctx)
    expr = solver.solve(term_generator, pred_generator)
    return (expr, len(solver.points))


if __name__ == '__main__':
    import time
    import sys
    if (len(sys.argv) < 3):
        print('Usage: %s <num args to max function> <log file name>' % sys.argv[0])
        exit(1)
    max_cardinality = int(sys.argv[1])
    log_file = open(sys.argv[2], 'a')
    start_time = time.clock()
    (sol, npoints) = test_solver_max(max_cardinality)
    end_time = time.clock()
    total_time = end_time - start_time
    log_file.write('max of %d arguments:\n%s\ncomputed in %s seconds\n' % (max_cardinality,
                                                                           exprs.expression_to_string(sol),
                                                                           str(total_time)))
    log_file.write('Added %d counterexample points in total\n' % npoints)



#
# solvers.py ends here
