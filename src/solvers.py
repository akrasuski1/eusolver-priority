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
# from semantics_bv import BitVector
from bitvectors import BitVector
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
import enumerators

import signal
import resource

EUSOLVER_MEMORY_LIMIT = (1 << 31)

_expr_to_str = exprs.expression_to_string
_expr_to_smt = semantics_types.expression_to_smt
_is_expr = exprs.is_expression
_get_expr_with_id = exprs.get_expr_with_id

def _point_list_to_str(points):
    retval = ''
    for point in points:
        retval += str([x.value_object for x in point])
        retval += '\n'
    return retval

def _guard_term_list_to_str(guard_term_list):
    retval = ''
    for (guard, term_list) in guard_term_list:
        retval += _expr_to_str(guard)
        retval += ' ->\n'
        for term in term_list:
            retval += '        '
            retval += _expr_to_str(term)
            retval += '\n'
    return retval

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
            # point[i] = exprs.Value(int(str(eval_value)), var_info_list.variable_type)
            # Z3 always prints unsigned integers?
            point[i] = exprs.Value(BitVector(int(str(eval_value)),
                                             var_info_list[i].variable_type.size),
                                   var_info_list[i].variable_type)
        else:
            raise basetypes.UnhandledCaseError('solvers.In model_to_point')
    return tuple(point)

def _decision_tree_to_guard_term_list_internal(decision_tree, pred_list, term_list,
                                               syn_ctx, retval, guard_stack):
    if (decision_tree.is_leaf()):
        retval.append((syn_ctx.make_ac_function_expr('and', *guard_stack),
                       [term_list[x] for x in decision_tree.get_all_label_ids()]))
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

# The leaves of the decision trees are listed left to right
def decision_tree_to_guard_term_list(decision_tree, pred_list, term_list, syn_ctx):
    retval = []
    _decision_tree_to_guard_term_list_internal(decision_tree, pred_list,
                                               term_list, syn_ctx, retval, [])
    return retval

def _decision_tree_to_expr_internal(decision_tree, pred_list, syn_ctx, selected_leaf_terms):
    if (decision_tree.is_leaf()):
        return selected_leaf_terms.pop(0)
    else:
        if_term = _decision_tree_to_expr_internal(decision_tree.get_positive_child(),
                                                  pred_list, syn_ctx, selected_leaf_terms)
        else_term = _decision_tree_to_expr_internal(decision_tree.get_negative_child(),
                                                    pred_list, syn_ctx, selected_leaf_terms)
        return syn_ctx.make_function_expr('ite', pred_list[decision_tree.get_split_attribute_id()],
                                          if_term, else_term)

# We use the fact that the guard_term_list lists leaves left to right
def decision_tree_to_expr(decision_tree, pred_list, syn_ctx, selected_leaf_terms):
    return _decision_tree_to_expr_internal(decision_tree, pred_list, syn_ctx, selected_leaf_terms)

def guard_term_list_to_expr(guard_term_list, syn_ctx):
    num_branches = len(guard_term_list)
    retval = guard_term_list[num_branches-1][1]
    for i in reversed(range(0, num_branches-1)):
        retval = syn_ctx.make_function_expr('ite', guard_term_list[i][0],
                                            guard_term_list[i][1], retval)
    return retval

def check_term_sufficiency(sig_to_term, num_points):
    accumulator = BitSet(num_points)
    for (sig, term) in sig_to_term.items():
        accumulator |= sig
    return (accumulator.is_full())

def check_one_term_sufficiency(sig_to_term, num_points):
    for (sig, term) in sig_to_term.items():
        if sig.is_full():
            return True
    return False

def get_decision_tree_size(dt):
    if (dt.is_leaf()):
        return 1
    else:
        return (1 + get_decision_tree_size(dt.get_positive_child()) +
                get_decision_tree_size(dt.get_negative_child()))


class DuplicatePointException(Exception):
    def __init__(self, point):
        self.point = point

    def __str__(self):
        return 'Duplicate Point %s' % str([self.point[i].value_object
                                           for i in range(len(self.point))])


class TermSolver(object):
    def __init__(self, spec, term_generator, max_term_size = 1024):
        self.spec = spec
        self.term_generator = term_generator
        self.points = []
        self.max_term_size = max_term_size
        self.eval_ctx = evaluation.EvaluationContext()
        self.eval_cache = {}
        self.current_largest_term_size = 0
        self.signature_to_term = {}
        self.bunch_generator = None

    def _trivial_solve(self):
        term_size = 1
        while (term_size <= self.max_term_size):
            self.term_generator.set_size(term_size)
            for term in self.term_generator.generate():
                self.signature_to_term = {None : term}
                return True
            term_size += 1

        return False

    def add_points(self, new_points):
        points = self.points
        points.extend(new_points)
        self.signature_factory = BitSet.make_factory(len(points))
        self._do_complete_sig_to_term()

    def _compute_term_signature(self, term):
        points = self.points
        num_points = len(points)
        retval = self.signature_factory()
        eval_ctx = self.eval_ctx
        eval_ctx.set_interpretation_map([term])
        spec = self.spec
        eval_cache = self.eval_cache

        try:
            r = eval_cache[term.expr_id]
            retval.copy_in(r)
            num_old_points = r.size_of_universe()
            num_new_points = retval.size_of_universe()
            for i in range(num_old_points, num_new_points):
                eval_ctx.set_valuation_map(points[i])
                # print(_expr_to_str(term), points[i], evaluation.evaluate_expression_raw(spec, eval_ctx))
                if (evaluation.evaluate_expression_raw(spec, eval_ctx)):
                    retval.add(i)
            if (num_new_points > num_old_points):
                eval_cache[term.expr_id] = retval
            return retval

        except KeyError:
            # need to actually evaluate at every point :-(
            for i in range(num_points):
                eval_ctx.set_valuation_map(points[i])
                # print(_expr_to_str(term), points[i], _expr_to_str(spec), evaluation.evaluate_expression_raw(spec, eval_ctx))
                if (evaluation.evaluate_expression_raw(spec, eval_ctx)):
                    retval.add(i)
            eval_cache[term.expr_id] = retval
            return retval

    def _do_complete_sig_to_term(self):
        old_sig_to_term = self.signature_to_term
        new_sig_to_term = {}

        for sig, term in old_sig_to_term.items():
            new_sig = self._compute_term_signature(term)
            if not new_sig.is_empty():
                new_sig_to_term[new_sig] = term

        self.signature_to_term = new_sig_to_term

    def extend_sig_to_term_map(self):
        points = self.points
        num_points = len(points)
        signature_to_term = self.signature_to_term

        assert (num_points > 0)

        bunch_generator_state = self.bunch_generator_state
        try:
            bunch = next(bunch_generator_state)
        except StopIteration:
            return False

        for term in bunch:
            # print('Generated Term: %s' % _expr_to_str(term))
            term = _get_expr_with_id(term, self.monotonic_expr_id)
            self.monotonic_expr_id += 1
            sig = self._compute_term_signature(term)
            # print('Signature:', sig)

            if (sig in signature_to_term or sig.is_empty()):
                continue

            signature_to_term[sig] = term
        return True

    def get_largest_term_size_enumerated(self):
        if self.bunch_generator is None:
            return self.current_largest_term_size
        return max(self.current_largest_term_size,
                self.bunch_generator.current_object_size)

    def solve(self, one_term_coverage=False):
        num_points = len(self.points)
        signature_to_term = self.signature_to_term

        if one_term_coverage:
            stopping_condition = check_one_term_sufficiency
        else:
            stopping_condition = check_term_sufficiency

        if (num_points == 0): # No points, any term will do
            return self._trivial_solve()
        elif stopping_condition(signature_to_term, num_points): # Old terms will do
            return True

        # Book keeping
        if self.bunch_generator is not None:
            self.current_largest_term_size = max(self.current_largest_term_size,
                    self.bunch_generator.current_object_size)

        self.bunch_generator = enumerators.BunchedGenerator(self.term_generator,
                                                            self.max_term_size)
        self.bunch_generator_state = self.bunch_generator.generate()

        self.monotonic_expr_id = 0

        while (not stopping_condition(signature_to_term, num_points)):
            success = self.extend_sig_to_term_map()
            if not success:
                return False
        return True

class Unifier(object):
    def __init__(self, syn_ctx, smt_ctx, pred_generator, term_solver, max_pred_size = 1024):
        self.pred_generator = pred_generator
        self.term_solver = term_solver
        self.syn_ctx = syn_ctx
        self.true_expr = exprs.ConstantExpression(exprs.Value(True, exprtypes.BoolType()))
        self.false_expr = exprs.ConstantExpression(exprs.Value(False, exprtypes.BoolType()))
        spec_tuple = syn_ctx.get_synthesis_spec()
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = spec_tuple

        self.smt_ctx = smt_ctx
        self.smt_solver = z3.Solver(ctx=self.smt_ctx.ctx())

        self.var_info_list = var_list
        self.var_expr_list = [exprs.VariableExpression(x) for x in self.var_info_list]
        self.var_smt_expr_list = [_expr_to_smt(x, self.smt_ctx) for x in self.var_expr_list]

        self.canon_spec = canon_spec
        self.clauses = clauses
        self.neg_clauses = neg_clauses
        self.intro_vars = intro_vars
        self.smt_intro_vars = [_expr_to_smt(x, self.smt_ctx) for x in self.intro_vars]
        self.points = []
        self.eval_ctx = evaluation.EvaluationContext()
        self.eval_cache = {}
        self.max_pred_size = max_pred_size

        fun_app = syn_ctx.make_function_expr(fun_list[0], *intro_vars)
        fun_app_subst_var = syn_ctx.make_variable_expr(fun_list[0].range_type, '__output__')
        self.outvar_cnstr = syn_ctx.make_function_expr('eq', fun_app_subst_var, fun_app)
        canon_spec_with_outvar = exprs.substitute(canon_spec, fun_app, fun_app_subst_var)
        neg_canon_spec_with_outvar = syn_ctx.make_function_expr('not', canon_spec_with_outvar)
        frozen_smt_cnstr = _expr_to_smt(neg_canon_spec_with_outvar, self.smt_ctx)
        self.smt_solver.add(frozen_smt_cnstr)
        self.signature_to_pred = {}

    def add_points(self, new_points):
        points = self.points
        self.points.extend(new_points)
        self.signature_factory = BitSet.make_factory(len(points))
        self._do_complete_sig_to_pred()


    def _do_complete_sig_to_pred(self):
        old_sig_to_pred = self.signature_to_pred
        new_sig_to_pred = {}

        for sig, pred in old_sig_to_pred.items():
            new_sig = self._compute_pred_signature(pred)
            if not new_sig.is_empty():
                new_sig_to_pred[new_sig] = pred

        self.signature_to_pred = new_sig_to_pred


    def _compute_pred_signature(self, pred):
        points = self.points;
        num_points = len(points)
        retval = self.signature_factory()
        eval_ctx = self.eval_ctx
        eval_cache = self.eval_cache;

        try:
            r = eval_cache[pred.expr_id]
            retval.copy_in(r)
            # print('computing signature of predicate: %s' % _expr_to_str(pred))
            # print('r      = %s' % str(r))
            num_old_points = r.size_of_universe()
            num_new_points = retval.size_of_universe()
            for i in range(num_old_points, num_new_points):
                eval_ctx.set_valuation_map(points[i])
                if (evaluation.evaluate_expression_raw(pred, eval_ctx)):
                    retval.add(i)
            # print('retval = %s' % str(retval))
            if (num_new_points > num_old_points):
                eval_cache[pred.expr_id] = retval
            # return retval

        except KeyError:
            # need to actually evaluate
            for i in range(num_points):
                eval_ctx.set_valuation_map(points[i])
                if (evaluation.evaluate_expression_raw(pred, eval_ctx)):
                    retval.add(i)
            eval_cache[pred.expr_id] = retval
            # return retval
        # print(_expr_to_str(pred), " has signature ", retval, " on ", [ str(x[0].value_object) for x in points])
        return retval


    def _verify_expr(self, term):
        smt_ctx = self.smt_ctx
        smt_solver = self.smt_solver

        smt_ctx.set_interpretation_map([term])
        eq_cnstr = _expr_to_smt(self.outvar_cnstr, smt_ctx)
        smt_solver.push()
        smt_solver.add(eq_cnstr)
        r = smt_solver.check()
        smt_solver.pop()

        if (r == z3.sat):
            cex_point = model_to_point(smt_solver.model(),
                                       self.var_smt_expr_list,
                                       self.var_info_list)
            return [cex_point]
        else:
            return term

    def _verify_guard_term_list(self, guard_term_list, dt_tuple):
        smt_ctx = self.smt_ctx
        smt_solver = self.smt_solver
        intro_vars = self.smt_intro_vars
        cex_points = []
        selected_leaf_terms = []

        at_least_one_branch_failed = False
        for (pred, term_list) in guard_term_list:
            smt_solver.push()
            smt_pred = _expr_to_smt(pred, smt_ctx, intro_vars)
            # print('SMT guard')
            # print(smt_pred)
            smt_solver.add(smt_pred)
            all_terms_failed = True
            for term in term_list:
                # print('Verifying term')
                # print(_expr_to_str(term))
                # print('with guard')
                # print(_expr_to_str(pred))
                smt_ctx.set_interpretation_map([term])
                eq_cnstr = _expr_to_smt(self.outvar_cnstr, smt_ctx);
                # print('SMT constraint')
                # print(eq_cnstr)
                smt_solver.push()
                smt_solver.add(eq_cnstr)
                r = smt_solver.check()
                smt_solver.pop()
                if (r == z3.sat):
                    cex_points.append(model_to_point(smt_solver.model(),
                                                     self.var_smt_expr_list,
                                                     self.var_info_list))
                else:
                    all_terms_failed = False
                    selected_leaf_terms.append(term)
                    break

            if (all_terms_failed):
                at_least_one_branch_failed = True
            smt_solver.pop()

        if (at_least_one_branch_failed):
            retval = list(set(cex_points))
            retval.sort()
            return retval
        else:
            (term_list, term_sig_list, pred_list, pred_sig_list, dt) = dt_tuple
            e = decision_tree_to_expr(dt, pred_list, self.syn_ctx, selected_leaf_terms)
            return e


    def _try_trivial_unification(self):
        # we can trivially unify if there exists a term
        # which satisfies the spec at all points
        trivial_term = None
        for (sig, term) in self.term_solver.signature_to_term.items():
            if (sig is None or sig.is_full()):
                trivial_term = term
                break

        if (trivial_term == None):
            return None

        # try to verify the trivial term
        return self._verify_expr(trivial_term)

    def _try_decision_tree_learning(self):
        term_list = []
        term_sig_list = []
        pred_list = []
        pred_sig_list = []
        for (term_sig, term) in self.term_solver.signature_to_term.items():
            term_list.append(term)
            term_sig_list.append(term_sig)
        for (pred_sig, pred) in self.signature_to_pred.items():
            pred_list.append(pred)
            pred_sig_list.append(pred_sig)

        # print('Calling native decision tree learner...')
        # print('pred_sig_list: %s' % [str(x) for x in pred_sig_list])
        # print('term_sig_list: %s' % [str(x) for x in term_sig_list], flush=True)
        # print('pred_list: %s' % [_expr_to_str(x) for x in pred_list], flush=True)
        # print('term_list: %s' % [_expr_to_str(x) for x in term_list], flush=True)
        # print('points   :\n%s' % _point_list_to_str(self.points), flush=True)
        dt = eusolver.eus_learn_decision_tree_for_ml_data(pred_sig_list,
                                                          term_sig_list)
        # print('Done!', flush=True)
        # print(dt, flush=True)
        # print('Obtained decision tree:\n%s' % str(dt))
        if (dt == None):
            return None
        else:
            return (term_list, term_sig_list, pred_list, pred_sig_list, dt)

    """returns/yields one of:
    1. (expression, DT size, num terms, num preds, max term size, max pred size)
    2. [list of counterexample points]
    3. None, in case of exhaustion of terms/preds
    """
    def unify(self):
        term_solver = self.term_solver
        signature_to_term = term_solver.signature_to_term
        signature_to_pred = self.signature_to_pred
        # print('Unifying:')
        # print([ (str(sig), sig is None or sig.is_full(), _expr_to_str(term)) for sig,term in term_solver.signature_to_term.items()])
        # print(signature_to_pred)
        triv = self._try_trivial_unification()
        if (triv != None):
            # print('Unifier: returning %s' % str(triv))
            if (_is_expr(triv)):
                yield (triv, 0, len(signature_to_term), 0,
                       term_solver.get_largest_term_size_enumerated(), 0)
            else:
                yield triv
            return

        # cannot be trivially unified
        num_points = len(self.points)
        self.signature_factory = BitSet.make_factory(num_points)
        max_pred_size = self.max_pred_size
        generator = self.pred_generator
        monotonic_pred_id = 0
        bunch_generator = enumerators.BunchedGenerator(generator, max_pred_size)

        for bunch in bunch_generator.generate():
            new_preds_generated = False
            for pred in bunch:
                # print('Generated pred: %s' % _expr_to_str(pred), flush=True)
                pred = _get_expr_with_id(pred, monotonic_pred_id)
                monotonic_pred_id += 1

                sig = self._compute_pred_signature(pred)
                # print('Generated predicate %s with sig %s' % (_expr_to_str(pred), str(sig)))
                # if the predicate evaluates universally to true or false
                # at all points, then it isn't worth considering it.
                if (not sig.is_empty() and not sig.is_full() and sig not in signature_to_pred):
                    # print('Generated pred %s' % _expr_to_str(pred))
                    # print('predicate was new!')
                    signature_to_pred[sig] = pred
                    new_preds_generated = True
                else:
                    # print('predicate was already seen!')
                    continue

            if (not new_preds_generated):
                # print(('Unifier.unify(): no new predicates generated at size %d, ' +
                #       'continuing...') % pred_size)
                continue

            # we've generated a bunch of (new) predicates
            # try to learn a decision tree
            # print('Unifier.unify(): Attempting to learn decision tree...', flush=True)
            dt_tuple = self._try_decision_tree_learning()
            if (dt_tuple == None):
                # print('Unifier.unify(): Could not learn decision tree!')
                success = term_solver.extend_sig_to_term_map()
                # if not success:
                #     yield None
                #     return

                continue

            # print('Unifier.unify(): Learned a decision tree!')
            (term_list, term_sig_list, pred_list, pred_sig_list, dt) = dt_tuple
            guard_term_list = decision_tree_to_guard_term_list(dt, pred_list,
                                                               term_list,
                                                               self.syn_ctx)
            # print('Guard term list:\n%s' % _guard_term_list_to_str(guard_term_list))
            # print('Unifier: enumerated %d predicates!' % monotonic_pred_id)
            # return self._verify_expr(expr)
            sol_or_cex = self._verify_guard_term_list(guard_term_list, dt_tuple)
            if (_is_expr(sol_or_cex)):
                yield (sol_or_cex, get_decision_tree_size(dt),
                       len(signature_to_term), len(signature_to_pred),
                       term_solver.get_largest_term_size_enumerated(),
                       bunch_generator.current_object_size)

                success = term_solver.extend_sig_to_term_map()
                # if not success:
                #     return
                continue
            else:
                # this a counterexample. stop yielding after this
                yield sol_or_cex
                return
        return

class Solver(object):
    def __init__(self, syn_ctx):
        self.syn_ctx = syn_ctx
        self.spec_tuple = syn_ctx.get_synthesis_spec()
        self.reset()
        self.term_solver_time = 0
        self.unifier_time = 0

    def reset(self):
        self.spec = None
        self.eval_ctx = evaluation.EvaluationContext()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.points = []
        self.point_set = set()

    def add_points(self, points):
        for point in points:
            # print('Solver: Added point %s' % str([str(c.value_object) for c in point]))
            # print([ (str(x[0].value_object), hash(x[0].value_object)) for x in self.point_set ])
            if (point in self.point_set):
                raise DuplicatePointException(point)
            self.point_set.add(point)
            self.points.append(point)

    def add_specification(self, specification):
        syn_ctx = self.syn_ctx
        if (self.spec == None):
            self.spec = specification
        else:
            self.spec = syn_ctx.make_ac_function_expr('and', self.spec,
                                                      specification)

    def solve(self, term_generator, pred_generator, divide_and_conquer=True):
        import time
        act_spec, var_list, uf_list, clauses, neg_clauses, canon_spec, intro_vars = self.spec_tuple
        # print('Solver.solve(), variable infos:\n%s' % [str(x) for x in self.var_info_list])
        term_solver = TermSolver(canon_spec, term_generator)
        unifier = Unifier(self.syn_ctx, self.smt_ctx, pred_generator, term_solver)
        time_origin = time.clock()

        while (True):
            # iterate until we have terms that are "sufficient"
            success = term_solver.solve(one_term_coverage=not divide_and_conquer)
            if not success:
                return None
            # we now have a sufficient set of terms
            # print('Term solve complete!')
            # print([ _expr_to_str(term) for sig,term in term_solver.signature_to_term.items()])
            unifier_state = unifier.unify()

            while (True):
                r = next(unifier_state)
                # print('Unification Complete!')
                # print([ _expr_to_str(pred) for sig,pred in unifier.signature_to_pred.items()])
                if (isinstance(r, tuple)):
                    (sol, dt_size, num_t, num_p, max_t, max_p) = r
                    solution_found_at = time.clock() - time_origin
                    yield (sol, dt_size, num_t, num_p, max_t, max_p,
                           len(self.points), solution_found_at)

                elif (isinstance(r, list)):
                    # this is a set of counterexamples
                    # print('Solver: Adding %d points' % len(r))
                    # for p in r:
                        # print('\t', p)
                    term_solver.add_points(r) # Term solver can add all points at once
                    unifier.add_points(r)
                    self.add_points(r)
                    break
                else:
                    return None


########################################################################
# TEST CASES
########################################################################
def _do_solve(solver, term_generator, pred_generator, run_anytime_version):
    reported_expr_string_set = set()
    for sol_tuple in solver.solve(term_generator, pred_generator):
        (sol, dt_size, num_t, num_p, max_t, max_p, card_p, sol_time) = sol_tuple
        sol_str = _expr_to_str(sol)
        if (sol_str in reported_expr_string_set):
            continue

        reported_expr_string_set.add(sol_str)

        print('----------------------------------------------')
        print('Solution Size                : %d' % exprs.get_expression_size(sol))
        print('Solution Time from start (s) : %f' % sol_time)
        print('DT Size                      : %d' % dt_size)
        print('Num Dist. Terms Enumerated   : %d' % num_t)
        print('Num Dist. Preds Enumerated   : %d' % num_p)
        print('Max Term Size Enumerated     : %d' % max_t)
        print('Max Pred Size Enumerated     : %d' % max_p)
        print('Num Points                   : %d' % card_p)
        print('Solution                     : %s' % _expr_to_str(sol), flush=True)
        print('----------------------------------------------')
        if (not run_anytime_version):
            return sol


def test_solver_max(num_vars, run_anytime_version):
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
    _do_solve(solver, term_generator, pred_generator, run_anytime_version)

def test_solver_icfp(benchmark_name, run_anytime_version):
    import synthesis_context
    import semantics_core
    import semantics_bv
    import enumerators
    import icfp_helpers

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_bv.BVInstantiator(64))
    synth_fun = syn_ctx.make_unknown_function('f', [exprtypes.BitVectorType(64)],
                                            exprtypes.BitVectorType(64))

    term_generator, pred_generator = icfp_helpers.icfp_grammar(syn_ctx, synth_fun, full_grammer=True)
    valuations = icfp_helpers.get_icfp_valuations(benchmark_name)
    constraint = icfp_helpers.points_to_spec(syn_ctx, synth_fun, valuations) 

    syn_ctx.assert_spec(constraint)

    solver = Solver(syn_ctx)
    sol = _do_solve(solver, term_generator, pred_generator, run_anytime_version)
    icfp_helpers.verify_solution(sol, valuations, solver.eval_ctx)

def die():
    print('Usage: %s [--anytime] <timeout in seconds> max <num args to max function>' % sys.argv[0])
    print('Usage: %s [--anytime] <timeout in seconds> icfp <benchmark file>' % sys.argv[0])
    exit(1)

def _timeout_handler(signum, frame):
    if (signum != -1):
        print('[solvers.main]: Timed out!')
        print('[solvers.main]: Trying to exit gracefully...')
        sys.exit(1)
    else:
        print('[solvers.main]: Exiting gracefully...')
        sys.exit(1)

def _memout_checker(signum, frame):
    rusage = resource.getrusage(resource.RUSAGE_SELF)
    if ((rusage[2] * 1024) > EUSOLVER_MEMORY_LIMIT):
        print('[solvers.main: Memory out!')
        print('[solvers.main: Trying to exit gracefully...')
        sys.exit(1)

if __name__ == '__main__':
    import time
    import sys
    if (len(sys.argv) < 4):
        die()
    run_anytime_version = False
    try:
        if (sys.argv[1] == '--anytime'):
            time_limit = int(sys.argv[2])
            benchmark_type = sys.argv[3]
            benchmark_subtype = sys.argv[4]
            run_anytime_version = True
        else:
            time_limit = int(sys.argv[1])
            benchmark_type = sys.argv[2]
            benchmark_subtype = sys.argv[3]
    except Exception:
        die()

    start_time = time.clock()
    print('[solvers.main]: Started %s %s %s' % (benchmark_type, benchmark_subtype,
                                                ', running anytime version.' if run_anytime_version else ', running one solution version.'))
    print('[solvers.main]: Setting time limit to %d seconds' % time_limit)
    signal.signal(signal.SIGVTALRM, _timeout_handler)
    signal.setitimer(signal.ITIMER_VIRTUAL, time_limit)
    print('[solvers.main]: Memory limit is %d bytes.' % EUSOLVER_MEMORY_LIMIT)
    signal.signal(signal.SIGPROF, _memout_checker)
    signal.setitimer(signal.ITIMER_PROF, 15, 15)

    if (benchmark_type == 'max'):
        max_cardinality = int(benchmark_subtype)
        test_solver_max(max_cardinality, run_anytime_version)
    elif (benchmark_type == 'icfp'):
        benchmark_file = benchmark_subtype
        test_solver_icfp(benchmark_file, run_anytime_version)
    else:
        die()

    _timeout_handler(-1, None)

#
# solvers.py ends here
