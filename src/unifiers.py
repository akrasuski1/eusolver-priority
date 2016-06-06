#!/usr/bin/env python3
# unifiers.py ---
#
# Filename: unifiers.py
# Author: Arjun Radhakrishna
# Created: Mon, 06 Jun 2016 14:32:01 -0400
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

import exprs
import exprtypes
import z3
import semantics_types
import evaluation
import enumerators
from eusolver import BitSet
import eusolver

_expr_to_str = exprs.expression_to_string
_expr_to_smt = semantics_types.expression_to_smt
_is_expr = exprs.is_expression
_get_expr_with_id = exprs.get_expr_with_id

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

def get_decision_tree_size(dt):
    if (dt.is_leaf()):
        return 1
    else:
        return (1 + get_decision_tree_size(dt.get_positive_child()) +
                get_decision_tree_size(dt.get_negative_child()))

class Unifier(object):
    def __init__(self, syn_ctx, smt_ctx, pred_generator, term_solver, synth_fun, max_pred_size = 1024):
        self.pred_generator = pred_generator
        self.term_solver = term_solver
        self.syn_ctx = syn_ctx
        self.true_expr = exprs.ConstantExpression(exprs.Value(True, exprtypes.BoolType()))
        self.false_expr = exprs.ConstantExpression(exprs.Value(False, exprtypes.BoolType()))
        spec_tuple = syn_ctx.get_synthesis_spec()
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = spec_tuple
        self.synth_fun = synth_fun

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

        smt_ctx.set_interpretation(self.synth_fun, term)
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
                smt_ctx.set_interpretation(self.synth_fun, term)
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
        for (sig, term) in self.term_solver.get_signature_to_term().items():
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
        for (term_sig, term) in self.term_solver.get_signature_to_term().items():
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
        signature_to_term = term_solver.get_signature_to_term()
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
                success = term_solver.generate_more_terms()
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

                success = term_solver.generate_more_terms()
                # if not success:
                #     return
                continue
            else:
                # this a counterexample. stop yielding after this
                yield sol_or_cex
                return
        return

