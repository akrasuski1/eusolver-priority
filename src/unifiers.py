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
import evaluation
import enumerators
from eusolver import BitSet
import eusolver

_expr_to_str = exprs.expression_to_string
_is_expr = exprs.is_expression
_get_expr_with_id = exprs.get_expr_with_id

def get_decision_tree_size(dt):
    if (dt.is_leaf()):
        return 1
    else:
        return (1 + get_decision_tree_size(dt.get_positive_child()) +
                get_decision_tree_size(dt.get_negative_child()))

class UnifierInterface(object):
    def add_points(self):
        raise basetypes.AbstractMethodError('UnifierInterface.add_points()')

    def unify(self):
        raise basetypes.AbstractMethodError('UnifierInterface.solve()')

class EnumerativeUnifierBase(object):
    def __init__(self, pred_generator, term_solver):
        self.pred_generator = pred_generator
        self.term_solver = term_solver
        self.points = []
        self.pred_solver = None

    def add_points(self, new_points):
        self.points.extend(new_points)
        self.pred_solver.add_points(new_points)

class Unifier(object):
    def __init__(self, pred_generator, term_solver):
        self.pred_generator = pred_generator
        self.term_solver = term_solver
        self.points = []
        self.eval_ctx = evaluation.EvaluationContext()
        self.eval_cache = {}
        self.signature_to_pred = {}
        self.bunch_generator = None
        self.max_pred_size = 1024
        self.current_largest_pred_size = 0
        self.last_dt_size = 1

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

    def _try_trivial_unification(self):
        # we can trivially unify if there exists a term
        # which satisfies the spec at all points
        trivial_term = None
        for (sig, term) in self.term_solver.get_signature_to_term().items():
            if (sig is None or sig.is_full()):
                trivial_term = term
                break
        return trivial_term

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

    def get_largest_pred_size_enumerated(self):
        if self.bunch_generator is None:
            return self.current_largest_pred_size
        return max(self.current_largest_pred_size,
                self.bunch_generator.current_object_size)


    """returns/yields one of:
    1. (expression, DT size, num terms, num preds, max term size, max pred size)
    2. [list of counterexample points]
    3. None, in case of exhaustion of terms/preds
    """
    def unify(self):
        term_solver = self.term_solver
        signature_to_term = term_solver.get_signature_to_term()
        signature_to_pred = self.signature_to_pred
        triv = self._try_trivial_unification()
        if triv is not None:
            yield ("TERM", triv)
            return

        # cannot be trivially unified
        num_points = len(self.points)
        self.signature_factory = BitSet.make_factory(num_points)
        monotonic_pred_id = 0

        if self.bunch_generator is not None:
            self.current_largest_pred_size = max(self.current_largest_pred_size,
                    self.bunch_generator.current_object_size)

        self.bunch_generator = enumerators.BunchedGenerator(self.pred_generator, self.max_pred_size)

        for bunch in self.bunch_generator.generate():
            new_preds_generated = False
            for pred in bunch:
                pred = _get_expr_with_id(pred, monotonic_pred_id)
                monotonic_pred_id += 1

                sig = self._compute_pred_signature(pred)
                if (not sig.is_empty() and not sig.is_full() and sig not in signature_to_pred):
                    signature_to_pred[sig] = pred
                    new_preds_generated = True
                else:
                    continue

            if (not new_preds_generated):
                continue

            dt_tuple = self._try_decision_tree_learning()
            self.last_dt_size = get_decision_tree_size(dt_tuple[-1])
            if (dt_tuple == None):
                success = term_solver.generate_more_terms()
                continue

            yield ("DT_TUPLE", dt_tuple)
            success = term_solver.generate_more_terms()

