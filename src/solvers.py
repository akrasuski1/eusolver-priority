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
from semantics_bv import BitVector
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
_get_expr_with_id = exprs.get_expr_with_id

_term_id_point_id_to_sat = {}
_pred_id_point_id_to_sat = {}

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
            point[i] = exprs.Value(BitVector(
                    bitstring.BitArray(
                        uint=int(str(eval_value)),
                        length=var_info_list.variable_type.size),
                    var_info_list.variable_type))
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

def decision_tree_to_guard_term_list(decision_tree, pred_list, term_list, syn_ctx):
    retval = []
    _decision_tree_to_guard_term_list_internal(decision_tree, pred_list,
                                               term_list, syn_ctx, retval, [])
    return retval

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

def decision_tree_to_expr(decision_tree, pred_list, term_list, syn_ctx):
    return _decision_tree_to_expr_internal(decision_tree, pred_list, term_list, syn_ctx)

def guard_term_list_to_expr(guard_term_list, syn_ctx):
    num_branches = len(guard_term_list)
    retval = guard_term_list[num_branches-1][1]
    for i in reversed(range(0, num_branches-1)):
        retval = syn_ctx.make_function_expr('ite', guard_term_list[i][0],
                                            guard_term_list[i][1], retval)
    return retval


class DuplicatePointException(Exception):
    def __init__(self, point):
        self.point = point

    def __str__(self):
        return 'Duplicate Point %s' % str([self.point[i].value_object
                                           for i in range(len(self.point))])


class TermSolver(object):
    def __init__(self, spec, term_generator, max_term_size = 20):
        self.spec = spec
        self.term_generator = term_generator
        self.points = []
        self.max_term_size = max_term_size
        self.eval_ctx = evaluation.EvaluationContext()
        self.eval_cache = {}

    def _trivial_solve(self):
        term_size = 1
        while (term_size <= self.max_term_size):
            self.term_generator.set_size(term_size)
            for term in self.term_generator.generate():
                retval = {None : term}
                # print('Term Solve complete!')
                # print({str(x) : _expr_to_str(y) for (x, y) in retval[1].items()})
                return retval
            term_size += 1

        # print('Term Solve failed!')
        return None

    def add_point(self, point):
        self.points.append(point)

    def _compute_term_signature(self, term, sig_to_term):
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
                if (evaluation.evaluate_expression_raw(spec, eval_ctx)):
                    retval.add(i)
            if (num_new_points > num_old_points):
                eval_cache[term.expr_id] = retval
            return retval

        except KeyError:
            # need to actually evaluate at every point :-(
            for i in range(num_points):
                eval_ctx.set_valuation_map(points[i])
                if (evaluation.evaluate_expression_raw(spec, eval_ctx)):
                    retval.add(i)
            eval_cache[term.expr_id] = retval
            return retval

    def solve(self):
        points = self.points;
        num_points = len(points)
        if (num_points == 0):
            return self._trivial_solve()

        sig_to_term = {}
        self.signature_factory = BitSet.make_factory(num_points)
        spec_satisfied_at_points = self.signature_factory()

        current_term_size = 1
        max_term_size = self.max_term_size
        generator = self.term_generator
        monotonic_expr_id = 0
        while (current_term_size <= max_term_size):
            generator.set_size(current_term_size)
            for term in generator.generate():
                term = _get_expr_with_id(term, monotonic_expr_id)
                monotonic_expr_id += 1
                sig = self._compute_term_signature(term, sig_to_term)

                if (sig in sig_to_term or sig.is_empty()):
                    continue

                sig_to_term[sig] = term

                spec_satisfied_at_points |= sig
                if (spec_satisfied_at_points.is_full()):
                    # print('Term solver: enumerated %d terms!' % monotonic_expr_id)
                    return sig_to_term

            current_term_size += 1

        return None

class Unifier(object):
    def __init__(self, syn_ctx, pred_generator, max_pred_size = 20):
        self.pred_generator = pred_generator
        self.syn_ctx = syn_ctx
        self.true_expr = exprs.ConstantExpression(exprs.Value(True, exprtypes.BoolType()))
        self.false_expr = exprs.ConstantExpression(exprs.Value(False, exprtypes.BoolType()))
        spec_tuple = syn_ctx.get_synthesis_spec()
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = spec_tuple

        self.smt_ctx = z3smt.Z3SMTContext()
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
        canon_spec_with_outvar = exprs.substitute(canon_spec, fun_app, fun_app_subst_var, syn_ctx)
        # print('Unifier.__init__(), canon_spec_with_outvar:\n%s' % _expr_to_str(canon_spec_with_outvar))
        neg_canon_spec_with_outvar = syn_ctx.make_function_expr('not', canon_spec_with_outvar)
        frozen_smt_cnstr = _expr_to_smt(neg_canon_spec_with_outvar, self.smt_ctx)
        self.smt_solver.add(frozen_smt_cnstr)

    def add_point(self, point):
        self.points.append(point)

    def _compute_pred_signature(self, pred, sig_to_pred):
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
            return retval

        except KeyError:
            # need to actually evaluate
            for i in range(num_points):
                eval_ctx.set_valuation_map(points[i])
                if (evaluation.evaluate_expression_raw(pred, eval_ctx)):
                    retval.add(i)
            eval_cache[pred.expr_id] = retval
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

    def _verify_guard_term_list(self, guard_term_list):
        smt_ctx = self.smt_ctx
        smt_solver = self.smt_solver
        intro_vars = self.smt_intro_vars
        cex_points = []
        working_terms_list = []

        at_least_one_branch_failed = False
        for (pred, term_list) in guard_term_list:
            smt_solver.push()
            smt_solver.add(_expr_to_smt(pred, smt_ctx, intro_vars))
            all_terms_failed = True
            for term in term_list:
                smt_ctx.set_interpretation_map([term])
                eq_cnstr = _expr_to_smt(self.outvar_cnstr, smt_ctx);
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
                    working_terms_list.append((pred, term))
                    break

            if (all_terms_failed):
                at_least_one_branch_failed = True
            smt_solver.pop()

        if (at_least_one_branch_failed):
            retval = list(set(cex_points))
            retval.sort()
            return retval
        else:
            return guard_term_list_to_expr(working_terms_list, self.syn_ctx)

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

    def unify(self, signature_to_term):
        triv = self._try_trivial_unification(signature_to_term)
        if (triv != None):
            # print('Unifier: returning %s' % str(triv))
            return triv

        # cannot be trivially unified
        num_points = len(self.points)
        self.signature_factory = BitSet.make_factory(num_points)
        pred_size = 0
        signature_to_pred = {}
        current_pred_size = 1
        max_pred_size = self.max_pred_size
        generator = self.pred_generator
        monotonic_pred_id = 0

        while (current_pred_size <= max_pred_size):
            generator.set_size(current_pred_size)
            new_preds_generated = False
            for pred in generator.generate():
                # print('Generated pred: %s' % _expr_to_str(pred), flush=True)
                pred = _get_expr_with_id(pred, monotonic_pred_id)
                monotonic_pred_id += 1

                sig = self._compute_pred_signature(pred, signature_to_pred)
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
                current_pred_size += 1
                continue

            # we've generated a bunch of (new) predicates
            # try to learn a decision tree
            # print('Unifier.unify(): Attempting to learn decision tree...', flush=True)
            dt_tuple = self._try_decision_tree_learning(signature_to_term,
                                                        signature_to_pred)
            if (dt_tuple == None):
                # print('Unifier.unify(): Could not learn decision tree!')
                current_pred_size += 1
                continue

            # print('Unifier.unify(): Learned a decision tree!')
            (term_list, term_sig_list, pred_list, pred_sig_list, dt) = dt_tuple
            # expr = decision_tree_to_expr(dt, pred_list, term_list, self.syn_ctx)
            guard_term_list = decision_tree_to_guard_term_list(dt, pred_list,
                                                               term_list,
                                                               self.syn_ctx)
            # print('Guard term list:\n%s' % _guard_term_list_to_str(guard_term_list))
            # print('Obtained expr: %s' % _expr_to_str(expr))
            # print('Unifier: enumerated %d predicates!' % monotonic_pred_id)
            # return self._verify_expr(expr)
            return self._verify_guard_term_list(guard_term_list)

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
        term_solver = TermSolver(canon_spec, term_generator)
        unifier = Unifier(self.syn_ctx, pred_generator)

        while (True):
            # iterate until we have terms that are "sufficient"
            sig_to_term = term_solver.solve()
            if (sig_to_term == None):
                return None
            # we now have a sufficient set of terms
            # print('Term solve complete!')
            r = unifier.unify(sig_to_term)
            # print('Unification Complete!')
            if (exprs.is_expression(r)):
                return r
            else:
                # this is a set of counterexamples
                # print('Solver: Adding %d points' % len(r))
                for point in r:
                    self.add_point(point)
                    term_solver.add_point(point)
                    unifier.add_point(point)
                    # print('Solver: Added point %s' % str([c.value_object for c in point]))
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
    return (expr, solver.points)

def get_icfp_valuations(benchmark_name):
    import bitstring
    test_icfp_valuations =  [
            (
                BitVector(bitstring.BitArray(uint=1, length=64)),
                BitVector(bitstring.BitArray(uint=1, length=64))
            ),
            (
                BitVector(bitstring.BitArray(uint=2, length=64)),
                BitVector(bitstring.BitArray(uint=2, length=64))
            ),
            (
                BitVector(bitstring.BitArray(uint=3, length=64)),
                BitVector(bitstring.BitArray(uint=3, length=64))
            ),
            (
                BitVector(bitstring.BitArray(uint=4, length=64)),
                BitVector(bitstring.BitArray(uint=4, length=64))
            )
            ]
    print("Getting points from benchmark not implemented! Using test points")
    return test_icfp_valuations

def test_solver_icfp(benchmark_name):
    import synthesis_context
    import semantics_core
    import semantics_bv
    import enumerators
    import bitstring

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_bv.BVInstantiator(64))
    synth_fun = syn_ctx.make_unknown_function('f', [exprtypes.BitVectorType(64)],
                                            exprtypes.BitVectorType(64))

    # Unary
    unary_funcs = [ syn_ctx.make_function(name, exprtypes.BitVectorType(64))
            for name in [ 'shr1', 'shr4', 'shr16', 'shl1', 'bvnot' ]]
    # Binary
    binary_funcs = [ syn_ctx.make_function(name, exprtypes.BitVectorType(64), exprtypes.BitVectorType(64))
            for name in [ 'bvand', 'bvor', 'bvxor', 'bvadd' ]]

    param_exprs = [exprs.FormalParameterExpression(synth_fun, exprtypes.BitVectorType(64), 0)]
    param_generator = enumerators.LeafGenerator(param_exprs, 'Argument Generator')
    zero_value = exprs.Value(BitVector(bitstring.BitArray(uint=0, length=64)), exprtypes.BitVectorType(64))
    one_value = exprs.Value(BitVector(bitstring.BitArray(uint=1, length=64)), exprtypes.BitVectorType(64))
    const_generator = enumerators.LeafGenerator([exprs.ConstantExpression(zero_value),
                                                 exprs.ConstantExpression(one_value)])
    leaf_generator = enumerators.AlternativesGenerator([param_generator, const_generator],
                                                       'Leaf Term Generator')

    generator_factory = enumerators.RecursiveGeneratorFactory()
    term_generator_ph = generator_factory.make_placeholder('TermGenerator')
    pred_bool_generator_ph = generator_factory.make_placeholder('PredGenerator')

    unary_function_generators = [ 
            enumerators.FunctionalGenerator(func, [term_generator_ph]) 
            for func in unary_funcs
            ]
    binary_function_generators = [ 
            enumerators.FunctionalGenerator(func, [term_generator_ph, term_generator_ph]) 
            for func in binary_funcs 
            ]

    term_generator = \
            generator_factory.make_generator('TermGenerator',
                    enumerators.AlternativesGenerator, (
                        ([leaf_generator] +
                        unary_function_generators +
                        binary_function_generators),
                        ))

    pred_generator = \
    generator_factory.make_generator('PredGenerator', enumerators.AlternativesGenerator, (term_generator,))

    valuations = get_icfp_valuations(benchmark_name)

    # construct the spec
    arg_exprs = [ exprs.ConstantExpression(exprs.Value(arg, exprtypes.BitVectorType(64)))
            for (arg, result) in valuations ]
    result_exprs = [ exprs.ConstantExpression(exprs.Value(result, exprtypes.BitVectorType(64)))
            for (arg, result) in valuations ]

    constraints = []
    for (arg_expr, result_expr) in zip(arg_exprs, result_exprs):
        app = syn_ctx.make_function_expr(synth_fun, arg_expr)
        c = syn_ctx.make_function_expr('eq', app, result_expr)
        constraints.append(c)

    constraint = syn_ctx.make_function_expr('and', *constraints)

    syn_ctx.assert_spec(constraint)

    solver = Solver(syn_ctx)
    expr = solver.solve(term_generator, pred_generator)
    return (expr, solver.points)

def die():
    print('Usage: %s max <num args to max function> <log file name>' % sys.argv[0])
    print('Usage: %s icfp <benchmark file> <log file name>' % sys.argv[0])
    exit(1)

if __name__ == '__main__':
    import time
    import sys
    if (len(sys.argv) < 4):
        die()

    log_file = open(sys.argv[3], 'a')
    start_time = time.clock()

    if sys.argv[1] == "max":
        max_cardinality = int(sys.argv[2])
        (sol, points) = test_solver_max(max_cardinality)
        log_file.write('max of %d arguments:\n%s\n' % (max_cardinality, exprs.expression_to_string(sol)))
    elif sys.argv[1] == "icfp":
        benchmark_file = sys.argv[2]
        (sol, points) = test_solver_icfp(benchmark_file)
        log_file.write('f in %s:\n%s\n' % (
            benchmark_file,
            exprs.expression_to_string(sol)))
    else:
        die()

    end_time = time.clock()
    total_time = end_time - start_time

    log_file.write('Added %d counterexample points in total\n' % len(points))
    log_file.write('computed in %s seconds\n' % (str(total_time)))

    # log_file.write('Counterexample points:\n')
    # log_file.write(_point_list_to_str(points))

#
# solvers.py ends here
