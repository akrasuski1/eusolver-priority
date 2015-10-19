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

def model_to_point(model, var_smt_expr_list, var_info_list):
    num_vars = len(var_smt_expr_list)
    point = [None] * num_vars
    for i in range(num_vars):
        eval_value = model.evaluate(var_smt_expr_list[i], True)
        if (var_info_list[i].variable_type == exprtypes.BoolType()):
            point[i] = exprs.Value(bool(str(eval_value)), exprtypes.BoolType())
        elif (var_info_list[i].variable_type == exprtypes.IntType()):
            point[i] = expr.Value(int(str(eval_value)), exprtypes.IntType())
        elif (var_info_list[i].variable_type.type_code == exprtypes.TypeCodes.bit_vector_type):
            point[i] = expr.Value(int(str(eval_value)), var_info_list.variable_type)
        else:
            raise basetypes.UnhandledCaseError('solvers.In model_to_point')
    return tuple(point)


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
            res = evaluation.evaluate_expression_raw(spec, eval_ctx)
            if (res):
                retval.add(i)
        return retval

    def _trivial_solve(self):
        for term in self.term_generator.generate():
            return (True, {term : None})
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
            sig = self._compute_term_signature(term, self.spec, eval_ctx)
            if (sig in signature_to_term):
                continue
            # sig not in signature_set
            signature_set[sig] = term
            spec_satisfied_at_points |= sig
            if (spec_satisfied_at_points.is_full()):
                return (True, signature_to_term)

       return (False, None)


    def solve(self, term_size, points):
        self.points = points
        self.signature_to_term = {}
        self.num_points = len(points)
        self.signature_factory = BitSet.make_factory(num_points)
        self.current_term_size = term_size - 1
        self.spec_satisfied_at_points = self.signature_factory()
        self.eval_ctx = evaluation.EvaluationContext()

        return self.continue_solve()

class Unifier(object):
    def __init__(self, clauses, neg_clauses, pred_generator):
        self.pred_generator = pred_generator
        self.clauses = clauses
        self.neg_clauses = neg_clauses

    def unify(self, signature_to_term):
        while (True):




class Solver(object):
    def __init__(self, syn_ctx, specification = None):
        self.syn_ctx = syn_ctx
        self.spec = specification
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
        t = expr_transforms.canonicalize_specification(self.spec)
        var_list, uf_list, clauses, neg_clauses, mapping_list = t
        self.var_info_list = var_list
        var_expr_list = [exprs.VariableExpression(x) for x in var_list]
        self.var_smt_expr_list = [_expr_to_smt(x, self.smt_ctx) for x in var_expr_list]

        while (True):
            term_solver = TermSolver(self.spec, term_generator)
            # iterate until we have terms that are "sufficient"
            (terms_done, sig_to_term) = term_solver.solve(0, self.points)
            while (not terms_done):
                (terms_done, sig_to_term) = term_solver.continue_solve()
            # we now have a sufficient set of terms
            unifier = Unifier(clauses, neg_clauses, pred_generator)








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
