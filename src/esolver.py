#!/usr/bin/env python3
# solvers.py ---
#
# Filename: solvers.py
# Author: Arjun Radhakrishna
# Created: Sat, 04 Jun 2016 18:40:10 -0400
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

import evaluation
import exprs
import exprtypes
import z3smt
import enumerators
import z3
import semantics_types

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

class ESolver(object):
    def __init__(self, syn_ctx, grammar):
        self.syn_ctx = syn_ctx
        self.spec_tuple = syn_ctx.get_synthesis_spec()
        self.reset()
        self.grammar = grammar
        self.generator_factory = enumerators.PointDistinctGeneratorFactory()
        self.smt_solver = z3.Solver(ctx=self.smt_ctx.ctx())

    def reset(self):
        self.spec = None
        self.eval_ctx = evaluation.EvaluationContext()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.points = []
        self.point_set = set()

    def add_points(self, points):
        for point in points:
            print('Adding point:', [ x.value_object for x in point])
            if (point in self.point_set):
                raise DuplicatePointException(point)
            self.point_set.add(point)
            self.points.append(point)
            self.generator_factory.add_point(point)

    def add_specification(self, specification):
        syn_ctx = self.syn_ctx
        if (self.spec == None):
            self.spec = specification
        else:
            self.spec = syn_ctx.make_ac_function_expr('and', self.spec,
                                                      specification)

    def _concrete_verify(self, term):
        eval_ctx = self.eval_ctx
        eval_ctx.set_interpretation(self.synth_fun, term)
        for point in self.points:
            eval_ctx.set_valuation_map(point)
            if not evaluation.evaluate_expression_raw(self.canon_spec, eval_ctx):
                return False
        return True

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

    def solve(self):
        # print(self.grammar)

        act_spec, var_list, uf_list, clauses, neg_clauses, canon_spec, intro_vars = self.spec_tuple
        self.synth_fun = uf_list[0]
        self.canon_spec = canon_spec

        self.var_info_list = var_list
        self.var_expr_list = [exprs.VariableExpression(x) for x in self.var_info_list]
        self.var_smt_expr_list = [_expr_to_smt(x, self.smt_ctx) for x in self.var_expr_list]

        fun_app = self.syn_ctx.make_function_expr(uf_list[0], *intro_vars)
        fun_app_subst_var = self.syn_ctx.make_variable_expr(uf_list[0].range_type, '__output__')
        self.outvar_cnstr = self.syn_ctx.make_function_expr('eq', fun_app_subst_var, fun_app)

        canon_spec_with_outvar = exprs.substitute(canon_spec, fun_app, fun_app_subst_var)
        neg_canon_spec_with_outvar = self.syn_ctx.make_function_expr('not', canon_spec_with_outvar)
        frozen_smt_cnstr = _expr_to_smt(neg_canon_spec_with_outvar, self.smt_ctx)
        self.smt_solver.add(frozen_smt_cnstr)

        print([_expr_to_str(var) for var in self.var_expr_list])

        term_generator = self.grammar.to_generator(self.generator_factory)
        size = 1

        term_generator.set_size(size)
        terms = term_generator.generate()
        while True:
            try:
                term = next(terms)
                # print(exprs.expression_to_string(term))
            except StopIteration:
                # self.generator_factory.print_caches()
                size = size + 1
                print(size)
                term_generator.set_size(size)
                terms = term_generator.generate()
                continue

            # print('Got term:', _expr_to_str(term))
            if not self._concrete_verify(term):
                continue
            # print('Passed concrete verify:', _expr_to_str(term))

            cex_or_term = self._verify_expr(term)
            if term == cex_or_term:
                print('Found solution:', exprs.expression_to_string(term))
                return term
            else:
                self.add_points(cex_or_term)
                # self.generator_factory.print_caches()
                # print('Resetting size')
                size = 1
                term_generator.set_size(size)
                terms = term_generator.generate()


# Tests:
