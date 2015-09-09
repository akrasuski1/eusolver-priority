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

import evaluation
from enumerators import *
import functools
import hashcache
import exprs
import expr_transforms
import z3
import z3smt
import semantics_types
import enum import Enum

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

class UnifStatus(Enum):
    synthesis_complete = 1
    uncovered_new_point = 2

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
        if point in self.point_set:
            raise basetypes.ArgumentError('Duplicate point added: %s' % str(point))
        self.point_set.add(point)
        self.points.append(point)

    def add_point_from_model(self, model):
        point = model_to_point(model, self.var_smt_expr_list, self.var_info_list)
        self.add_point(point)

    def test_expr(self, expr):
        num_points = len(self.points)
        eval_ctx = self.eval_ctx
        points = self.points
        eval_ctx.set_interpretation_map([expr])

        points_satisfied = []
        for i in range(num_points):
            eval_ctx.set_valuation_map(points[i])
            res = evaluation.evaluate_expression_raw(expr, eval_ctx)
            if (res):
                self.sat_point_set.add(i)
                points_satisfied.append(i)

        if (len(points_satisfied) > 0):
            self.sat_expr_list.append((expr, set(points_satisfied)))
            if (len(self.sat_point_set) == num_points):
                return True

        return False

    def get_next_term_from_sat_expr_list(self, covered_points)
        index = 0
        num_points = len(self.points)
        while (self.sat_expr_list[index][1].is_subset(covered_points) and index < num_points):
            index += 1
        if (index >= num_points):
            return None
        else:
            (expr, points_covered_by_expr) = sat_expr_list[index]
            newly_covered_points = points_covered_by_expr - covered_points
            for i in range(num_points):
                (old_expr, old_points) = self.sat_expr_list[i]
                self.sat_expr_list[i] = (old_expr, old_points - newly_covered_points)
            self.sat_expr_list.sort(key=lambda x: len(x[1]))
            return (expr, newly_covered_points, self.point_set - covered_points - newly_covered_points)


    def try_unification(self, pred_generator):
        num_points = len(self.points)
        self.sat_expr_list.sort(key=lambda x: len(x[1]))
        smt_predicates_so_far = z3.BoolVal(False)
        index_in_sat_expr_list = 0
        term_guard_list = []
        while (len(covered_points) != num_points):
            cur_term, pos_pts, neg_pts = self.get_next_term_from_sat_expr_list(covered_points)
            covered_points = covered_points | pos_pts
            if (len(covered_points) == num_points):
                # last point, no pred required
                term_guard_list.append((cur_term, None))
                return term_guard_list
            # learn a guard for the point

    def solve(self, syn_ctx, generator, predicate_generator):
        self.spec, self.var_info_list, self.fun_list = syn_ctx.get_synthesis_spec()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.eval_ctx = evaluation.EvaluationContext()
        var_expr_list = [exprs.VariableExpression(var_info) for var_info in var_info_list]
        self.var_smt_expr_list = [semantics_types.expression_to_smt(expr, smt_ctx)
                                  for expr in var_expr_list]
        self.sat_point_set = set()
        self.sat_expr_list = []
        solver = z3.Solver(smt_ctx.ctx())

        while (True):
            for expr in generator.generate():
                done = self.test_expr(expr)
                if (done):
                    self.try_unification(predicate_generator)





########################################################################
# TEST CASES
########################################################################

def test_cegsolver_max(num_vars):
    import synthesis_context
    import semantics_core
    import semantics_lia
    import enumerators

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_lia.LIAInstantiator())
    var_infos = [syn_ctx.make_variable(exprtypes.IntType(), 'x%d' % x, x)
                 for x in range(num_vars)]
    var_exprs = [exprs.VariableExpression(var_info) for var_info in var_infos]
    var_generator = enumerators.LeafGenerator(var_exprs, 'Variable Generator')
    const_generator = enumerators.LeafGenerator([exprs.Value(0, exprtypes.IntType()),
                                                 exprs.Value(1, exprtypes.IntType())])
    leaf_generator = AlternativesGenerator([var_generator, const_generator],
                                           'Leaf Term Generator')

    generator_factory = RecursiveGeneratorFactory()
    start_generator_ph = generator_factory.make_placeholder('Start')
    start_bool_generator_ph = generator_factory.make_placeholder('StartBool')
    start_generator = \
    generator_factory.make_generator('Start',
                                     AlternativesGenerator,
                                     ([leaf_generator] +
                                      [FunctionalGenerator('add',
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator('sub',
                                                           [start_generator_ph,
                                                            start_generator_ph])]))

    start_bool_generator = \
    generator_factory.make_generator('StartBool',
                                     AlternativesGenerator,
                                     ([FunctionalGenerator('le',
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator('eq',
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator('ge',
                                                           [start_generator_ph,
                                                            start_generator_ph])]))


if __name__ == '__main__':
    test_cegsolver()

#
# solvers.py ends here
