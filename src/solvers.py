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

class PointDescriptor(object):
    def __init__(self, point_map):
        self.point_map = point_map
        self.satisfying_exprs = []

    def reset(self):
        self.satisfied = False
        self.satisfying_exprs = []


class TermSolver(object):
    """A solver for terms. Assumes that the spec is single-invocation/separable."""
    def __init__(self):
        self.points = []
        self.spec = None
        self.evaluation_context = evaluation.EvaluationContext()

    def solve(*generators):
        for exprs in enumerators.cartesian_product_of_generators(generators):


class CEGSolver(object):
    def __init__(self, spec = None):
        self.spec = spec
        self.variables = set()
        self.var_to_smt_exprs = {}

    def add_spec(self, spec):
        self.spec = spec

    def add_variable(self, var_name):
        self.variables.add(var_name)
        self.var_to_smt_exprs[var_name] = evaluation.to_smt(var_name)

    def _model_to_point_map(self, model):
        point_map = {}
        for (var_name, var_smt_expr) in self.var_to_smt_exprs:
            point_map[var_name] = model.evaluate(var_smt_expr)
        return point_map


    def solve(self, term_generator, pred_generator):
        """Solves for the spec given the term and predicate generators."""

        term_solver = ConcreteSolver()
        pred_solver = ConcreteSolver()

        # add at least one point to the term solver
        solver = z3.Solver()

        solver.push()
        solver.add(evaluation.to_smt(spec))
        res = solver.check()
        if (res != z3.sat):
            return None

        model = solver.model()
        point_map = self._model_to_point_map(model)

        term_solver.add_spec(spec)
        term_solver.add_point(point_map)

        term_solver.solve(generator)


########################################################################
# TEST CASES
########################################################################

def test_cegsolver():
    var_generator = LeafGenerator(['Int_varA', 'Int_varB', 'Int_varC'],
                                  validator, 'Variable Generator')
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
