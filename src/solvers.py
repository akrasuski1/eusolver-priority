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
import expr_transforms

class PointDescriptor(object):
    def __init__(self, point_map):
        self.point_map = point_map
        self.satisfying_exprs = []

    def reset(self):
        self.satisfied = False
        self.satisfying_exprs = []




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
