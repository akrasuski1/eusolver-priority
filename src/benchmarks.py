#!/usr/bin/env python3
# benchmarks.py ---
#
# Filename: benchmarks.py
# Author: Arjun Radhakrishna
# Created: Wed, 01 Jun 2016 11:27:20 -0400
#
#
# Copyright (c) 2015, Arjun Radhakrishna, University of Pennsylvania
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

from bitvectors import BitVector
import parser
import expr_transforms
import random
import verifiers
import termsolvers
import specifications
import unifiers
import unifiers_lia
import solvers
import exprs
import enumerators
import exprtypes
import semantics_core
import semantics_bv
import semantics_types
import semantics_lia
import semantics_slia
import synthesis_context
import grammars

def get_pbe_valuations(constraints, synth_fun):
    valuations = []
    for constraint in constraints:
        if not exprs.is_application_of(constraint, 'eq') and \
                not exprs.is_application_of(constraint, '='):
            return None
        if len(exprs.get_all_variables(constraint)) > 0:
            return None
        arg_func, arg_other = None, None
        for a in constraint.children:
            if exprs.is_application_of(a, synth_fun):
                arg_func = a
            else:
                arg_other = a
        if arg_func is None or arg_other is None:
            return None
        valuations.append((arg_func.children, arg_other))
    return valuations

def massage_constraints(syn_ctx, macro_instantiator, uf_instantiator, constraints):
    # Instantiate all macro functions
    constraints = [ macro_instantiator.instantiate_all(c)
            for c in constraints ]

    constraints = expr_transforms.AckermannReduction.apply(constraints, uf_instantiator, syn_ctx)

    # Rewrite ITE?
    return constraints

def make_solver(file_sexp):
    benchmark_tuple = parser.extract_benchmark(file_sexp)
    (
            theory,
            syn_ctx,
            synth_fun,
            macro_instantiator,
            uf_instantiator,
            constraints,
            grammar
            ) = benchmark_tuple

    constraints = massage_constraints(syn_ctx, macro_instantiator, uf_instantiator, constraints)

    # Spec type (and verifier)
    valuations = get_pbe_valuations(constraints, synth_fun)
    if valuations is not None:
        specification = specifications.PBESpec(valuations, synth_fun)
        Verifier = verifiers.PBEVerifier
    else:
        spec_expr = constraints[0] if len(constraints) == 1 \
                else syn_ctx.make_function_expr('and', *constraints)
        specification = specifications.StandardSpec(spec_expr, syn_ctx, synth_fun)
        Verifier = verifiers.StdVerifier
    syn_ctx.assert_spec(specification, synth_fun)

    if grammar == 'Default grammar':
        raise NotImplementedError

    TermSolver = termsolvers.PointlessTermSolver
    Unifier = unifiers_lia.SpecAwareLIAUnifier

    # One shot or unification
    ans = grammar.decompose(macro_instantiator)
    if ans == None:
        # Have to configure solver for naivete
        raise NotImplementedError
    else:
        term_grammar, pred_grammar = ans
        # print("Original grammar:\n", grammar)
        # print("Term grammar:\n", term_grammar)
        # print("Pred grammar:\n", pred_grammar)
        # generator_factory = enumerators.RecursiveGeneratorFactory()
        generator_factory = enumerators.RecursiveGeneratorFactory()
        term_generator = term_grammar.to_generator(generator_factory)
        pred_generator = pred_grammar.to_generator(generator_factory)
        solver = solvers.Solver(syn_ctx)
        solvers._do_solve(solver, generator_factory, term_generator, pred_generator, TermSolver, Unifier, Verifier, False)


# Tests:

def test_make_solver():
    import parser

    # for benchmark_file in [ "../benchmarks/one_off/invertD.sl", "../benchmarks/one_off/str.sl" ]:
    # for benchmark_file in [ "../benchmarks/max/max_15.sl" ]:
    # for benchmark_file in [ "../benchmarks/max/max_2.sl" ]:
    # for benchmark_file in [ '../benchmarks/SyGuS-COMP15/LIA-Track/All/fg_mpg_example1.sl' ]:
    # for benchmark_file in [ "../benchmarks/icfp/icfp_103_10.sl" ]:
    for benchmark_file in [ "../benchmarks/one_off/uf.sl" ]:
        print("Doing", benchmark_file)
        file_sexp = parser.sexpFromFile(benchmark_file)
        make_solver(file_sexp)

if __name__ == "__main__":
    test_make_solver()
