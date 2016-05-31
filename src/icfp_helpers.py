#!/usr/bin/env python3
# basetypes.py ---
#
# Filename: icfp_helpers.py
# Author: Arjun Radhakrishna
# Created: Fri, 20 May 2016 17:14:58 (-0400)
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

import enumerators
import evaluation
import exprtypes
import exprs
import icfp_generator
from bitvectors import BitVector


def icfp_predicate_indicator_grammar(syn_ctx, synth_fun):
    (term_generator, pred_generator) = icfp_grammar(syn_ctx, synth_fun)

    zero_value = exprs.Value(BitVector(0, 64), exprtypes.BitVectorType(64))
    one_value = exprs.Value(BitVector(1, 64), exprtypes.BitVectorType(64))
    const_generator = enumerators.LeafGenerator([exprs.ConstantExpression(zero_value),
                                                 exprs.ConstantExpression(one_value)])

    leaf_generator = enumerators.AlternativesGenerator([const_generator],
                                                       'Leaf Term Generator')
    generator_factory = enumerators.RecursiveGeneratorFactory()
    term_generator_ph = generator_factory.make_placeholder('01TermGenerator')
    new_term_generator = \
            generator_factory.make_generator('01TermGenerator',
                    enumerators.AlternativesGenerator, (
                        ([leaf_generator]),
                        ))

    return new_term_generator, pred_generator



def icfp_grammar(syn_ctx, synth_fun, full_grammer=True, operations=[]):
    unary_funcs = [ syn_ctx.make_function(name, exprtypes.BitVectorType(64))
            for name in [ 'shr1', 'shr4', 'shr16', 'shl1', 'bvnot' ] if full_grammer or (name in operations) ]
    # Binary
    binary_funcs = [ syn_ctx.make_function(name, exprtypes.BitVectorType(64), exprtypes.BitVectorType(64))
            for name in [ 'bvand', 'bvor', 'bvxor', 'bvadd' ] if full_grammer or (name in operations) ]

    param_exprs = [exprs.FormalParameterExpression(synth_fun, exprtypes.BitVectorType(64), 0)]
    param_generator = enumerators.LeafGenerator(param_exprs, 'Argument Generator')
    zero_value = exprs.Value(BitVector(0, 64), exprtypes.BitVectorType(64))
    one_value = exprs.Value(BitVector(1, 64), exprtypes.BitVectorType(64))
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

    is1 = syn_ctx.make_function('is1', exprtypes.BitVectorType(64))
    is1_generator = enumerators.FunctionalGenerator(is1, [term_generator_ph])

    pred_generator = \
            generator_factory.make_generator('PredGenerator', enumerators.AlternativesGenerator, ([is1_generator],))

    return (term_generator, pred_generator)


def get_icfp_valuations(benchmark_name):
    import parser

    sexp = parser.sexpFromFile(benchmark_name)
    if sexp is None:
        die()

    points = parser.get_icfp_points(sexp)
    if points == None:
        print("Could not parse icfp")

    return points

def benchmark_file(bench_id):
    return '../benchmarks/icfp/' + bench_id + '.sl'

def get_generator(gen_id):
    basename = gen_id.partition('.')[0]
    filename = '../benchmarks/icfp_gen/' + basename + '.json'
    generators = parse_generator_json_file(filename, ids=[gen_id])
    assert len(generators) == 1
    return generators[0]

def parse_generator_json_file(file_name, ids=None):
    import json
    with open(file_name, 'r') as json_file:
        json_string = json_file.read()
    benchmark_json_objects = json.loads(json_string)
    if ids is not None:
        benchmark_json_objects = [ benchmark 
                for benchmark in benchmark_json_objects 
                if benchmark['id'] in ids ]
    icfp_generator_instances = [
            icfp_generator.IcfpInstanceGenerator(benchmark['id'],
                                  benchmark['size'],
                                  benchmark['operators'],
                                  benchmark['challenge'])
            for benchmark in benchmark_json_objects ]
    return icfp_generator_instances

benchmark_generator_mapping = {
        "icfp_103_10" : "6.3",
        "icfp_104_10" : "6.4",
        "icfp_105_1000" : "6.5",
        "icfp_105_100" : "6.5",
        "icfp_113_1000" : "6.13",
        "icfp_114_100" : "6.14",
        "icfp_118_100" : "6.18",
        "icfp_118_10" : "6.18",
        "icfp_125_10" : "7.5",
        "icfp_134_1000" : "7.14",
        "icfp_135_100" : "7.15",
        "icfp_139_10" : "7.19",
        "icfp_14_1000" : "1.14",
        "icfp_143_1000" : "8.3",
        "icfp_144_1000" : "8.4",
        "icfp_144_100" : "8.4",
        "icfp_147_1000" : "8.7",
        "icfp_150_10" : "8.10",
        "icfp_21_1000" : "2.1",
        "icfp_25_1000" : "2.5",
        "icfp_28_10" : "11.17",
        "icfp_28_10" : "11.7",
        "icfp_28_10" : "2.8",
        "icfp_28_10" : "4.10",
        "icfp_30_10" : "2.10",
        "icfp_32_10" : "2.12",
        "icfp_38_10" : "2.18",
        "icfp_39_100" : "2.19",
        "icfp_45_1000" : "3.5",
        "icfp_45_10" : "3.5",
        "icfp_5_1000" : "1.5",
        "icfp_51_10" : "3.11",
        "icfp_54_1000" : "3.14",
        "icfp_56_1000" : "3.16",
        "icfp_64_10" : "4.4",
        "icfp_68_1000" : "4.8",
        "icfp_69_10" : "4.9",
        "icfp_7_1000" : "1.7",
        "icfp_7_10" : "1.7",
        "icfp_72_10" : "4.12",
        "icfp_73_10" : "4.13",
        "icfp_81_1000" : "5.1",
        "icfp_82_100" : "5.2",
        "icfp_82_10" : "5.2",
        "icfp_87_10" : "5.7",
        "icfp_9_1000" : "1.9",
        "icfp_93_1000" : "5.13",
        "icfp_94_1000" : "5.14",
        "icfp_94_100" : "5.14",
        "icfp_95_100" : "5.15",
        "icfp_96_1000" : "5.16",
        "icfp_96_10" : "5.16",
        "icfp_99_100" : "5.19"
    }

def points_to_spec(syn_ctx, synth_fun, points):
    if len(points) == 0:
        zero = exprs.ConstantExpression(exprs.Value(BitVector(0, 64), exprtypes.BitVectorType(64)))
        fzero = syn_ctx.make_function_expr(synth_fun, zero)
        return syn_ctx.make_function_expr('eq', fzero, fzero)
    arg_exprss = [ [ exprs.ConstantExpression(exprs.Value(arg, exprtypes.BitVectorType(64)))
            for arg in args ] for (args, result) in points ]
    result_exprs = [ exprs.ConstantExpression(exprs.Value(result, exprtypes.BitVectorType(64)))
            for (arg, result) in points ]
    constraints = []
    for (arg_exprs, result_expr) in zip(arg_exprss, result_exprs):
        app = syn_ctx.make_function_expr(synth_fun, *arg_exprs)
        c = syn_ctx.make_function_expr('eq', app, result_expr)
        constraints.append(c)
    if len(constraints) == 1:
        return constraints[0]
    else:
        return syn_ctx.make_function_expr('and', *constraints)

def verify_solution(solution, valuations, eval_ctx):
    for args, result in valuations:
        eval_ctx.set_valuation_map([exprs.Value(inp, exprtypes.BitVectorType(64)) for inp in args])
        sol_out = evaluation.evaluate_expression_raw(solution, eval_ctx)
        if sol_out != result:
            print(inp, sol_out, result)
        assert sol_out == result

