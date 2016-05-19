#!/usr/bin/env python3
# basetypes.py ---
#
# Filename: icfp_generator.py
# Author: Arjun Radhakrishna
# Created: Fri, 13 May 2016 17:56:50 (-0400)
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

""" ICFP generator stuff """

import synthesis_context
import evaluation
import z3smt
import z3
import semantics_core
import semantics_types
import semantics_bv
import exprtypes
from bitvectors import *
import exprs
from sexp import sexp

# ICFP functions and their built-in equivalents
icfp_function_alias_map = {
        'if0': 'if0',
        'and': 'bvand',
        'plus': 'bvadd',
        'xor': 'bvxor',
        'not': 'bvnot',
        'or': 'bvor',
        'shr1': 'shr1',
        'shr4': 'shr4',
        'shr16': 'shr16',
        'shl1': 'shl1'
        }

class IcfpInstanceGenerator(object):
    def __init__(self, id, intended_solution_size, operators, solution_str):
        self.syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_bv.BVInstantiator(64))
        self.synth_fun = self.syn_ctx.make_unknown_function('f', [exprtypes.BitVectorType(64)],
                                            exprtypes.BitVectorType(64))
        self.id = id
        self.intended_solution_size = intended_solution_size
        self.operators = [ icfp_function_alias_map[op] for op in operators ]
        self.solution = self._challenge_str_to_solution(solution_str)

        self.smt_ctx = z3smt.Z3SMTContext()
        self.eval_ctx = evaluation.EvaluationContext()

    def __str__(self):
        return ("id: " + str(self.id) +
                "\nsol_size: " + str(self.intended_solution_size) +
                "\nops: " + str(self.operators) +
                "\nsolution: " + exprs.expression_to_string(self.solution)
                )

    def intended_solution_at_point(self, point):
        self.eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
        return evaluation.evaluate_expression_raw(self.solution, self.eval_ctx)

    def expr_parse_to_expr(self, arg_names, full_expr_parse):
        arg_map = dict([ (name, exprs.FormalParameterExpression(self.synth_fun, exprtypes.BitVectorType(64), position))
                for (position, name) in zip(range(len(arg_names)), arg_names) ])

        def to_expr(parse):
            if type(parse) == str and parse in arg_map:  # Arguments
                return arg_map[parse]
            elif type(parse) == list and parse[0] in icfp_function_alias_map:   # ICFP function applications
                function_name = icfp_function_alias_map[parse[0]]
                args = [ to_expr(arg) for arg in parse[1:] ]
                return self.syn_ctx.make_function_expr(function_name, *args)
            elif type(parse) == tuple and parse[0] == 'Int': # Constants 
                value = exprs.Value(BitVector(parse[1], 64), exprtypes.BitVectorType(64))
                return exprs.ConstantExpression(value)
            else:
                print(type(parse), '\n', parse)
                raise NotImplementedError

        return to_expr(full_expr_parse)

    def _challenge_str_to_solution(self, challenge_str):
        parse = sexp.parseString(challenge_str, parseAll=True)[0].asList()

        # Sanity: It should be a lambda expression with string parameter names
        assert len(parse) == 3 and parse[0] == 'lambda'
        assert all([ type(arg_name) == str for arg_name in parse[1] ])

        return self.expr_parse_to_expr(parse[1], parse[2])

    def _points_to_spec(self, points):
        arg_exprss = [ [ exprs.ConstantExpression(exprs.Value(arg, exprtypes.BitVectorType(64)))
                for arg in args ] for (args, result) in points ]
        result_exprs = [ exprs.ConstantExpression(exprs.Value(result, exprtypes.BitVectorType(64)))
                for (arg, result) in points ]
        constraints = []
        for (arg_exprs, result_expr) in zip(arg_exprss, result_exprs):
            app = self.syn_ctx.make_function_expr(self.synth_fun, *arg_exprs)
            c = self.syn_ctx.make_function_expr('eq', app, result_expr)
            constraints.append(c)
        return self.syn_ctx.make_function_expr('and', *constraints)

    def check_solution(self, found_solution):
        arg_variables = [ z3.BitVec('x'+str(i), 64, self.smt_ctx.ctx()) for i in range(self.synth_fun.function_arity) ]
        found_smt = semantics_types.expression_to_smt(found_solution, self.smt_ctx, arg_variables)
        intended_smt = semantics_types.expression_to_smt(self.solution, self.smt_ctx, arg_variables)
        formula = (found_smt != intended_smt)

        smt_solver = z3.Solver(ctx=self.smt_ctx.ctx())
        smt_solver.push()
        smt_solver.add(formula)
        r = smt_solver.check()
        smt_solver.pop()

        if (r == z3.sat):
            eval_values = [ smt_solver.model().evaluate(arg_variable, True) 
                    for arg_variable in arg_variables ]
            point = [ BitVector(int(str(eval_value)), 64) for eval_value in eval_values ]
            output = self.intended_solution_at_point(point)
            return (point, output)
        else:
            return None

    def do_complete_benchmark(self, initial_valuations):
        import solvers 

        term_generator, pred_generator = icfp_grammar(self.syn_ctx, self.synth_fun, full_grammer=True)
        valuations = initial_valuations
        while True:
            self.syn_ctx.clear_assertions()
            self.syn_ctx.assert_spec(self._points_to_spec(valuations))
            solver = solvers.Solver(self.syn_ctx)

            for sol_tuple in solver.solve(term_generator, pred_generator):
                (sol, dt_size, num_t, num_p, max_t, max_p, card_p, sol_time) = sol_tuple

                act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = self.syn_ctx.get_synthesis_spec()

                maybe_cex_point = self.check_solution(sol)

                if maybe_cex_point is None:
                    return (valuations, sol)
                else:
                    # print('Added point ' + str(maybe_cex_point))
                    assert maybe_cex_point not in valuations
                    valuations.append(maybe_cex_point)

                break



def parse_json_file(file_name):
    import json
    with open(file_name, 'r') as json_file:
        json_string = json_file.read()
    benchmark_json_objects = json.loads(json_string)
    icfp_generator_instances = [
            IcfpInstanceGenerator(benchmark['id'],
                                  benchmark['size'],
                                  benchmark['operators'],
                                  benchmark['challenge'])
            for benchmark in benchmark_json_objects ]
    return icfp_generator_instances

def icfp_grammar(syn_ctx, synth_fun, full_grammer=True, operations=[]):
    import enumerators

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


'''
Property functions
'''
def get_max_term_size(expr):
    if not exprs.is_function_expression(expr):
        return 1
    elif exprs.is_application_of(expr, 'if0'):
        return max(get_max_term_size(expr.children[1]), get_max_term_size(expr.children[2]))
    else:
        return 1 + sum([get_max_term_size(child) for child in expr.children])

def get_all_terms(syn_ctx, expr):
    import itertools
    if not exprs.is_function_expression(expr):
        return [ expr ]
    elif exprs.is_application_of(expr, 'if0'):
        return get_all_terms(syn_ctx, expr.children[1]) + get_all_terms(syn_ctx, expr.children[2])
    else:
        children_list = itertools.product(*[get_all_terms(syn_ctx, child) for child in expr.children])
        return [ syn_ctx.make_function_expr(expr.function_info, *children) for children in children_list ]

def get_pred_term_mapping(syn_ctx, expr):
    import itertools
    if not exprs.is_function_expression(expr):
        return [ ([], expr) ]
    elif exprs.is_application_of(expr, 'if0'):
        thens = [ (ps + [(expr.children[0], True)], t) for ps, t in get_pred_term_mapping(syn_ctx, expr.children[1]) ]
        elses = [ (ps + [(expr.children[0], False)], t)for ps, t in get_pred_term_mapping(syn_ctx, expr.children[2]) ]
        return thens + elses
    else:
        combs = itertools.product(*[get_pred_term_mapping(syn_ctx, child) for child in expr.children])
        ret = []
        for comb in combs:
            (plists, children) = zip(*comb)
            plist = list(itertools.chain(*plists))
            term = syn_ctx.make_function_expr(expr.function_info, *children) 
            ret.append((plist, term))
        return ret

'''
Testing methods
'''

def get_generator(gen_id):
    basename = gen_id.partition('.')[0]
    generators = [ igi for igi in parse_json_file('../benchmarks/icfp_gen/' + basename + '.json')
            if igi.id == gen_id ]
    assert len(generators) == 1
    return generators[0]

def benchmark_file(bench_id):
    return '../benchmarks/icfp/' + bench_id + '.sl'

def test_parsing(debug=False):
    import os
    generator_file_dir = '../benchmarks/icfp_gen/'
    icfp_generator_instances = []
    for root, dirs, files in os.walk(generator_file_dir):
        for file_name in files:
            if file_name.endswith('.json'):
                icfp_generator_instances.extend(parse_json_file(os.path.join(root, file_name)))
    print("Parsed", len(icfp_generator_instances), "generators")

    if debug:
        for igi in icfp_generator_instances:
            print(str(igi))

    return icfp_generator_instances

def test_benchmark_completeness(debug=True):
    import solvers
    import evaluation
    for bench_id in benchmark_generator_mapping.keys():
        print("Starting", bench_id)

        points = solvers.get_icfp_valuations(benchmark_file(bench_id))
        assert len(points[0]) == 2
        points = [ (list(t[0:-1]), t[-1]) for t in points ]

        generator = get_generator(benchmark_generator_mapping[bench_id])

        # Sanity check: benchmark corresponds to generator
        for (args, value) in points:
            assert value == generator.intended_solution_at_point(args)

        new_points, found_solution = generator.do_complete_benchmark(points.copy())

        print("Completed", bench_id, "with", len(new_points) - len(points), "additional points")

def test_max_term_size(generators):
    for generator in generators:
        solution = generator.solution
        term_size = get_max_term_size(solution)
        print(generator.id, '->', term_size)

def test_get_all_terms(generators):
    for generator in generators:
        solution = generator.solution
        terms = get_all_terms(generator.syn_ctx, solution)
        print(generator.id, '->', [ exprs.expression_to_string(e) for e in terms ] )

def test_get_pred_term_mapping(generators):
    for generator in generators:
        solution = generator.solution
        pred_term_mapping = get_pred_term_mapping(generator.syn_ctx, solution)
        print(generator.id, '->')
        for preds, term in pred_term_mapping:
            print([ (exprs.expression_to_string(p[0]), p[1]) for p in preds ], "====>", exprs.expression_to_string(term))

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

if __name__ == '__main__':
    # test_benchmark_completeness(debug=False)
    # test_parsing(debug=False)
    generators = test_parsing(debug=False)
    test_max_term_size(generators)
    test_get_all_terms(generators)
    test_get_pred_term_mapping(generators)

