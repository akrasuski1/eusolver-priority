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
from icfp_helpers import *
import solvers
import evaluation
import z3smt
import z3
import semantics_types
import semantics_bv
import exprtypes
from bitvectors import *
import exprs
from sexp import sexp

_expr_to_str = exprs.expression_to_string

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
        import semantics_core
        import z3
        self.syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_bv.BVInstantiator(64))
        self.num_args = 1
        self.synth_fun = self.syn_ctx.make_unknown_function('f', [exprtypes.BitVectorType(64)] * self.num_args,
                                            exprtypes.BitVectorType(64))
        self.id = id
        self.intended_solution_size = intended_solution_size
        self.operators = [ icfp_function_alias_map[op] for op in operators ]
        self.solution = self._challenge_str_to_solution(solution_str)

        self.smt_ctx = z3smt.Z3SMTContext()
        self.eval_ctx = evaluation.EvaluationContext()
        self.arg_vars = [ z3.Const('x_' + str(i), exprtypes.BitVectorType(64).get_smt_type(self.smt_ctx))
                for i in range(self.num_args) ]

    def __str__(self):
        return ("id: " + str(self.id) +
                "\nsol_size: " + str(self.intended_solution_size) +
                "\nops: " + str(self.operators) +
                "\nsolution: " + _expr_to_str(self.solution)
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

    def check_solution(self, found_solution):
        raw_point = exprs.check_equivalence(found_solution, self.solution, self.smt_ctx, self.arg_vars)
        if raw_point is None:
            return None
        point = [ BitVector(int(str(p)), 64) for p in raw_point ]
        output = self.intended_solution_at_point(point)
        return (point, output)

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

def get_sufficient_samples(syn_ctx, synth_fun, grammar, check_solution, initial_valuations, divide_and_conquer=True):
    assert len(initial_valuations) > 0
 
    term_generator, pred_generator = grammar
    valuations = initial_valuations
    while True:
        syn_ctx.clear_assertions()
        syn_ctx.assert_spec(points_to_spec(syn_ctx, synth_fun, valuations))
        solver = solvers.Solver(syn_ctx)

        sol_tuple = next(solver.solve(term_generator, pred_generator, divide_and_conquer))
        (sol, dt_size, num_t, num_p, max_t, max_p, card_p, sol_time) = sol_tuple
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = syn_ctx.get_synthesis_spec()

        maybe_cex_point = check_solution(sol)
        if maybe_cex_point is None:
            return valuations
        else:
            assert maybe_cex_point not in valuations
            # print('Added point: ', maybe_cex_point)
            valuations.append(maybe_cex_point)

def do_complete_benchmark(generator, initial_valuations):
    def check_solution(found_solution):
        return generator.check_solution(found_solution)
    return get_sufficient_samples(
            generator.syn_ctx,
            generator.synth_fun,
            icfp_grammar(syn_ctx, synth_fun, full_grammer=True),
            check_solution,
            initial_valuations,
            divide_and_conquer=True)

def get_guarded_term_sufficient_samples(generator, guard_pred, term, initial_valuations):
    def get_valuation(raw_point):
        point = [ BitVector(int(str(p)), 64) for p in raw_point ]
        generator.eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
        output = evaluation.evaluate_expression_raw(term, generator.eval_ctx)
        return (point, output)
    def check_solution(found_term):
        raw_point = exprs.check_equivalence_under_constraint(found_term, term, generator.smt_ctx, generator.arg_vars)
        if raw_point is None:
            return None
        return get_valuation(raw_point)
    if len(initial_valuations) == 0:
        raw_point = exprs.sample(guard_pred, generator.smt_ctx, generator.arg_vars)
        if raw_point is None:
            return []
        initial_valuations.append(get_valuation(raw_point))
    return get_sufficient_samples(
            generator.syn_ctx,
            generator.synth_fun,
            icfp_grammar(generator.syn_ctx, generator.synth_fun, full_grammer=True),
            check_solution,
            initial_valuations,
            divide_and_conquer=False)

def get_atomic_predicates(syn_ctx, expr):
    ifs = exprs.find_all_applications(expr, 'if0')
    preds = set([ e.children[0] for e in ifs ])

    while True:
        for pred in preds:
            app = exprs.find_application(pred, 'if0')
            if app is not None:
                preds.remove(pred)
                preds.add(exprs.substitute(pred, app, app.children[1], syn_ctx))
                preds.add(exprs.substitute(pred, app, app.children[2], syn_ctx))
                break
        else:
            return preds


def get_pred_sufficient_samples(generator, initial_valuations):
    syn_ctx = generator.syn_ctx
    atomic_preds = get_atomic_predicates(syn_ctx, generator.solution)
    ap_term_mapping = [ (dict(pv),t) for pv,t in get_atomic_pred_term_mapping(syn_ctx, generator.solution) ]

    for ap_vals_d1, term1 in ap_term_mapping:
        for ap_vals_d2, term2 in ap_term_mapping:
            if term1 == term2:
                continue
            differing_pred_vals = [ p for p in atomic_preds if ap_vals_d1[p] != ap_vals_d2[p] ]
            same_pred_vals = [ (p, ap_vals_d1[p]) for p in atomic_preds if ap_vals_d1[p] == ap_vals_d2[p] ]
            # conditional1 = pred_valuation_list_to_pred(syn_ctx, same_pred_vals)
            # conditional2 = syn_ctx.make_function_expr('ne', term1, term2)
            # pre_condition = syn_ctx.make_function_expr('and', conditional1, conditional2)

            # Generate points till you can semantically synthesize (if pre_condition (if differing_pred_vals 1 else 0))

    raise NotImplementedError

def get_atomic_pred_term_mapping(syn_ctx, expr):
    def power_set_as_indicators(x):
        if len(x) == 0:
            return [ [] ]
        elem = x.pop()
        sub_ps = power_set_as_indicators(x)
        return [ [(elem, False)] + s for s in sub_ps ] + [ [(elem, True)] + s for s in sub_ps ]
    def evaluate_pred(pred, ap_map_d):
        if pred in ap_map_d:
            return ap_map_d[pred]
        else:
            if0 = exprs.find_application(pred, 'if0')
            assert if0 is not None
            child = 1 if evaluate_pred(if0.children[0], ap_map_d) else 2
            return evaluate_pred(exprs.substitute(pred, if0, if0.children[child], syn_ctx), ap_map_d)
    def evaluate_pred_list(pred_list, ap_map_d):
        for pred, tv in pred_list:
            if evaluate_pred(pred, ap_map_d) != tv:
                return False
        return True

    pred_term_mapping = get_pred_term_mapping(syn_ctx, expr)

    ret = []
    atomic_preds = get_atomic_predicates(syn_ctx, expr)
    for ap_map in power_set_as_indicators(atomic_preds):
        good_terms = [ term for pred_list, term in pred_term_mapping
                if evaluate_pred_list(pred_list, dict(ap_map)) ]
        assert len(good_terms) == 1
        ret.append((ap_map, good_terms[0]))
    return ret


def pred_valuation_list_to_pred(syn_ctx, pred_list):
    full_preds = []
    for pred, tv in pred_list:
        base_pred = syn_ctx.make_function_expr('is1', pred)
        if tv:
            full_pred = base_pred
        else:
            full_pred = syn_ctx.make_function_expr('not', base_pred)
        full_preds.append(full_pred)
    if len(full_preds) == 1:
        return full_preds[0]
    else:
        return syn_ctx.make_function_expr('and', *full_preds)

def get_term_sufficient_samples(generator, initial_valuations):
    syn_ctx = generator.syn_ctx
    pred_term_mapping = get_pred_term_mapping(syn_ctx, generator.solution)

    def eval_pred_list(pred_list, point):
        generator.eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
        for (pred, tv) in pred_list:
            pred_value = evaluation.evaluate_expression_raw(pred, generator.eval_ctx)
            if (pred_value == BitVector(1, 64)) != tv:
                return False
        return True

    for pred_list, term in pred_term_mapping:
        # print([ (_expr_to_str(p[0]), p[1]) for p in pred_list ], "====>", _expr_to_str(term))
        print("Some pred", "====>", _expr_to_str(term))
        relevent_valuations = [ (point, output) 
                for point, output in initial_valuations 
                if eval_pred_list(pred_list, point) ]
        guard_pred = pred_valuation_list_to_pred(syn_ctx, pred_list)
        new_valuations = get_guarded_term_sufficient_samples(generator, guard_pred, term, relevent_valuations.copy())
        for valuation in new_valuations:
            if valuation not in relevent_valuations:
                print('Added: ', valuation)

'''
Testing methods
'''

def test_parsing(debug=False):
    import os
    generator_file_dir = '../benchmarks/icfp_gen/'
    icfp_generator_instances = []
    for root, dirs, files in os.walk(generator_file_dir):
        for file_name in files:
            if file_name.endswith('.json'):
                icfp_generator_instances.extend(parse_generator_json_file(os.path.join(root, file_name)))
    print("Parsed", len(icfp_generator_instances), "generators")

    if debug:
        for igi in icfp_generator_instances:
            print(str(igi))

    return icfp_generator_instances

def test_benchmark_completeness(debug=True):
    import evaluation
    for bench_id in benchmark_generator_mapping.keys():
        print("Starting", bench_id)

        points = get_icfp_valuations(benchmark_file(bench_id))
        generator = get_generator(benchmark_generator_mapping[bench_id])

        # Sanity check: benchmark corresponds to generator
        for (args, value) in points:
            assert value == generator.intended_solution_at_point(args)

        new_points = do_complete_benchmark(generator, points.copy())

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
        print(generator.id, '->', [ _expr_to_str(e) for e in terms ] )

def test_get_pred_term_mapping(generators):
    for generator in generators:
        solution = generator.solution
        pred_term_mapping = get_pred_term_mapping(generator.syn_ctx, solution)
        print(generator.id, '->')
        for preds, term in pred_term_mapping:
            print([ (_expr_to_str(p[0]), p[1]) for p in preds ], "====>", _expr_to_str(term))


def test_get_term_sufficient_samples():
    for bench_id in benchmark_generator_mapping.keys():
        if bench_id not in [ 'icfp_96_1000', 'icfp_9_1000' ]:
            print("Starting", bench_id)
            valuations = get_icfp_valuations(benchmark_file(bench_id))
            generator = get_generator(benchmark_generator_mapping[bench_id])
            get_term_sufficient_samples(generator, valuations)

def test_get_pred_sufficient_samples():
    bench_id = "icfp_105_1000"
    valuations = get_icfp_valuations(benchmark_file(bench_id))
    generator = get_generator(benchmark_generator_mapping[bench_id])
    get_pred_sufficient_samples(generator, valuations)

def test_get_atomic_predicates():
    bench_id = "icfp_105_1000"
    valuations = get_icfp_valuations(benchmark_file(bench_id))
    generator = get_generator(benchmark_generator_mapping[bench_id])
    for ap in get_atomic_predicates(generator.syn_ctx, generator.solution):
        print(_expr_to_str(ap))

if __name__ == '__main__':
    # test_benchmark_completeness(debug=False)
    # generators = test_parsing(debug=False)
    # test_max_term_size(generators)
    # test_get_all_terms(generators)
    # test_get_pred_term_mapping(generators)
    test_get_term_sufficient_samples()
    # test_get_pred_sufficient_samples()
    # test_get_atomic_predicates()

