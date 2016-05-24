#!/usr/bin/env python3
# basetypes.py ---
#
# Filename: sample_sufficiency.py
# Author: Arjun Radhakrishna
# Created: Tue, 24 May 2016 13:16:37 (-0400)
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

def get_term_sufficient_samples(generator, initial_valuations):
    syn_ctx = generator.syn_ctx
    pred_term_mapping = generator.get_pred_term_mapping()

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

if __name__ == '__main__':
    # test_benchmark_completeness(debug=False)
    # test_get_term_sufficient_samples()
    # test_get_pred_sufficient_samples()
    # test_get_atomic_predicates()

# def pred_valuation_list_to_pred(syn_ctx, pred_list):
#     full_preds = []
#     for pred, tv in pred_list:
#         base_pred = syn_ctx.make_function_expr('is1', pred)
#         if tv:
#             full_pred = base_pred
#         else:
#             full_pred = syn_ctx.make_function_expr('not', base_pred)
#         full_preds.append(full_pred)
#     if len(full_preds) == 1:
#         return full_preds[0]
#     else:
#         return syn_ctx.make_function_expr('and', *full_preds)

