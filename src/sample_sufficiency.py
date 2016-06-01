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

from icfp_helpers import *
import solvers
import itertools
import signal

_expr_to_str = exprs.expression_to_string

def _eval_pred_list(eval_ctx, pred_list, point):
    eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
    for (pred, tv) in pred_list:
        pred_value = evaluation.evaluate_expression_raw(pred, eval_ctx)
        if (pred_value == BitVector(1, 64)) != tv:
            return False
    return True

def _pred_valuation_list_to_pred(syn_ctx, pred_list):
    if len(pred_list) == 0:
        return exprs.ConstantExpression(exprs.Value(True, exprtypes.BoolType()))
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


def get_sufficient_samples(syn_ctx, synth_fun, grammar, check_solution, initial_valuations, divide_and_conquer=True):
    # print("Entering get_sufficient_samples")
    term_generator, pred_generator = grammar
    valuations = initial_valuations.copy()
    # print('\x1b[s', end="", flush=True) # Save cursor position
    # print('')
    while True:
        syn_ctx.clear_assertions()
        syn_ctx.assert_spec(points_to_spec(syn_ctx, synth_fun, valuations))
        solver = solvers.Solver(syn_ctx)

        sol_tuple = next(solver.solve(term_generator, pred_generator, divide_and_conquer))
        (sol, dt_size, num_t, num_p, max_t, max_p, card_p, sol_time) = sol_tuple
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = syn_ctx.get_synthesis_spec()

        # print("Intermediate solution:", _expr_to_str(sol))

        maybe_cex_point = check_solution(sol)
        if maybe_cex_point is None:
            # print("Exiting get_sufficient_samples")
            return [ val for val in valuations if val not in initial_valuations ]
        else:
            assert maybe_cex_point not in valuations
            valuations.append(maybe_cex_point)

def get_guarded_term_sufficient_samples(generator, guard_pred, term, initial_valuations, random):
    def get_valuation(raw_point):
        point = [ BitVector(int(str(p)), 64) for p in raw_point ]
        generator.eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
        output = evaluation.evaluate_expression_raw(term, generator.eval_ctx)
        # print(_expr_to_str(term), 'evaluated to', output, 'at', point)
        return (point, output)
    def check_solution(found_term):
        raw_point = exprs.check_equivalence_under_constraint(found_term, term, generator.smt_ctx, generator.arg_vars, guard_pred, random)
        if raw_point is None:
            return None
        return get_valuation(raw_point)
    if len(initial_valuations) == 0:
        raw_point = exprs.random_sample(guard_pred, generator.smt_ctx, generator.arg_vars)
        if raw_point is None:
            return []
        sampled_vals = [ get_valuation(raw_point) ]
        # print('Sampled:', sampled_vals)
    else:
        sampled_vals = []
    suff = get_sufficient_samples(
            generator.syn_ctx,
            generator.synth_fun,
            icfp_grammar(generator.syn_ctx, generator.synth_fun, full_grammer=True),
            check_solution,
            initial_valuations + sampled_vals,
            divide_and_conquer=False)
    return suff + sampled_vals


def _pred_term_mapping_to_expr(syn_ctx, mapping):
    def _filter_but(pl, np):
        return [ (p, tv) for p,tv in pl if p != np ]
    if len(mapping) == 1:
        pl, t = mapping[0]
        assert len(pl) == 0
        return t
    cond = mapping[0][0][0][0]
    pt = [ (_filter_but(pl, cond), t) for pl, t in mapping if (cond, True) in pl ]
    pf = [ (_filter_but(pl, cond), t) for pl, t in mapping if (cond, False) in pl ]
    tt = _pred_term_mapping_to_expr(syn_ctx, pt)
    tf = _pred_term_mapping_to_expr(syn_ctx, pf)
    return syn_ctx.make_function_expr('if0', cond, tt, tf)

def get_distinguishing_points(generator,
        current_pred,
        fixed_preds_val,
        unfixed_preds,
        relevant_valuations, 
        relevant_ap_term_mapping,
        random):
    syn_ctx = generator.syn_ctx

    # fixed_pred_vals to condition
    condition = _pred_valuation_list_to_pred(syn_ctx, fixed_preds_val)

    # unfixed predicate mapping + current_pred = True to terms
    # unfixed predicate mapping + current_pred = False to terms
    def _filter_to(pl, s):
        return [ (p, tv) for p,tv in pl.items() if p in s ]
    true_mapping = [ (_filter_to(pl, unfixed_preds), t) for pl, t in relevant_ap_term_mapping
            if (current_pred, True) in pl.items() ]
    false_mapping = [ (_filter_to(pl, unfixed_preds), t) for pl, t in relevant_ap_term_mapping
            if (current_pred, False) in pl.items() ]
    true_term = _pred_term_mapping_to_expr(syn_ctx, true_mapping)
    false_term = _pred_term_mapping_to_expr(syn_ctx, false_mapping)

    # condition and true_term != false_term
    pre_cond = syn_ctx.make_function_expr('and', condition, 
            syn_ctx.make_function_expr('ne', true_term, false_term))

    # To be synthesized function
    zero_value = exprs.Value(BitVector(0, 64), exprtypes.BitVectorType(64))
    one_value = exprs.Value(BitVector(1, 64), exprtypes.BitVectorType(64))
    correct_term = syn_ctx.make_function_expr('if0', current_pred, exprs.ConstantExpression(one_value),
                                                 exprs.ConstantExpression(zero_value))

    def get_valuation(raw_point):
        point = [ BitVector(int(str(p)), 64) for p in raw_point ]
        generator.eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
        output = evaluation.evaluate_expression_raw(correct_term, generator.eval_ctx)
        return (point, output)

    remapped_relevant_valuations = []
    for point, value in relevant_valuations:
        generator.eval_ctx.set_valuation_map([ exprs.Value(arg, exprtypes.BitVectorType(64)) for arg in point ])
        output = evaluation.evaluate_expression_raw(correct_term, generator.eval_ctx)
        remapped_relevant_valuations.append((point, output))

    def check_solution(found_term):
        # print('\tChecking solution:', _expr_to_str(found_term))
        # print('\tIntended solution:', _expr_to_str(correct_term))
        # print('\tPrecondition:', _expr_to_str(pre_cond))
        raw_point = exprs.check_equivalence_under_constraint(found_term, correct_term, generator.smt_ctx, generator.arg_vars, pre_cond, random=random)
        if raw_point is None:
            # print('\tGot no point')
            return None
        val = get_valuation(raw_point)
        # print('\tGot point:', val)
        return val

    return get_sufficient_samples(
            syn_ctx,
            generator.synth_fun,
            icfp_predicate_indicator_grammar(generator.syn_ctx, generator.synth_fun),
            check_solution,
            remapped_relevant_valuations,
            divide_and_conquer=True)

def get_pred_sufficient_samples(generator, initial_valuations, random):
    syn_ctx = generator.syn_ctx
    atomic_preds = generator.get_atomic_predicates()
    ap_term_mapping = [ (dict(pv),t) for pv,t in generator.get_atomic_pred_term_mapping() ]
    valuations = initial_valuations.copy()

    def _consistent(pred_mapping, partial_pred_mapping):
        for p, tv in partial_pred_mapping.items():
            if pred_mapping[p] != tv:
                return False
        return True

    # Current atomic pred
    # Fixed atomic preds
    # Unfixed atomic preds

    # The samples should be sufficient no matter which order the dt picks predicates
    # Fix one path to some (possibly non-leaf) node in the decision tree: fixed_pred_vals
    # Let current_pred be the next chosen predicate
    # We should be able to decide between (pred = true) and (pred = false)
    total = len(atomic_preds)
    current = 0
    for current_pred in atomic_preds:
        current += 1
        # print('\x1b[2K\x1b[G', end="", flush=True)
        print("Doing pred", current, "of", total, '[ size =', exprs.get_expression_size(current_pred), ']', _expr_to_str(current_pred))
        other_preds = atomic_preds - { current_pred }
        subsets = itertools.chain.from_iterable(
                itertools.combinations(other_preds, r) for r in range(len(other_preds) + 1)
                )
        for fixed_preds in subsets:
            unfixed_preds = [ p for p in atomic_preds if p not in fixed_preds and p != current_pred ]
            all_vals = itertools.product(*([[True, False]] * len(fixed_preds)))
            all_fixed_preds_vals = [ list(zip(fixed_preds, vals)) for vals in all_vals ]
            for fixed_preds_val in all_fixed_preds_vals:
                relevant_valuations = [ (point, output) for point, output in valuations 
                    if _eval_pred_list(generator.eval_ctx, fixed_preds_val, point) ]
                relevant_ap_term_mapping = [ (pv, t) for pv, t in ap_term_mapping 
                    if _consistent(pv, dict(fixed_preds_val)) ]

                # print('Distinguishing', _expr_to_str(current_pred))
                # print('When')
                # for p,tv in fixed_preds_val:
                #     print('\t', _expr_to_str(p),tv)
                # print('\tINIT:', len(valuations))
                # for point in valuations:
                #     print('\t\t', point)

                # print("\tRelevant valuations: ", len(relevant_valuations))
                # for point in relevant_valuations:
                #     print('\t\t', point)

                more_points = get_distinguishing_points(generator,
                        current_pred,
                        fixed_preds_val,
                        unfixed_preds,
                        relevant_valuations,
                        relevant_ap_term_mapping,
                        random)
                more_points = [ (point, generator.intended_solution_at_point(point)) for point,value in more_points ]
                # print('Added', len(more_points))
                # for point in more_points:
                #     print('\t', point)
                #     assert point not in valuations

                valuations.extend(more_points)

    # print('\x1b[2K\x1b[G', end="", flush=True)
    return [ x for x in valuations if x not in initial_valuations ]


def get_term_sufficient_samples(generator, initial_valuations, random):
    syn_ctx = generator.syn_ctx
    pred_term_mapping = generator.get_pred_term_mapping()
    valuations = initial_valuations

    total = len(pred_term_mapping)
    current = 0
    for pred_list, term in pred_term_mapping:
        current += 1
        print("Doing conditional term", current, "of", total, '[ size =', exprs.get_expression_size(term), ']', _expr_to_str(term))
        # print([ (_expr_to_str(p[0]), p[1]) for p in pred_list ], "====>", _expr_to_str(term))
        relevant_valuations = [ (point, output) 
                for point, output in valuations
                if _eval_pred_list(generator.eval_ctx, pred_list, point) ]
        # print("Relevant Vals:", len(relevant_valuations))
        # for val in relevant_valuations:
        #     print('\t', val)
        guard_pred = _pred_valuation_list_to_pred(syn_ctx, pred_list)
        # print("Guard pred:", _expr_to_str(guard_pred))
        new_valuations = get_guarded_term_sufficient_samples(generator, guard_pred, term, relevant_valuations, random)
        # print("Added:", len(new_valuations))
        # for val in new_valuations:
        #     print('\t', val)
        valuations.extend(new_valuations)

    return [ x for x in valuations if x not in initial_valuations ] 


def get_icfp_sufficient_samples(generator, initial_valuations):
    syn_ctx = generator.syn_ctx
    print('Solution:', _expr_to_str(generator.solution))
    valuations = initial_valuations.copy()
    valuations.extend(get_term_sufficient_samples(generator, valuations, random=True))
    print('Term sufficient: ', len(valuations) - len(initial_valuations))
    valuations.extend(get_pred_sufficient_samples(generator, valuations, random=True))
    print('Pred sufficient: ', len(valuations) - len(initial_valuations))
    valuations.extend(generator.do_complete_benchmark(valuations, random_samples=True))
    print('Full sufficient: ', len(valuations) - len(initial_valuations))
    # return [ x for x in valuations if x not in initial_valuations ]
    return valuations

def get_icfp_samples(json_id):
    import random
    generator = get_generator(json_id)
    if json_id in generator_benchmark_mapping:
        bench_id = generator_benchmark_mapping[json_id]
        initial_valuations = get_icfp_valuations(benchmark_file(bench_id))
    else:
        initial_points = [ [ BitVector(random.getrandbits(64), 64) ] for k in range(10) ]
        initial_valuations = [ (p, generator.intended_solution_at_point(p)) 
                for p in initial_points ]
    print("Max term size:", generator.get_max_term_size())
    print("Max pred size:", generator.get_max_atomic_pred_size())
    all_valuations = get_icfp_sufficient_samples(generator, initial_valuations)
    for v in all_valuations:
        print(v)
    return all_valuations


def get_blind_icfp_samples(json_id):
    import random
    generator = get_generator(json_id)
    num_points = 5

    sampled_points = []
    for ap_map_list, term in generator.get_atomic_pred_term_mapping():
        cond = _pred_valuation_list_to_pred(generator.syn_ctx, ap_map_list)
        for i in range(num_points):
            raw_point =  exprs.random_sample(cond, generator.smt_ctx, generator.arg_vars)
            if raw_point is not None:
                point = [ BitVector(int(str(p)), 64) for p in raw_point ]
                if point not in sampled_points:
                    sampled_points.append(point)

    valuations = [ (p, generator.intended_solution_at_point(p))
            for p in sampled_points ]
    # for v in valuations:
    #     print(v)
    return valuations


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

        new_points = generator.do_complete_benchmark(points, random_samples=True)
        print("Completed", bench_id, "with", len(new_points), "additional points")

def test_get_term_sufficient_samples():
    for bench_id in benchmark_generator_mapping.keys():
        if bench_id not in [ 'icfp_96_1000', 'icfp_9_1000' ]:
            print("Starting", bench_id)
            valuations = get_icfp_valuations(benchmark_file(bench_id))
            generator = get_generator(benchmark_generator_mapping[bench_id])
            get_term_sufficient_samples(generator, valuations)

def test_get_pred_sufficient_samples():
    for bench_id in benchmark_generator_mapping.keys():
        print("Starting", bench_id)
        valuations = get_icfp_valuations(benchmark_file(bench_id))
        generator = get_generator(benchmark_generator_mapping[bench_id])
        get_pred_sufficient_samples(generator, valuations)

def test_get_icfp_sufficient_samples():
    for bench_id in benchmark_generator_mapping.keys():
        print("Starting", bench_id)
        valuations = get_icfp_valuations(benchmark_file(bench_id))
        generator = get_generator(benchmark_generator_mapping[bench_id])
        print("Max term size:", generator.get_max_term_size())
        print("Max pred size:", generator.get_max_atomic_pred_size())
        new_valuations = get_icfp_sufficient_samples(generator, valuations)
        print('Added', len(new_valuations), 'points to complete benchmark')

def test_get_blind_icfp_sufficient_samples():
    for file_no in range(1, 16):
        for bench_no in range(1, 21):
            json_id = str(file_no) + '.' + str(bench_no)
            valuations = get_blind_icfp_samples(json_id)
            print('Sampled', len(valuations), 'for', json_id)
            generator = get_generator(json_id)
            # new_valuations = generator.do_complete_benchmark(valuations, random_samples=True)
            # print('Completed benchmark with', len(new_valuations), 'additional samples')


# if __name__ == '__main__':
    # test_benchmark_completeness(debug=False)
    # test_get_term_sufficient_samples()
    # test_get_pred_sufficient_samples()
    # test_get_icfp_sufficient_samples()

def die():
    print('Usage: %s <timeout in seconds> icfp_gen <json id>' % sys.argv[0])
    exit(1)

def _timeout_handler(signum, frame):
    if (signum != -1):
        print('[sample_sufficiency.main]: Timed out!')
        print('[sample_sufficiency.main]: Trying to exit gracefully...')
        sys.exit(1)
    else:
        print('[sample_sufficiency.main]: Exiting gracefully...')
        sys.exit(1)

if __name__ == '__main__':
    test_get_blind_icfp_sufficient_samples()

# if __name__ == '__main__':
#     import time
#     import sys
#     if (len(sys.argv) < 3):
#         die()
#     run_anytime_version = False
#     try:
#         time_limit = int(sys.argv[1])
#         benchmark_type = sys.argv[2]
#         assert benchmark_type == "icfp_gen"
#         json_id = sys.argv[3]
#     except Exception:
#         die()

#     start_time = time.clock()
#     print('[sample_sufficiency.main]: Started %s %s' % (benchmark_type, json_id))
#     print('[sample_sufficiency.main]: Setting time limit to %d seconds' % time_limit)
#     signal.signal(signal.SIGVTALRM, _timeout_handler)
#     signal.setitimer(signal.ITIMER_VIRTUAL, time_limit)

#     get_icfp_samples(json_id)

#     _timeout_handler(-1, None)

#
# solvers.py ends here
