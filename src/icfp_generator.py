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
import itertools
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
                                                 semantics_bv.BVInstantiator())
        self.num_args = 1
        self.synth_fun = self.syn_ctx.make_synth_function('f', [exprtypes.BitVectorType(64)] * self.num_args,
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
        result = evaluation.evaluate_expression_raw(self.solution, self.eval_ctx)
        return result

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

    def check_solution(self, found_solution, random_samples):
        raw_point = exprs.check_equivalence(found_solution, self.solution, self.smt_ctx, self.arg_vars, random=random_samples)
        if raw_point is None:
            return None
        point = [ BitVector(int(str(p)), 64) for p in raw_point ]
        output = self.intended_solution_at_point(point)
        return (point, output)

    def get_all_terms(self):
        syn_ctx = self.syn_ctx
        def _get_all_terms(expr):
            if not exprs.is_function_expression(expr):
                return [ expr ]
            elif exprs.is_application_of(expr, 'if0'):
                return _get_all_terms(expr.children[1]) + _get_all_terms(expr.children[2])
            else:
                children_list = itertools.product(*[_get_all_terms(child) for child in expr.children])
                return [ syn_ctx.make_function_expr(expr.function_info, *children) for children in children_list ]
        return _get_all_terms(self.solution)

    def get_max_term_size(self):
        return max([ exprs.get_expression_size(t) for t in self.get_all_terms() ])

    def get_max_atomic_pred_size(self):
        return max([ exprs.get_expression_size(ap) for ap in self.get_atomic_predicates() ])

    def get_pred_term_mapping(self):
        syn_ctx = self.syn_ctx
        def _get_pred_term_mapping(expr):
            if not exprs.is_function_expression(expr):
                return [ ([], expr) ]
            elif exprs.is_application_of(expr, 'if0'):
                thens = [ (ps + [(expr.children[0], True)], t) for ps, t in _get_pred_term_mapping(expr.children[1]) ]
                elses = [ (ps + [(expr.children[0], False)], t)for ps, t in _get_pred_term_mapping(expr.children[2]) ]
                return thens + elses
            else:
                combs = itertools.product(*[_get_pred_term_mapping(child) for child in expr.children])
                ret = []
                for comb in combs:
                    (plists, children) = zip(*comb)
                    plist = list(itertools.chain(*plists))
                    term = syn_ctx.make_function_expr(expr.function_info, *children) 
                    ret.append((plist, term))
                return ret
        return _get_pred_term_mapping(self.solution)

    def get_atomic_predicates(self):
        syn_ctx = self.syn_ctx
        ifs = exprs.find_all_applications(self.solution, 'if0')
        preds = set([ e.children[0] for e in ifs ])

        while True:
            for pred in preds:
                app = exprs.find_application(pred, 'if0')
                if app is not None:
                    preds.remove(pred)
                    preds.add(exprs.substitute(pred, app, app.children[1]))
                    preds.add(exprs.substitute(pred, app, app.children[2]))
                    break
            else:
                return preds

    def get_atomic_pred_term_mapping(self):
        syn_ctx = self.syn_ctx
        def power_set_as_indicators(xs):
            all_set_tuples = itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))
            indicators = [ [ (x, x in st) for x in xs ] for st in all_set_tuples ]
            assert len(indicators) == 2**len(xs)
            return indicators
        def evaluate_pred(pred, ap_map_d):
            if pred in ap_map_d:
                return ap_map_d[pred]
            if0 = exprs.find_application(pred, 'if0')
            assert if0 is not None
            child = 1 if evaluate_pred(if0.children[0], ap_map_d) else 2
            return evaluate_pred(exprs.substitute(pred, if0, if0.children[child]), ap_map_d)
        def evaluate_pred_list(pred_list, ap_map_d):
            return all([ evaluate_pred(pred, ap_map_d) == tv for pred, tv in pred_list ])

        pred_term_mapping = self.get_pred_term_mapping()

        ret = []
        ap_vals = power_set_as_indicators(self.get_atomic_predicates())
        for ap_val in ap_vals:
            for pred_list, term in pred_term_mapping:
                if evaluate_pred_list(pred_list, dict(ap_val)):
                    ret.append((ap_val, term))
        assert len(ap_vals) == len(ret)
        return ret

    def do_complete_benchmark(self, initial_valuations, random_samples):
        import sample_sufficiency
        import icfp_helpers
        def _check_solution(sol):
            return self.check_solution(sol, random_samples)
        return sample_sufficiency.get_sufficient_samples(
                self.syn_ctx,
                self.synth_fun,
                icfp_helpers.icfp_grammar(self.syn_ctx, self.synth_fun, full_grammer=True),
                _check_solution,
                initial_valuations,
                divide_and_conquer=True)



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

def test_max_sizes(generators):
    for generator in generators:
        term_size = generator.get_max_term_size()
        pred_size = generator.get_max_atomic_pred_size()
        print(generator.id, '->', term_size, ',', pred_size)

def test_get_all_terms(generators):
    for generator in generators:
        terms = generator.get_all_terms()
        print(generator.id, '->')
        for t in terms:
            print('\t',  _expr_to_str(t))

def test_get_pred_term_mapping(generators):
    for generator in generators:
        solution = generator.solution
        pred_term_mapping = generator.get_pred_term_mapping()
        print(generator.id, '->')
        for preds, term in pred_term_mapping:
            print('\t', [ (_expr_to_str(p[0]), p[1]) for p in preds ], "====>", _expr_to_str(term))

def test_get_atomic_predicates(generators):
    for generator in generators:
        print(generator.id, '->')
        for ap in generator.get_atomic_predicates():
            print('\t', _expr_to_str(ap))

def test_get_atomic_pred_term_mapping(generators):
    for generator in generators:
        print(generator.id, '->')
        for ap,term in generator.get_atomic_pred_term_mapping():
            for p,tv in ap:
                print('\t', _expr_to_str(p), tv)
            print('\t\t', '====>', _expr_to_str(term))


if __name__ == '__main__':
    generators = test_parsing(debug=False)
    # test_get_all_terms(generators)
    test_max_sizes(generators)
    # test_get_pred_term_mapping(generators)
    # test_get_atomic_predicates(generators)
    # test_get_atomic_pred_term_mapping(generators)

