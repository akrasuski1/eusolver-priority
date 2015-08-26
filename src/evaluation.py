#!/usr/bin/env python3
# evaluation.py ---
#
# Filename: evaluation.py
# Author: Abhishek Udupa
# Created: Mon Aug 24 14:03:03 2015 (-0400)
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

import utils
import exprtypes
import sys
import functools
import hashcache

# if __name__ == '__main__':
#     utils.print_module_misuse_and_exit()

def _evaluate_and(expr, point_map):
    eval_values = [evaluate(x, point_map) for x in expr[1:]]
    return functools.reduce(lambda x, y: (x and y), eval_values)

def _evaluate_or(expr, point_map):
    eval_values = [evaluate(x, point_map) for x in expr[1:]]
    return functools.reduce(lambda x, y: (x or y), eval_values)

def _evaluate_not(expr, point_map):
    res = evaluate(expr[1], point_map)
    return (not res)

def _evaluate_implies(expr, point_map):
    ant = evaluate(expr[1], point_map)
    con = evaluate(expr[2], point_map)
    return ((not ant) or con)

def _evaluate_xor(expr, point_map):
    eval_values = [evaluate(x, point_map) for x in expr[1:]]
    return (eval_values[0] != eval_values[1])

def _evaluate_eq(expr, point_map):
    eval_values = [evaluate(x, point_map) for x in expr[1:]]
    return (eval_values[0] == eval_values[1])

def _evaluate_ne(expr, point_map):
    eval_values = [evaluate(x, point_map) for x in expr[1:]]
    return (eval_values[0] != eval_values[1])

def _evaluate_ite(expr, point_map):
    eval_cond = evaluate(expr[1], point_map)
    if (eval_cond):
        return evaluate(expr[2], point_map)
    else:
        return evaluate(expr[3], point_map)

def _evaluate_add(expr, point_map):
    return functools.reduce(lambda x, y: (x + y), [evaluate(x, point_map) for x in expr[1:]])

def _evaluate_sub(expr, point_map):
    return functools.reduce(lambda x, y: (x - y), [evaluate(x, point_map) for x in expr[2:]], evaluate(expr[1], point_map))

def _evaluate_le(expr, point_map):
    return (evaluate(expr[1], point_map) <= evaluate(expr[2], point_map))

def _evaluate_ge(expr, point_map):
    return (evaluate(expr[1], point_map) >= evaluate(expr[2], point_map))

def _evaluate_lt(expr, point_map):
    return (evaluate(expr[1], point_map) < evaluate(expr[2], point_map))

def _evaluate_gt(expr, point_map):
    return (evaluate(expr[1], point_map) > evaluate(expr[2], point_map))

def evaluate(expr, point_map):
    if (not isinstance(expr, tuple)):
        # constant or variable
        if (isinstance(expr, str)):
            # variable
            return point_map[expr]
        else:
            # constant
            return expr
    else:
        # function application
        evaluator_name = '_evaluate_%s' % expr[0]
        evaluator = getattr(sys.modules[__name__], evaluator_name)
        return evaluator(expr, point_map)


class ConcreteEvaluator(object):
    def __init__(self, hash_cache_num_sets = (1 << 20),
                 hash_cache_associativity = 1,
                 hash_cache_replacement_function = hashcache.RandomReplacementFunction(),
                 hash_cache_hash_function = hashcache.default_hash_function):
        self.points = []
        self.signature_cache = hashcache.HashCache(hash_cache_num_sets,
                                                   hash_cache_associativity,
                                                   hash_cache_replacement_function,
                                                   hash_cache_hash_function)

    def add_point(self, point_map):
        self.points.append(point_map)

    def compute_signature(self, expr):
        return tuple([evaluate(expr, x) for x in self.points])

    def validate(self, expr):
        sig = self.compute_signature(expr)
        if (self.signature_cache.exists(sig)):
            return False
        else:
            self.signature_cache.insert(sig)
            return True


def test_evaluation():
    enumerator_module = __import__('enumerators')
    assert(enumerator_module != None)

    concrete_evaluator = ConcreteEvaluator()

    generator = enumerator_module._generate_test_generators()
    generator.set_size(8)

    concrete_evaluator.add_point({'varA' : 3, 'varB' : 5, 'varC' : 4})
    concrete_evaluator.add_point({'varA' : 5, 'varB' : 10, 'varC' : 2})
    concrete_evaluator.add_point({'varA' : 15, 'varB' : 6, 'varC' : 10})
    concrete_evaluator.add_point({'varA' : 42, 'varB' : 4, 'varC' : 8})
    concrete_evaluator.add_point({'varA' : 4, 'varB' : 42, 'varC' : 84})

    for expr in generator.generate():
        print(concrete_evaluator.compute_signature(expr))

if __name__ == '__main__':
    test_evaluation()

#
# evaluation.py ends here
