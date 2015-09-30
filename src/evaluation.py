#!/usr/bin/env python3
# evaluation.py ---
#
# Filename: evaluation.py
# Author: Abhishek Udupa
# Created: Mon Aug 31 16:29:35 2015 (-0400)
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
import exprs
import basetypes

# if __name__ == '__main__':
#     utils.print_module_misuse_and_exit()

def evaluate_expression_on_stack(expr_object, eval_context):
    kind = expr_object.expr_kind
    if (kind == exprs.ExpressionKinds.variable_expression):
        o = expr_object.variable_info.variable_eval_offset
        eval_context.push(eval_context.valuation_map[o].value_object)
    elif (kind == exprs.ExpressionKinds.formal_parameter_expression):
        o = expr_object.parameter_position
        eval_context.push(eval_context.valuation_map[o].value_object)
    elif (kind == exprs.ExpressionKinds.constant_expression):
        eval_context.push(expr_object.value_object.value_object)
    elif (kind == exprs.ExpressionKinds.function_expression):
        fun_info = expr_object.function_info
        fun_info.evaluate(expr_object, eval_context)
    else:
        raise basetypes.UnhandledCaseError('Odd expression kind: %s' % kind)

def evaluate_expression_raw(expr_object, eval_context):
    evaluate_expression_on_stack(expr_object, eval_context)
    retval = eval_context.peek()
    eval_context.pop()
    return retval

def evaluate_expression(expr_object, eval_context):
    retval = evaluate_expression_raw(expr_object, eval_context)
    retval = exprs.Value(retval, exprs.get_expression_type(expr_object))
    return retval

class EvaluationContext(object):
    def __init__(self, eval_stack_size = 131072):
        self.eval_stack = [int(0)] * eval_stack_size
        self.eval_stack_size = eval_stack_size
        self.eval_stack_top = 0
        self.valuation_map = None
        self.interpretation_map = None

    def peek(self, peek_depth = 0):
        return self.eval_stack[self.eval_stack_top - 1 - peek_depth]

    def peek_items(self, peek_depth = 1):
        return self.eval_stack[(self.eval_stack_top - peek_depth):self.eval_stack_top]

    def pop(self, num_elems = 1):
        self.eval_stack_top -= num_elems

    def push(self, value_object):
        self.eval_stack[self.eval_stack_top] = value_object
        self.eval_stack_top += 1

    def set_valuation_map(self, valuation_map):
        self.valuation_map = valuation_map

    def clear_valuation_map(self):
        self.valuation_map = None

    def set_interpretation_map(self, interpretation_map):
        self.interpretation_map = interpretation_map

    def clear_interpretation_map(self):
        self.interpretation_map = None


def test_evaluation():
    import enumerators
    generator = enumerators._generate_test_generators()
    generator.set_size(8)
    points = [(1, 2, 3), (2, 5, 6), (6, 1, 3), (10, 4, 6), (7, 1, 5)]
    eval_context = EvaluationContext()
    for expr in generator.generate():
        cur_sig = [None] * len(points)
        for i in range(len(points)):
            eval_context.set_valuation_map(points[i])
            cur_sig[i] = evaluate_expression_raw(expr, eval_context)
        print((exprs.expression_to_string(expr), tuple(cur_sig)))

if __name__ == '__main__':
    test_evaluation()

#
# evaluation.py ends here
