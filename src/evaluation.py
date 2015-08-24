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

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

class EvalValue(object):
    """Represents a (typed) value."""
    def __init__(self, value_type, actual_value):
        self.value_type = value_type
        self.actual_value = actual_value

    def __eq__(self, other):
        return ((self.value_type == other.value_type) and
                (self.actual_value == other.actual_value))

    def __neq__(self, other):
        return (not (self.__eq__(other)))

    def __str__(self, other):
        if (self.value_type == exprtypes.BoolType() ||
            self.value_type == exprtypes.IntType()):
            return str(self.actual_value)
        elif (self.value_type.typecode == exprtypes.TypeCodes.bit_vector_type):
            if (self.value_type.size % 4 == 0):
                format_string = '0%dX' % self.value_type.size / 4
                prefix_string = '#x'
            else:
                format_string = '0%db' % self.value_type.size
                prefix_string = '#b'
            return prefix_string + format(self.actual_value, format_string)

class EvaluationContext(object):
    """Provides a context (an evaluation stack) for evaluating expressions."""
    default_eval_stack_size = 4096
    def __init__(self, eval_stack_size = default_eval_stack_size):
        self.eval_stack = [EvalValue(exprtypes.IntType(), 0)] * eval_stack_size
        self.eval_stack_top = 0

    def push(self, new_value, value_type = None):
        """Can either have new_value to be an EvalValue object, or
        something that can be used together with value_type to construct
        an EvalValue object."""

        if (value_type == None):
            self.eval_stack[self.eval_stack_top] = new_value
        else:
            self.eval_stack[self.eval_stack_top] = EvalValue(value_type, new_value)
        self.eval_stack_top += 1

    def push_raw_value(self, new_value, value_type = None):
        self.eval_stack[self.eval_stack_top].value_type = value_type
        self.eval_stack[self.eval_stack_top].actual_value = new_value
        self.eval_stack_top += 1

    def peek(self, depth = 0):
        return self.eval_stack[self.eval_stack_top - depth - 1]

    def pop(self, num_items = 1):
        self.eval_stack_top -= num_items

#
# evaluation.py ends here
