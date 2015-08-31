#!/usr/bin/env python3
# semantics_core.py ---
#
# Filename: semantics_core.py
# Author: Abhishek Udupa
# Created: Tue Aug 18 16:25:53 2015 (-0400)
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
"""This module implements the semantics for the core theory,
i.e., equality, conditionals and basic boolean operations."""

import basetypes
from enum import IntEnum
import exprs
import exprtypes
import functools
import utils
import z3

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

class _BuiltinFunctionBase(_FunctionBase):
    """A base class for builtin functions."""
    def __init__(self, function_code,
                 function_name, function_arity,
                 domain_types, range_type):
        super().__init__(FunctionKinds.builtin_function, function_name,
                         function_arity, domain_types, range_type)
        self.function_code = function_code


class EqFunction(_BuiltinFunctionBase):
    """A function object for equality. Parametrized by the domain type."""
    def __init__(self, domain_type):
        super().__init__(BuiltInFunctionCodes.builtin_function_eq, '=', 2,
                         (domain_type, domain_type), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return (child_terms[0] == child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (eval_context_object.peek(0).actual_value ==
                  eval_context_object.peek(1).actual_value)
        eval_context_object.pop(2)
        eval_context_object.push_raw_value(result)


class AndFunction(_BuiltinFunctionBase):
    """A function object for conjunctions. Allows arbitrary number of arguments."""
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_and, 'and', -1,
                         (exprtypes.BoolType(), ), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return z3.And(*child_terms)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = True
        for i in range(len(expr_object.children)):
            if (not eval_context_object.peek(i).actual_value):
                result = False
                break
        eval_context_object.pop(len(expr_object.children))
        eval_context_object.push_raw_value(result)


class OrFunction(_BuiltinFunctionBase):
    """A function object for disjunctions. Allows arbitrary number of arguments."""
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_or, 'or', -1,
                         (exprtypes.BoolType(), ), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return z3.Or(*child_terms)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = False
        for i in range(len(expr_object.children)):
            if (eval_context_object.peek(i).actual_value):
                result = True
                break
        eval_context_object.pop(len(expr_object.children))
        eval_context_object.push_raw_value(result)


class NotFunction(_BuiltinFunctionBase):
    """A function object for negation."""
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_not, 'not', 1,
                         (exprtypes.BoolType(),), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return z3.Not(child_terms[0])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (not eval_context_object.peek(0).actual_value)
        eval_context_object.pop(1)
        eval_context_object.push_raw_value(result)


class ImpliesFunction(_BuiltinFunctionBase):
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_implies, 'implies', 2,
                         (exprtypes.BoolType(), exprtypes.BoolType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return z3.Implies(child_terms[0], child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        b = eval_context_object.peek(0)
        a = eval_context_object.peek(1)
        result = ((not a.actual_value) or (b.actual_value))
        eval_context_object.pop(2)
        eval_context_object.push_raw_value(result)

class IffFunction(_BuiltinFunctionBase):
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_iff, 'iff', 2,
                         (exprtypes.BoolType(), exprtypes.BoolType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return (child_terms[0] == child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object):
        result = (eval_context_object.peek(0).actual_value ==
                  eval_context_object.peek(1).actual_value)

        eval_context_object.pop(2)
        eval_context_object.push_raw_value(result)

class XorFunction(_BuiltinFunctionBase):
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_xor, 'xor', 2,
                         (exprtypes.BoolType(), exprtypes.BoolType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return z3.Xor(child_terms[0], child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object):
        result = (eval_context_object.peek(0).actual_value !=
                  eval_context_object.peek(1).actual_value)

        eval_context_object.pop(2)
        eval_context_object.push_raw_value(result)

class IteFunction(_BuiltinFunctionBase):
    def __init__(self, range_type):
        super().__init__(BuiltInFunctionCodes.builtin_function_ite, 'ite', 3,
                         (exprtypes.BoolType(), range_type, range_type), range_type)

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object);
        return z3.If(child_terms[0], child_terms[1], child_terms[2])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_expr(expr_object.children[0], eval_context_object)
        condition = eval_context_object.peek(0).actual_value
        eval_context_object.pop(1)
        if (condition):
            self._evaluate_expr(expr_object.children[1], eval_context_object)
        else:
            self._evaluate_expr(expr_object.children[2], eval_context_object)

class AddFunction(_BuiltinFunctionBase):
    def __init__(self):
        super().__init__(BuiltInFunctionCodes.builtin_function_add, 'add', -1,
                         (exprtypes.IntType(), ), exprtypes.IntType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return z3.Sum(*child_terms)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        num_children = len(expr_object.children)
        retval = 0
        for i in range(num_children):
            retval += eval_context_object.peek(i)
#
# operators.py ends here
