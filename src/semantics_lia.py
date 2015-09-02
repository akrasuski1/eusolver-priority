#!/usr/bin/env python3
# semantics_lia.py ---
# Filename: semantics_lia.py
# Author: Abhishek Udupa
# Created: Mon Aug 31 21:50:39 2015 (-0400)
#
# Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
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

import basetypes
import exprs
import exprtypes
import functools
import utils
import z3
import semantics_types
from semantics_types import FunctionBase, InterpretedFunctionBase
from semantics_types import UnknownFunctionBase

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

class AddFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('add', -1, (exprtypes.IntType(), ), exprtypes.IntType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Sum(*child_terms)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        num_children = len(expr_object.children)
        retval = sum(eval_context_object.peek_items(num_children))
        eval_context_object.pop(num_children)
        eval_context_object.push(retval)


class SubFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('sub', 2, (exprtypes.IntType(), exprtypes.IntType()), exprtypes.IntType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return child_terms[0] - child_terms[1]

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        retval = eval_context_object.peek(1) - eval_context_object.peek(0)
        eval_context_object.pop(2)
        eval_context_object.push(retval)


class MinusFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('sub', 1, (exprtypes.IntType(),), exprtypes.IntType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return -(child_terms[0])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        retval = -(eval_context_object.peek())
        eval_context_object.pop()
        eval_context_object.push(retval)


class MulFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('mul', -1 (exprtypes.IntType(), ), exprtypes.IntType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Product(*child_terms)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        num_children = len(expr_object.children)
        retval = functools.reduce(lambda x,y: x*y, eval_context_object.peek_items(num_children), 1)
        eval_context_object.pop(num_children)
        eval_context_object.push(retval)


class DivFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('div', -1, (exprtypes.IntType(), exprtypes.IntType()), exprtypes.IntType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return child_terms[0] / child_terms[1]

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = self.peek(1) / self.peek(0)
        eval_context_object.pop(2)
        eval_context_object.push(res)


class LEFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('<=', 2, (exprtypes.IntType(), exprtypes.IntType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return child_terms[0] <= child_terms[1]

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(1) <= eval_context_object.peek(0))
        eval_context_object.pop(2)
        eval_context_object.push(res)


class LTFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('<', 2, (exprtypes.IntType(), exprtypes.IntType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return child_terms[0] < child_terms[1]

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(1) < eval_context_object.peek(0))
        eval_context_object.pop(2)
        eval_context_object.push(res)


class GEFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('>=', 2, (exprtypes.IntType(), exprtypes.IntType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return child_terms[0] >= child_terms[1]

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(1) >= eval_context_object.peek(0))
        eval_context_object.pop(2)
        eval_context_object.push(res)


class GTFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('>', 2, (exprtypes.IntType(), exprtypes.IntType()), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return child_terms[0] > child_terms[1]

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(1) > eval_context_object.peek(0))
        eval_context_object.pop(2)
        eval_context_object.push(res)


class LIAInstantiator(semantics_types.InstantiatorBase):
    def __init__(self):
        super().__init__('lia')
        self.add_instance = None
        self.mul_instance = None

    def _get_add_instance(self):
        if (self.add_instance == None):
            self.add_instance = AddFunction()
        return self.add_instance

    def _get_mul_instance(self):
        if (self.mul_instance == None):
            self.mul_instance = MulFunction()
        return self.mul_instance

    def _get_canonical_function_name(self, function_name):
        if (function_name == '+' or function_name == 'add'):
            return 'add'
        elif (function_name == '-' or function_name == 'sub'):
            return 'sub'
        elif (function_name == '*' or function_name == 'mul'):
            return 'mul'
        elif (function_name == '/' or function_name == 'div'):
            return 'div'
        elif (function_name == 'le' or function_name == '<='):
            return 'le'
        elif (function_name == 'ge' or function_name == '>='):
            return 'ge'
        elif (function_name == 'lt' or function_name == '<'):
            return 'lt'
        elif (function_name == 'gt' or function_name == '>'):
            return 'gt'
        else:
            return function_name

    def _do_instantiation(self, function_name, mangled_name, arg_types):
        if (function_name == 'add' or function_name == 'mul'):
            if (len(arg_types) < 2 or
                (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.integer_type))):
                self._raise_failure(function_name, arg_types)

            if (function_name == 'add'):
                return self._get_add_instance()
            else:
                return self._get_mul_instance()

        elif (function_name == 'div' or function_name == 'sub'):
            if (len(arg_types) != 2 or
                (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.integer_type))):
                self._raise_failure(function_name, arg_types)

            if (function_name == 'div'):
                return DivFunction()
            else:
                return SubFunction()

        elif (function_name == 'minus'):
            if (len(arg_types != 1) or arg_types[0].type_code != exprtypes.TypeCodes.integer_type):
                self._raise_failure(function_name, arg_types)
            return MinusFunction()

        elif (function_name == 'le' or function_name == 'ge' or
              function_name == 'gt' or function_name == 'lt'):
            if (len(arg_types) != 2 or
                (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.integer_type))):
                self._raise_failure(function_name, arg_types)

            if (function_name == 'le'):
                return LEFunction()
            elif (function_name == 'ge'):
                return GEFunction()
            elif (function_name == 'lt'):
                return LTFunction()
            else:
                return GTFunction()

        else:
            self._raise_failure(function_name, arg_types)

#
# semantics_lia.py ends here
