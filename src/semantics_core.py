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
import exprs
import exprtypes
import utils
import z3
import semantics_types
from semantics_types import FunctionBase, InterpretedFunctionBase

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()


class EqFunction(InterpretedFunctionBase):
    """A function object for equality. Parametrized by the domain type."""
    def __init__(self, domain_type):
        super().__init__('=', 2, (domain_type, domain_type), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] == child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (eval_context_object.peek(0) == eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(result)


class NeFunction(InterpretedFunctionBase):
    def __init__(self, domain_type):
        super().__init__('ne', 2, (domain_type, domain_type), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] != child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (eval_context_object.peek(0) != eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(result)


class AndFunction(InterpretedFunctionBase):
    """A function object for conjunctions. Allows arbitrary number of arguments."""
    def __init__(self):
        super().__init__('and', -1, (exprtypes.BoolType(), ), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.And(*(child_terms + [child_terms[0].ctx]))

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = True
        num_children = len(expr_object.children)
        for i in range(num_children):
            if (not eval_context_object.peek(i)):
                result = False
                break
        eval_context_object.pop(num_children)
        eval_context_object.push(result)


class OrFunction(InterpretedFunctionBase):
    """A function object for disjunctions. Allows arbitrary number of arguments."""
    def __init__(self):
        super().__init__('or', -1, (exprtypes.BoolType(), ), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Or(*(child_terms + [child_terms[0].ctx]))

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        num_children = len(expr_object.children)
        result = False
        for i in range(num_children):
            if (eval_context_object.peek(i)):
                result = True
                break
        eval_context_object.pop(num_children)
        eval_context_object.push(result)


class NotFunction(InterpretedFunctionBase):
    """A function object for negation."""
    def __init__(self):
        super().__init__('not', 1, (exprtypes.BoolType(),), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Not(child_terms[0])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (not eval_context_object.peek())
        eval_context_object.pop()
        eval_context_object.push(result)


class ImpliesFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('implies', 2, (exprtypes.BoolType(), exprtypes.BoolType()),
                         exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Implies(child_terms[0], child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        b = eval_context_object.peek(0)
        a = eval_context_object.peek(1)
        result = ((not a) or b)
        eval_context_object.pop(2)
        eval_context_object.push(result)


class IffFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('iff', 2, (exprtypes.BoolType(), exprtypes.BoolType()),
                         exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] == child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (eval_context_object.peek(0) == eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(result)


class XorFunction(InterpretedFunctionBase):
    def __init__(self):
        super().__init__('xor', 2, (exprtypes.BoolType(), exprtypes.BoolType()),
                         exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Xor(child_terms[0], child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        result = (eval_context_object.peek(0) != eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(result)


class IteFunction(InterpretedFunctionBase):
    def __init__(self, range_type):
        super().__init__('ite', 3, (exprtypes.BoolType(),
                                    range_type, range_type),
                         range_type)

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.If(child_terms[0], child_terms[1], child_terms[2])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_expr(expr_object.children[0], eval_context_object)
        condition = eval_context_object.peek(0)
        eval_context_object.pop(1)
        if (condition):
            self._evaluate_expr(expr_object.children[1], eval_context_object)
        else:
            self._evaluate_expr(expr_object.children[2], eval_context_object)


class CoreInstantiator(semantics_types.InstantiatorBase):
    def __init__(self):
        super().__init__('core')
        self.and_instance = None
        self.or_instance = None

    def _get_and_instance(self):
        if (self.and_instance == None):
            self.and_instance = AndFunction()
        return self.and_instance

    def _get_or_instance(self):
        if (self.or_instance == None):
            self.or_instance = OrFunction()
        return self.or_instance

    def _get_canonical_function_name(self, function_name):
        if (function_name == '=' or function_name == 'eq'):
            return 'eq'
        elif (function_name == '!=' or function_name == 'ne'):
            return 'ne'
        else:
            return function_name

    def _do_instantiation(self, function_name, mangled_name, arg_types):
        function_name = self._get_canonical_function_name(function_name)
        if (function_name == 'eq' or function_name == 'ne'):
            if (len(arg_types) != 2 or arg_types[0] != arg_types[1]):
                self._raise_failure(function_name, arg_types)
            if (function_name == 'eq'):
                return EqFunction(arg_types[0])
            else:
                return NeFunction(arg_types[0])

        elif (function_name == 'and' or function_name == 'or'):
            if (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.boolean_type)):
                self._raise_failure(function_name, arg_types)
            return self._get_and_instance() if function_name == 'and' else self._get_or_instance()

        elif (function_name == 'not'):
            if (len(arg_types) != 1 or arg_types[0].type_code != exprtypes.TypeCodes.boolean_type):
                self._raise_failure(function_name, arg_types)
            return NotFunction()

        elif (function_name == 'implies' or function_name == 'iff' or function_name == 'xor'):
            if (len(arg_types) != 2 or
                (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.boolean_type))):
                self._raise_failure(function_name, arg_types)
            if (function_name == 'implies'):
                return ImpliesFunction()
            elif (function_name == 'iff'):
                return IffFunction()
            else:
                return XorFunction()

        elif (function_name == 'ite'):
            if (len(arg_types) != 3 or
                arg_types[0].type_code != exprtypes.TypeCodes.boolean_type or
                arg_types[1] != arg_types[2]):
                self._raise_failure(function_name, arg_types)
            return IteFunction(arg_types[1])

        else:
            return None


class MacroInstantiator(semantics_types.InstantiatorBase):
    def __init__(self, function_interpretations={}):
        super().__init__('macro')
        self.function_interpretations = function_interpretations

    def _do_instantiation(self, function_name, mangled_name, arg_types):
        if function_name not in self.function_interpretations:
            return None

        function_interpretation = self.function_interpretations[function_name]
        assert function_name == function_interpretation.function_name
        assert len(arg_types) == function_interpretation.function_arity
        assert arg_types == function_interpretation.domain_types

        return function_interpretation

    def _get_canonical_function_name(self, function_name):
        return function_name

    def add_function(self, function_name, function_interpretation):
        self.function_interpretations[function_name] = function_interpretation

#
# semantics_core.py ends here
