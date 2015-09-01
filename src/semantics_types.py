#!/usr/bin/env python3
# semantics_types.py ---
#
# Filename: semantics_types.py
# Author: Abhishek Udupa
# Created: Mon Aug 31 17:00:48 2015 (-0400)
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

"""This module implements some base types required for defining semantics of
various function symbols."""

import basetypes
import utils
import exprtypes
from evaluation import evaluate_expression, evaluate_expression_raw,
from evaluation import evaluate_expression_on_stack
import evaluation
import exprs
import z3

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

class FunctionKinds(IntEnum):
    """Function Kinds.
    builtin_function: represents a builtin function.
    macro_function: represents a user defined macro.
    unknown_function: represents a function to be synthesized for.
    """
    interpreted_function = 1
    unknown_function = 2

def mangle_function_name(function_name, domain_types):
    return '_'.join([function_name] + [str(dom_type.typeid) for dom_type in domain_types])


def _to_smt_variable_expression(expr_object, smt_context_object, var_subst_map):
    var_info = expr_object.variable_info
    if (var_subst_map == None):
        var_type = var_info.variable_type
        var_type_smt = var_type.get_smt_type(smt_context_object)
        var_name = var_info.variable_name
        return z3.Const(var_name, var_type_smt)
    else:
        return var_subst_map[var_info.variable_eval_offset]

def _to_smt_constant_expression(expr_object, smt_context_object):
    val_obj = expr_object.val_obj
    constant_type = val_obj.value_type
    if (constant_type.type_code == exprtypes.TypeCodes.boolean_type):
        return z3.BoolVal(val_obj.value_object, smt_context_object.ctx())
    elif (constant_type.type_code == exprtypes.TypeCodes.integer_type):
        return z3.IntVal(val_obj.value_object, smt_context_object.ctx())
    elif (constant_type.type_code == exprtypes.TypeCodes.bit_vector_type):
        return z3.BitVecVal(val_obj.value_object, constant_type.size,
                            smt_context_object.ctx())
    else:
        raise basetypes.UnhandledCaseError('Odd type code: %s' % constant_type.type_code)


def expression_to_smt(expr_object, smt_context_object, var_subst_map = None):
    kind = expr_object.expr_kind
    if (kind == exprs.ExpressionKinds.variable_expression):
        return _to_smt_variable_expression(expr_object, smt_context_object, var_subst_map)
    elif (kind == exprs.ExpressionKinds.constant_expression):
        return _to_smt_constant_expression(expr_object, smt_context_object)
    elif (kind == exprs.ExpressionKinds.function_expression):
        fun_info = expr_object.function_info
        return fun_info.to_smt(expr_object, smt_context_object, var_subst_map)
    else:
        raise basetypes.UnhandledCaseError('Odd expression kind: %s' % kind)


class FunctionBase(object):
    """A base class for functions.
    Manages the following aspects of a function:
    Arity: negative values indicate arbitrary arity,
        i.e., the function is associative and commutative
    DomainTypes: A tuple that indicates the types of the domain of the function.
        The tuple should have the same size as the arity, unless the arity is
        negative, in which case, the tuple ought to contain only one element.
    RangeType: The type of the range of the function.
    Provides some convenience methods for evaluating children, etc.
    """
    def __init__(self, function_kind, function_name, function_arity,
                 domain_types, range_type):
        assert function_arity != 0, "Arity of functions cannot be zero!"

        self.function_kind = function_kind
        self.function_name = function_name
        self.function_arity = function_arity
        self.domain_types = domain_types
        self.range_type = range_type

        if (function_arity > 0):
            assert (len(domain_types) == function_arity), "Size of domain must be equal to arity!"
        else:
            assert len(domain_types) == 1, ("Only one domain type is allowed for " +
                                            "associative and commutative functions")
        # build the mangled function name
        self.mangled_function_name = mangle_function_name(self.function_name, self.domain_types)

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        raise basetypes.AbstractMethodError('FunctionBase.to_smt()')

    def evaluate(self, expr_object, eval_context_object):
        raise basetypes.AbstractMethodError('FunctionBase.evaluate()')

    def _evaluate_expr(self, expr_object, eval_context_object):
        evaluate_expression_on_stack(expr_object, eval_context_object)

    def _evaluate_children(self, expr_object, eval_context_object):
        for child in expr_object.children:
            evaluate_expression_on_stack(child, eval_context_object)

    def _to_smt_children(self, expr_object, smt_context_object, var_subst_map = None):
        assert (expr_object.expr_kind == exprs.ExpressionKinds.function_expression)
        return [expression_to_smt(child, smt_context_object, var_subst_map)
                for child in expr_object.children]


class UnknownFunctionBase(FunctionBase):
    _undefined_function_id = 1000000000
    def __init__(self, function_name, function_arity, domain_types, range_type):
        super().__init__(FunctionKinds.unknown_function, function_name, function_arity,
                         domain_types, range_type)
        assert (len(domain_types) == function_arity)
        self.unknown_function_id = _undefined_function_id

    def evaluate(self, expr_object, eval_context_object):
        """The eval_context_object is assumed to have a map called interpretations.
        The interpretation will be an expression, except that it will be in terms of
        the formal parameters to the function. We substitute the formal parameters
        with the values obtained by evaluating the children."""

        num_children = len(expr_object.children)
        self._evaluate_children(expr_object, eval_context_object)
        parameter_map = eval_context_object.peek_items(num_children)
        eval_context_object.pop(num_children)

        orig_valuation_map = eval_context_object.valuation_map
        eval_context_object.valuation_map = parameter_map
        interpretation = eval_context_object.interpretation_map[self.unknown_function_id]
        evaluate_expression_on_stack(interpretation, eval_context_object)
        eval_context_object.valuation_map = orig_valuation_map

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._to_smt_children(expr_object, smt_context_object, var_subst_map)
        interpretation = smt_context_object.interpretation_map[self.unknown_function_id]
        return expression_to_smt(interpretation, smt_context_object, child_terms)


class InterpretedFunctionBase(FunctionBase):
    def __init__(self, function_name, function_arity, domain_types, range_type):
        super().__init__(FunctionKinds.interpreted_function, function_name, function_arity,
                         domain_types, range_type)

class MacroFunction(InterpretedFunctionBase):
    def __init__(self, function_name, function_arity,
                 domain_types, range_type, interpretation_expression):
        super().__init__(FunctionKinds.interpreted_function, function_name, function_arity,
                         domain_types, range_type):
        assert (len(domain_types) == function_arity)
        self.interpretation_expression = interpretation_expression

    def evaluate(self, expr_object, eval_context_object):
        num_children = len(expr_object.children)
        self._evaluate_children(expr_object, eval_context_object)
        parameter_map = eval_context_object.peek_items(num_children)
        eval_context_object.pop(num_children)

        orig_valuation_map = eval_context_object.valuation_map
        eval_context_object.valuation_map = parameter_map
        evaluate_expression_on_stack(self.interpretation_expression, eval_context_object)
        eval_context_object.valuation_map = orig_valuation_map

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms =self._to_smt_children(expr_object, smt_context_object, var_subst_map)
        return expression_to_smt(self.interpretation_expression, smt_context_object, child_terms)


class InstantiatorBase(object):
    def __init__(self, logic_name):
        self.name = 'instantiator_' + logic_name
        self.function_object_map = {}

    def find_cached(self, mangled_function_name):
        return self.function_object_map.get(mangled_function_name, None)

    def add_to_cache(self, mangled_function_name, function_object):
        self.function_object_map[mangled_function_name] = function_object

    def instantiate(function_name, child_exps):
        canonical_function_name = self._get_canonical_function_name(function_name)
        arg_types = [exprs.get_expression_type(x) for x in child_exps]
        mangled_name = semantics_types.mangle_function_name(canonical_function_name, arg_types)
        cached = self.find_cached(mangled_name)
        if (cached != None):
            return cached

        retval = self._do_instantiation(function_name, mangled_name, arg_types)
        self.add_to_cache(retval.mangled_function_name, retval)
        return retval

    def _is_all_of_type(self, iterable, type_code):
        return utils.all_of(iterable, lambda t: t.type_code == type_code)

    def _raise_failure(function_name, arg_types):
        error_msg = 'Could not instantiate function ' + function_name
        error_msg += ' with argument types ('
        error_msg += (', '.join([str(arg_type) for arg_type in arg_types]) + ')')
        raise TypeError(error_msg)

    def _do_instantiation(self, function_name, mangled_name, arg_types):
        raise basetypes.AbstractMethodError('InstantiatorBase._do_instantiation()')

    def _get_canonical_function_name(self, function_name):
        raise basetypes.AbstractMethodError('InstantiatorBase._get_canonical_function_name()')


#
# semantics_types.py ends here
