#!/usr/bin/env python3
# operators.py ---
#
# Filename: operators.py
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

import utils
import basetypes
from enum import IntEnum
import z3

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

class FunctionKinds(IntEnum):
    """Function Kinds.
    builtin_function: represents a builtin function.
    macro_function: represents a user defined macro.
    unknown_function: represents a function to be synthesized for.
    """
    builtin_function = 1
    macro_function = 2
    unknown_function = 3


class _FunctionBase(object):
    """A base class for function.
    Manages the following aspects of a function:
    Arity: negative values indicate arbitrary arity,
        i.e., the function is associative and commutative
    DomainTypes: A tuple that indicates the types of the domain of the function.
        The tuple should have the same size as the arity, unless the arity is
        negative, in which case, the tuple ought to contain only one element.
    RangeType: The type of the range of the function
    """
    def __init__(self, function_kind, function_name,
                 function_arity, domain_types, range_type):
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


    def to_smt(self, expr_object, smt_context_object):
        raise AbstractMethodError('OperatorBase.to_smt()')

    def evaluate(self, expr_object, eval_context_object):
        raise AbstractMethodError('OperatorBase.evaluate()')

    def _children_to_smt(self, expr_object, smt_context_object):
        """Returns a tuple containing the smt terms representing the children."""
        return (tuple(x.function_info.to_smt(x, smt_context_object)
                      for x in expr_object.children))

    def _evaluate_children(self, expr_object, eval_context_object):
        """Pushes the values obtained from the evaluation of the children
        onto the evaluation stack of the eval_context_object."""
        for child in expr_object.children:
            child.function_info.evaluate(child, eval_context_object)


class BuiltInFunctionCodes(IntEnum):
    """Represents codes for the set of built-in functions"""
    # builtins for the CORE logic
    builtin_function_eq = 1
    builtin_function_and = 2
    builtin_function_or = 3
    builtin_function_not = 4
    builtin_function_implies = 5
    builtin_function_iff = 6
    builtin_function_xor = 7
    builtin_function_xnor = 8
    builtin_function_ite = 9

    # builtins for LIA
    builtin_function_add = 10
    builtin_function_sub = 11
    builtin_function_minus = 12
    builtin_function_mul = 13
    builtin_function_div = 14

    # builtins for BV
    builtin_function_bvconcat = 15
    builtin_function_bvextract = 16
    builtin_function_bvnot = 17
    builtin_function_bvand = 18
    builtin_function_bvor = 19
    builtin_function_bvneg = 20
    builtin_function_bvadd = 21
    builtin_function_bvmul = 22
    builtin_function_bvudiv = 23
    builtin_function_bvurem = 24
    builtin_function_bvshl = 25
    builtin_function_bvlshr = 26
    builtin_function_bvult = 27
    builtin_function_bvnand = 28
    builtin_function_bvnor = 29
    builtin_function_bvxor = 30
    builtin_function_bvxnor = 31
    builtin_function_bvcomp = 32
    builtin_function_bvsub = 33
    builtin_function_bvsdiv = 34
    builtin_function_bvsrem = 35
    builtin_function_bvsmod = 36
    builtin_function_bvashr = 37
    builtin_function_bvule = 38
    builtin_function_bvugt = 39
    builtin_function_bvuge = 40
    builtin_function_bvslt = 41
    builtin_function_bvsle = 42
    builtin_function_bvsgt = 43
    builtin_function_bvsge = 44

    # all builtin functions must be below this
    # value
    builtin_function_max_sentinel = 1000000


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
    def __init__(domain_type):
        super().__init__(BuiltInFunctionCodes.builtin_function_eq, '=', 2,
                         (domain_type, domain_type), exprtypes.BoolType())

    def to_smt(self, expr_object, smt_context_object):
        child_terms = self._children_to_smt(expr_object, smt_context_object)
        return (child_terms[0] == child_terms[1])

    def evaluate(self, expr_object,


#
# operators.py ends here
