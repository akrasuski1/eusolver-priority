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

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

class OperatorTypes(IntEnum):
    """Operator types
    builtin_function_operator: represents a builtin function.
    macro_function_operator: represents a user defined macro.
    unknown_function_operator: represents a function to be synthesized for.
    """
    builtin_function_operator = 1
    macro_function_operator = 2
    unknown_function_operator = 3

class _OperatorBase(object):
    """A base class for operators. Only manages OperatorTypes"""
    def __init__(self, operator_type):
        self.operator_type = operator_type

    def __str__(self):
        raise AbstractMethodError('OperatorBase.__str__()')

    def __repr__(self):
        raise AbstractMethodError('OperatorBase.__repr__()')

    def to_smt(self, expr_object, smt_context_object):
        raise AbstractMethodError('OperatorBase.to_smt()')

    def evaluate(self, expr_object, eval_context_object):
        raise AbstractMethodError('OperatorBase.evaluate()')

class BuiltInFunctionCodes(IntEnum):
    """Represents codes for the set of built-in functions"""
    # builtins for the CORE logic
    builtin_operator_eq = 1
    builtin_operator_and = 2
    builtin_operator_or = 3
    builtin_operator_not = 4
    builtin_operator_implies = 5
    builtin_operator_iff = 6
    builtin_operator_xor = 7
    builtin_operator_xnor = 8
    builtin_operator_ite = 9

    # builtins for LIA
    builtin_operator_add = 10
    builtin_operator_sub = 11
    builtin_operator_minus = 12
    builtin_operator_mul = 13
    builtin_operator_div = 14

    # builtins for BV
    builtin_operator_bvconcat = 15
    builtin_operator_bvextract = 16
    builtin_operator_bvnot = 17
    builtin_operator_bvand = 18
    builtin_operator_bvor = 19
    builtin_operator_bvneg = 20
    builtin_operator_bvadd = 21
    builtin_operator_bvmul = 22
    builtin_operator_bvudiv = 23
    builtin_operator_bvurem = 24
    builtin_operator_bvshl = 25
    builtin_operator_bvlshr = 26
    builtin_operator_bvult = 27
    builtin_operator_bvnand = 28
    builtin_operator_bvnor = 29
    builtin_operator_bvxor = 30
    builtin_operator_bvxnor = 31
    builtin_operator_bvcomp = 32
    builtin_operator_bvsub = 33
    builtin_operator_bvsdiv = 34
    builtin_operator_bvsrem = 35
    builtin_operator_bvsmod = 36
    builtin_operator_bvashr = 37
    builtin_operator_bvule = 38
    builtin_operator_bvugt = 39
    builtin_operator_bvuge = 40
    builtin_operator_bvslt = 41
    builtin_operator_bvsle = 42
    builtin_operator_bvsgt = 43
    builtin_operator_bvsge = 44

    # all builtin functions must be below this
    # value
    builtin_operator_max_sentinel = 1000000


class BuiltInFunctionBase(OperatorBase):
    """A base class for "builtin" functions"""
    def __init__(self, operator_code):
        super().__init__()
        self.operator_code = operator_code

#
# operators.py ends here
