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

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

def OperatorTypes(IntEnum):
    built_in_function_operator = 1
    macro_function_operator = 2
    unknown_function_operator = 3

def OperatorBase(object):
    """A base class for operators. Only manages OperatorTypes"""
    def __init__(self, operator_type):
        self.operator_type = operator_type

    def __str__(self):
        raise AbstractMethodError('OperatorBase.__str__()')

    def __repr__(self):
        raise AbstractMethodError('OperatorBase.__repr__()')

    def to_smt(self, expr_object):
        raise AbstractMethodError('OperatorBase.to_smt()')

    def evaluate(self, expr_object):
        raise AbstractMethodError('OperatorBase.evaluate()')

def BuiltInFunctionCodes(IntEnum):
    """Represents codes for the set of built-in functions"""
    # builtins for the CORE logic
    built_in_operator_eq = 1
    built_in_operator_and = 2
    built_in_operator_or = 3
    built_in_operator_not = 4
    built_in_operator_implies = 5
    built_in_operator_iff = 6
    built_in_operator_xor = 7
    built_in_operator_xnor = 8
    built_in_operator_ite = 9

    # builtins for LIA
    builtin_operator_add = 10
    builtin_operator_sub = 11
    builtin_operator_minus = 12
    builtin_operator_mul = 13
    builtin_operator_div = 14

    # builtins for BV



def BuiltInFunction(OperatorBase)

#
# operators.py ends here
