#!/usr/bin/env python3
# semantics_bv.py ---
#
# Filename: semantics_bv.py
# Author: Abhishek Udupa
# Created: Tue Sep  1 12:39:38 2015 (-0400)
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


# (concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
# - concatenation of bitvectors of size i and j to get a new bitvector of
# size m, where m = i + j

class BVConcat(InterpretedFunctionBase):
    def __init__(self, size1, size2):
        super().__init__('concat', 2, (exprtypes.BitVectorType(size1),
                                       exprtypes.BitVectorType(size2)),
                         exprtypes.BitVectorType(size1 + size2))
        self.size1 = size1
        self.size2 = size2

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Concat(child_terms[0], child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        a = eval_context_object.peek(0)
        b = eval_context_object.peek(1)
        res = (a << size2) | (b)
        eval_context_object.pop(2)
        eval_context_object.push(res)



# ((_ extract i j) (_ BitVec m) (_ BitVec n))
# - extraction of bits i down to j from a bitvector of size m to yield a
# new bitvector of size n, where n = i - j + 1

class BVExtract(InterpretedFunctionBase):
    def __init__(self, start_offset, end_offset, bv_type):
        super().__init__('extract', 1, (exprtypes.BitVectorType(bv_size),),
                         exprtypes.BitVectorType(end_offset - start_offset + 1))

        self.start_offset = start_offset
        self.end_offset = end_offset
        self.mangled_function_name = 'extract_%d_%d_%d' % (start_offset, end_offset,
                                                           self.domain_types[0].type_code)

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.Extract(end_offset, start_offset, child_terms[0])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        mask = (1 << (self.end_offset - self.start_offset + 1)) - 1
        if (self.start_offset > 0):
            mask = mask << self.start_offset
        res = eval_context_object.peek() & mask
        eval_context_object.pop()
        eval_context_object.push(mask)

# (bvnot (_ BitVec m) (_ BitVec m))
# - bitwise negation

# (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise and

# (bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise or

# (bvneg (_ BitVec m) (_ BitVec m))
# - 2's complement unary minus

# (bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - addition modulo 2^m

# (bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - multiplication modulo 2^m

# (bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - unsigned division, truncating towards 0 (undefined if divisor is 0)

# (bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - unsigned remainder from truncating division (undefined if divisor is 0)

# (bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - shift left (equivalent to multiplication by 2^x where x is the value of
# the second argument)

# (bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - logical shift right (equivalent to unsigned division by 2^x where x is
# the value of the second argument)

# (bvult (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for unsigned less-than

# (bvnand (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise nand (negation of and)

# (bvnor (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise nor (negation of or)

# (bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise exclusive or

# (bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise equivalence (equivalently, negation of bitwise exclusive or)

# (bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))
# - bit comparator: equals #b1 iff all bits are equal

# (bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - 2's complement subtraction modulo 2^m

# (bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - 2's complement signed division

# (bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - 2's complement signed remainder (sign follows dividend)

# (bvsmod (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - 2's complement signed remainder (sign follows divisor)

# (bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - Arithmetic shift right, like logical shift right except that the most
# significant bits of the result always copy the most significant
# bit of the first argument.

# The following symbols are parameterized by the numeral i, where i >= 1.
# ((_ repeat i) (_ BitVec m) (_ BitVec i*m))
# - ((_ repeat i) x) means concatenate i copies of x

# The following symbols are parameterized by the numeral i, where i >= 0.

# ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
# - ((_ zero_extend i) x) means extend x with zeroes to the (unsigned)
# equivalent bitvector of size m+i

# ((_ sign_extend i) (_ BitVec m) (_ BitVec m+i))
# - ((_ sign_extend i) x) means extend x to the (signed) equivalent bitvector
# of size m+i

# ((_ rotate_left i) (_ BitVec m) (_ BitVec m))
# - ((_ rotate_left i) x) means rotate bits of x to the left i times

# ((_ rotate_right i) (_ BitVec m) (_ BitVec m))
# - ((_ rotate_right i) x) means rotate bits of x to the right i times

# (bvule (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for unsigned less than or equal

# (bvugt (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for unsigned greater than

# (bvuge (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for unsigned greater than or equal

# (bvslt (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for signed less than

# (bvsle (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for signed less than or equal

# (bvsgt (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for signed greater than

# (bvsge (_ BitVec m) (_ BitVec m) Bool)
# - binary predicate for signed greater than or equal


#
# semantics_bv.py ends here
