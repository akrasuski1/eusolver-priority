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
import bitstring
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

'''
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
    def __init__(self, start_offset, end_offset, bv_size):
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
'''

# (bvnot (_ BitVec m) (_ BitVec m))
# - bitwise negation

class BVNot(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvnot', 1, (exprtypes.BitVectorType(bv_size),),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (~ child_terms[0])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = ~(eval_context_object.peek(0))
        eval_context_object.pop()
        eval_context_object.push(res)

# (is0 (_ BitVec m) (_ Bool))
# - is 0

class BVIs0(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('is0', 1, (exprtypes.BitVectorType(bv_size),),
                         exprtypes.BoolType())
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] == 0)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = eval_context_object.peek(0).is_zero()
        eval_context_object.pop()
        eval_context_object.push(res)

# (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise and

class BVAnd(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvand', 2, (exprtypes.BitVectorType(bv_size),
                                     exprtypes.BitVectorType(bv_size)),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] & child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(0) & eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(res)

# (bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - bitwise or

class BVOr(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvor', 2, (exprtypes.BitVectorType(bv_size),
                                    exprtypes.BitVectorType(bv_size)),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] | child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(0) | eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(res)

'''
# (bvneg (_ BitVec m) (_ BitVec m))
# - 2's complement unary minus

class BVNeg(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvneg', 1, (exprtypes.BitVectorType(bv_size),),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (-child_terms[0])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (-(eval_context_object.peek(0)))
        eval_context_object.pop()
        eval_context_object.push(res)
'''

# (bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - addition modulo 2^m

class BVAdd(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvadd', 2, (exprtypes.BitVectorType(bv_size),
                                     exprtypes.BitVectorType(bv_size)),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] + child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = eval_context_object.peek(0) + eval_context_object.peek(1)
        eval_context_object.pop(2)
        eval_context_object.push(res)


class ShrConst(InterpretedFunctionBase):
    def __init__(self, bv_size, shift_amount):
        super().__init__('shr'+ str(shift_amount), 1, (exprtypes.BitVectorType(bv_size), ),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size
        self.shift_amount = shift_amount

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return z3.LShR(child_terms[0], self.shift_amount)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = eval_context_object.peek(0) >> self.shift_amount
        eval_context_object.pop(1)
        eval_context_object.push(res)

class ShlConst(InterpretedFunctionBase):
    def __init__(self, bv_size, shift_amount):
        super().__init__('shl' + str(shift_amount), 1, (exprtypes.BitVectorType(bv_size), ),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size
        self.shift_amount = shift_amount

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] << self.shift_amount)

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = eval_context_object.peek(0) << self.shift_amount
        eval_context_object.pop(1)
        eval_context_object.push(res)

'''
# (bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))
# - multiplication modulo 2^m

class BVMul(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvmul', 2, (exprtypes.BitVectorType(bv_size),
                                     exprtypes.BitVectorType(bv_size)),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] * child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(0) * eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(res)

'''

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

class BVXor(InterpretedFunctionBase):
    def __init__(self, bv_size):
        super().__init__('bvxor', 2, (exprtypes.BitVectorType(bv_size),
                                    exprtypes.BitVectorType(bv_size)),
                         exprtypes.BitVectorType(bv_size))
        self.bv_size = bv_size

    def to_smt(self, expr_object, smt_context_object, var_subst_map):
        child_terms = self._children_to_smt(expr_object, smt_context_object, var_subst_map)
        return (child_terms[0] ^ child_terms[1])

    def evaluate(self, expr_object, eval_context_object):
        self._evaluate_children(expr_object, eval_context_object)
        res = (eval_context_object.peek(0) ^ eval_context_object.peek(1))
        eval_context_object.pop(2)
        eval_context_object.push(res)


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

class BVInstantiator(semantics_types.InstantiatorBase):
    def __init__(self, bv_size):
        super().__init__('bv')
        self.instances = {}
        self.bv_size = bv_size

    def _get_instance(self, function_name):
        if function_name not in self.instances:
            if function_name == 'shr1':
                self.instances[function_name] = ShrConst(self.bv_size, 1)
            elif function_name == 'shr4':
                self.instances[function_name] = ShrConst(self.bv_size, 4)
            elif function_name == 'shr16':
                self.instances[function_name] = ShrConst(self.bv_size, 16)
            elif function_name == 'shl1':
                self.instances[function_name] = ShlConst(self.bv_size, 1)
            elif function_name == 'bvnot':
                self.instances[function_name] = BVNot(self.bv_size)
            elif function_name == 'bvand':
                self.instances[function_name] = BVAnd(self.bv_size)
            elif function_name == 'bvor':
                self.instances[function_name] = BVOr(self.bv_size)
            elif function_name == 'bvxor':
                self.instances[function_name] = BVXor(self.bv_size)
            elif function_name == 'bvadd':
                self.instances[function_name] = BVAdd(self.bv_size)
            elif function_name == 'is0':
                self.instances[function_name] = BVIs0(self.bv_size)
            else:
                self._raise_failure(function_name, [])
        return self.instances[function_name]

    def _get_canonical_function_name(self, function_name):
        return function_name

    def is_unary(self, function_name):
        return function_name in [ 'shr1', 'shr4', 'shr16', 'shl1', 'bvnot', 'is0' ]

    def is_binary(self, function_name):
        return function_name in [ 'bvand', 'bvor', 'bvxor', 'bvadd' ]

    def _do_instantiation(self, function_name, mangled_name, arg_types):
        if self.is_unary(function_name):
            if (len(arg_types) != 1 or
                    (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.bit_vector_type))):
                self._raise_failure(function_name, arg_types)
            return self._get_instance(function_name)

        elif self.is_binary(function_name):
            if (len(arg_types) != 2 or
                    (not self._is_all_of_type(arg_types, exprtypes.TypeCodes.bit_vector_type))):
                self._raise_failure(function_name, arg_types)
            return self._get_instance(function_name)

        else:
            return None

class BitVector(object):
    __slots__ = ['value']
    def __init__(self, value):
        self.value = value

    def __hash__(self):
        return hash(str(self.value))

    def __lt__(self, other):
        if isinstance(other, BitVector):
            return self.value.uint < other.value.uint
        elif isinstance(other, int):
            return self.value.uint < other
        raise ArgumentError()

    def __eq__(self, other):
        return self.value == other.value

    def __str__(self):
        return str(self.value)

    def is_zero(self):
        return self.value.uint == 0

    def __rshift__(self, other):
        if isinstance(other, int):
            return BitVector(self.value >> other)
        elif isinstance(other, BitVector):
            return BitVector(self.value >> other.value)
        else:
            raise ArgumentError()

    def __lshift__(self, other):
        if isinstance(other, int):
            return BitVector(self.value << other)
        elif isinstance(other, BitVector):
            return BitVector(self.value << other.value)
        else:
            raise ArgumentError()

    def __and__(self, other):
        if isinstance(other, BitVector):
            return BitVector(self.value & other.value)
        else:
            raise ArgumentError()

    def __or__(self, other):
        if isinstance(other, BitVector):
            return BitVector(self.value | other.value)
        else:
            raise ArgumentError()

    def __xor__(self, other):
        if isinstance(other, BitVector):
            return BitVector(self.value ^ other.value)
        else:
            raise ArgumentError()

    def __add__(self, other):
        if isinstance(other, BitVector):
            a = self.value.uint
            b = other.value.uint
            length = self.value.length
            if length != other.value.length:
                raise ArgumentError()
            return BitVector(bitstring.BitArray(uint=(a+b) % (2**length), length=length))
        else:
            raise ArgumentError()

    def __invert__(self):
        return BitVector(~self.value)


#
# semantics_bv.py ends here
