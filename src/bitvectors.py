#!/usr/bin/env python3
# bitvectors.py ---
# Filename: bitvectors.py
# Author: Abhishek Udupa
# Created: Mon Jan 25 01:04:51 2016 (-0500)
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

"""Implementation of fixed length (which can be arbitrary) bitvectors"""

import utils
import basetypes

class BitVector(object):
    __slots__ = ['value', 'size', 'mask', 'sign_mask']

    def __init__(self, value, size):
        if (isinstance(value, int)):
            self.value = value
        elif (isinstance(value, str)):
            self.value = int(value)
        else:
            raise ArgumentError('Invalid value for BitVector')
        self.size = size
        if (size <= 0):
            raise ArgumentError('Size of BitVector must be greater than 1')
        self.mask = (1 << size) - 1
        self.sign_mask = (1 << (size - 1))
        self._apply_mask()

    def _apply_mask(self):
        self.value &= self.mask

    def __hash__(self):
        return (hash(self.value) ^ hash(self.size))

    def __lt__(self, other):
        return (self.value < other.value)

    def _is_negative(self):
        return ((self.value & self.sign_mask) != 0)

    def _twos_complement_of_value(self):
        return (((~self.value) + 1) & self.mask)

    def __repr__(self):
        return 'BitVector(0x%X, %d)' % (self.value, self.size)

    def __str__(self):
        if (self.size % 4 != 0):
            size_str = str(self.size)
            formatted_value = format(self.value, '0' + size_str + 'b')
            return '#b' + formatted_value
        else:
            size_str = str(self.size >> 2)
            formatted_value = format(self.value, '0' + size_str + 'x')
            return '#x' + formatted_value


    def __add__(self, other):
        return BitVector(self.value + other.value, self.size)

    def __sub__(self, other):
        return BitVector(self.value - other.value, self.size)

    def __lshift__(self, shift_amount):
        if (shift_amount == 0):
            return self
        return BitVector(self.value << shift_amount, self.size)

    def __rshift__(self, shift_amount):
        if (shift_amount == 0):
            return self
        return BitVector(self.value >> shift_amount, self.size)

    def __eq__(self, other):
        return (self.value == other.value and self.size == other.size)

    def is_one(self):
        return (self.value == 1)

    def __and__(self, other):
        return BitVector(self.value & other.value, self.size)

    def __or__(self, other):
        return BitVector(self.value | other.value, self.size)

    def __xor__(self, other):
        return BitVector(self.value ^ other.value, self.size)

    def __invert__(self):
        return BitVector(~(self.value), self.size)


###################################################################
#        TESTS AND SUCH
###################################################################

def _test_repr_str():
    a = BitVector(123, 8)
    print(a)
    print(a.__repr__())

if __name__ == '__main__':
    _test_repr_str()

#
# bitvectors.py ends here
