#!/usr/bin/env python3
# eusolver.py ---
#
# Filename: eusolver.py
# Author: Abhishek Udupa
# Created: Mon Sep 21 16:03:49 2015 (-0400)
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

import ctypes
import sys
import os

class BitSetException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg

    def __str__(self):
        return 'BitSetException: ' + self.error_msg

class BitSetObject(ctypes.c_void_p):
    def __init__(self, bitset_ptr):
        super().__init__(bitset_ptr)

    def __del__(self):
        bitset_destroy_bitset(self)

_loaded_lib = None

def lib():
    global _loaded_lib
    if (_loaded_lib == None):
        mydir = os.path.dirname(os.path.abspath(__file__))
        lib_dir = os.path.join(mydir, './libeusolver.so')
        try:
            init(lib_dir)
        except Exception as e:
            print('Could not load libeusolver.so!')
            raise e

    return _loaded_lib

def _to_ascii(s):
    if isinstance(s, str):
        return s.encode('ascii')
    else:
        return s

def _to_pystr(s):
    if sys.version < '3':
        return s
    else:
        return s.decode('utf-8')


def init(path_to_lib):
    global _loaded_lib
    _loaded_lib = ctypes.CDLL(path_to_lib)

    _loaded_lib.eus_bitset_construct.argtypes = [ctypes.c_ulong, ctypes.c_bool]
    _loaded_lib.eus_bitset_construct.restype = BitSetObject

    _loaded_lib.eus_bitset_destroy.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_destroy.restype = None

    _loaded_lib.eus_bitsets_equal.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitsets_equal.restype = ctypes.c_bool

    _loaded_lib.eus_bitsets_not_equal.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitsets_not_equal.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_is_proper_subset.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_is_proper_subset.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_is_subset.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_is_subset.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_is_proper_superset.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_is_proper_superset.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_is_superset.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_is_superset.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_set_bit.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_set_bit.restype = None

    _loaded_lib.eus_bitset_clear_bit.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_clear_bit.restype = None

    _loaded_lib.eus_bitset_flip_bit.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_flip_bit.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_test_bit.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_test_bit.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_set_all.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_set_all.restype = None

    _loaded_lib.eus_bitset_clear_all.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_clear_all.restype = None

    _loaded_lib.eus_bitset_flip_all.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_flip_all.restype = None

    _loaded_lib.eus_bitset_get_size_of_universe.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_get_size_of_universe.restype = ctypes.c_ulong

    _loaded_lib.eus_bitset_get_length.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_get_length.restype = ctypes.c_ulong

    _loaded_lib.eus_bitset_is_full.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_is_full.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_is_empty.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_is_empty.restype = ctypes.c_bool

    _loaded_lib.eus_bitset_and_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_and_functional.restype = BitSetObject

    _loaded_lib.eus_bitset_or_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_or_functional.restype = BitSetObject

    _loaded_lib.eus_bitset_xor_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_xor_functional.restype = BitSetObject

    _loaded_lib.eus_bitset_minus_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_minus_functional.restype = BitSetObject

    _loaded_lib.eus_bitset_negate_functional.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_negate_functional.restype = BitSetObject

    _loaded_lib.eus_bitset_inplace_and.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_inplace_and.restype = None

    _loaded_lib.eus_bitset_inplace_or.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_inplace_or.restype = None

    _loaded_lib.eus_bitset_inplace_xor.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_inplace_xor.restype = None

    _loaded_lib.eus_bitset_inplace_minus.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.eus_bitset_inplace_minus.restype = None

    _loaded_lib.eus_bitset_inplace_negate.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_inplace_negate.restype = None

    _loaded_lib.eus_bitset_get_next_element_greater_than_or_equal_to.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_get_next_element_greater_than_or_equal_to.restype = ctypes.c_long

    _loaded_lib.eus_bitset_get_next_element_greater_than.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_get_next_element_greater_than.restype = ctypes.c_long

    _loaded_lib.eus_bitset_get_prev_element_lesser_than_or_equal_to.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_get_prev_element_lesser_than_or_equal_to.restype = ctypes.c_long

    _loaded_lib.eus_bitset_get_prev_element_lesser_than.argtypes = [BitSetObject, ctypes.c_ulong]
    _loaded_lib.eus_bitset_get_prev_element_lesser_than.restype = ctypes.c_long

    _loaded_lib.eus_bitset_get_hash.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_get_hash.restype = ctypes.c_ulong

    _loaded_lib.eus_bitset_to_string.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_to_string.restype = ctypes.c_char_p

    _loaded_lib.eus_bitset_clone.argtypes = [BitSetObject]
    _loaded_lib.eus_bitset_clone.restype = BitSetObject

    _loaded_lib.eus_check_error.argtypes = []
    _loaded_lib.eus_check_error.restype = ctypes.c_bool

    _loaded_lib.eus_get_last_error_string.argtypes = []
    _loaded_lib.eus_get_last_error_string.restype = ctypes.c_char_p


def eus_check_error():
    return eus_check_error()

def eus_get_last_error_string():
    return _to_pystr(lib().eus_get_last_error_string())

def _raise_exception_if_error():
    if (eus_check_error()):
        raise BitSetException(eus_get_last_error_string())

def eus_bitset_construct(a0, a1):
    r = lib().eus_bitset_construct(a0, a1)
    _raise_exception_if_error()
    return r

def eus_bitset_destroy(a0):
    r = lib().eus_bitset_destroy(a0)
    _raise_exception_if_error()
    return r

def eus_bitsets_equal(a0, a1):
    r = lib().eus_bitsets_equal(a0, a1)
    _raise_exception_if_error()
    return r

def eus_bitsets_not_equal(a0, a1):
    r = lib().eus_bitsets_not_equal(a0, a1)
    _raise_exception_if_error()
    return r




class BitSet(object):
    __slots__ = ['bitset_object', 'cached_hash_code']

    def __init__(self, num_bits_or_bitset_object):
        if (isinstance(num_bits_or_bitset_object, int)):
            self.bitset_object = bitset_create_bitset(num_bits_or_bitset_object)
        elif (isinstance(num_bits_or_bitset_object, BitSetObject)):
            self.bitset_object = num_bits_or_bitset_object
        else:
            raise NotImplemented
        self.cached_hash_code = None


    @classmethod
    def make_factory(cls, size_of_universe):
        def _factory_function():
            return cls(size_of_universe)
        return _factory_function

    def _check_mutability(self):
        if (self.cached_hash_code != None):
            raise BitSetException('Attempted to modify a "frozen" BitSet object!')

    def __iter__(self):
        num_bits = bitset_get_bitset_size(self.bitset_object)
        for i in range(num_bits):
            if (bitset_test_bit_in_bitset(i, self.bitset_object)):
                yield i
        return

    def __contains__(self, elem):
        return bitset_test_bit_in_bitset(elem, self.bitset_object)

    def __str__(self):
        retval = ', '.join([str(x) for x in self])
        retval = 'BitSet: {' + retval + '}'
        return retval

    def __getitem__(self, index):
        return (index in self)

    def __setitem__(self, key, value):
        self._check_mutability()
        if (value):
            bitset_set_bit_in_bitset(key, self.bitset_object)
        else:
            bitset_clear_bit_in_bitset(key, self.bitset_object)

    def __and__(self, other):
        return BitSet(bitset_and_bitsets_functional(self.bitset_object, other.bitset_object))

    def __iand__(self, other):
        bitset_and_bitsets(self.bitset_object, other.bitset_object)
        return self

    def __or__(self, other):
        return BitSet(bitset_or_bitsets_functional(self.bitset_object, other.bitset_object))

    def __ior__(self, other):
        return bitset_or_bitsets(self.bitset_object, other.bitset_object)

    def __not__(self):
        return Bitset(bitset_negate_bitset_functional(self.bitset_object))

    def __xor__(self, other):
        return BitSet(bitset_xor_bitsets_functional(self.bitset_object, other.bitset_object))

    def __ixor__(self, other):
        bitset_xor_bitsets(self.bitset_object, other.bitset_object)
        return self

    def __sub__(self, other):
        return BitSet(bitset_negate_and_bitsets_functional(self.bitset_object, other.bitset_object))

    def __isub__(self, other):
        bitset_negate_and_bitsets(self.bitset_object, other.bitset_object)
        return self

    def __le__(self, other):
        return self.issubset(other)

    def __lt__(self, other):
        return self.is_proper_subset(other)

    def __ge__(self, other):
        return self.issuperset(other)

    def __gt__(self, other):
        return self.is_proper_superset(other)

    def __eq__(self, other):
        return bitset_are_bitsets_equal(self.bitset_object, other.bitset_object)

    def __ne__(self, other):
        return (not (self == other))

    def __len__(self):
        return bitset_get_num_one_bits(self.bitset_object)

    def __hash__(self):
        if (self.cached_hash_code == None):
            self.cached_hash_code = bitset_compute_bitset_hash(self.bitset_object)
        return self.cached_hash_code

    def union(self, other):
        return (self or other)

    def in_place_union(self, other):
        self._check_mutability()
        bitset_or_bitsets(self.bitset_object, other.bitset_object)

    def intersection(self, other):
        return (self and other)

    def in_place_intersection(self, other):
        self._check_mutability()
        bitset_and_bitsets(self.bitset_object, other.bitset_object)

    def inter(self, other):
        return (self and other)

    def in_place_inter(self, other):
        self.in_place_intersection(other)

    def size_of_universe(self):
        return bitset_get_bitset_size(self.bitset_object)

    def add(self, elem):
        self._check_mutability()
        return bitset_set_bit_in_bitset(elem, self.bitset_object)

    def clear_all(self):
        self._check_mutability()
        return bitset_clear_all_bits_in_bitset(self.bitset_object)

    def set_all(self):
        self._check_mutability()
        return bitset_set_all_bits_in_bitset(self.bitset_object)

    def is_full(self):
        return bitset_is_full_set(self.bitset_object)

    def is_empty(self):
        return bitset_is_empty_set(self.bitset_object)

    def isdisjoint(self, other):
        return bitset_are_bitsets_disjoint(self.bitset_object, other.bitset_object)

    def issubset(self, other):
        return bitset_is_first_subset_of_second(self.bitset_object, other.bitset_object)

    def is_proper_subset(self, other):
        return bitset_is_first_proper_subset_of_second(self.bitset_object, other.bitset_object)

    def issuperset(self, other):
        return bitset_is_first_subset_of_second(other.bitset_object, self.bitset_object)

    def is_proper_superset(self, other):
        return bitset_is_first_proper_subset_of_second(other.bitset_object, self.bitset_object)

    def difference(self, other):
        return (self - other)

    def in_place_difference(self, other):
        self._check_mutability()
        bitset_negate_and_bitsets(self.bitset_object, other.bitset_object)

    def in_place_negate(self):
        self._check_mutability()
        bitset_negate_bitset(self.bitset_object)

    def symmetric_difference(self, other):
        return (self ^ other)

    def in_place_symmetric_difference(self, other):
        self._check_mutability()
        bitset_xor_bitsets(self.bitset_object, other.bitset_object)

    def copy(self):
        return BitSet(bitset_clone_bitset(self.bitset_object))

    def clone(self):
        return self.copy()

    def debug_print(self):
        bitset_debug_print_bitset(self.bitset_object)


################################################################################
# TEST CASES
################################################################################

def test_bitsets():
    a = BitSet(1024)
    a.add(1)
    a.add(4)
    assert (1 in a)
    assert (4 in a)
    assert (3 not in a)
    assert (42 not in a)
    assert (str(a) == 'BitSet: {1, 4}')
    assert (len(a) == 2)

    a[2] = True
    assert (len(a) == 3)

    iter_list = []
    for elem in a:
        iter_list.append(elem)
    assert(len(iter_list) == 3)
    assert(iter_list[0] == 1)
    assert(iter_list[1] == 2)
    assert(iter_list[2] == 4)

    a.clear_all()
    assert (1 not in a)
    assert (4 not in a)
    assert (3 not in a)
    assert (42 not in a)
    assert (len(a) == 0)

    a.set_all()
    assert (1 in a)
    assert (4 in a)
    assert (3 in a)
    assert (42 in a)
    assert (len(a) == 1024)

    b = BitSet(1024)
    b.set_all()

    assert (a == b)
    a = a - b
    assert (len(a) == 0)
    assert (str(a) == 'BitSet: {}')

    a.set_all()
    b.clear_all()

    b = a | b
    assert(a == b)
    b[0] = False
    assert(a != b)

    a.set_all()
    b.set_all()
    a = a & b
    assert(a == b)
    assert(len(b) == 1024)

    a.clear_all()
    a = a & b
    assert(len(a) == 0)

    a.add(0)
    a.add(3)
    a.add(4)

    assert(hash(a) != None and hash(a) == hash(a) and hash(a) != 0)

    # check immutability
    try:
        try:
            a.add(123)
        except BitSetException as e:
            print('Caught exception (expected behavior, not an error!)\n%s' % str(e))
            raise e
        assert False
    except BitSetException as e:
        pass


    a = BitSet(1024)
    a.add(0)
    a.add(3)
    a.add(4)
    b.clear_all()
    b.add(0)
    b.add(4)
    a &= b
    assert(len(a) == 2)
    assert(0 in a)
    assert(4 in a)
    assert(3 not in a)

    a.clear_all()
    b.clear_all()

    a.add(0)
    a.add(1023)
    a.add(42)

    b.add(1)
    b.add(1022)
    b.add(42)

    a ^= b
    assert(len(a) == 4)
    assert(str(a) == 'BitSet: {0, 1, 1022, 1023}')

    a = BitSet(1024)
    assert (a.is_empty())
    assert (not a.is_full())

    a.set_all()
    assert (a.is_full)
    assert (not a.is_empty())

    a.clear_all()
    assert (a.is_empty())
    assert (not a.is_full())

    a[128] = True
    assert (not a.is_empty())
    assert (not a.is_full())

    factory = BitSet.make_factory(300)
    new_bs = factory()
    assert (new_bs.size_of_universe() == 300)
    assert (new_bs.is_empty())
    assert (not new_bs.is_full())

if __name__ == '__main__':
    test_bitsets()


#
# eusolver.py ends here
