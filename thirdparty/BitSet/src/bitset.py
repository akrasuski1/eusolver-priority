#!/usr/bin/env python3
# bitset.py ---
#
# Filename: bitset.py
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
        lib_dir = os.path.join(mydir, './libbitset.so')
        try:
            init(lib_dir)
        except Exception as e:
            print('Could not load libbitset.so!')
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

    _loaded_lib.bitset_create_bitset.argtypes = [ctypes.c_ulong]
    _loaded_lib.bitset_create_bitset.restype = BitSetObject

    _loaded_lib.bitset_destroy_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_destroy_bitset.restype = None

    _loaded_lib.bitset_resize_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_resize_bitset.restype = None

    _loaded_lib.bitset_set_bit_in_bitset.argtypes = [ctypes.c_ulong, BitSetObject]
    _loaded_lib.bitset_set_bit_in_bitset.restype = None

    _loaded_lib.bitset_clear_bit_in_bitset.argtypes = [ctypes.c_ulong, BitSetObject]
    _loaded_lib.bitset_clear_bit_in_bitset.restype = None

    _loaded_lib.bitset_flip_bit_in_bitset.argtypes = [ctypes.c_ulong, BitSetObject]
    _loaded_lib.bitset_flip_bit_in_bitset.restype = ctypes.c_bool

    _loaded_lib.bitset_test_bit_in_bitset.argtypes = [ctypes.c_ulong, BitSetObject]
    _loaded_lib.bitset_test_bit_in_bitset.restype = ctypes.c_bool

    _loaded_lib.bitset_clear_all_bits_in_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_clear_all_bits_in_bitset.restype = None

    _loaded_lib.bitset_set_all_bits_in_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_set_all_bits_in_bitset.restype = None

    _loaded_lib.bitset_get_bitset_size.argtypes = [BitSetObject]
    _loaded_lib.bitset_get_bitset_size.restype = ctypes.c_ulong

    _loaded_lib.bitset_get_num_one_bits.argtypes = [BitSetObject]
    _loaded_lib.bitset_get_num_one_bits.restype = ctypes.c_ulong

    _loaded_lib.bitset_get_num_zero_bits.argtypes = [BitSetObject]
    _loaded_lib.bitset_get_num_zero_bits.restype = ctypes.c_ulong

    _loaded_lib.bitset_are_bitsets_equal.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_are_bitsets_equal.restype = ctypes.c_bool

    _loaded_lib.bitset_are_bitsets_disjoint.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_are_bitsets_disjoint.restype = ctypes.c_bool

    _loaded_lib.bitset_is_first_subset_of_second.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_is_first_subset_of_second.restype = ctypes.c_bool

    _loaded_lib.bitset_is_first_proper_subset_of_second.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_is_first_proper_subset_of_second.restype = ctypes.c_bool

    _loaded_lib.bitset_and_bitsets_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_and_bitsets_functional.restype = BitSetObject

    _loaded_lib.bitset_or_bitsets_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_or_bitsets_functional.restype = BitSetObject

    _loaded_lib.bitset_xor_bitsets_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_xor_bitsets_functional.restype = BitSetObject

    _loaded_lib.bitset_negate_and_bitsets_functional.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_negate_and_bitsets_functional.restype = BitSetObject

    _loaded_lib.bitset_and_bitsets.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_and_bitsets.restype = None

    _loaded_lib.bitset_or_bitsets.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_or_bitsets.restype = None

    _loaded_lib.bitset_xor_bitsets.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_xor_bitsets.restype = None

    _loaded_lib.bitset_negate_and_bitsets.argtypes = [BitSetObject, BitSetObject]
    _loaded_lib.bitset_negate_and_bitsets.restype = None

    _loaded_lib.bitset_negate_bitset_functional.argtypes = [BitSetObject]
    _loaded_lib.bitset_negate_bitset_functional.restype = BitSetObject

    _loaded_lib.bitset_negate_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_negate_bitset.restype = None

    _loaded_lib.bitset_clone_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_clone_bitset.restype = BitSetObject

    _loaded_lib.bitset_get_error_code.argtypes = []
    _loaded_lib.bitset_get_error_code.restype = ctypes.c_ulong

    _loaded_lib.bitset_get_error_string_for_error_code.argtypes = [ctypes.c_ulong]
    _loaded_lib.bitset_get_error_string_for_error_code.restype = ctypes.c_char_p

    _loaded_lib.bitset_get_error_string_for_last_error.argtypes = []
    _loaded_lib.bitset_get_error_string_for_last_error.restype = ctypes.c_char_p

    # hashing
    _loaded_lib.bitset_compute_bitset_hash.argtypes = [BitSetObject]
    _loaded_lib.bitset_compute_bitset_hash.restype = ctypes.c_ulong

    # debug functions
    _loaded_lib.bitset_debug_print_bitset.argtypes = [BitSetObject]
    _loaded_lib.bitset_debug_print_bitset.restype = None

def bitset_get_error_code():
    return lib().bitset_get_error_code()

def bitset_get_error_string_for_error_code(error_code):
    return lib().bitset_get_error_string_for_error_code(error_code)

def bitset_get_error_string_for_last_error():
    return lib().bitset_get_error_string_for_last_error()

def bitset_check_error():
    return (bitset_get_error_code() != 0)

def _raise_exception_if_error():
    if (bitset_check_error()):
        raise BitSetException(_to_pystr(bitset_get_error_string_for_last_error()))

def bitset_create_bitset(a0):
    r = lib().bitset_create_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_destroy_bitset(a0):
    r = lib().bitset_destroy_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_set_bit_in_bitset(a0, a1):
    r = lib().bitset_set_bit_in_bitset(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_clear_bit_in_bitset(a0, a1):
    r = lib().bitset_clear_bit_in_bitset(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_flip_bit_in_bitset(a0, a1):
    r = lib().bitset_flip_bit_in_bitset(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_test_bit_in_bitset(a0, a1):
    r = lib().bitset_test_bit_in_bitset(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_clear_all_bits_in_bitset(a0):
    r = lib().bitset_clear_all_bits_in_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_set_all_bits_in_bitset(a0):
    r = lib().bitset_set_all_bits_in_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_get_bitset_size(a0):
    r = lib().bitset_get_bitset_size(a0)
    _raise_exception_if_error()
    return r

def bitset_get_num_one_bits(a0):
    r = lib().bitset_get_num_one_bits(a0)
    _raise_exception_if_error()
    return r

def bitset_get_num_zero_bits(a0):
    r = lib().bitset_get_num_zero_bits(a0)
    _raise_exception_if_error()
    return r

def bitset_are_bitsets_disjoint(a0, a1):
    r = lib().bitset_are_bitsets_disjoint(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_are_bitsets_equal(a0, a1):
    r = lib().bitset_are_bitsets_equal(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_is_first_subset_of_second(a0, a1):
    r = lib().bitset_is_first_subset_of_second(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_is_first_proper_subset_of_second(a0, a1):
    r = lib().bitset_is_first_proper_subset_of_second(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_and_bitsets_functional(a0, a1):
    r = lib().bitset_and_bitsets_functional(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_or_bitsets_functional(a0, a1):
    r = lib().bitset_or_bitsets_functional(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_xor_bitsets_functional(a0, a1):
    r = lib().bitset_xor_bitsets_functional(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_negate_and_bitsets_functional(a0, a1):
    r = lib().bitset_xor_bitsets_functional(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_and_bitsets(a0, a1):
    r = lib().bitset_and_bitsets(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_or_bitsets(a0, a1):
    r = lib().bitset_or_bitsets(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_xor_bitsets(a0, a1):
    r = lib().bitset_xor_bitsets(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_negate_and_bitsets(a0, a1):
    r = lib().bitset_xor_bitsets(a0, a1)
    _raise_exception_if_error()
    return r

def bitset_negate_bitset_functional(a0):
    r = lib().bitset_negate_bitset_functional(a0)
    _raise_exception_if_error()
    return r

def bitset_negate_bitset(a0):
    r = lib().bitset_negate_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_resize_bitset(a0):
    r = lib().bitset_resize_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_clone_bitset(a0):
    r = lib().bitset_clone_bitset(a0)
    _raise_exception_if_error()
    return r

def bitset_compute_bitset_hash(a0):
    r = lib().bitset_compute_bitset_hash(a0)
    _raise_exception_if_error()
    return r

def bitset_debug_print_bitset(a0):
    r = lib().bitset_debug_print_bitset(a0)
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
            print('Caught exception (expected behavior)\n%s' % str(e))
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

if __name__ == '__main__':
    test_bitsets()


#
# bitset.py ends here
