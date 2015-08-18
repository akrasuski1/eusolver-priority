# hashcache.py ---
#
# Filename: hashcache.py
# Author: Abhishek Udupa
# Created: Tue Aug 18 10:57:01 2015 (-0400)
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

#!/usr/bin/env python3

"""Implements a hashed cache, which is the dual of a bloom filter.
i.e., false negatives are allowed, but not false positives."""

import sys
import basetypes
import utils

if __name__ == '__main__':
    print_module_misuse_and_exit()

def default_hash_function(obj):
    return hash(obj)


class HashCacheEntry(object):
    """An entry in the HashCache"""
    def __init__(self, data = None,
                 timestamp = 0, num_hits = 0):
        self.data = data
        self.timestamp = timestamp
        self.num_hits = num_hits


class HashCache(object):
    """The main hash cache class"""

    def __init__(self, num_sets, associativity,
                 replacement_function,
                 hash_function = default_hash_function):
        """Constructs a HashCache.
        Args:
            num_sets (int): number of sets in the hash table, will be rounded up
                            to the next higher prime number.
            associativity (int): Associativity of the cache structure.
                                 1 - indicates direct-mapped, size = num_sets.
                                     (replacement function will not be used)
                                 > 1 - indicates some level of associativity,
                                       size = num_sets * associativity.
                                 < 1 - illegal.
            replacement_function: A function from list(object) -> index, indicating
                                  which index is to be replaced.
            hash_function: A function object -> int which hashes the object
        """

        self.num_sets = utils.round_to_next_higher_prime(num_sets)
        self.associativity = associativity
        self.replacement_function = replacement_function
        self.hash_function = hash_function
        self.monotonic_timestamp = 0

        if (self.associativity == 1):
            self.hash_table = [None] * self.num_sets
        elif (self.associativity > 1):
            self.hash_table = [None] * self.num_sets
            for i in range(self.num_sets):
                self.hash_table[i] = [None] * self.associativity
        else:
            raise basetypes.OptionError('Associativity out of bounds ' +
                                        'in HashCache.__init__()')

    def _lookup_in_set(self, set_index, key):
        set_entry = self.hash_table[set_index]

        for i in range(self.associativity):
            if (set_entry[i] == key):
                set_entry[i].num_accesses += 1
                set_entry[i].timestamp = self.monotonic_timestamp
                self.monotonic_timestamp += 1
                return True

        return False

    def exists(self, key):
        """Checks if a key exists in the hash cache"""
        hash_value = self.hash_function(key)
        set_index = hash_value % self.num_sets

        if (self.associativity > 1):
            return self._lookup_in_set(set_index, key)
        else:
            if (self.hash_table[set_index] == key):
                self.hash_table[set_index].num_hits += 1
                self.hash_table[set_index].timestamp = self.monotonic_timestamp
                self.monotonic_timestamp += 1
                return True
            else:
                return False

    def _insert_into_set(self, set_index, key):
        # is there an empty slot in the set somewhere?
        empty_slot_index = -1
        set_entry = self.hash_table[set_index]
        for i in range(self.associativity):
            if (set_entry[i] == None):
                empty_slot_index = i
                break

        if (empty_slot_index < 0):
            empty_slot_index = self.replacement_function(set_entry)

        set_entry[empty_slot_index] = HashCacheEntry(key, self.monotonic_timestamp)
        self.monotonic_timestamp += 1

    def insert(self, key):
        """Inserts key into the hash cache.
        Requires: The key is not currently present in the hash cache
        """
        hash_value = self.hash_function(key)
        set_index = hash_value % self.num_sets

        if (self.associativity > 1):
            self._insert_into_set(set_index, key)
        else:
            self.hash_table[set_index] = HashCacheEntry(key, self.monotonic_timestamp)
            self.monotonic_timestamp += 1

#
# hashcache.py ends here
