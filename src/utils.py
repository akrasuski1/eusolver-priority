#!/usr/bin/env python3
# utils.py ---
#
# Filename: utils.py
# Author: Abhishek Udupa
# Created: Tue Aug 18 12:03:06 2015 (-0400)
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


"""Some utility functions, which are largely self-explanatory"""

import math
import sys

def print_module_misuse_and_exit():
    print('This module is intented for use as a library, and not as a ' +
          'standalone program!')
    sys.exit(1)


if __name__ == '__main__':
    print_module_misuse_and_exit()


def is_number_prime(number):
    for i in range(2, math.ceil(math.sqrt(number))):
        if (number % i == 0):
            return False
    return True


def round_to_next_higher_prime(number):
    while (not is_number_prime(number)):
        number += 1
    return number


def partitions(n, k):
    """generate all splits of n into k components. Order
    "of the split components is considered relevant.
    """
    if (n < k):
        raise ArgumentError('n must be greater than or equal to k in call ' +
                            'to utils.partitions(n, k)')

    cuts = []
    cuts.append(0)
    cuts.append(n-k+1)
    for i in range(k - 1):
      cuts.append(n - k + 1 + i + 1)

    done = False

    while (not done):
        retval = tuple([cuts[i] - cuts[i-1] for i in range(1, k+1)])
        rightmost = 0
        for i in range(1,k):
            if cuts[i] - cuts[i - 1] > 1:
                rightmost = i
                cuts[i] = cuts[i] - 1
                break
        if rightmost == 0:
            done = True
        else:
            accum = 1
            for i in reversed(range(1, rightmost)):
                cuts[i] = cuts[rightmost] - accum
                accum = accum + 1
        yield retval

def is_subsequence_of(iterable1, iterable2):
    """Tests if :iterable1: is a subsequence of :iterable2:."""
    if (len(iterable1) > len(iterable2)):
        return False

    for i in range(len(iterable1)):
        if (iterable1[i] != iterable2[i]):
            return False

    return True

#
# utils.py ends here
