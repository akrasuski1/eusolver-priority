#!/usr/bin/env python3
# max_generator.py ---
#
# Filename: max_generator.py
# Author: Abhishek Udupa
# Created: Tue Jan 26 18:42:27 2016 (-0500)
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

import sys

def make_sygus_file(size, prefix):
    with open(('%s_%d.sl' % (prefix, size)), 'w') as out_file:
        out_file.write('(set-logic LIA)\n\n')
        out_file.write('(synth-fun max%d (' % size)
        for i in range(size):
            out_file.write('(a%d Int)' % i)
            if (i != size-1):
                out_file.write(' ')
        out_file.write(') Int\n')
        out_file.write('    ((Start Int (a0\n')
        for i in range(size-1):
            out_file.write('                 a%d\n' % (i+1))
        out_file.write("""                 0
                 1
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))
""")
        for i in range(size):
            out_file.write('(declare-var x%d Int)\n' % i)
        out_file.write('\n\n')
        for i in range(size):
            out_file.write('(constraint (>= (max%d' % size)
            for j in range(size):
                out_file.write(' x%d' % j)
            out_file.write(') x%d))\n' % i)
        out_file.write('(constraint\n')
        for i in range(size - 1):
            out_file.write('    (or (= (max%d' % size)
            for j in range(size):
                out_file.write(' x%d' % j)
            out_file.write(') x%d)\n' % i)
        out_file.write('        (= (max%d' % size)
        for j in range(size):
            out_file.write(' x%d' % j)
        out_file.write(') x%d)' % (size-1))
        out_file.write(')' * size)
        out_file.write('\n\n')
        out_file.write('(check-synth)\n\n')



if __name__ == '__main__':
    if (len(sys.argv) < 4):
        print('Usage: %s <file prefix> <start range> <end range>' % sys.argv[0])
        sys.exit(1)

    prefix = sys.argv[1]

    start_range = int(sys.argv[2])
    end_range = int(sys.argv[3])
    assert (start_range >= 2)

    for i in range(start_range, end_range + 1):
        make_sygus_file(i, prefix)

#
# max_generator.py ends here
