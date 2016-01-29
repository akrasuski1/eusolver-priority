#!/usr/bin/env python3
# make_cumulative_stats.py ---
#
# Filename: make_cumulative_stats.py
# Author: Abhishek Udupa
# Created: Thu Jan 28 22:36:14 2016 (-0500)
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
import os
import glob
import re

file_names = glob.glob('*.stdout')

completion_times = []
min_found_times = []
percent_improvements=[]

for file_name in file_names:
    benchmark_name = os.path.basename(file_name)
    _temp = benchmark_name.split('-')
    benchmark_name = _temp[0]

    with open(file_name, 'r') as f:
        data = f.read()
        matches = re.findall('Solution Size\s*:\s*(\d+)\s*Solution Time from start \(s\)\s*:\s*(\d+\.\d+)', data)

        if (len(matches) == 0):
            completion_times.append(100000)
            min_found_times.append(100000)
            continue

        completion_times.append(float(matches[0][1]))
        min_completion_time = float(matches[0][1])
        min_size = int(matches[0][0])
        first_size = min_size
        for match in matches[1:]:
            if (int(match[0]) < min_size):
                min_size = int(match[0])
                min_completion_time = float(match[1])
        min_found_times.append(min_completion_time)

        percent_improvements.append((first_size, min_size))


completion_times.sort()
min_found_times.sort()

for i in range(len(completion_times)):
    print('%d %d' % (int(completion_times[i]), i+1))

print('\n\n')

for i in range(len(min_found_times)):
    print('%d %d' % (int(min_found_times[i]), i+1))

print('\n\n')

for i in range(len(percent_improvements)):
    print('%d %d' % (percent_improvements[i][0], percent_improvements[i][1]))

# print(completion_times)
# print(min_found_times)

#
# make_cumulative_stats.py ends here
