#!/usr/bin/env python3
# scrub_log.py ---
#
# Filename: scrub_log.py
# Author: Abhishek Udupa
# Created: Mon Nov 23 21:52:42 2015 (-0500)
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
import re
import os

log_file = open(sys.argv[1], 'r')

# re_pat = 'START BENCHMARK: (.)*$.*Added (\d+) counterexample points in total.*computed in (\d+.\d+) seconds.*Solution size: (\d+)'
re_pat = 'START BENCHMARK: (.*)\s.*sl\s.*sl:\s.*\\)\sAdded (\d+).*\scomputed in (\d+.\d+).*\sSolution size: (\d+)'
log_str = log_file.read()
matches = re.findall(re_pat, log_str, re.MULTILINE)
re_to_pat = 'START BENCHMARK: (.*)\sEND BENCHMARK:.*\s'
to_matches = re.findall(re_to_pat, log_str, re.MULTILINE)
print(to_matches)

print_list = []
for match in matches:
    print_list.append('%s %s %s %s' % (os.path.basename(match[0]), match[2], match[3], match[1]))
for to_match in to_matches:
    print_list.append('%s TO -- --' % (os.path.basename(to_match)))

print_list.sort()
for e in print_list:
    print(e)

#
# scrub_log.py ends here
