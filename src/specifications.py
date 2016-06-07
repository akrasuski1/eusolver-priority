#!/usr/bin/env python3
# Specifications.py ---
#
# Filename: specifications.py
# Author: Arjun Radhakrishna
# Created: Tue, 07 Jun 2016 14:10:26 -0400
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
import evaluation
import expr_transforms

class SpecInterface(object):
    def term_signature(self, term, points):
        raise basetypes.AbstractMethodError('SpecInterface.check_on_point()')

class StandardSpec(SpecInterface):
    def __init__(self, spec_clause, syn_ctx, synth_fun):
        self.syn_ctx = syn_ctx
        expr_transforms.check_expr_binding_to_context(spec_clause, syn_ctx)
        self.specification_clauses = [ spec_clause ]
        self.eval_ctx = evaluation.EvaluationContext()
        self.synth_fun = synth_fun

        self.init_spec_tuple()

    def init_spec_tuple(self):
        syn_ctx = self.syn_ctx
        if (len(self.specification_clauses) == 1):
            actual_spec = self.specification_clauses[0]
        else:
            actual_spec = syn_ctx.make_function_expr('and', *self.specification_clauses)
        variables_list, functions_list, canon_spec, clauses, neg_clauses, intro_vars = \
                expr_transforms.canonicalize_specification(actual_spec, syn_ctx)
        self.spec_tuple = (actual_spec, variables_list, functions_list, clauses,
                neg_clauses, canon_spec, intro_vars)
        self.canon_spec = canon_spec
        self.intro_vars = intro_vars
        self.point_vars = variables_list

    def get_spec_tuple(self):
        return self.spec_tuple

    def get_point_variables(self):
        return self.point_vars

    def get_intro_vars(self):
        return self.intro_vars
    
    def get_canonical_specification(self):
        return self.canon_spec


    def term_signature(self, term, points):
        eval_ctx = self.eval_ctx
        eval_ctx.set_interpretation(self.synth_fun, term)

        retval = []
        for point in points:
            eval_ctx.set_valuation_map(point)
            retval.append(evaluation.evaluate_expression_raw(self.canon_spec, eval_ctx))

        return retval

class PBESpec(SpecInterface):
    def __init__(self, valuations, synth_fun):
        self.valuations = valuations
        self.synth_fun = synth_fun
        self.eval_ctx = evaluation.EvaluationContext()
        
        args = [ exprs.FormalParameterExpression(func, argtype, i) 
                for i, argtype in enumerate(synth_fun.domain_types)] 
        self.synth_fun_expr = exprs.FunctionExpression(synth_fun, *args)

    def term_signature(self, term, points):
        eval_ctx = self.eval_ctx
        eval_ctx.set_interpretation(self.synth_fun, term)
        synth_fun_expr = self.synth_fun_expr

        retval = []
        for point in points:
            if point not in valuations:
                print("Something is almost certainly wrong!")
                retval.append(True)
                continue
            eval_ctx.set_valuation_map(point)
            retval.append(valuations[point] == evaluation.evaluate_expression_raw(synth_fun_expr, eval_ctx))

        return retval


