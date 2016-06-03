#!/usr/bin/env python3
# grammars.py ---
#
# Filename: grammars.py
# Author: Arjun Radhakrishna
# Created: Wed, 01 Jun 2016 10:10:59 -0400
#
#
# Copyright (c) 2015, Arjun Radhakrishna, University of Pennsylvania
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
import exprs
import enumerators


def _nt_to_generator_name(nt):
    return nt + '_Generator'

class RewriteBase(object):
    def __init__(self, type):
        self.type = type

    def _to_template_expr(self):
        raise basetypes.AbstractMethodError('RewriteBase._to_template_expr()')

class ExpressionRewrite(RewriteBase):
    def __init__(self, expr):
        super().__init__(exprs.get_expression_type(expr))
        self.expr = expr

    def _to_template_expr(self):
        return [], [], self.expr

class NTRewrite(RewriteBase):
    def __init__(self, non_terminal, nt_type):
        super().__init__(nt_type)
        self.non_terminal = non_terminal

    def _to_template_expr(self):
        import random
        name = self.non_terminal + '_ph_' + str(random.randint(1, 1000000))
        ph_var = exprs.VariableExpression(exprs.VariableInfo(self.type, name))
        return [ph_var], [self.non_terminal], ph_var

class FunctionRewrite(RewriteBase):
    def __init__(self, function_info, *children):
        super().__init__(function_info.range_type)
        self.function_info = function_info
        self.children = children

    def _to_template_expr(self):
        ph_vars = []
        nts = []
        child_exprs = []
        for child in self.children:
            curr_ph_vars, curr_nts, child_expr = child._to_template_expr()
            ph_vars.extend(curr_ph_vars)
            nts.extend(curr_nts)
            child_exprs.append(child_expr)
        expr_template = exprs.FunctionExpression(self.function_info, tuple(child_exprs))
        return ph_vars, nts, expr_template

    def to_generator(self, place_holders):
        ph_vars, nts, expr_template = self._to_template_expr()
        if len(ph_vars) == 0:
            return enumerators.LeafGenerator([expr_template])
        sub_gens = [ place_holders[_nt_to_generator_name(nt)] for nt in nts ]
        return enumerators.ExpressionTemplateGenerator(expr_template, ph_vars, sub_gens)

class Grammar(object):
    def __init__(self, non_terminals, nt_type, rules):
        self.non_terminals = non_terminals
        self.nt_type = nt_type
        self.rules = rules

    def to_generator(self):
        generator_factory = enumerators.RecursiveGeneratorFactory()
        place_holders = {
                _nt_to_generator_name(nt):generator_factory.make_placeholder(_nt_to_generator_name(nt))
                for nt in self.non_terminals }
        ret = None
        for nt in self.non_terminals:
            generators = []
            leaves = []
            for rewrite in self.rules[nt]:
                if type(rewrite) == ExpressionRewrite:
                    leaves.append(rewrite.expr)
                elif type(rewrite) == NTRewrite:
                    generators.append(place_holders[_nt_to_generator_name(rewrite.non_terminal)])
                elif type(rewrite) == FunctionRewrite:
                    generators.append(rewrite.to_generator(place_holders))
                else:
                    raise Exception('Unknown rewrite type: %s' % str(type(rewrite)))
            leaf_generator = enumerators.LeafGenerator(leaves)
            nt_generator = generator_factory.make_generator(_nt_to_generator_name(nt),
                    enumerators.AlternativesGenerator,
                            ([ leaf_generator ] + generators ,))
            if nt == 'Start':
                ret = nt_generator
        return ret

    def decompose(self):
        if len(self.non_terminals) != 1:
            return None
        raise NotImplementedError

# Tests:
