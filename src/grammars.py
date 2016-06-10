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
import itertools
import exprtypes
import semantics_types
import random
import exprs
import enumerators


def _nt_to_generator_name(nt):
    return nt + '_Generator'

class RewriteBase(object):
    def __init__(self, type):
        self.type = type

    def _to_template_expr(self):
        raise basetypes.AbstractMethodError('RewriteBase._to_template_expr()')

    def rename_nt(self, old_name, new_name):
        raise basetypes.AbstractMethodError('RewriteBase.rename_nt()')

class ExpressionRewrite(RewriteBase):
    def __init__(self, expr):
        super().__init__(exprs.get_expression_type(expr))
        self.expr = expr

    def _to_template_expr(self):
        return [], [], self.expr

    def rename_nt(self, old_name, new_name):
        return self

class NTRewrite(RewriteBase):
    def __init__(self, non_terminal, nt_type):
        super().__init__(nt_type)
        self.non_terminal = non_terminal

    def _to_template_expr(self):
        import random
        name = self.non_terminal + '_ph_' + str(random.randint(1, 1000000))
        ph_var = exprs.VariableExpression(exprs.VariableInfo(self.type, name))
        return [ph_var], [self.non_terminal], ph_var

    def rename_nt(self, old_name, new_name):
        if self.non_terminal == old_name:
            return NTRewrite(new_name, self.type)
        else:
            return self

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

    def rename_nt(self, old_name, new_name):
        new_children = [ child.rename_nt(old_name, new_name) 
                for child in self.children ]
        return FunctionRewrite(self.function_info, *new_children)

def expr_template_to_rewrite(expr_template, ph_var_nt_map, grammar):
    if expr_template in ph_var_nt_map:
        nt = ph_var_nt_map[expr_template]
        nt_type = grammar.nt_type[nt]
        return NTRewrite(nt, nt_type)
    elif exprs.is_function_expression(expr_template):
        children = [ expr_template_to_rewrite(child, ph_var_nt_map, grammar) 
                for child in expr_template.children ]
        return FunctionRewrite(expr_template.function_info, *children)
    else:
        return ExpressionRewrite(expr_template)

class Grammar(object):
    def __init__(self, non_terminals, nt_type, rules, start='Start'):
        self.non_terminals = non_terminals
        self.nt_type = nt_type
        self.rules = rules
        self.start = start

    def __str__(self):
        return self.str()

    def str(self):
        ret = ""
        for nt in self.non_terminals:
            ret = ret + nt + "[" + str(self.nt_type[nt]) + "] ->\n"
            for rule in self.rules[nt]:
                ph_vars, nts, expr_template = rule._to_template_expr()
                ret = ret + "\t" + exprs.expression_to_string(expr_template) + "\n"
        return ret

    def to_generator(self, generator_factory=None):
        if generator_factory == None:
            generator_factory = enumerators.RecursiveGeneratorFactory()
        for nt in self.non_terminals:
            if not generator_factory.has_placeholder(_nt_to_generator_name(nt)):
                generator_factory.make_placeholder(_nt_to_generator_name(nt))
        place_holders = generator_factory.generator_map
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
            if nt == self.start:
                ret = nt_generator
        return ret

    def copy_with_nt_rename(self, old_nt_name, new_nt_name):
        new_nts = [ nt if nt != old_nt_name else new_nt_name 
                for nt in self.non_terminals ]

        new_nt_type = self.nt_type.copy()
        type = new_nt_type.pop(old_nt_name)
        new_nt_type[new_nt_name] = type

        new_rules = {}
        for nt in self.non_terminals:
            rewrites = self.rules[nt]
            new_nt = nt if nt != old_nt_name else new_nt_name
            new_rules[new_nt] = [ rew.rename_nt(old_nt_name, new_nt_name)
                    for rew in rewrites ]
        return Grammar(new_nts, new_nt_type, new_rules)

    # Quick and dirty for now
    def decompose(self, macro_instantiator):
        start_nt = self.start
        reverse_mapping = []

        term_productions = []
        pred_productions = []
        for rewrite in self.rules[start_nt]:
            ph_vars, nts, orig_expr_template = rewrite._to_template_expr()
            ph_var_nt_map = dict(zip(ph_vars, nts))
            expr_template = macro_instantiator.instantiate_all(orig_expr_template)
            ifs = exprs.find_all_applications(expr_template, 'ite')

            # Either there are no ifs or it is an concrete expression
            if len(ifs) == 0 or len(nts) == 0:
                term_productions.append(rewrite)
                continue
            elif len(ifs) > 1 and ifs[0] != expr_template:
                return None

            [cond, thent, elset] = ifs[0].children
            if (
                    thent not in ph_vars or \
                    elset not in ph_vars or \
                    ph_var_nt_map[thent] != start_nt or \
                    ph_var_nt_map[elset] != start_nt):
                return None

            cond_rewrite = expr_template_to_rewrite(cond, ph_var_nt_map, self)

            # Make dummy function to recognize predicate
            arg_var = exprs.VariableExpression(exprs.VariableInfo(exprtypes.BoolType(), 'd', 0))
            dummy_macro_func = semantics_types.MacroFunction(
                    'dummy_pred_id_' + str(random.randint(1, 1000000)), 1, (exprtypes.BoolType(),),
                    exprtypes.BoolType(), arg_var, [arg_var])
            pred_production = FunctionRewrite(dummy_macro_func, cond_rewrite)
            pred_productions.append(pred_production)
            
            reverse_mapping.append((dummy_macro_func, cond, orig_expr_template, expr_template))

        # Non-terminals
        [ term_start, pred_start ] = [ x + start_nt for x in  [ 'Term', 'Pred' ] ]
        [ term_nts, pred_nts ] = [ self.non_terminals + [ x ] 
                for x in [ term_start, pred_start ]  ]
        term_nts.remove(start_nt)
        pred_nts.remove(start_nt)

        # Non-terminal types
        term_nt_type, pred_nt_type = self.nt_type.copy(), self.nt_type.copy()
        term_nt_type.pop(start_nt)
        term_nt_type[term_start] = self.nt_type[start_nt]
        pred_nt_type.pop(start_nt)
        pred_nt_type[pred_start] = exprtypes.BoolType()

        # Rules
        term_rules = {}
        term_rules[term_start] = [ rew.rename_nt(start_nt, term_start)
                for rew in term_productions ]
        for nt in self.non_terminals:
            if nt != start_nt:
                term_rules[nt] = [ rew.rename_nt(start_nt, term_start)
                for rew in self.rules[nt] ]

        pred_rules = {}
        pred_rules[pred_start] = [ rew.rename_nt(start_nt, term_start)
                for rew in pred_productions ]
        for nt in self.non_terminals:
            if nt != start_nt:
                pred_rules[nt] = [ rew.rename_nt(start_nt, term_start)
                for rew in self.rules[nt] ]

        term_grammar = Grammar(term_nts, term_nt_type, term_rules, term_start)
        pred_grammar = Grammar(pred_nts, pred_nt_type, pred_rules, pred_start)
        return term_grammar, pred_grammar, reverse_mapping

# Tests:
