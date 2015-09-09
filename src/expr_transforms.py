#!/usr/bin/env python3
# expr_transforms.py ---
#
# Filename: expr_transforms.py
# Author: Abhishek Udupa
# Created: Wed Sep  2 18:19:39 2015 (-0400)
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

import utils
import exprs
import exprtypes
import semantics_types

if __name__ == '__main__':
    utils.print_module_misuse_and_exit()

def check_expr_binding_to_context(expr, syn_ctx):
    kind = expr.expr_kind
    if (kind == exprs.ExpressionKinds.variable_expression):
        if (not syn_ctx.validate_variable(expr.variable_info)):
            raise TypeError(('Expression %s was not formed using the given ' +
                             'context!') % exprs.expression_to_string(expr))
    elif (kind == exprs.ExpressionKinds.function_expression):
        if (not syn_ctx.validate_function(expr.function_info)):
            raise TypeError(('Expression %s was not formed using the given ' +
                             'context!') % exprs.expression_to_string(expr))
        for child in expr.children:
            check_expr_binding_to_context(child, syn_ctx)
    else:
        return

def _check_single_invocation_property(expr, unknown_function_terms):
    kind = expr.expr_kind
    if (kind == exprs.ExpressionKinds.function_expression):
        fun_info = expr.function_info
        if (function_info.function_kind == semantics_types.FunctionKinds.unknown_function):
            if (len(unknown_function_terms) == 0):
                unknown_function_terms.add(expr)
            elif (expr not in unknown_function_terms):
                return False

        for child in expr.children:
            return _check_single_invocation_property(child, unknown_function_terms)
    else:
        return True


def check_single_invocation_property(expr):
    """Checks if the expression has only one unknown function, and also
    that the expression satisfies the single invocation property, i.e.,
    the unknown function appears only in one syntactic form in the expression."""
    if (not _check_single_invocation_property(expr, set())):
        raise TypeError(('The (specification) expression: %s does not have the single ' +
                         'invocation property!') % exprs.expression_to_string(expr))

def _gather_variables(expr, accumulator):
    kind = expr.expr_kind
    if (kind == exprs.ExpressionKinds.variable_expression):
        accumulator.add(expr)
    elif (kind == exprs.ExpressionKinds.function_expression):
        for child in expr.children:
            _gather_variables(child, accumulator)

def gather_variables(expr):
    """Gets the set of variable expressions present in the expr."""
    var_set = set()
    _gather_variables(expr, var_set)
    return var_set

def _gather_unknown_functions(expr, fun_set):
    kind = expr.expr_kind
    if (kind == exprs.ExpressionKinds.function_expression):
        if (isinstance(expr.function_info, semantics_types.UnknownFunctionBase)):
            fun_set.add(expr.function_info)
        for child in expr.children:
            _gather_unknown_functions(child, fun_set)

def gather_unknown_functions(expr):
    fun_set = set()
    _gather_unknown_functions(expr, fun_set)
    return fun_set

def canonicalize_specification(expr, syn_ctx):
    """Assigns variable offsets for all the vars appearing in the spec.
    Assigns function ids for unknown functions appearing in the spec.
    Returns a pair containing:
    1. A list of variable_info objects, with the position each variable_info
       being equal to its var_eval_offset.
    2. A list of UnknownFunctionBase objects, with the position of each function_info
       being equal to its unknown_function_id
    """
    check_expr_binding_to_context(expr, syn_ctx)
    unknown_function_set = gather_unknown_functions(expr)
    variable_set = gather_variables(expr)

    unknown_function_list = list(unknown_function_set)
    variable_list = [expr.variable_info for expr in variable_set]
    num_vars = len(variable_list)
    num_funs = len(unknown_function_list)
    for i in range(num_vars):
        variable_list[i].variable_eval_offset = i
    for i in range(num_funs):
        unknown_function_list[i].unknown_function_id = i

    return (variable_list, unknown_function_list)

#
# expr_transforms.py ends here
