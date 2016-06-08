#!/usr/bin/env python3
# benchmarks.py ---
#
# Filename: benchmarks.py
# Author: Arjun Radhakrishna
# Created: Wed, 01 Jun 2016 11:27:20 -0400
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

from bitvectors import BitVector
import parser
import termsolvers
import specifications
import unifiers
import solvers
import exprs
import enumerators
import exprtypes
import semantics_core
import semantics_bv
import semantics_types
import semantics_lia
import semantics_slia
import synthesis_context
import grammars

_known_theories = [ "LIA", "BV", "SLIA" ]

def get_theory_instantiator(theory):
    if theory == "LIA":
        return semantics_lia.LIAInstantiator()
    elif theory == "BV":
        return semantics_bv.BVInstantiator()
    elif theory == "SLIA":
        return semantics_slia.SLIAInstantiator()
    else:
        raise Exception("Unknown theory")

def filter_sexp_for(head, file_sexp):
    curr = []
    rest = []
    for sexp in file_sexp:
        if sexp[0] == head:
            curr.append(sexp[1:])
        else:
            rest.append(sexp)
    return curr, rest

def sexp_to_value(sexp):
    (type_sexp, value_exp) = sexp
    value_type = sexp_to_type(type_sexp)
    if value_type.type_code == exprtypes.TypeCodes.integer_type:
        value = int(value_exp)
    elif value_type.type_code == exprtypes.TypeCodes.boolean_type:
        assert value_exp == 'true' or value_exp == 'false'
        value = True if value_exp == 'true' else False
    elif value_type.type_code == exprtypes.TypeCodes.bit_vector_type:
        value = BitVector(int(str(value_exp)), value_type.size)
    elif value_type.type_code == exprtypes.TypeCodes.string_type:
        value = value_exp
    else:
        raise Exception('Unknown type: %s' % value_type)
    return exprs.Value(value, value_type)

def sexp_to_expr(sexp, syn_ctx, arg_var_map, synth_fun=None):
    # Must be a value
    if type(sexp) == tuple:
        value = sexp_to_value(sexp)
        return exprs.ConstantExpression(value)
    elif type(sexp) == str:
        assert sexp in arg_var_map
        return arg_var_map[sexp]
    elif type(sexp) == list:
        function_name_or_info = synth_fun \
                if synth_fun != None and sexp[0] == synth_fun.function_name else sexp[0]
        children = [ sexp_to_expr(child, syn_ctx, arg_var_map, synth_fun) for child in sexp[1:] ]
        return syn_ctx.make_function_expr(function_name_or_info, *children)
    else:
        raise Exception('Unknown sexp type: %s', str(sexp))

def sexp_to_type(sexp):
    if type(sexp) == list and sexp[0] == 'BitVec':
        assert type(sexp[1]) == tuple and sexp[1][0] == 'Int'
        length = sexp[1][1]
        return exprtypes.BitVectorType(length)
    elif sexp == 'Int':
        return exprtypes.IntType()
    elif sexp == 'Bool':
        return exprtypes.BoolType()
    elif sexp == 'String':
        return exprtypes.StringType()
    else:
        raise Exception("Unknown type: %s" % str(sexp))

def _process_function_defintion(args_data, ret_type_data):
    return_type = sexp_to_type(ret_type_data)

    arg_vars = []
    arg_var_map = {}
    arg_types = []
    for (offset, (arg_name, arg_type_sexp)) in enumerate(args_data):
        arg_type = sexp_to_type(arg_type_sexp)
        arg_types.append(arg_type)
        arg_var = exprs.VariableExpression(
                exprs.VariableInfo(arg_type, arg_name, offset))
        arg_vars.append(arg_var)
        arg_var_map[arg_name] = arg_var
    return ((arg_vars, arg_types, arg_var_map), return_type)

def process_definitions(defs, syn_ctx, macro_instantiator):
    for [name, args_data, ret_type_data, interpretation] in defs:
        ((arg_vars, arg_types, arg_var_map), return_type) = _process_function_defintion(args_data, ret_type_data)

        expr = sexp_to_expr(interpretation, syn_ctx, arg_var_map)
        macro_func = semantics_types.MacroFunction(name, len(arg_vars), tuple(arg_types), return_type, expr, arg_vars)
        macro_instantiator.add_function(name, macro_func)

def process_synth_func(synth_fun_data, syn_ctx):
    [name, args_data, ret_type_data, grammar_data] = synth_fun_data
    ((arg_vars, arg_types, arg_var_map), return_type) = _process_function_defintion(args_data, ret_type_data)

    synth_fun = syn_ctx.make_synth_function(name, arg_types, return_type)

    return synth_fun, arg_var_map, grammar_data


def _process_rule(non_terminals, nt_type, syn_ctx, arg_var_map, synth_fun, rule_data):
    if type(rule_data) == tuple:
        value = sexp_to_value(rule_data)
        return grammars.ExpressionRewrite(exprs.ConstantExpression(value))
    elif type(rule_data) == str and rule_data in arg_var_map:
        variable = arg_var_map[rule_data]
        parameter_position = variable.variable_info.variable_eval_offset
        expr = exprs.FormalParameterExpression(synth_fun,
                variable.variable_info.variable_type,
                variable.variable_info.variable_eval_offset)
        return grammars.ExpressionRewrite(expr)
    elif type(rule_data) == str and rule_data in non_terminals:
        return grammars.NTRewrite(rule_data, nt_type[rule_data])
    elif type(rule_data) == list:
        function_name = rule_data[0]
        function_args = [ _process_rule(non_terminals, nt_type, syn_ctx, arg_var_map, synth_fun, child) for child in rule_data[1:] ]
        function_arg_types = tuple([ x.type for x in function_args ])
        function = syn_ctx.make_function(function_name, *function_arg_types)
        assert function is not None
        return grammars.FunctionRewrite(function, *function_args)
    else:
        raise Exception('Unknown right hand side: %s' % rule_data)

def _process_forall_vars(forall_vars_data, syn_ctx):
    forall_var_map = {}
    for [variable_name, var_type_data] in forall_vars_data:
        variable_type = sexp_to_type(var_type_data)
        variable = syn_ctx.make_variable_expr(variable_type, variable_name)
        forall_var_map[variable_name] = variable
    return forall_var_map

def process_constraints(constraints_data, syn_ctx, forall_var_map, synth_fun):
    constraints = []
    for [constraint_data] in constraints_data:
        constraint = sexp_to_expr(constraint_data, syn_ctx, forall_var_map, synth_fun)
        constraints.append(constraint)
    return constraints

def sexp_to_grammar(arg_var_map, grammar_sexp, synth_fun, syn_ctx):
    non_terminals = [ t[0] for t in grammar_sexp ]
    nt_type = { nt:sexp_to_type(nt_type_data) for nt, nt_type_data, rules_data in grammar_sexp }
    rules = {}
    for nt, nt_type_data, rules_data in grammar_sexp:
        rewrites = []
        for rule_data in rules_data:
            rewrite = _process_rule(non_terminals, nt_type, syn_ctx, arg_var_map, synth_fun, rule_data)
            rewrites.append(rewrite)
        rules[nt] = rewrites
    return grammars.Grammar(non_terminals, nt_type, rules)

def get_pbe_valuations(constraints, synth_fun):
    valuations = []
    for constraint in constraints:
        if not exprs.is_application_of(constraint, 'eq') and \
                not exprs.is_application_of(constraint, '='):
            return None
        if len(exprs.get_all_variables(constraint)) > 0:
            return None
        arg_func, arg_other = None, None
        for a in constraint.children:
            if exprs.is_application_of(a, synth_fun):
                arg_func = a
            else:
                arg_other = a
        if arg_func is None or arg_other is None:
            return None
        valuations.append((arg_func.children, arg_other))
    return valuations

def extract_benchmark(file_sexp):
    core_instantiator = semantics_core.CoreInstantiator()

    theories, file_sexp = filter_sexp_for('set-logic', file_sexp)
    assert len(theories) == 1
    [theory] = theories[0]
    assert theory in _known_theories
    theory_instantiator = get_theory_instantiator(theory)

    macro_instantiator = semantics_core.MacroInstantiator()

    syn_ctx = synthesis_context.SynthesisContext(
            core_instantiator,
            theory_instantiator,
            macro_instantiator)

    defs, file_sexp = filter_sexp_for('define-fun', file_sexp)
    process_definitions(defs, syn_ctx, macro_instantiator)

    synth_funs_data, file_sexp = filter_sexp_for('synth-fun', file_sexp)
    assert len(synth_funs_data) == 1
    synth_fun, arg_var_map, grammar_data = process_synth_func(synth_funs_data[0], syn_ctx)
    grammar = sexp_to_grammar(arg_var_map, grammar_data, synth_fun, syn_ctx)

    forall_vars_data, file_sexp = filter_sexp_for('declare-var', file_sexp)
    forall_vars_map = _process_forall_vars(forall_vars_data, syn_ctx)

    constraints_data, file_sexp = filter_sexp_for('constraint', file_sexp)
    constraints = process_constraints(constraints_data, syn_ctx, forall_vars_map, synth_fun)

    check_sats, file_sexp = filter_sexp_for('check-synth', file_sexp)
    assert check_sats == [[]]
    assert file_sexp == []

    return syn_ctx, synth_fun, macro_instantiator, constraints, grammar

def make_solver(file_sexp):
    syn_ctx, synth_fun, macro_instantiator, constraints, grammar = extract_benchmark(file_sexp)

    valuations = get_pbe_valuations(constraints, synth_fun)
    if valuations is not None:
        specification = specifications.PBESpec(valuations, synth_fun)
    else:
        specification = specifications.StandardSpec(
                syn_ctx.make_function_expr('and', *constraints),
                syn_ctx, synth_fun)
    syn_ctx.assert_spec(specification, synth_fun)

    ans = grammar.decompose(macro_instantiator)
    if ans == None:
        # Have to configure solver for naivete
        raise NotImplementedError
    else:
        term_grammar, pred_grammar = ans
        # print("Original grammar:\n", grammar)
        # print("Term grammar:\n", term_grammar)
        # print("Pred grammar:\n", pred_grammar)
        # generator_factory = enumerators.RecursiveGeneratorFactory()
        generator_factory = enumerators.RecursiveGeneratorFactory()
        term_generator = term_grammar.to_generator(generator_factory)
        pred_generator = pred_grammar.to_generator(generator_factory)
        solver = solvers.Solver(syn_ctx)
        solvers._do_solve(solver, generator_factory, term_generator, pred_generator, False)


# Tests:

def test_make_solver():
    import parser

    # for benchmark_file in [ "../benchmarks/one_off/invertD.sl", "../benchmarks/one_off/str.sl" ]:
    # for benchmark_file in [ "../benchmarks/max/max_2.sl", "../benchmarks/max/max_3.sl" ]:
    # for benchmark_file in [ "../benchmarks/icfp/icfp_103_10.sl" ]:
    for benchmark_file in [ "../benchmarks/one_off/str.sl" ]:
        file_sexp = parser.sexpFromFile(benchmark_file)
        make_solver(file_sexp)

if __name__ == "__main__":
    test_make_solver()
