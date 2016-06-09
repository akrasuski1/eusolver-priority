# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

import sexp
import exprs
import grammars
import semantics_core
import semantics_lia
import semantics_bv
import semantics_slia
import synthesis_context
import semantics_types
import exprtypes
from bitvectors import BitVector

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


def sexpFromFile(benchmarkFileName):
    try:
        benchmarkFile = open(benchmarkFileName)
    except:
        print('File not found: %s' % benchmarkFileName)
        return None

    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    benchmarkFile.close()
    return bmExpr

def parse_bitvec(bv_exp):
    if len(bv_exp) != 2:
        return None
    type_, value = bv_exp[0], bv_exp[1]
    if (
            len(type_) != 2 or
            type_[0] != 'BitVec' or
            len(type_[1]) != 2 or
            type_[1][0] != 'Int'):
        return None
    length = int(type_[1][1])
    if length != 64:
        return None
    return BitVector(value, length)

def parse_icfp_constraint(exp):
    if exp[0] != '=':
        return None
    lhs = exp[1]
    rhs = exp[2]
    if len(lhs) != 2 or lhs[0] != 'f':
        return None
    arg = parse_bitvec(lhs[1])
    val = parse_bitvec(rhs)
    if arg is None or val is None:
        return None
    return ([arg], val)

def get_icfp_points(exp):
    icfp_rest = [['set-logic', 'BV'], ['define-fun', 'shr1', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvlshr', 'x', (['BitVec', ('Int', 64)], 1)]], ['define-fun', 'shr4', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvlshr', 'x', (['BitVec', ('Int', 64)], 4)]], ['define-fun', 'shr16', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvlshr', 'x', (['BitVec', ('Int', 64)], 16)]], ['define-fun', 'shl1', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvshl', 'x', (['BitVec', ('Int', 64)], 1)]], ['define-fun', 'if0', [['x', ['BitVec', ('Int', 64)]], ['y', ['BitVec', ('Int', 64)]], ['z', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['ite', ['=', 'x', (['BitVec', ('Int', 64)], 1)], 'y', 'z']], ['synth-fun', 'f', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], [['Start', ['BitVec', ('Int', 64)], [(['BitVec', ('Int', 64)], 0), (['BitVec', ('Int', 64)], 1), 'x', ['bvnot', 'Start'], ['shl1', 'Start'], ['shr1', 'Start'], ['shr4', 'Start'], ['shr16', 'Start'], ['bvand', 'Start', 'Start'], ['bvor', 'Start', 'Start'], ['bvxor', 'Start', 'Start'], ['bvadd', 'Start', 'Start'], ['if0', 'Start', 'Start', 'Start']]]]], ['check-synth']]
    constraints = [ c for c in exp if c[0] == 'constraint' ]
    rest = [ c for c in exp if c[0] != 'constraint' ]
    if rest != icfp_rest:
        print("Not an icfp benchmark")
        return None

    points = []
    for constraint in constraints:
        if len(constraint) != 2:
            print("Could not parse icfp constraint: %s" % constraint)
        point = parse_icfp_constraint(constraint[1])
        if point == None:
            print("Could not parse icfp constraint: %s" % constraint)
            return None
        points.append(point)
    return points

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
    if len(synth_fun_data) == 4:
        [name, args_data, ret_type_data, grammar_data] = synth_fun_data
    else:
        [name, args_data, ret_type_data] = synth_fun_data
        grammar_data = 'Default grammar'
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

_known_theories = [ "LIA", "BV", "SLIA" ]

def _process_uninterpreted_funcs(uninterpreted_funcs_data, syn_ctx, uf_instantiator):
    for [ name, arg_types_data, ret_type_data] in uninterpreted_funcs_data:
        arg_types = tuple([ sexp_to_type(arg_type_data) for arg_type_data in arg_types_data ])
        ret_type = sexp_to_type(ret_type_data)
        func = semantics_types.UninterpretedFunction(name, len(arg_types), arg_types, ret_type) 
        uf_instantiator.add_function(name, func)


def extract_benchmark(file_sexp):
    core_instantiator = semantics_core.CoreInstantiator()

    theories, file_sexp = filter_sexp_for('set-logic', file_sexp)
    assert len(theories) == 1
    [theory] = theories[0]
    assert theory in _known_theories
    theory_instantiator = get_theory_instantiator(theory)

    macro_instantiator = semantics_core.MacroInstantiator()
    uf_instantiator = semantics_core.UninterpretedFunctionInstantiator()

    syn_ctx = synthesis_context.SynthesisContext(
            core_instantiator,
            theory_instantiator,
            macro_instantiator,
            uf_instantiator)

    defs, file_sexp = filter_sexp_for('define-fun', file_sexp)
    process_definitions(defs, syn_ctx, macro_instantiator)

    ufuncs_data, file_sexp = filter_sexp_for('declare-fun', file_sexp)
    _process_uninterpreted_funcs(ufuncs_data, syn_ctx, uf_instantiator)

    synth_funs_data, file_sexp = filter_sexp_for('synth-fun', file_sexp)
    assert len(synth_funs_data) == 1
    synth_fun, arg_var_map, grammar_data = process_synth_func(synth_funs_data[0], syn_ctx)
    if grammar_data == 'Default grammar':
        grammar = grammar_data
    else:
        grammar = sexp_to_grammar(arg_var_map, grammar_data, synth_fun, syn_ctx)

    forall_vars_data, file_sexp = filter_sexp_for('declare-var', file_sexp)
    forall_vars_map = _process_forall_vars(forall_vars_data, syn_ctx)

    constraints_data, file_sexp = filter_sexp_for('constraint', file_sexp)
    constraints = process_constraints(constraints_data, syn_ctx, forall_vars_map, synth_fun)

    check_sats, file_sexp = filter_sexp_for('check-synth', file_sexp)
    assert check_sats == [[]]
    assert file_sexp == []

    return theory, syn_ctx, synth_fun, macro_instantiator, uf_instantiator, constraints, grammar

def get_theory_instantiator(theory):
    if theory == "LIA":
        return semantics_lia.LIAInstantiator()
    elif theory == "BV":
        return semantics_bv.BVInstantiator()
    elif theory == "SLIA":
        return semantics_slia.SLIAInstantiator()
    else:
        raise Exception("Unknown theory")

