#!/usr/bin/env python3
# solvers.py ---
#
# Filename: solvers.py
# Author: Abhishek Udupa
# Created: Wed Aug 26 09:34:54 2015 (-0400)
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
import eusolver
from eusolver import BitSet
# from semantics_bv import BitVector
from bitvectors import BitVector
import evaluation
import functools
import hashcache
import exprtypes
import exprs
import expr_transforms
import z3
import z3smt
import semantics_types
from enum import IntEnum
import enumerators

_expr_to_str = exprs.expression_to_string
_expr_to_smt = semantics_types.expression_to_smt
_is_expr = exprs.is_expression
_get_expr_with_id = exprs.get_expr_with_id

_term_id_point_id_to_sat = {}
_pred_id_point_id_to_sat = {}

def _point_list_to_str(points):
    retval = ''
    for point in points:
        retval += str([x.value_object for x in point])
        retval += '\n'
    return retval

def model_to_point(model, var_smt_expr_list, var_info_list):
    num_vars = len(var_smt_expr_list)
    point = [None] * num_vars
    for i in range(num_vars):
        eval_value = model.evaluate(var_smt_expr_list[i], True)
        if (var_info_list[i].variable_type == exprtypes.BoolType()):
            point[i] = exprs.Value(bool(str(eval_value)), exprtypes.BoolType())
        elif (var_info_list[i].variable_type == exprtypes.IntType()):
            point[i] = exprs.Value(int(str(eval_value)), exprtypes.IntType())
        elif (var_info_list[i].variable_type.type_code == exprtypes.TypeCodes.bit_vector_type):
            # point[i] = exprs.Value(int(str(eval_value)), var_info_list.variable_type)
            # Z3 always prints unsigned integers?
            point[i] = exprs.Value(BitVector(int(str(eval_value)),
                                             var_info_list[i].variable_type.size),
                                   var_info_list[i].variable_type)
        else:
            raise basetypes.UnhandledCaseError('solvers.In model_to_point')
    return tuple(point)


class DuplicatePointException(Exception):
    def __init__(self, point):
        self.point = point

    def __str__(self):
        return 'Duplicate Point %s' % str([self.point[i].value_object
                                           for i in range(len(self.point))])

class Verifier(object):
    def __init__(self, syn_ctx, smt_ctx):
        self.syn_ctx = syn_ctx
        self.true_expr = exprs.ConstantExpression(exprs.Value(True, exprtypes.BoolType()))
        self.false_expr = exprs.ConstantExpression(exprs.Value(False, exprtypes.BoolType()))
        spec_tuple = syn_ctx.get_synthesis_spec()
        act_spec, var_list, fun_list, clauses, neg_clauses, canon_spec, intro_vars = spec_tuple

        self.smt_ctx = smt_ctx
        self.smt_solver = z3.Solver(ctx=self.smt_ctx.ctx())

        self.var_info_list = var_list
        self.var_expr_list = [exprs.VariableExpression(x) for x in self.var_info_list]
        self.var_smt_expr_list = [_expr_to_smt(x, self.smt_ctx) for x in self.var_expr_list]

        self.canon_spec = canon_spec
        self.clauses = clauses
        self.neg_clauses = neg_clauses
        self.intro_vars = intro_vars
        self.smt_intro_vars = [_expr_to_smt(x, self.smt_ctx) for x in self.intro_vars]

        fun_app = syn_ctx.make_function_expr(fun_list[0], *intro_vars)
        fun_app_subst_var = syn_ctx.make_variable_expr(fun_list[0].range_type, '__output__')
        self.outvar_cnstr = syn_ctx.make_function_expr('eq', fun_app_subst_var, fun_app)
        canon_spec_with_outvar = exprs.substitute(canon_spec, fun_app, fun_app_subst_var, syn_ctx)
        # print('Unifier.__init__(), canon_spec_with_outvar:\n%s' % _expr_to_str(canon_spec_with_outvar))
        neg_canon_spec_with_outvar = syn_ctx.make_function_expr('not', canon_spec_with_outvar)
        frozen_smt_cnstr = _expr_to_smt(neg_canon_spec_with_outvar, self.smt_ctx)
        self.smt_solver.add(frozen_smt_cnstr)


    def verify_term(self, term):
        smt_ctx = self.smt_ctx
        smt_solver = self.smt_solver

        smt_ctx.set_interpretation_map([term])
        eq_cnstr = _expr_to_smt(self.outvar_cnstr, smt_ctx)
        smt_solver.push()
        smt_solver.add(eq_cnstr)
        r = smt_solver.check()
        smt_solver.pop()

        if (r == z3.sat):
            cex_point = model_to_point(smt_solver.model(),
                                       self.var_smt_expr_list,
                                       self.var_info_list)
            return cex_point
        else:
            return term


class Solver(object):
    def __init__(self, syn_ctx):
        self.syn_ctx = syn_ctx
        self.spec_tuple = syn_ctx.get_synthesis_spec()
        self.reset()

    def reset(self):
        self.spec = None
        self.eval_ctx = evaluation.EvaluationContext()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.points = []
        self.point_set = set()

    def add_point(self, point):
        # print('Solver: Added point %s' % str([str(c.value_object) for c in point]))
        # print([ (str(x[0].value_object), hash(x[0].value_object)) for x in self.point_set ])
        if (point in self.point_set):
            raise DuplicatePointException(point)
        self.point_set.add(point)
        self.points.append(point)

    def _check_term_correctness_on_points(self, term):
        points = self.points
        num_points = len(points)
        eval_ctx = self.eval_ctx
        eval_ctx.set_interpretation_map([term])
        spec = self.spec
        for i in range(num_points):
            eval_ctx.set_valuation_map(points[i])
            if (not evaluation.evaluate_expression_raw(spec, eval_ctx)):
                return False
        return True

    def _solve_for_points(self):
        stream_state = self.stream_generator_state
        while (True):
            try:
                term = next(stream_state)
                # print('Generated term: %s' % _expr_to_str(term))
                if (self._check_term_correctness_on_points(term)):
                    return term
            except StopIteration:
                return None

    def solve(self, term_generator):
        import time

        act_spec, var_list, uf_list, clauses, neg_clauses, canon_spec, intro_vars = self.spec_tuple
        self.spec = canon_spec
        self.stream_generator = enumerators.StreamGenerator(term_generator, True)
        self.stream_generator_state = self.stream_generator.generate()

        verifier = Verifier(self.syn_ctx, self.smt_ctx)

        solve_start_time = time.clock()
        solution = None

        while (True):
            pointwise_solution = self._solve_for_points()
            sol_or_cex = verifier.verify_term(pointwise_solution)
            if (_is_expr(sol_or_cex)):
                solve_end_time = time.clock()
                solution = sol_or_cex
                break
            else:
                self.add_point(sol_or_cex)
        print('Solver.solve(): Completed in %f seconds.' % (solve_end_time - solve_start_time))
        return solution


########################################################################
# TEST CASES
########################################################################

def test_solver_max(num_vars):
    import synthesis_context
    import semantics_core
    import semantics_lia
    import enumerators

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_lia.LIAInstantiator())
    max_fun = syn_ctx.make_unknown_function('max', [exprtypes.IntType()] * num_vars,
                                            exprtypes.IntType())
    add_fun = syn_ctx.make_function('add', exprtypes.IntType(), exprtypes.IntType())
    sub_fun = syn_ctx.make_function('sub', exprtypes.IntType(), exprtypes.IntType())
    le_fun = syn_ctx.make_function('le', exprtypes.IntType(), exprtypes.IntType())
    ge_fun = syn_ctx.make_function('ge', exprtypes.IntType(), exprtypes.IntType())
    eq_fun = syn_ctx.make_function('eq', exprtypes.IntType(), exprtypes.IntType())
    ite_fun = syn_ctx.make_function('ite', exprtypes.BoolType(), exprtypes.IntType(),
                                    exprtypes.IntType())

    param_exprs = [exprs.FormalParameterExpression(max_fun, exprtypes.IntType(), i)
                   for i in range(num_vars)]
    param_generator = enumerators.LeafGenerator(param_exprs, 'Argument Generator')
    zero_value = exprs.Value(0, exprtypes.IntType())
    one_value = exprs.Value(1, exprtypes.IntType())
    const_generator = enumerators.LeafGenerator([exprs.ConstantExpression(zero_value),
                                                 exprs.ConstantExpression(one_value)])
    leaf_generator = enumerators.AlternativesGenerator([param_generator, const_generator],
                                                       'Leaf Term Generator')

    generator_factory = enumerators.RecursiveGeneratorFactory()
    term_generator_ph = generator_factory.make_placeholder('TermGenerator')
    pred_bool_generator_ph = generator_factory.make_placeholder('PredGenerator')
    term_generator = \
    generator_factory.make_generator('TermGenerator',
                                     enumerators.AlternativesGenerator,
                                     ([leaf_generator] +
                                      [enumerators.FunctionalGenerator(add_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(sub_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(ite_fun,
                                                                       [pred_bool_generator_ph,
                                                                        term_generator_ph,
                                                                        term_generator_ph])],))

    pred_generator = \
    generator_factory.make_generator('PredGenerator',
                                     enumerators.AlternativesGenerator,
                                     ([enumerators.FunctionalGenerator(le_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(eq_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph]),
                                       enumerators.FunctionalGenerator(ge_fun,
                                                                       [term_generator_ph,
                                                                        term_generator_ph])],))

   # construct the spec
    uvar_infos = [syn_ctx.make_variable(exprtypes.IntType(), 'x%d' % x, x)
                  for x in range(num_vars)]
    uvar_exprs = [exprs.VariableExpression(var_info) for var_info in uvar_infos]
    max_app = syn_ctx.make_function_expr(max_fun, *uvar_exprs)
    ge_constraints = []
    eq_constraints = []
    for i in range(num_vars):
        c = syn_ctx.make_function_expr('ge', max_app, uvar_exprs[i])
        ge_constraints.append(c)
        c = syn_ctx.make_function_expr('eq', max_app, uvar_exprs[i])
        eq_constraints.append(c)

    constraint = syn_ctx.make_function_expr('and', *ge_constraints)
    constraint = syn_ctx.make_function_expr('and', constraint,
                                            syn_ctx.make_function_expr('or', *eq_constraints))
    syn_ctx.assert_spec(constraint)

    solver = Solver(syn_ctx)
    expr = solver.solve(term_generator)
    return (expr, solver.points)

def get_icfp_valuations(benchmark_name):
    import parser
    test_icfp_valuations =  [
            (
                BitVector(1, 64),
                BitVector(1, 64)
            ),
            (
                BitVector(2, 64),
                BitVector(0, 64)
            ),
            (
                BitVector(3, 64),
                BitVector(3, 64)
            ),
            (
                BitVector(4, 64),
                BitVector(0, 64)
            ),
            (
                BitVector(5, 64),
                BitVector(5, 64)
            )
            ]

    sexp = parser.sexpFromFile(benchmark_name)
    if sexp is None:
        die()

    points = parser.get_icfp_points(sexp)
    if points == None:
        print("Could not parse icfp")

    return points
    # return test_icfp_valuations

def test_solver_icfp(benchmark_name):
    import synthesis_context
    import semantics_core
    import semantics_bv
    import enumerators

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                 semantics_bv.BVInstantiator(64))
    synth_fun = syn_ctx.make_unknown_function('f', [exprtypes.BitVectorType(64)],
                                            exprtypes.BitVectorType(64))

    # Unary
    unary_funcs = [ syn_ctx.make_function(name, exprtypes.BitVectorType(64))
            for name in [ 'shr1', 'shr4', 'shr16', 'shl1', 'bvnot' ]]
    # Binary
    binary_funcs = [ syn_ctx.make_function(name, exprtypes.BitVectorType(64), exprtypes.BitVectorType(64))
            for name in [ 'bvand', 'bvor', 'bvxor', 'bvadd' ]]

    param_exprs = [exprs.FormalParameterExpression(synth_fun, exprtypes.BitVectorType(64), 0)]
    param_generator = enumerators.LeafGenerator(param_exprs, 'Argument Generator')
    zero_value = exprs.Value(BitVector(0, 64), exprtypes.BitVectorType(64))
    one_value = exprs.Value(BitVector(1, 64), exprtypes.BitVectorType(64))
    const_generator = enumerators.LeafGenerator([exprs.ConstantExpression(zero_value),
                                                 exprs.ConstantExpression(one_value)])
    leaf_generator = enumerators.AlternativesGenerator([param_generator, const_generator],
                                                       'Leaf Term Generator')

    generator_factory = enumerators.RecursiveGeneratorFactory()
    term_generator_ph = generator_factory.make_placeholder('TermGenerator')
    pred_bool_generator_ph = generator_factory.make_placeholder('PredGenerator')

    unary_function_generators = [
            enumerators.FunctionalGenerator(func, [term_generator_ph])
            for func in unary_funcs
            ]
    binary_function_generators = [
            enumerators.FunctionalGenerator(func, [term_generator_ph, term_generator_ph])
            for func in binary_funcs
            ]

    term_generator = \
            generator_factory.make_generator('TermGenerator',
                    enumerators.AlternativesGenerator, (
                        ([leaf_generator] +
                        unary_function_generators +
                        binary_function_generators),
                        ))

    is1 = syn_ctx.make_function('is1', exprtypes.BitVectorType(64))
    is1_generator = enumerators.FunctionalGenerator(is1, [term_generator_ph])

    pred_generator = \
            generator_factory.make_generator('PredGenerator', enumerators.AlternativesGenerator, ([is1_generator],))

    valuations = get_icfp_valuations(benchmark_name)

    # construct the spec
    arg_exprs = [ exprs.ConstantExpression(exprs.Value(arg, exprtypes.BitVectorType(64)))
            for (arg, result) in valuations ]
    result_exprs = [ exprs.ConstantExpression(exprs.Value(result, exprtypes.BitVectorType(64)))
            for (arg, result) in valuations ]

    constraints = []
    for (arg_expr, result_expr) in zip(arg_exprs, result_exprs):
        app = syn_ctx.make_function_expr(synth_fun, arg_expr)
        c = syn_ctx.make_function_expr('eq', app, result_expr)
        constraints.append(c)

    constraint = syn_ctx.make_function_expr('and', *constraints)

    syn_ctx.assert_spec(constraint)

    solver = Solver(syn_ctx)
    expr = solver.solve(term_generator, pred_generator)

    # print("Term solver time: ", solver.term_solver_time)
    # print("Unifier time: ", solver.unifier_time)
    return (expr, solver.points)

def die():
    print('Usage: %s max <num args to max function> <log file name>' % sys.argv[0])
    print('Usage: %s icfp <benchmark file> <log file name>' % sys.argv[0])
    exit(1)

if __name__ == '__main__':
    import time
    import sys
    if (len(sys.argv) < 4):
        die()

    log_file = open(sys.argv[3], 'a')
    start_time = time.clock()

    log_file.write('Started %s\n' % sys.argv[2])

    if sys.argv[1] == "max":
        max_cardinality = int(sys.argv[2])
        (sol, points) = test_solver_max(max_cardinality)
        log_file.write('max of %d arguments:\n%s\n' % (max_cardinality, exprs.expression_to_string(sol)))
    elif sys.argv[1] == "icfp":
        benchmark_file = sys.argv[2]
        (sol, points) = test_solver_icfp(benchmark_file)
        log_file.write('f in %s:\n%s\n' % (
            benchmark_file,
            exprs.expression_to_string(sol)))
    else:
        die()

    end_time = time.clock()
    total_time = end_time - start_time

    log_file.write('Added %d counterexample points in total\n' % len(points))
    log_file.write('computed in %s seconds\n' % (str(total_time)))
    log_file.write('Solution size: %d\n' % exprs.get_expression_size(sol))
    log_file.close()

    # log_file.write('Counterexample points:\n')
    # log_file.write(_point_list_to_str(points))

#
# solvers.py ends here
