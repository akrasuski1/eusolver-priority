#!/usr/bin/env python3
# termsolvers_lia.py ---
#
# Filename: termsolvers_lia.py
# Author: Arjun Radhakrishna
# Created: Wed, 08 Jun 2016 21:12:20 -0400
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

from termsolvers import TermSolverInterface
import exprs
import exprtypes
import itertools
import semantics_types
import semantics_core
import z3smt
import evaluation

_expr_to_str = exprs.expression_to_string
_expr_to_smt = semantics_types.expression_to_smt

def _is_constant(d):
    if len(d) == 1 and 1 in d.keys():
        return True
    return False

def _dict_to_expr(d, syn_ctx):
    if 1 in d:
        ret = exprs.ConstantExpression(exprs.Value(d.pop(1), exprtypes.IntType()))
    else:
        ret = None
    for v, i in d.items():
        if i == 1:
            vt = v
        else:
            vt = syn_ctx.make_function_expr('mul', v, exprs.ConstantExpression(exprs.Value(i, exprtypes.IntType())))
        if ret is None:
            ret = vt
        else:
            ret = syn_ctx.make_function_expr('add', ret, vt)
    return ret

def collect_terms(expr):
    if exprs.is_variable_expression(expr) or exprs.is_formal_parameter_expression(expr):
        return {expr:1}
    elif exprs.is_constant_expression(expr):
        return {1:expr.value_object.value_object}

    func_name = expr.function_info.function_name
    if func_name in [ '+', 'add' ]:
        ret = {}
        ds = [ collect_terms(c) for c in expr.children ]
        for d in ds:
            for v, i in d.items():
                ret[v] = ret.get(v, 0) + i
        return ret
    elif func_name == 'sub' or (func_name == '-' and len(expr.children) == 2):
        [ d1, d2 ] = [ collect_terms(c) for c in expr.children ]
        ret = d1.copy()
        for v, i in d2.items():
            ret[v] = ret.get(v, 0) - i
        return ret
    elif func_name in [ '*', 'mul' ]:
        [ d1, d2 ] = [ collect_terms(c) for c in expr.children ]
        (c, t) = (d1, d2) if _is_constant(d1) else (d2, d1)
        constant = c[1]
        ret = {}
        for v, i in t.items():
            ret[v] = i * constant
        return ret
    elif func_name == '-':
        d = collect_terms(expr.children[0])
        ret = {}
        for v, i in d.items():
            ret[v] = - i
        return ret
    else:
        # print(_expr_to_str(expr))
        raise NotImplementedError

def solve_inequalities(model, outvars, inequalities, syn_ctx):
    if len(outvars) == 1:
        return solve_inequalities_one_outvar(model, outvars[0], inequalities, syn_ctx)

    # Check if we can get away with factoring out one outvar
    for ineq in inequalities:
        if not ineq.function_info.function_name == '=' and not ineq.function_info.function_name == 'eq':
            continue
        l, r = collect_terms(ineq.children[0]), collect_terms(ineq.children[1])
        for outvar in outvars:
            coeff = l.get(outvar, 0) - r.get(outvar, 0)
            if abs(coeff) == 1:
                [t] = solve_inequalities_one_outvar(model, outvar, [ineq], syn_ctx)
                rest_ineqs = [ exprs.substitute(e, outvar, t) for e in inequalities if e != ineq ]
                rest_outvars = [ o for o in outvars if o != outvar ]
                rest_sol = solve_inequalities(model, rest_outvars, rest_ineqs, syn_ctx)
                sols = list(zip(rest_outvars, rest_sol))
                while True:
                    tp = exprs.substitute_all(t, sols)
                    if tp == t:
                        break
                    t = tp
                sols_dict = dict(sols)
                sols_dict[outvar] = t
                return [ sols_dict[o] for o in outvars ]

    # Otherwise, need to do some complicated stuff
    raise NotImplementedError

def solve_inequalities_one_outvar(model, outvar, inequalities, syn_ctx):
    if len(inequalities) == 0:
        return [ exprs.ConstantExpression(exprs.Value(0, exprtypes.IntType())) ]
    # print(model)
    # print([ _expr_to_str(i) for i in inequalities ])
    def evaluate(d):
        d = d.copy()
        ret = d.pop(1, 0)
        for v, i in d.items():
            ret += model[v.variable_info.variable_eval_offset].value_object.value_object
        return ret

    flip = { '>=':'<=', '>':'<', '<=':'>=', '<':'>', 'eq':'eq', '=':'=' }
    normalized_ineqs = []
    for ineq in inequalities:
        left = collect_terms(ineq.children[0])
        right = collect_terms(ineq.children[1])
        outvar_coeff = left.get(outvar, 0) - right.get(outvar, 0)
        if outvar_coeff == 0:
            continue

        normalized = {}
        for v in left.keys() | right.keys():
            normalized[v] = right.get(v, 0) - left.get(v, 0)
            if outvar_coeff < 0:
                normalized[v] *= -1
        normalized.pop(outvar)

        func_name = ineq.function_info.function_name
        assert func_name in [ '=', 'eq', '<=', '>=', '>', '<' ]
        if outvar_coeff < 0:
            func_name = flip[func_name]
        if func_name == '<':
            func_name = '<='
            normalized[1] = normalized.get(1, 0) - 1
        elif func_name == '>':
            func_name = '>='
            normalized[1] = normalized.get(1, 0) + 1
        normalized_ineqs.append((abs(outvar_coeff), func_name, normalized))
        # print(_expr_to_str(ineq), ' =========> ')
        # print('\t', outvar_coeff, ' * outvar', func_name, [ (i, _expr_to_str(v) if exprs.is_expression(v) else 1) for (v, i) in normalized.items() ])

    # Equalities
    eqs = [ ineq for ineq in  normalized_ineqs if ineq[1] == 'eq' or ineq[1] == '=' ]
    if len(eqs) > 0:
        (coeff, _, rhs) = eqs[0]
        rhs = _dict_to_expr(rhs, syn_ctx)
        if coeff == 1:
            return [ rhs ]
        else:
            return [ syn_ctx.make_function_expr('div', rhs,
                    exprs.ConstantExpression(exprs.Value(coeff, exprtypes.IntType()))) ]

    # Upper bounds
    uppers = [ ineq for ineq in  normalized_ineqs if ineq[1] == '<=' ]
    if len(uppers) == 0:
        tighest_upper = None
    else:
        tighest_upper = min(uppers, key=lambda a: evaluate(a[2]) / a[0] )

    # Lower bounds
    lowers = [ ineq for ineq in  normalized_ineqs if ineq[1] == '>=' ]
    if len(lowers) == 0:
        tighest_lower = None
    else:
        tighest_lower = max(lowers, key=lambda a: evaluate(a[2]) / a[0] )
    # print(tighest_lower)

    if tighest_upper is not None:
        coeff = tighest_upper[0]
        rhs = _dict_to_expr(tighest_upper[2], syn_ctx)
        if coeff == 1:
            return [ rhs ]
        return [ syn_ctx.make_function_expr('div', rhs,
                exprs.ConstantExpression(exprs.Value(coeff, exprtypes.IntType()))) ]
    elif tighest_lower is not None:
        coeff = tighest_lower[0]
        rhs = _dict_to_expr(tighest_lower[2], syn_ctx)
        if coeff == 1:
            return [ rhs ]
        return [ syn_ctx.make_function_expr('div',
                syn_ctx.make_function_expr('add', rhs, exprs.ConstantExpression(exprs.Value(1, exprtypes.IntType()))),
                exprs.ConstantExpression(exprs.Value(coeff, exprtypes.IntType()))) ]
    else:
        return exprs.ConstantExpression(exprs.Value(0, exprtypes.IntType()))

class SpecAwareLIATermSolver(TermSolverInterface):
    def __init__(self, term_signature, spec):
        super().__init__()
        self.term_signature = term_signature
        self.synth_funs = spec.synth_funs
        self.spec = spec
        self.syn_ctx = self.spec.syn_ctx
        self.point_var_exprs =  [ exprs.VariableExpression(v) for v in spec.point_vars ]
        self.clauses = spec.get_canon_clauses()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.eval_ctx = evaluation.EvaluationContext()

        self.canon_apps = [ self.spec.canon_application[sf] for sf in self.synth_funs ]

        self.outvars = []
        for fn in self.synth_funs:
            self.outvars.append(
                    exprs.VariableExpression(exprs.VariableInfo(
                        exprtypes.IntType(), 'outvar_' + fn.function_name,
                        len(self.point_var_exprs) + len(self.outvars))))
        all_vars = self.point_var_exprs + self.outvars
        self.all_vars_z3 = [ _expr_to_smt(v, self.smt_ctx) for v in all_vars ]

    def generate_more_terms(self):
        pass

    def _compute_term_signature(self, term):
        return self._default_compute_term_signature(term)

    def _trivial_solve(self):
        ret = exprs.ConstantExpression(exprs.Value(0, exprtypes.IntType()))
        if len(self.synth_funs) > 1:
            domain_types = tuple([exprtypes.IntType()] * len(self.synth_funs))
            ret = exprs.FunctionExpression(semantics_core.CommaFunction(domain_types),
                    tuple([ret] * len(self.synth_funs)))
        self.signature_to_term = {None:ret}
        return True

    def _single_solve_single_point(self, ivs, point):
        syn_ctx = self.syn_ctx
        smt_ctx = self.smt_ctx
        eval_ctx = self.eval_ctx
        canon_spec = self.spec.get_canonical_specification()

        # Find one value of output
        eq_constrs = []
        for var, value in zip(self.point_var_exprs, point):
            c = self.syn_ctx.make_function_expr('eq', 
                    exprs.ConstantExpression(value), var)
            eq_constrs.append(c)
        full_constr = self.syn_ctx.make_function_expr('and',
                canon_spec, *eq_constrs)

        for synth_fun, outvar in zip(self.synth_funs, self.outvars):
            smt_ctx.set_interpretation(synth_fun, outvar)
            eval_ctx.set_interpretation(synth_fun, outvar)

        raw_z3_model = exprs.sample(full_constr, smt_ctx, self.all_vars_z3)
        model = [ exprs.Value(z3_value.as_long(), exprtypes.IntType()) for z3_value in raw_z3_model ]

        # Filter to disjuncts that are true in this model
        model_clauses = []
        for clause in self.clauses:
            new_clause = []
            for disjunct in clause:
                d = exprs.substitute_all(disjunct, list(zip(self.canon_apps, self.outvars)))
                eval_ctx.set_valuation_map(model)
                if evaluation.evaluate_expression_raw(d, eval_ctx):
                    new_clause.append(d)
            model_clauses.append(new_clause)


        # Filter to disjuncts that have outvar occurring in them
        outvar_clauses = []
        outvar_set = set(self.outvars)
        for clause in model_clauses:
            new_clause = []
            for disjunct in clause:
                if len(outvar_set & exprs.get_all_variables(disjunct)) > 0:
                    new_clause.append(disjunct)
            outvar_clauses.append(new_clause)

        # Pick the first disjunct from each clause and solve 
        relevent_disjuncts = []
        for outvar_clause in outvar_clauses:
            if len(outvar_clause) > 0:
                relevent_disjuncts.append(outvar_clause[0])

        return solve_inequalities(model, self.outvars, relevent_disjuncts, syn_ctx)

    def _single_solve(self, ivs, points):
        if len(points) == 1:
            return self._single_solve_single_point(ivs, points[0])
        else:
            raise NotImplementedError

    def solve(self):
        if len(self.points) == 0:
            # print("Trivial solve!")
            return self._trivial_solve()

        # for point in self.points:
        #     print("POINT:", [ p.value_object for p in point])
        # for sig, term in self.signature_to_term.items():
        #     print('SIGTOTERM:', str(sig), _expr_to_str(term))

        intro_var_signature = []
        for point in self.points:
            ivs = point[:len(self.spec.intro_vars)]
            intro_var_signature.append((ivs, point))

        # Nobody can understand what python groupby returns!!!
        # ivs_groups = itertools.groupby(
        #         sorted(intro_var_signature, key=lambda a: a[0]),
        #         key=lambda a: a[0])
        curr_ivs = None
        ivs_groups = []
        for ivs, point in intro_var_signature:
            if ivs == curr_ivs:
                ivs_groups[-1][1].append(point)
            else:
                ivs_groups.append((ivs, [point]))
                curr_ivs = ivs

        for ivs, points in ivs_groups:
            terms = self._single_solve(ivs, points)
            new_terms = []
            for term, sf in zip(terms, self.synth_funs):
                new_terms.append(exprs.substitute_all(term, 
                    list(zip(self.spec.intro_vars, self.spec.formal_params[sf]))))
            terms = new_terms
            print([ _expr_to_str(t) for t in terms ])

            sig = self.signature_factory()
            if len(self.synth_funs) > 1:
                domain_types = tuple([exprtypes.IntType()] * len(self.synth_funs))
                single_term = exprs.FunctionExpression(semantics_core.CommaFunction(domain_types),
                        tuple(terms))
            else:
                single_term = terms[0]

            for i, t in enumerate(self.term_signature(single_term, self.points)):
                if t:
                    sig.add(i)
            self.signature_to_term[sig] = single_term

        return True

