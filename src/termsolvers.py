#!/usr/bin/env python3
# termsolvers.py ---
#
# Filename: termsolvers.py
# Author: Arjun Radhakrishna
# Created: Mon, 06 Jun 2016 13:54:34 -0400
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


import evaluation
from eusolver import BitSet
import enumerators
import exprs
import semantics_types

_expr_to_str = exprs.expression_to_string
_is_expr = exprs.is_expression
_get_expr_with_id = exprs.get_expr_with_id

def check_term_sufficiency(sig_to_term, num_points):
    accumulator = BitSet(num_points)
    for (sig, term) in sig_to_term.items():
        accumulator |= sig
    return (accumulator.is_full())

def check_one_term_sufficiency(sig_to_term, num_points):
    for (sig, term) in sig_to_term.items():
        if sig.is_full():
            return True
    return False

class TermSolverInterface(object):
    def get_signature_to_term(self):
        raise basetypes.AbstractMethodError('TermSolverInterface.get_signature_to_term()')

    def add_points(self):
        raise basetypes.AbstractMethodError('TermSolverInterface.add_points()')

    def solve(self):
        raise basetypes.AbstractMethodError('TermSolverInterface.solve()')

    def generate_more_terms(self):
        raise basetypes.AbstractMethodError('TermSolverInterface.generate_more_terms()')

class EnumerativeTermSolverBase(TermSolverInterface):
    def __init__(self, spec, synth_fun):
        self.spec = spec
        self.synth_fun = synth_fun

        self.points = []
        self.eval_ctx = evaluation.EvaluationContext()
        self.current_largest_term_size = 0
        self.signature_to_term = {}

        self.bunch_generator = None
        self.max_term_size = 1024

    def set_max_term_size(self, size):
        self.max_term_size = size

    def get_signature_to_term(self):
        return self.signature_to_term

    def _trivial_solve(self):
        term_size = 1
        while (term_size <= self.max_term_size):
            self.term_generator.set_size(term_size)
            for term in self.term_generator.generate():
                self.signature_to_term = {None : term}
                return True
            term_size += 1
        return False

    def _default_add_points(self, new_points):
        points = self.points
        points.extend(new_points)
        self.signature_factory = BitSet.make_factory(len(points))
        self._do_complete_sig_to_term()

    def get_largest_term_size_enumerated(self):
        if self.bunch_generator is None:
            return self.current_largest_term_size
        return max(self.current_largest_term_size,
                self.bunch_generator.current_object_size)

    def restart_bunched_generator(self):
        # Book keeping
        if self.bunch_generator is not None:
            self.current_largest_term_size = max(self.current_largest_term_size,
                    self.bunch_generator.current_object_size)

        self.bunch_generator = enumerators.BunchedGenerator(self.term_generator,
                                                            self.max_term_size)
        self.bunch_generator_state = self.bunch_generator.generate()


    def _default_solve(self, one_term_coverage=False):
        num_points = len(self.points)
        if (num_points == 0): # No points, any term will do
            return self._trivial_solve()

        stopping_condition = \
                check_term_sufficiency if not one_term_coverage \
                else check_one_term_sufficiency

        signature_to_term = self.signature_to_term
        self.restart_bunched_generator()
        while (not stopping_condition(signature_to_term, num_points)):
            success = self.generate_more_terms()
            if not success:
                return False
        return True

    def _default_compute_term_signature(self, term, old_signature=None):
        points = self.points
        num_points = len(points)
        retval = self.signature_factory()
        eval_ctx = self.eval_ctx
        eval_ctx.set_interpretation(self.synth_fun, term)
        spec = self.spec

        if old_signature is not None:
            retval.copy_in(old_signature)
            start_index = old_signature.size_of_universe()
        else:
            start_index = 0

        num_new_points = retval.size_of_universe()
        for i in range(start_index, num_new_points):
            eval_ctx.set_valuation_map(points[i])
            if (evaluation.evaluate_expression_raw(spec, eval_ctx)):
                retval.add(i)
        return retval

    def _do_complete_sig_to_term(self):
        old_sig_to_term = self.signature_to_term
        new_sig_to_term = {}

        for sig, term in old_sig_to_term.items():
            new_sig = self._compute_term_signature(term)
            if not new_sig.is_empty():
                new_sig_to_term[new_sig] = term

        self.signature_to_term = new_sig_to_term

    def get_num_distinct_terms(self):
        return len(self.signature_to_term)

    def _default_generate_more_terms(self, transform_term=None):
        signature_to_term = self.signature_to_term
        bunch_generator_state = self.bunch_generator_state
        try:
            bunch = next(bunch_generator_state)
        except StopIteration:
            return False

        for term in bunch:
            if transform_term is not None:
                term = transform_term(term)
            sig = self._compute_term_signature(term)
            if (sig in signature_to_term or sig.is_empty()):
                continue
            signature_to_term[sig] = term

        return True



class PointlessTermSolver(EnumerativeTermSolverBase):
    def __init__(self, spec, term_generator, synth_fun):
        super().__init__(spec, synth_fun)
        self.term_generator = term_generator
        self.eval_cache = {}
        self.monotonic_expr_id = 0

    def add_points(self, new_points):
        return self._default_add_points(new_points)

    def _compute_term_signature(self, term):
        eval_cache = self.eval_cache
        old_signature = eval_cache.get(term.expr_id)
        retval = self._default_compute_term_signature(term, old_signature)
        eval_cache[term.expr_id] = retval
        return retval

    def generate_more_terms(self):
        def add_expr_id(term):
            term = _get_expr_with_id(term, self.monotonic_expr_id)
            self.monotonic_expr_id += 1
            return term
        return self._default_generate_more_terms(transform_term=add_expr_id)

    def solve(self, one_term_coverage=False):
        self.monotonic_expr_id = 0
        return self._default_solve(one_term_coverage)


class PointDistinctTermSolver(EnumerativeTermSolverBase):
    def __init__(self, spec, term_generator, synth_fun):
        super().__init__(spec, synth_fun)
        assert term_generator is enumerators.PointDistinctGenerator
        self.term_generator = term_generator

    def add_points(self, new_points):
        return self._default_add_points(new_points)

    def _compute_term_signature(self, term):
        return self._default_compute_term_signature(term)

    def generate_more_terms(self):
        return self._default_generate_more_terms(transform_term=None)

    def solve(self, one_term_coverage=False):
        return self._default_solve(one_term_coverage)

TermSolver = PointlessTermSolver
