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

import evaluation
import unifiers_lia
import exprs
import termsolvers
import unifiers
import verifiers
import z3smt
import semantics_types
from enum import IntEnum

import signal
import resource

EUSOLVER_MEMORY_LIMIT = (1 << 31)

_expr_to_str = exprs.expression_to_string
_expr_to_smt = semantics_types.expression_to_smt
_is_expr = exprs.is_expression
_get_expr_with_id = exprs.get_expr_with_id

class DuplicatePointException(Exception):
    def __init__(self, point):
        self.point = point

    def __str__(self):
        return 'Duplicate Point %s' % str([self.point[i].value_object
                                           for i in range(len(self.point))])

class Solver(object):
    def __init__(self, syn_ctx):
        self.syn_ctx = syn_ctx
        self.reset()
        self.term_solver_time = 0
        self.unifier_time = 0

    def reset(self):
        self.eval_ctx = evaluation.EvaluationContext()
        self.smt_ctx = z3smt.Z3SMTContext()
        self.points = []
        self.point_set = set()

    def add_points(self, points):
        for point in points:
            if (point in self.point_set):
                raise DuplicatePointException(point)
            self.point_set.add(point)
            self.points.append(point)

    def solve(self, term_generator, pred_generator, generator_factory, TermSolver, Unifier, Verifier, divide_and_conquer=True):
        import time
        syn_ctx = self.syn_ctx
        synth_fun = syn_ctx.synth_fun
        spec = syn_ctx.get_specification()

        term_solver = TermSolver(spec.term_signature, term_generator, spec, synth_fun)
        unifier = Unifier(pred_generator, term_solver, synth_fun, syn_ctx, spec)
        verifier = Verifier(syn_ctx, self.smt_ctx)
        time_origin = time.clock()

        while (True):
            # iterate until we have terms that are "sufficient"
            success = term_solver.solve(one_term_coverage=not divide_and_conquer)
            if not success:
                return None
            # we now have a sufficient set of terms
            # print('Term solve complete!')
            # print([ _expr_to_str(term) for sig,term in term_solver.get_signature_to_term().items()])

            # Check term solver for completeness
            cexs = verifier.verify_term_solve(list(term_solver.get_signature_to_term().values()))

            if cexs is None:
                unifier_state = unifier.unify()
                unification = next(unifier_state)
                sol_or_cex = verifier.verify(unification)
            else:
                # print('Term solve incomplete!')
                sol_or_cex = cexs

            if _is_expr(sol_or_cex):
                solution_found_at = time.clock() - time_origin
                yield (sol_or_cex,
                        unifier.last_dt_size,
                        term_solver.get_num_distinct_terms(),
                        unifier.get_num_distinct_preds(),
                        term_solver.get_largest_term_size_enumerated(),
                        unifier.get_largest_pred_size_enumerated(),
                        len(self.points),
                        solution_found_at)
                return

            term_solver.add_points(sol_or_cex) # Term solver can add all points at once
            unifier.add_points(sol_or_cex)
            self.add_points(sol_or_cex)
            generator_factory.add_points(sol_or_cex)


########################################################################
# TEST CASES
########################################################################
def _do_solve(solver, generator_factory, term_generator, pred_generator, TermSolver, Unifier, Verifier, run_anytime_version):
    reported_expr_string_set = set()
    sol_tuples = solver.solve(
            term_generator,
            pred_generator,
            generator_factory,
            TermSolver,
            Unifier,
            Verifier)
            # unifiers_lia.SpecAwareLIAUnifier)
    for sol_tuple in sol_tuples:
        (sol, dt_size, num_t, num_p, max_t, max_p, card_p, sol_time) = sol_tuple
        sol_str = _expr_to_str(sol)
        if (sol_str in reported_expr_string_set):
            continue

        reported_expr_string_set.add(sol_str)

        print('----------------------------------------------')
        print('Solution Size                : %d' % exprs.get_expression_size(sol))
        print('Solution Time from start (s) : %f' % sol_time)
        print('DT Size                      : %d' % dt_size)
        print('Num Dist. Terms Enumerated   : %d' % num_t)
        print('Num Dist. Preds Enumerated   : %d' % num_p)
        print('Max Term Size Enumerated     : %d' % max_t)
        print('Max Pred Size Enumerated     : %d' % max_p)
        print('Num Points                   : %d' % card_p)
        print('Solution                     : %s' % _expr_to_str(sol), flush=True)
        print('----------------------------------------------')
        if (not run_anytime_version):
            return sol


def die():
    print('Usage: %s [--anytime] <timeout in seconds> max <num args to max function>' % sys.argv[0])
    print('Usage: %s [--anytime] <timeout in seconds> icfp <benchmark file>' % sys.argv[0])
    exit(1)

def _timeout_handler(signum, frame):
    if (signum != -1):
        print('[solvers.main]: Timed out!')
        print('[solvers.main]: Trying to exit gracefully...')
        sys.exit(1)
    else:
        print('[solvers.main]: Exiting gracefully...')
        sys.exit(1)

def _memout_checker(signum, frame):
    rusage = resource.getrusage(resource.RUSAGE_SELF)
    if ((rusage[2] * 1024) > EUSOLVER_MEMORY_LIMIT):
        print('[solvers.main: Memory out!')
        print('[solvers.main: Trying to exit gracefully...')
        sys.exit(1)

if __name__ == '__main__':
    import time
    import sys
    if (len(sys.argv) < 4):
        die()
    run_anytime_version = False
    try:
        if (sys.argv[1] == '--anytime'):
            time_limit = int(sys.argv[2])
            benchmark_type = sys.argv[3]
            benchmark_subtype = sys.argv[4]
            run_anytime_version = True
        else:
            time_limit = int(sys.argv[1])
            benchmark_type = sys.argv[2]
            benchmark_subtype = sys.argv[3]
    except Exception:
        die()

    start_time = time.clock()
    print('[solvers.main]: Started %s %s %s' % (benchmark_type, benchmark_subtype,
                                                ', running anytime version.' if run_anytime_version else ', running one solution version.'))
    print('[solvers.main]: Setting time limit to %d seconds' % time_limit)
    signal.signal(signal.SIGVTALRM, _timeout_handler)
    signal.setitimer(signal.ITIMER_VIRTUAL, time_limit)
    print('[solvers.main]: Memory limit is %d bytes.' % EUSOLVER_MEMORY_LIMIT)
    signal.signal(signal.SIGPROF, _memout_checker)
    signal.setitimer(signal.ITIMER_PROF, 15, 15)

    if (benchmark_type == 'max'):
        max_cardinality = int(benchmark_subtype)
        test_solver_max(max_cardinality, run_anytime_version)
    elif (benchmark_type == 'icfp'):
        benchmark_file = benchmark_subtype
        test_solver_icfp(benchmark_file, run_anytime_version)
    else:
        die()

    _timeout_handler(-1, None)

#
# solvers.py ends here
