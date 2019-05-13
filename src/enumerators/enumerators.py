#!/usr/bin/env python3
# enumerators.py ---
#
# Filename: enumerators.py
# Author: Abhishek Udupa
# Created: Tue Aug 25 11:44:38 2015 (-0400)
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

from utils import utils
from exprs import evaluation
from utils import basetypes
from exprs import exprs
from exprs import exprtypes
from queue import PriorityQueue
from collections import defaultdict
import os
import random

# if __name__ == '__main__':
#     utils.print_module_misuse_and_exit()

def commutative_good_size_tuple(sizes):
    return sizes[0] >= sizes[1]

def default_good_size_tuple(sizes):
    return True

def union_of_generators(*generators):
    for gen in generators:
        for e in gen:
            yield e

def smart_union_of_generators(*generators):
    index = 0
    queue = PriorityQueue()
    for i, gen in enumerate(generators):
        try:
            elem = next(gen)
            queue.put((-elem.score, index, elem, i))
            index += 1
        except StopIteration:
            pass

    while not queue.empty():
        score, _, elem, i = queue.get()
        yield elem

        try:
            elem = next(generators[i])
            queue.put((-elem.score, index, elem, i))
            index += 1
        except StopIteration:
            pass

def cartesian_product_of_generators(*generators):
    """A generator that produces the cartesian product of the input
    "sub-generators."""
    tuple_size = len(generators)
    if (tuple_size == 1):
        for elem in generators[0].generate():
            yield (elem, )

    else:
        for sub_tuple in cartesian_product_of_generators(*generators[1:]):
            for elem in generators[0].generate():
                yield (elem, ) + sub_tuple


def smart_cartesian_product_of_generators(*generators):
    for val in _smart_cartesian_product_of_generators(*generators):
        yield val.val


def _smart_cartesian_product_of_generators(*generators):
    class Element:
        def __init__(self, score, val):
            self.score = score
            self.val = val

        def __str__(self):
            return "%s\tscore = %s" % (self.val, self.score)

    if len(generators) == 1:
        for elem in generators[0].generate():
            yield Element(elem.score, (elem, ))
    else:
        rgen = _smart_cartesian_product_of_generators(*generators[1:])
        egen = generators[0].generate()

        # This may throw StopIteration, but it's expected.
        rec = [next(rgen)]
        elems = [next(egen)]

        rfinished = False
        efinished = False

        index = 0 # For tie resolution...
        queue = PriorityQueue()
        queue.put((-score_children_combiner([elems[0].score, rec[0].score]), index, (0, 0)))
        index += 1

        # maxvis[e] - maximum r, such that (e, r) was at one point in queue
        maxvis = [0]

        while not queue.empty():
            score, _, (e, r) = queue.get()
            yield Element(-score, (elems[e], ) + rec[r].val)

            # Try to add e+1, 0
            if r == 0 and len(elems) <= e + 1:
                try:
                    elems.append(next(egen))
                    maxvis.append(-1)
                except StopIteration:
                    pass

            if len(elems) > e + 1 and maxvis[e+1] == -1:
                queue.put((-score_children_combiner([elems[e+1].score, rec[r].score]), index, (e+1, 0)))
                index += 1
                maxvis[e+1] = 0

            # Try to add e, r+1
            if len(rec) <= r + 1:
                try:
                    rec.append(next(rgen))
                except StopIteration:
                    pass

            if len(rec) > r + 1 and maxvis[e] < r+1:
                queue.put((-score_children_combiner([elems[e].score, rec[r+1].score]), index, (e, r+1)))
                index += 1
                maxvis[e] = r+1


class GeneratorBase(object):
    object_counter = 0

    def __init__(self, name = None):
        if (name != None or name != ''):
            self.name = name
        else:
            self.name = 'AnonymousGenerator_%d' % self.object_counter
        self.object_counter += 1

    def generate(self):
        raise basetypes.AbstractMethodError('GeneratorBase.generate()')

    def set_size(self, new_size):
        raise basetypes.AbstractMethodError('GeneratorBase.set_size()')

    def clone(self):
        raise basetypes.AbstractMethodError('GeneratorBase.clone()')


def parse_as_int(s):
    if s[:2] == "#x":
        num = int(s[2:], 16)
        return num
    else:
        return int(s)

def parsable_as_int(s):
    try:
        parse_as_int(s)
        return True
    except ValueError:
        return False

import ast, sexpdata
def from_sexp(s):
    return ast.literal_eval(str(sexpdata.loads(s)).replace("Symbol", ""))


def rule_to_word(rule):
    rule = str(rule)
    if "dummy_pred" in rule:
        word = from_sexp(rule)[1][0]
    elif rule[0] == "(":
        word = from_sexp(rule)[0]
    else:
        word = rule.split()[0]

    if word.startswith("_arg_"):
        word = "__arg"
    elif parsable_as_int(word):
        num = parse_as_int(word)
        if num > 1:
            word = "__bigint"
        else:
            word = str(num)

    return word


def leaf_expr_to_word(expr):
    s = exprs.expression_to_string(expr)
    if parsable_as_int(s):
        num = parse_as_int(s)
        if num > 1:
            return "__bigint"
        else:
            return str(num)
    elif s.startswith("_arg_"):
        return "__arg"
    elif s == "z":
        return "z"

    print(s)
    assert False



def get_preferences_for_size_normal(sz):
    if sz in alt_preferences:
        pref = alt_preferences[sz]
    else:
        if sz > max(alt_preferences):
            pref = alt_preferences[max(alt_preferences)]
        else:
            pref = []

    return pref
def get_preferences_for_size_conflated(sz):
    return alt_preferences


def score_expr_combiner_normal(op_score, children_score):
    return op_score * children_score
def score_expr_combiner_naive(op_score, children_score):
    return op_score + children_score/1e4
def score_expr_combiner_random(op_score, children_score):
    return random.random()


def score_children_combiner_normal(children_scores):
    score = 1.0
    for s in children_scores:
        score *= s
    return score
def score_children_combiner_naive(children_scores):
    score = 0.0
    for s in children_scores:
        score /= 10000.0
        score += s
    return s
def score_children_combiner_random(children_scores):
    return random.random()

min_prio = 1e-4
union_fun = smart_union_of_generators
product_fun = smart_cartesian_product_of_generators
get_preferences_for_size = get_preferences_for_size_normal

settings = os.environ["EUSOLVER_SETTINGS"].split(",")
for setting in settings:
    setting = setting.split("=")
    if setting[0] == "algo":
        if setting[1] == "random":
            score_children_combiner = score_children_combiner_random
            score_expr_combiner = score_expr_combiner_random
        elif setting[1] == "greedy":
            score_children_combiner = score_children_combiner_naive
            score_expr_combiner = score_expr_combiner_naive
        elif setting[1] == "stochastic":
            score_children_combiner = score_children_combiner_normal
            score_expr_combiner = score_expr_combiner_normal
        else:
            assert False
    elif setting[0] == "min_prio":
        min_prio = float(setting[1])
    elif setting[0] == "weights":
        alt_preferences = ast.literal_eval(open(setting[1]).read())
    elif setting[0] == "conflate_size":
        get_preferences_for_size = get_preferences_for_size_conflated
    else:
        assert False






class LeafGenerator(GeneratorBase):
    """A generator for leaf objects.
    Variables, constants and the likes."""

    def __init__(self, leaf_objects, name = None):
        super().__init__(name)
        self.leaf_objects = list(leaf_objects)
        self.iterable_size = len(self.leaf_objects)
        self.allowed_size = 0

        assert len(self.leaf_objects) == 1

        pref = get_preferences_for_size(1)
        self.pref = defaultdict(lambda: min_prio)
        for el, score in pref:
            self.pref[el] = score
        self.leaf_objects = [x._replace(score=self.pref[leaf_expr_to_word(x)]) for x in self.leaf_objects]

    def generate(self):
        current_position = 0
        if (self.allowed_size != 1):
            return

        while (current_position < self.iterable_size):
            retval = self.leaf_objects[current_position]
            current_position += 1
            yield retval

    def set_size(self, new_size):
        self.allowed_size = new_size

    def clone(self):
        return LeafGenerator(self.leaf_objects, self.name)


class AlternativesGenerator(GeneratorBase):
    """A generator that accepts multiple "sub-generators" and
    generates a sequence that is equivalent to the concatenation of
    the sequences generated by the sub-generators."""
    def __init__(self, sub_generators, nt, rules, name = None):
        # assert (len(sub_generators) > 1)
        super().__init__(name)
        self.sub_generators = [x.clone() for x in sub_generators]
        #import random
        #random.shuffle(self.sub_generators)
        self.nt = nt
        self.rules = rules
        #self.generator_factory = generator_factory

    def set_size(self, new_size):
        print("ALT %s set size" % self.nt, new_size)

        self.allowed_size = new_size

        for sub_generator in self.sub_generators:
            sub_generator.set_size(new_size)

    def generate(self):
        for obj in union_fun(*[g.generate() for g in self.sub_generators]):
            yield obj

    def clone(self):
        return AlternativesGenerator([x.clone() for x in self.sub_generators],
                self.nt, self.rules,
                                     self.name)

class AlternativesExpressionTemplateGenerator(GeneratorBase):
    def __init__(self, expr_template, place_holder_vars, sub_generators, good_size_tuple, name=None):
        super().__init__(name)
        self.nlgens = [x.clone() for x in sub_generators]
        self.arity = len(sub_generators)
        self.allowed_size = 0
        assert self.arity > 0
        self.good_size_tuple = good_size_tuple
        self.expr_template = expr_template
        self.place_holder_vars = place_holder_vars

    def set_size(self, new_size):
        self.allowed_size = new_size
        
        if (self.allowed_size - 1 < self.arity):
            ps = []
        else:
            ps = list(utils.partitions(self.allowed_size - 1, self.arity))
            ps = [p for p in ps if self.good_size_tuple(p)]
        print("ANLG:PARTS", ps)

        lgens = []
        self.cloned_gens = []

        for partition in ps:
            gens = [x.clone() for x in self.nlgens]
            for i in range(self.arity):
                gens[i].set_size(partition[i])

            self.cloned_gens.append(gens)

        pref = get_preferences_for_size(new_size)

        self.pref = defaultdict(lambda: min_prio)
        for el, score in pref:
            self.pref[el] = score

    def generate(self):
        newgens = []
        for gens in self.cloned_gens:
            def gen(gens):
                for product_tuple in product_fun(*gens):
                    retval = exprs.substitute_all(
                            self.expr_template, list(zip(
                                self.place_holder_vars, product_tuple)))
                    word = rule_to_word(exprs.expression_to_string(retval))
                    score = self.pref[word]

                    children_score = score_children_combiner(x.score for x in product_tuple)
                    score = score_expr_combiner(score, children_score)
                    retval = retval._replace(score=score)
                    yield retval

            newgens.append(gen(gens))

        for val in union_fun(*newgens):
            yield val

    def clone(self):
        return AlternativesExpressionTemplateGenerator(self.expr_template,
                self.place_holder_vars, self.nlgens, self.good_size_tuple, self.name)

class _RecursiveGeneratorPlaceholder(GeneratorBase):
    """A type for placeholders for recursive generators.
    Really just a wrapper around a string."""

    def __init__(self, factory, identifier):
        self.identifier = identifier
        self.factory = factory

    def __eq__(self, other):
        return (self.identifier == other.identifier)

    def __ne__(self, other):
        return (not self.__eq__(other))

    def set_size(self, new_size):
        if (new_size > 0):
            self.actual_generator = self.factory._instantiate_placeholder(self)
            self.actual_generator.set_size(new_size)
        else:
            self.actual_generator = None

    def generate(self):
        if (self.actual_generator == None):
            return
        else:
            yield from self.actual_generator.generate()
            # # audupa: comment out above and uncomment below for python3 < 3.3
            # for obj in self.actual_generator.generate():
            #     yield obj

    def clone(self):
        return _RecursiveGeneratorPlaceholder(self.factory, self.identifier)

class GeneratorFactoryBase(object):
    """A factory for creating recursive generators
    (possibly mutually recursive as well). We associate names with
    generator objects, and also allow these names to be used as placeholders.
    In the end, we actually create the generator object, when :set_size(): is called
    on the returned generator objects."""

    def __init__(self):
        self.generator_map = {}
        self.generator_constructors = {}

    def add_points(self, points):
        raise basetypes.AbstractMethodError('GeneratorFactoryBase.add_points()')

    def make_placeholder(self, identifier):
        if (identifier in self.generator_map):
            raise basetypes.ArgumentError('Identifier already used as placeholder!')
        retval = _RecursiveGeneratorPlaceholder(self, identifier)
        self.generator_map[identifier] = retval
        return retval

    def make_generator(self, generator_name, generator_constructor,
                       arg_tuple_to_constructor):
        self.generator_constructors[generator_name] = (generator_constructor, arg_tuple_to_constructor)
        return self.generator_map[generator_name]

    def has_placeholder(self, identifier):
        return identifier in self.generator_map

    def _instantiate_placeholder(self, placeholder):
        raise basetypes.AbstractMethodError('GeneratorFactoryBase._instantiate_placeholder()')

class NullGeneratorFactory(GeneratorFactoryBase):
    def __init__(self):
        super().__init__()

    def add_points(self, points):
        pass

class RecursiveGeneratorFactory(GeneratorFactoryBase):
    def __init__(self):
        super().__init__() 

    def add_points(self, points):
        pass

    def _instantiate_placeholder(self, placeholder):
        assert (placeholder.factory is self)
        (constructor, arg_tuple) = self.generator_constructors[placeholder.identifier]
        return constructor(*arg_tuple)


class PointDistinctGenerator(GeneratorBase):
    def __init__(self, placeholder, factory):
        super().__init__()
        self.factory = factory
        self.size = None
        self.generated = 0
        self.placeholder = placeholder

    def generate(self):
        self.generated = 0
        while True:
            #print("PDGEN", self.placeholder.identifier)
            ret = self.factory.get_from(self.placeholder, self.size, self.generated)
            if ret is None:
                break
            yield ret
            self.generated += 1

    def set_size(self, new_size):
        self.size = new_size
        self.generated = 0

    def clone(self):
        raise basetypes.UnhandledCaseError('PointDistinctGenerator.clone()')


class PointDistinctGeneratorFactory(GeneratorFactoryBase):
    def __init__(self, spec):
        super().__init__()
        self.points = []
        self.signatures = {}
        self.cache = {}
        self.base_generators = {}
        self.finished_generators = {}
        self.eval_ctx = evaluation.EvaluationContext()
        self.cache_sizes = []
        self.all_caches = []

        if spec.is_multipoint:
            assert len(spec.synth_funs) == 1
            self.applications = spec.get_applications()[spec.synth_funs[0]]
            for app in self.applications:
                for child in app.children:
                    if exprs.find_application(child, spec.synth_funs[0].function_name) is not None:
                        raise Exception("Unable to form point out of forall variables")
            self.point_profiles = []
        else:
            self.applications = None
            self.point_profiles = None

    def get_cache_size(self):
        sm = 0
        for placeholder, size in self.cache:
            sm += len(self.cache[(placeholder, size)])
        return sm

    def finalize(self):
        self.cache_sizes.append(self.get_cache_size())

    def get_cache_sizes(self):
        return self.cache_sizes

    def clear_caches(self):
        # self.print_caches()
        self.cache_sizes.append(self.get_cache_size())
        self.all_caches.append(self.cache)
        self.cache = {}
        self.signatures = {}
        self.base_generators = {}
        self.finished_generators = {}

    def print_caches(self):
        for i, cache in enumerate(self.all_caches):
            print('++++++++++++', i)
            for placeholder, size in cache:
                print(placeholder, size, '->')
                for term in cache[(placeholder, size)]:
                    print("\tscore=", term.score, "\t", exprs.expression_to_string(term))
        print('++++++++++++', "fin")

    def add_points(self, points):
        self.points.extend(points)
        if self.applications is not None:
            for point in points:
                self.eval_ctx.set_valuation_map(point)
                point_profile = []
                for app in self.applications:
                    profile = tuple([ evaluation.evaluate_expression(c, self.eval_ctx) for c in app.children ])
                    point_profile.append(profile)
                self.point_profiles.append(point_profile)
        self.clear_caches()

    def _initialize_base_generator(self, placeholder, size):
        self.cache[(placeholder, size)] = []
        if placeholder not in self.signatures:
            self.signatures[placeholder] = []
        (constructor, arg_tuple) = self.generator_constructors[placeholder]
        generator = constructor(*arg_tuple)
        generator.set_size(size)
        print("TTT", generator.nt, id(generator))
        self.base_generators[(placeholder, size)] = generator.generate()
        self.finished_generators[(placeholder, size)] = False

    def _compute_signature(self, expr):
        if self.applications is None:
            # Single invocation (not multifunction)
            points = self.points
            res = [ None ] * len(points)
            for i in range(len(points)):
                # Assumes introvars are at the beginning of the point
                self.eval_ctx.set_valuation_map(points[i])
                res[i] = evaluation.evaluate_expression_raw(expr, self.eval_ctx)
            return res
        else:
            points = self.points
            res = [ None ] * len(points)
            for i in range(len(points)):
                sig = []
                for profile in self.point_profiles[i]:
                    self.eval_ctx.set_valuation_map(profile)
                    sig.append(evaluation.evaluate_expression_raw(expr, self.eval_ctx))
                res[i] = sig
            return res

    visited_cnt = 0
    def get_from(self, placeholder, size, position):
        placeholder = placeholder.identifier
        #print("GETFROM", placeholder, size, position)
        self.visited_cnt += 1

        # Have not started generation
        if (placeholder, size) not in self.cache:
            self._initialize_base_generator(placeholder, size)

        cached_exprs = self.cache[(placeholder, size)]
        assert position <= len(cached_exprs)

        # Have already generated required expression
        if position < len(cached_exprs):
            return cached_exprs[position]

        # Have finished generation
        if self.finished_generators[(placeholder, size)]:
            return None

        # In the middle of generation
        while True:
            next_expr = next(self.base_generators[(placeholder, size)])
            if next_expr is None:
                self.finished_generators[(placeholder, size)] = True
                return None
            try:
                signature = self._compute_signature(next_expr)
                if signature not in self.signatures[placeholder]:
                    cached_exprs.append(next_expr)
                    self.signatures[placeholder].append(signature)
                    #print('Generated', placeholder, size, ':', 
                    #        exprs.expression_to_string(next_expr))
                    #print('Generated', placeholder, size, ':', exprs.expression_to_string(next_expr),
                    #        'with signature', signature)
                    return next_expr 
                else:
                    pass
                    #print('Eliminated', placeholder, size, ':', 
                    #        exprs.expression_to_string(next_expr))
                    # print('Eliminated', placeholder, size, ':', exprs.expression_to_string(next_expr),
                    #         'with signature', signature)
            except (basetypes.PartialFunctionError, basetypes.UnboundLetVariableError):
                # print('Undefined', placeholder, size, ':', exprs.expression_to_string(next_expr))
                pass

    def _instantiate_placeholder(self, placeholder):
        return PointDistinctGenerator(placeholder, self)

class FilteredGenerator(GeneratorBase):
    """A class for implementing a filtered generator."""
    def __init__(self, filter_object, generator_object, name = None):
        super().__init__(name)
        self.filter_object = filter_object
        self.generator_object = generator_object

    def generate(self):
        for obj in self.generator_object.generate():
            if (self.filter_object.check(obj)):
                yield obj

    def set_size(self, new_size):
        self.generator_object.set_size(new_size)

    def clone(self):
        return FilteredGenerator(self.filter_object, self.generator_object.clone(), self.name)


class BunchedGenerator(GeneratorBase):
    """A wrapper for a generator that generates objects in bunches"""
    def __init__(self, generator_object, max_size, bunch_size = 16, name = None):
        super().__init__(name)
        self.generator_object = generator_object
        self.bunch_size = bunch_size
        self.max_size = max_size
        self.generator_state = None
        self.current_object_size = 0

    def generate(self):
        current_size = 1
        max_size = self.max_size
        sub_generator_object = self.generator_object
        bunch_size = self.bunch_size
        sub_generator_object.set_size(current_size)
        sub_generator_state = sub_generator_object.generate()
        finished = False

        while(True):
            retval = [None] * bunch_size
            current_index = 0
            while (current_index < bunch_size):
                try:
                    retval[current_index] = next(sub_generator_state)
                except StopIteration:
                    # can be bump up the subgenerator size?
                    if (current_size < max_size):
                        current_size += 1
                        # print(current_size)
                        sub_generator_object.set_size(current_size)
                        sub_generator_state = sub_generator_object.generate()
                        continue
                    elif (not finished):
                        finished = True
                        self.current_object_size = current_size
                        yield retval[:current_index]
                    else:
                        return
                current_index += 1
            self.current_object_size = current_size
            if all(map(lambda f: f is None, retval)):
                return
            else:
                yield retval


    def set_size(self, new_bunch_size):
        """selects a new bunch size"""
        self.bunch_size = new_bunch_size

    def clone(self):
        return BunchedGenerator(self.generator_object.clone(), self.bunch_size, self.name)

class StreamGenerator(GeneratorBase):
    """A wrapper for a generator that seamlessly generates objects of size [1, max_size]"""
    def __init__(self, generator_object, enable_logging = False, max_size = (1 << 20), name = None):
        super().__init__(name)
        self.generator_object = generator_object
        self.max_size = max_size
        self.generator_state = None
        self.enable_logging = enable_logging

    def generate(self):
        # import time

        current_size = 1
        # total_exps = 0
        # logging_enabled = self.enable_logging
        # if (logging_enabled):
        #     generation_start_time = time.clock()

        max_size = self.max_size
        sub_generator_object = self.generator_object

        while (current_size <= max_size):
            total_of_current_size = 0
            sub_generator_object.set_size(current_size)
            # if (logging_enabled):
            #     current_size_start_time = time.clock()

            sub_generator_state = sub_generator_object.generate()
            while (True):
                try:
                    retval = next(sub_generator_state)
                    total_of_current_size += 1
                    yield retval
                except StopIteration:
                    # if (logging_enabled):
                    #     current_size_end_time = time.clock()
                    #     current_size_time = current_size_end_time - current_size_start_time
                    #     cumulative_size_time = current_size_end_time - generation_start_time
                    #     total_exps += total_of_current_size

                    current_size += 1
                    break
        return

    def set_size(self, new_max_size):
        self.max_size = new_max_size

    def clone(self):
        return StreamGenerator(self.generator_object.clone(), self.bunch_size, self.name)


############################################################
# TEST CASES and utils for other test cases.
############################################################
def _generate_test_generators():
    from core import synthesis_context
    from semantics import semantics_core
    from semantics import semantics_lia

    syn_ctx = synthesis_context.SynthesisContext(semantics_core.CoreInstantiator(),
                                                  semantics_lia.LIAInstantiator())

    var_a_info = syn_ctx.make_variable(exprtypes.IntType(), 'varA', 0)
    var_b_info = syn_ctx.make_variable(exprtypes.IntType(), 'varB', 1)
    var_c_info = syn_ctx.make_variable(exprtypes.IntType(), 'varC', 2)

    var_a = exprs.VariableExpression(var_a_info)
    var_b = exprs.VariableExpression(var_b_info)
    var_c = exprs.VariableExpression(var_c_info)

    zero_value = exprs.Value(0, exprtypes.IntType())
    one_value = exprs.Value(1, exprtypes.IntType())
    zero_exp = exprs.ConstantExpression(zero_value)
    one_exp = exprs.ConstantExpression(one_value)

    var_generator = LeafGenerator([var_a, var_b, var_c], 'Variable Generator')
    const_generator = LeafGenerator([zero_exp, one_exp], 'Constant Generator')
    leaf_generator = AlternativesGenerator([var_generator, const_generator],
                                           'Leaf Term Generator')
    generator_factory = RecursiveGeneratorFactory()
    start_generator_ph = generator_factory.make_placeholder('Start')
    start_bool_generator_ph = generator_factory.make_placeholder('StartBool')


    add_fun = syn_ctx.make_function('add', exprtypes.IntType(), exprtypes.IntType())
    sub_fun = syn_ctx.make_function('sub', exprtypes.IntType(), exprtypes.IntType())
    ite_fun = syn_ctx.make_function('ite', exprtypes.BoolType(),
                                               exprtypes.IntType(), exprtypes.IntType())
    and_fun = syn_ctx.make_function('and', exprtypes.BoolType(), exprtypes.BoolType())
    or_fun = syn_ctx.make_function('or', exprtypes.BoolType(), exprtypes.BoolType())
    not_fun = syn_ctx.make_function('not', exprtypes.BoolType())
    le_fun = syn_ctx.make_function('le', exprtypes.IntType(), exprtypes.IntType())
    ge_fun = syn_ctx.make_function('ge', exprtypes.IntType(), exprtypes.IntType())
    eq_fun = syn_ctx.make_function('eq', exprtypes.IntType(), exprtypes.IntType())

    start_generator = \
    generator_factory.make_generator('Start',
                                     AlternativesGenerator,
                                     ([leaf_generator] +
                                      [FunctionalGenerator(add_fun,
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator(sub_fun,
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator(ite_fun,
                                                           [start_bool_generator_ph,
                                                            start_generator_ph,
                                                            start_generator_ph])],))

    generator_factory.make_generator('StartBool',
                                     AlternativesGenerator,
                                     ([FunctionalGenerator(and_fun,
                                                           [start_bool_generator_ph,
                                                            start_bool_generator_ph]),
                                       FunctionalGenerator(or_fun,
                                                           [start_bool_generator_ph,
                                                            start_bool_generator_ph]),
                                       FunctionalGenerator(not_fun,
                                                           [start_bool_generator_ph]),
                                       FunctionalGenerator(le_fun,
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator(eq_fun,
                                                           [start_generator_ph,
                                                            start_generator_ph]),
                                       FunctionalGenerator(ge_fun,
                                                           [start_generator_ph,
                                                            start_generator_ph])],))
    return start_generator

def test_generators():
    start_generator = _generate_test_generators()
    start_generator.set_size(5)
    for exp in start_generator.generate():
        print(exprs.expression_to_string(exp))

    # tests for bunched generators
    print('Testing bunched generators....')
    bunch_generator = BunchedGenerator(start_generator, 10, 5)
    for bunch in bunch_generator.generate():
        print('Bunch:')
        for exp in bunch:
            print('    %s' % exprs.expression_to_string(exp))

if __name__ == '__main__':
    test_generators()

#
# enumerators.py ends here
