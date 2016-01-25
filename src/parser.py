# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

import sexp
# from semantics_bv import BitVector
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
    import bitstring
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
    return (arg, val)

icfp_rest = [['set-logic', 'BV'], ['define-fun', 'shr1', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvlshr', 'x', (['BitVec', ('Int', 64)], 1)]], ['define-fun', 'shr4', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvlshr', 'x', (['BitVec', ('Int', 64)], 4)]], ['define-fun', 'shr16', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvlshr', 'x', (['BitVec', ('Int', 64)], 16)]], ['define-fun', 'shl1', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['bvshl', 'x', (['BitVec', ('Int', 64)], 1)]], ['define-fun', 'if0', [['x', ['BitVec', ('Int', 64)]], ['y', ['BitVec', ('Int', 64)]], ['z', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], ['ite', ['=', 'x', (['BitVec', ('Int', 64)], 1)], 'y', 'z']], ['synth-fun', 'f', [['x', ['BitVec', ('Int', 64)]]], ['BitVec', ('Int', 64)], [['Start', ['BitVec', ('Int', 64)], [(['BitVec', ('Int', 64)], 0), (['BitVec', ('Int', 64)], 1), 'x', ['bvnot', 'Start'], ['shl1', 'Start'], ['shr1', 'Start'], ['shr4', 'Start'], ['shr16', 'Start'], ['bvand', 'Start', 'Start'], ['bvor', 'Start', 'Start'], ['bvxor', 'Start', 'Start'], ['bvadd', 'Start', 'Start'], ['if0', 'Start', 'Start', 'Start']]]]], ['check-synth']]

def get_icfp_points(exp):
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
