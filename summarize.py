import glob, sys
import random, math
import subprocess
import sexpdata, ast, json

outname = sys.argv[1]
sample_ratio = float(sys.argv[2])
globs = sys.argv[3:]

files = []
for g in globs:
    files += glob.glob("random_results_may/" + g)

print(len(files))
file_roots = [f.split(".sl")[0] for f in files]
file_roots = list(set(file_roots))
random.shuffle(file_roots)
file_roots = file_roots[:int(len(file_roots) * sample_ratio)]
files = [f for f in files if f.split(".sl")[0] in file_roots]
print(len(files))


# returns (tree_size, [(tree_size, ispred, expansion)])
def postorder(tree, args, ispred=False):
    if type(tree) is not list:
        if tree in args:
            tree = "__arg"
        elif type(tree) is str and tree[:2] == "#x":
            num = int(tree[2:], 16)
            if num > 1:
                tree = "__bigint"
            else:
                tree = str(num)
        elif type(tree) is int and tree > 1:
            tree = "__bigint"
        else:
            tree = str(tree)
        return (1, [(1, ispred, (tree, ()))])
    else:
        name = tree[0]
        tree_size = 1
        allexp = []
        subszs = ()
        for i, subtree in enumerate(tree[1:]):
            if name not in ["if0", "ite"] or i != 0:
                tsz, exp = postorder(subtree, args, ispred)
            else:
                tsz, exp = postorder(subtree, args, True)
            tree_size += tsz
            allexp += exp
            subszs = subszs + (tsz,)

        if name not in ["if0", "ite"]:
            allexp += [(tree_size, ispred, (name, subszs))]

        return (tree_size, allexp)


def from_sexp(s):
    return ast.literal_eval(str(sexpdata.loads(s)).replace("Symbol", ""))

def get_solution(fname):
    x = open(f).read().split("FINAL_SOLUTION")
    if len(x) == 1:
        return None
    tree = from_sexp(x[-1].strip())
    defun, funname, args, retval, tree = tree
    assert defun == "define-fun"
    args = [a[0] for a in args]
    tsz, exp = postorder(tree, args)
    return exp

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

grammar_cache = {}
def get_grammar(fname):
    fname = fname.split("/")[1][:-10].replace("@", "/")
    if fname not in grammar_cache:
        try:
            s = subprocess.check_output("EUSOLVER_SETTINGS='algo=random' bash ./eusolver '%s' | grep ________________ -m 1 -B 100000" % fname,
                    stderr=subprocess.DEVNULL, shell=True)
            grammar_cache[fname] = s
        except subprocess.CalledProcessError:
            grammar_cache[fname] = None
    s = grammar_cache[fname]
    if s is None:
        return None

    possibilities = []
    for line in s.decode("utf8").splitlines():
        if "EXPR" in line or "NTRW" in line or "FUNC" in line:
            line = line.strip().split(" ", 1)[1]
            first_word = None
            if "dummy_pred" in line:
                first_word = from_sexp(line)[1][0]
            elif line[0] == "(":
                first_word = from_sexp(line)[0]
            else:
                first_word = line.split()[0]

            if first_word.startswith("_arg_"):
                first_word = "__arg"
            elif parsable_as_int(first_word):
                num = parse_as_int(first_word)
                if num > 1:
                    first_word = "__bigint"
                else:
                    first_word = str(num)



            possibilities.append(first_word)

    return list(set(possibilities))


situations = {}
for f in sorted(files):
    print(f)
    grammar = get_grammar(f)
    exp = get_solution(f)
    if exp is None or grammar is None:
        print("no solution")
        continue
    print(grammar)
    for e in exp:
        print("  ", e)
        sz, ispred, choice = e
        choice = choice[0] # Just the name.
        if (sz) not in situations:
            situations[sz] = []
        situations[sz].append((choice, grammar))

print("---")

outfile = open("models/" + outname + ".situations", "w")
for e in sorted(situations):
    distinct = {}
    for cg in situations[e]:
        key = (cg[0], tuple(sorted(cg[1])))
        if key not in distinct:
            distinct[key] = 0
        distinct[key] += 1
    print("SITUATION %s\n - %d samples, %d distinct" % (e, len(situations[e]), len(distinct)))
    outfile.write("SITUATION %s\n - %d samples, %d distinct\n" % (e, len(situations[e]), len(distinct)))
    arr = sorted([(distinct[k], k) for k in distinct])[::-1]
    for cnt, key in arr:
        print("  %02d of %s from (%s)" % (cnt, key[0], ", ".join(key[1])))
        outfile.write("  %02d of %s from (%s)\n" % (cnt, key[0], ", ".join(key[1])))

    print("EOL")
    outfile.write("EOL\n")

open("models/" + outname + ".used", "w").write("".join(f + "\n" for f in file_roots))
