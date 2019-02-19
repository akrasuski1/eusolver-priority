import glob, sys
import random, math
import subprocess
import sexpdata, ast, json

files = glob.glob("random_results/*")
if len(sys.argv) > 1:
    files = sys.argv[1:]

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
    tree = from_sexp(open(f).read().split("FINAL_SOLUTION")[-1].strip())
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
        s = subprocess.check_output("bash ./eusolver '%s' | grep ________________ -m 1 -B 100000" % fname,
                stderr=subprocess.DEVNULL, shell=True)
        grammar_cache[fname] = s
    s = grammar_cache[fname]

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

def learn_weights(samples, smooth=1e-9):
    all_possibilities = set()
    for chosen, poss in samples:
        for p in poss:
            all_possibilities.add(p)

    predicted = {k: 1.0/len(all_possibilities) for k in all_possibilities}
    samples = samples[:]

    prevloss = None
    step = 1e-2
    while step > 1e-6:
        random.shuffle(samples)
        loss = 0
        for res, case in samples:
            s1 = sum(predicted[c] for c in case)
            loss += sum(math.log(predicted[c]/s1) for c in case if c != res)
            loss += math.log(1-predicted[res]/s1)

            predicted[res] = s1*(1-(1-predicted[res]/s1)/(1+step))
            for c in case:
                if c != res:
                    predicted[c] /= (1+step)

                mn = smooth * s1
                predicted[c] = max(predicted[c], mn)

            s2 = sum(predicted[c] for c in case)
            for p in case:
                predicted[p] *= s1/s2

        if prevloss is not None:
            delta = prevloss - loss
            # print(loss, delta, step)
            if delta < 1e-9: # Negative or zero.
                step /= 1.3
        prevloss = loss

    return predicted


situations = {}
for f in sorted(files):
    print(f)
    grammar = get_grammar(f)
    exp = get_solution(f)
    for e in exp:
        sz, ispred, choice = e
        choice = choice[0] # Just the name.
        if (sz) not in situations:
            situations[sz] = []
        situations[sz].append((choice, grammar))

print("---")
for e in sorted(situations):
    distinct = {}
    for cg in situations[e]:
        key = (cg[0], tuple(sorted(cg[1])))
        if key not in distinct:
            distinct[key] = 0
        distinct[key] += 1
    print("SITUATION %s\n - %d samples, %d distinct" % (e, len(situations[e]), len(distinct)))
    arr = sorted([(distinct[k], k) for k in distinct])[::-1]
    for cnt, key in arr:
        print("  %02d of %s from (%s)" % (cnt, key[0], ", ".join(key[1])))

    weights = learn_weights(situations[e])
    arr = sorted([(weights[p], p) for p in weights])[::-1]
    print("LEARNED:")
    for p, q in arr:
        print("\t", q, p)
    print("EOL")
