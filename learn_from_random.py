import glob, sys
import sexpdata, ast, json

files = glob.glob("random_results/*")
if len(sys.argv) > 1:
    files = sys.argv[1:]

# returns (tree_size, [(tree_size, ispred, expansion)])
def postorder(tree, args, ispred=False):
    if type(tree) is not list:
        if tree in args:
            tree = "__arg"
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





def parse_file(fname):
    s = open(f).read().split("FINAL_SOLUTION")[-1].strip()
    return ast.literal_eval(str(sexpdata.loads(s)).replace("Symbol", ""))


counts = {}
for f in sorted(files):
    print(f)
    tree = parse_file(f)
    defun, funname, args, retval, tree = tree
    assert defun == "define-fun"
    args = [a[0] for a in args]
    tsz, exp = postorder(tree, args)
    print tsz
    for e in exp:
        if e not in counts:
            counts[e] = 0
        counts[e] += 1
print "---"
for e in sorted(counts):
    print e, counts[e]
