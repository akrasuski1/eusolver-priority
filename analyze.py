import sys
from collections import defaultdict
import matplotlib.pyplot as plt
import glob
import ast


model = sys.argv[1]
print(model)
name = model.split(":")[1].split(".model.")[0]
globs = sys.argv[2:]

forbidden = ast.literal_eval(open("forbidden").read())

used = {}
for f in glob.glob("models/" + name + ".used"):
    lines = open(f).readlines()
    used[f.split("/")[1].split(".used")[0]] = [u.split("/")[1].strip() for u in lines]

files = []
for g in globs:
    files += glob.glob("results/" + model + "/" + g)

def get_slug(fname):
    return fname.split("/")[-1].split(".sl")[0]

print(len(files))
files = [f for f in files if get_slug(f) not in used[f.split(":")[1].split(".model")[0]]]
print(len(files))

def get_stat(fname):
    lines = open(fname).readlines()
    try:
        return int(lines[3].split()[-1])
    except IndexError:
        return None

def amean(ys):
    return sum(ys)/len(ys)

import numpy as np
def gmean(a):
    return np.exp(np.sum(np.log(x) for x in a)/len(a))
    

x = []
y = []
labels = []

for f in files:
    print(f)
    fstat = get_stat(f)
    if fstat is None:
        continue
    slug = get_slug(f)
    if slug in forbidden:
        print("skip, forbidden")
        continue
    #random_files = glob.glob("random_results_may/" + slug + "*")
    random_files = glob.glob("results/*random*/" + slug + "*")
    
    sm = []
    for ff in random_files:
        sm += [get_stat(ff)]

    sm = [s for s in sm if s is not None]
    sm = [gmean(sm)]

    for s in sm:
        x.append(s)
        y.append(fstat)
        l = None
        tc = f.split("/")[-1]
        if "max" in tc:
            l = "max"
        elif "icfp" in tc:
            l = "icfp"
        elif "arr" in tc:
            l = "arrays"
        elif "hack" in tc:
            l = "hackers"
        labels.append(l)
    print(fstat, sorted(sm), l)

print("Global stats:")
dd = [xx/yy for (xx, yy) in zip(x, y)]
print("A:", amean(x)/amean(y))
print("G:", gmean(dd))

y = [xx/yy for (xx, yy) in zip(x, y)]
d = defaultdict(list)
for xx, yy, l in zip(x, y, labels):
    d[l].append((xx, yy))

for l in d:
    print(l)
    plt.plot([q[0] for q in d[l]], [q[1] for q in d[l]], 
            {
                "max": "ro",
                "icfp": "g.",
                "arrays": "b*",
                "hackers": "kv"
            }[l],
            label = l)
    dd = [yy for (xx, yy) in d[l]]
    print("A:", amean([xx for (xx, yy) in d[l]]) / amean([yy*xx for (xx, yy) in d[l]]))
    print("G:", gmean(dd))
plt.legend()
#plt.ylim(0, 5)
plt.grid()
plt.xscale("log")
plt.yscale("log")
plt.xlabel("Expressions visited in original EUSolver")
plt.ylabel("Ratio of expressions visited (original : modified)")

title = ""
if "greedy" in model:
    title = "Greedy"
else:
    title = "Stochastic"

if "global" in model:
    title += " global"
else:
    title += " local"

plt.title(title)

plt.xlim(10, 1e4)
plt.ylim(0.1, 10)
plt.savefig("charts/" + model.replace("*", "ALL") + ".pdf")
#plt.show()
