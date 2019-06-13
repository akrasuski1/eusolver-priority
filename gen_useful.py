import glob
from collections import defaultdict


files = glob.glob("results/*/*")
slug_dirs = defaultdict(list)

for f in files:
    with open(f) as ff:
        lines = ff.readlines()
        ok = len(lines) == 7

    if ok:
        d = f.split("/")[1]
        slug = f.split("/")[-1].split(".sl")[0]
        slug_dirs[slug].append(d)

lengths = []
forbidden = []
for k in slug_dirs:
    print(k, len(slug_dirs[k]))
    lengths.append(len(slug_dirs[k]))
    if len(slug_dirs[k]) < 220:
        forbidden.append(k)

print(sorted(lengths))
print(forbidden)
open("forbidden", "w").write(str(forbidden))
