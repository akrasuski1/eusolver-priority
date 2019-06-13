import sys
import ast
import json

add = False
result = {}
for line in open(sys.argv[1]).readlines():
    if "SITUATION" in line:
        situation = ast.literal_eval(line.split(" ", 1)[1])
    elif "LEARNED" in line:
        add = True
        arr = []
    elif "EOL" in line:
        add = False
        result[situation] = arr
    elif add:
        kwd, flt = line[2:-1].rsplit(" ", 1)
        arr.append((kwd, float(flt)))

open(sys.argv[2], "w").write(str(result)+"\n")
