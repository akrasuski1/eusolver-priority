import sys


for fname in sys.argv[1:]:
    print fname
    lines = open(fname).readlines()
    newlines = []
    notyet = True
    for line in lines:
        newlines.append(line)
        if "set-logic" in line:
            newlines.append("(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))\n")
        if notyet and "Start" in line:
            newlines.append("(if0 Start Start Start)\n")
            notyet = False
    open(fname, "w").write("".join(newlines))



