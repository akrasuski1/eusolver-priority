import sys
import random
import math
from collections import defaultdict


name = sys.argv[1]

situations = {}

for line in open("models/" + name + ".situations"):
    if "SITUATION" in line:
        situation = int(line.split()[-1])
        situations[situation] = defaultdict(int)
    elif "from" in line:
        count = int(line.split()[0])
        what = line.split()[2]
        poss = tuple(line.split("(")[1].split(")")[0].split(", "))
        situations[situation][(what, poss)] = count
    elif "EOL" in line:
        pass


def train(tests):
    def pretty(weights):
        s = "{"
        ls = list(weights.keys())
        ls.sort(key = lambda x: weights[x], reverse = True)
        s += ", ".join(w + ": %.2e" % weights[w] for w in ls)
        s += "}"
        return s

    weights = {}
    for x, y in tests:
        assert x in y
        for c in y:
            weights[c] = 1.0

    for c in weights:
        weights[c] /= len(weights)

    speed = 1e-5
    prev_score = -float("inf")
    while speed > 1e-12:
        random.shuffle(tests)
        score = 0
        for x, y in tests:
            score += math.log(weights[x]) - math.log(sum(weights[c] for c in y))

            orig_sum = sum(weights[c] for c in y)
            delta_x = (orig_sum - weights[x]) / (weights[x] * orig_sum)
            delta_y = -1.0 / orig_sum

            delta_x *= speed
            delta_y *= speed

            weights[x] += delta_x
            weights[x] = max(1e-9, weights[x])
            for c in y:
                if c == x: continue
                weights[c] = max(1e-9, weights[c] + delta_y)

            final_sum = sum(weights[c] for c in y)
            for c in y:
                weights[c] *= orig_sum / final_sum
                weights[c] = max(1e-9, weights[c])

        print("score: %0.9f speed: %0.3e" % (score, speed), pretty(weights))

        if score < prev_score + 1e-6:
            speed /= 2

        prev_score = score

    return weights


for how in ["per_size", "global"]:
    print("Modelling", how)
    if how == "per_size":
        result = {}
        for sz in situations:
            tests = []
            for what, poss in situations[sz]:
                count = situations[sz][(what, poss)]
                tests += [(what, poss)] * count

            weights = train(tests)
            result[sz] = weights
    else:
        tests = []
        for sz in situations:
            for what, poss in situations[sz]:
                count = situations[sz][(what, poss)]
                tests += [(what, poss)] * count

        result = train(tests)

    open("models/" + name + ".model." + how, "w").write(str(result))
