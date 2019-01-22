import random
import math

real_weights = {
    "-": 0.1,
    "/": 0.2,
    "*": 0.3,
    "+": 0.4,
}

cases = ["-/*", "-+"]
#cases = ["-+"]

samples = []

for i in range(1000):
    case = random.choice(cases)
    weights = {}
    for c in case:
        weights[c] = real_weights[c]
    s = sum(weights.values())
    for c in case:
        weights[c] /= s
    p = random.random()
    res = None
    for k in weights:
        v = weights[k]
        p -= v
        if p < 0:
            res = k
            break
    samples.append((case, res))

predicted = {
    "-": 0.25,
    "/": 0.25,
    "*": 0.25,
    "+": 0.25,
}

for i in range(100):
    random.shuffle(samples)
    loss = 0
    for case, res in samples:
        loss += sum(math.log(predicted[c]) for c in case if c != res)
        loss += math.log(1-predicted[res])

        step = 1e-3
        s1 = sum(predicted[c] for c in case)
        predicted[res] = s1*(1-(1-predicted[res]/s1)/(1+step))
        for c in case:
            if c != res:
                predicted[c] /= (1+step)
                pass
        s2 = sum(predicted[c] for c in case)
        for p in case:
            predicted[p] *= s1/s2

    for p in predicted:
        print p, predicted[p]
    print loss
    print

