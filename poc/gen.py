

top = [
    (0.75, ("+", )),
    (0.25, ("-", )),
]

bot = [
    (0.7, ("x", )),
    (0.2, ("0", )),
    (0.1, ("1", )),
]

arr = []
for t in top:
    for b1 in bot:
        for b2 in bot:
            arr.append((t[0]*b1[0]*b2[0], t[1]+ b1[1]+ b2[1]))

arr.sort()
for a in arr[::-1]:
    print a

print "---"


def atomic_gen_factory(bot):
    def atomic():
        for b in bot:
            yield (b[0], b[1])
    return atomic


def combine(aa, bb):
    return (aa[0]*bb[0], aa[1]+bb[1])

def gen_combine(a, gen):
    for g in gen:
        yield combine(a, g)

import heapq
def gen_alternatives(xs):
    scores = []
    for i, x in enumerate(xs):
        try:
            score, tup = next(x)
            heapq.heappush(scores, (-score, i, tup))
        except StopIteration:
            pass

    while scores:
        score, i, tup = heapq.heappop(scores)
        score = -score
        try:
            nscore, ntup = next(xs[i])
            heapq.heappush(scores, (-nscore, i, ntup))
        except StopIteration:
            pass
        yield (score, tup)


def gen_sorted_alternatives(xs_gen):
    scores = []
    xs = []
    xs.append(next(xs_gen))

    for i, x in enumerate(xs):
        try:
            score, tup = next(x)
            heapq.heappush(scores, (-score, i, tup))
        except StopIteration:
            pass

    while scores:
        score, i, tup = heapq.heappop(scores)
        score = -score
        try:
            nscore, ntup = next(xs[i])
            heapq.heappush(scores, (-nscore, i, ntup))
        except StopIteration:
            pass
        yield (score, tup)
        if i == len(xs) - 1:
            try:
                xs.append(next(xs_gen))
                x = xs[-1]
                i = len(xs) - 1
                score, tup = next(x)
                heapq.heappush(scores, (-score, i, tup))
            except StopIteration:
                pass



def gen_cart(factories):
    if len(factories) == 0:
        yield (1.0, ())
    else:
        first = list(factories[0]())
        rest = factories[1:]
        generators = [gen_cart(rest) for f in first]
        for f in gen_sorted_alternatives(
            gen_combine(fir, gen) for fir, gen in zip(first, generators)):
            yield f


for f in gen_cart([
        atomic_gen_factory(bot),
        atomic_gen_factory(bot),
        ]):
    print f

print "xasx"

arr2 = []
for f in gen_alternatives([
    gen_combine(fir, 
        gen_cart([
        atomic_gen_factory(bot),
        atomic_gen_factory(bot),
        ])
    ) for fir in top]):
        arr2.append(f)
        print f

print "--- comparison ---"
for a, b in zip(arr[::-1], arr2):
    print a[0], b[0]
