



def parse_file(fname):
    s = open(fname).read()
    s = s.split("Global stats")[1]
    s = s.splitlines()
    res = {}
    res["Global"] = float(s[2].split()[1])
    for i in range(3, len(s), 3):
        res[s[i].strip()] = float(s[2+i].split()[1])
    return res


import numpy as np
def gmean(a):
    return np.exp(np.sum(np.log(x) for x in a)/len(a))

def get_table(slug):
    fnames = []
    for g in ["greedy", "stochastic"]:
        for f in ["per_size", "global"]:
            fnames.append("charts/%s:%s.model.%s.log" % (g, slug, f))

    results = []
    for f in fnames:
        results.append(parse_file(f))

    keys = sorted(results[0].keys())
    keys = keys[1:] + keys[:1]

    print "\n\n===%s===\n" % slug
    print "\\begin{tabular}{|c|c|c|c|c|}"
    print "\\hline"
    print "Dataset & Greedy local & Greedy global & Stochastic local & Stochastic global \\\\ \hline"
    for key in keys[:-1]:
        if key == "Global":
            print "\\hline"
        print key,
        for r in results:
            print "& %.3f" % r[key],
        print "\\\\"

    print "\\hline"
    print "Gmean",
    for r in results:
        g = gmean([r[key] for key in keys[:-1]])
        print "& %.3f" % g,

    print "\\\\\\hline"
    print "\\end{tabular}"






get_table("full_0.7_ALL")
get_table("array_0.7_ALL")
get_table("hackers_0.7_ALL")
get_table("icfp_0.7_ALL")
get_table("max_0.7_ALL")

get_table("not_array_ALL")
get_table("not_hackers_ALL")
get_table("not_icfp_ALL")
get_table("not_max_ALL")
