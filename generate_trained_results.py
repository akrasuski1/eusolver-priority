import glob
import os
import subprocess
import random
import sys
import time


def run_on(fname, settings, timeout=60):
    try:
        s = subprocess.check_output(["timeout", str(timeout), "./eusolver", fname], env={"EUSOLVER_SETTINGS": settings})
    except subprocess.CalledProcessError:
        print("  timed out")
        s = b""
    s = s.split(b"++++++++++++ fin")[-1]
    return s

files = []
files += glob.glob("benchmarks/icfp/*.sl")
files += glob.glob("benchmarks/icfp_generated/*.sl")
files += glob.glob("benchmarks/max/*.sl")
files += glob.glob("benchmarks_se/arrays/array_search*.sl")
files += glob.glob("benchmarks_custom/hackers_delight/*.sl")

model = sys.argv[1]
algo = sys.argv[2]
name = algo + ":" + model

os.system("mkdir -p results/%s" % name)

for f in files:
    print(f)
    t = time.time()
    conflate = ""
    if ".global" in model:
        conflate = ",conflate_size"
    s = run_on(f, "algo=%s,weights=%s%s" % (algo, "models/%s" % model, conflate))
    t = time.time() - t

    open("results/%s/%s_%09d" % (name,
        f.replace("/", "@"), random.randint(1, 10**9-1)), "wb").write(b"%f" % t + s)

