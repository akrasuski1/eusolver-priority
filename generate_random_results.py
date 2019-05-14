import glob
import subprocess
import random
import sys
import time


def run_on(fname, timeout=60):
    try:
        s = subprocess.check_output(["timeout", str(timeout), "./eusolver", fname], env={"EUSOLVER_SETTINGS":"algo=random"})
    except subprocess.CalledProcessError:
        print("  timed out")
        s = b""
    s = s.split(b"++++++++++++ fin")[-1]
    return s

files = []
files.append(glob.glob("benchmarks/icfp/*.sl"))
files.append(glob.glob("benchmarks/icfp_generated/*.sl"))
files.append(glob.glob("benchmarks/max/*.sl"))
files.append(glob.glob("benchmarks_se/arrays/array_search*.sl"))
files.append(glob.glob("benchmarks_custom/hackers_delight/*.sl"))

if len(sys.argv) > 1:
    files = sys.argv[1:]

while True:
    f = random.choice(files)
    f = random.choice(f)
    print(f)
    t = time.time()
    s = run_on(f)
    t = time.time() - t

    open("random_results_may/%s_%09d" % (
        f.replace("/", "@"), random.randint(1, 10**9-1)), "wb").write(b"%f" % t + s)

