import glob
import subprocess
import random
import sys


def run_on(fname, timeout=60):
    try:
        s = subprocess.check_output(["timeout", str(timeout), "./eusolver", fname])
    except subprocess.CalledProcessError:
        print("  timed out")
        s = b""
    s = s.split(b"++++++++++++")[-1]
    return s


files = glob.glob("benchmarks/icfp/*.sl")
files += glob.glob("benchmarks/icfp_generated/*.sl")
files += glob.glob("benchmarks/max/*.sl")
files += glob.glob("benchmarks_se/arrays/*.sl")
files += glob.glob("benchmarks_custom/hackers_delight/*.sl")

if len(sys.argv) > 1:
    files = sys.argv[1:]

while True:
    f = random.choice(files)
    print(f)
    s = run_on(f)
    if b"FINAL_SOLUTION" not in s:
        continue

    open("random_results/%s_%09d" % (
        f.replace("/", "@"), random.randint(1, 10**9-1)), "wb").write(s)

