# EUsolver Prority
This repository adds grammar prioritization support for EUsolver.

Original code by Rajeev Alur, Arjun Radhakrishna, and Abhishek Udupa written up at
https://www.cis.upenn.edu/~alur/Tacas17.pdf


## Changes

* There is a lot of cosmetic changes (think adding comments or logging code).
* Benchmark folders have been added (`benchmarks`, `benchmarks_se`, `benchmarks_custom`).
* Charts folder.
* Trained models (`models` folder).
* `src/enumerators/enumerators.py` - the place where novel prioritization algorithms have been
implemented (many heleper functions added, some changes to existing generators and
a new `AlternativesExpressionTemplateGenerator`).
* `fix_hackers.py` - script for fixing Hacker's Delight benchmarks (mainly adding `if0`)
* `generate_random_results.py` - runs randomized EUSolver many times on all instances 
to create dataset of solutions.
* `summarize.py`, `parse_raw_train.py` - scripts for creating intermediate model data representation.
* `learn_from_random.py`, `train.py` - scripts for training models (`train.py` actually used, the other is an old version)
* `generate_trained_results.py` - runs modified EUSolver, with given model and algorithm, on all instances once.
* `analyze.py` - script for analyzing final results
* `gen_charts.sh` - wrapper for `analyze.py`
* `gen_tables.py` - generates (nonfinal version of) result summary LaTeX tables

