#!/usr/bin/python

import os, subprocess, shlex, shutil, sys, time
from multiprocessing import Queue, Process, Manager, JoinableQueue

# A job list entry is a tuple consisting of the following
# 1. A list of strings that can be passed to subprocess.Popen for the executable and args
# 2. A string denoting the name of the log file
# 3. Another string denoting a header to print at the top of the log file

job_list = []

def print_usage():
    print('Usage: %s <job_list_filename> <log_directory_name> <num_concurrent_processes>' % sys.argv[0])

def process_entry_point(global_job_queue):
    while True:
        try:
            job = global_job_queue.get(True, 10)
        except:
            break

        with open(job[1], 'w') as job_out_file, open (job[1] + '.err', 'w') as job_err_file:
            job_out_file.write('@@@@@@@%s@@@@@@@\n\n' % job[2]);
            job_err_file.write('@@@@@@@%s@@@@@@@\n\n' % job[2]);
            job_out_file.write('$*$*$*$*/%s$*$*$*$' % ' '.join(job[0]))
            job_out_file.flush();
            job_err_file.flush();
            job_process = subprocess.Popen(job[0], stdout=job_out_file, stderr=job_err_file)
            (outdata, errdata) = job_process.communicate()

# I expect the following arguments:
# 1. A file name, which I can open and eval to get my job list
# 2. A log directory name where I write all logs
# 3. Number of concurrent processes to run

if len(sys.argv) < 4:
    print_usage()
    sys.exit(1)

with open(sys.argv[1], 'r') as job_file:
    job_list = eval(job_file.read())

log_directory_name = sys.argv[2]
num_concurrent_processes = int(sys.argv[3])

try:
    shutil.rmtree(log_directory_name)
except OSError as exc:
    if exc.errno != 2:
        raise exc

os.mkdir(log_directory_name)


# make a queue and push all jobs into it
mp_manager = Manager()
job_queue = mp_manager.Queue()

for job in job_list:
    job_queue.put((job[0], '%s/%s' % (log_directory_name, job[1]), job[2]))

# start the worker processes
worker_processes = []
for process_id in range(num_concurrent_processes):
    worker_processes.append(Process(target=process_entry_point, args=(job_queue,)))

print('Starting %d worker processes, with %d jobs to run' % (num_concurrent_processes, len(job_list)))
sys.stdout.flush()
begin_time = time.clock()
for worker_process in worker_processes:
    worker_process.start()

for worker_process in worker_processes:
    worker_process.join()
end_time = time.clock()
print('Completed %d jobs in %f seconds, with %d worker processes' % (len(job_list), end_time - begin_time, num_concurrent_processes))
