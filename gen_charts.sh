
type=greedy
other=global
python3 analyze.py $type':random_*.model.'$other '*' > \
			 charts/$type:random_ALL.model.$other.log

for type in greedy stochastic
do 
	for other in global per_size
	do 
		python3 analyze.py $type':not_max.model.'$other '*' > \
                     charts/$type:not_max_ALL.model.$other.log
		python3 analyze.py $type':not_array.model.'$other '*' > \
                     charts/$type:not_array_ALL.model.$other.log
		python3 analyze.py $type':not_hackers.model.'$other '*' > \
                     charts/$type:not_hackers_ALL.model.$other.log
		python3 analyze.py $type':not_icfp.model.'$other '*' > \
                     charts/$type:not_icfp_ALL.model.$other.log

		python3 analyze.py $type':full_0.7_*.model.'$other '*' > \
                     charts/$type:full_0.7_ALL.model.$other.log
		python3 analyze.py $type':array_0.7_*.model.'$other '*' > \
                     charts/$type:array_0.7_ALL.model.$other.log
		python3 analyze.py $type':hackers_0.7_*.model.'$other '*' > \
                     charts/$type:hackers_0.7_ALL.model.$other.log
		python3 analyze.py $type':icfp_0.7_*.model.'$other '*' > \
                     charts/$type:icfp_0.7_ALL.model.$other.log
		python3 analyze.py $type':max_0.7_*.model.'$other '*' > \
                     charts/$type:max_0.7_ALL.model.$other.log
	done
done
