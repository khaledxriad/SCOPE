test:
	python3 -m unittest discover -s tests

experiments:
	python3 experiments.py            # rewrites results/compiler_results.json (about 20 s)

prototype:
	python3 bench_proto.py            # rewrites results/proto_results.json (several minutes)
