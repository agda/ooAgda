

Running the binary tree benchmark

For details, refer to:
https://benchmarksgame.alioth.debian.org/u64q/binarytrees.html

For the correct output with parameter/depth 10, check this file:
https://benchmarksgame.alioth.debian.org/download/binarytrees-output.txt

1. compile the agda code
cd ooAgda/FSCD17/src
agda -c examples/benchmarks/binaryTreeBenchmark.agda

2. time the agda code (ooAgda using IORefs/fast version):
cd ooAgda/FSCD17/src
time ./binaryTreeBenchmark 9
time ./binaryTreeBenchmark 10

3. time the ruby code
cd ooAgda/FSCD17/src
time ruby ./examples/benchmarks/binaryTreeBenchmarkRuby.rb 9
time ruby ./examples/benchmarks/binaryTreeBenchmarkRuby.rb 10
