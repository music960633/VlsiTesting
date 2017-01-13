sample_cases=("c17" "c432" "c499" "c880" "c1355" "c1908" "c2670" "c3540" "c5315" "c6288" "c7552")
benchmark_cases=("adder" "bar" "dec" "max" "sin" "multi")
N=10
M=5

for i in $(seq 0 $N); do
  echo ""
  echo "running ${sample_cases[$i]}"
  time ./atpg -ndet 8 -compression -tdfatpg ../sample_circuits/${sample_cases[$i]}.ckt > pat/${sample_cases[$i]}.pat
  ../ref/golden_tdfsim -ndet 8 -tdfsim pat/${sample_cases[$i]}.pat ../sample_circuits/${sample_cases[$i]}.ckt
done

for i in $(seq 0 $M); do
  echo ""
  echo "running ${benchmark_cases[$i]}"
  time ./atpg -ndet 8 -compression -tdfatpg ../benchmarks/${benchmark_cases[$i]}.ckt > pat/${benchmark_cases[$i]}.pat
  ../ref/golden_tdfsim -ndet 8 -tdfsim pat/${benchmark_cases[$i]}.pat ../benchmarks/${benchmark_cases[$i]}.ckt
done


