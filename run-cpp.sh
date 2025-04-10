cd cpp_version
g++ -std=c++20 -o main main.cpp
./main ../tmp/input.instr
cd ..
python3 diagram-diag.py cpp_version/out2.tmp >out.trd
echo "------------------------------------" >>out.trd
python3 diagram-diag.py cpp_version/out1.tmp >>out.trd