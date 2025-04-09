cd cpp_version
g++ -std=c++20 -o main main.cpp
./main >out.tmp
cd ..
python3 diagram-diag.py cpp_version/out.tmp >out.trd