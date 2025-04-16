cd cpp_version
g++ -std=c++20 -o main main.cpp
./main $1
cd ..
python3 diagram-diag.py cpp_version/out2.tmp >tmp/out.trd
echo "------------------------------------" >>tmp/out.trd
python3 diagram-diag.py cpp_version/out1.tmp >>tmp/out.trd