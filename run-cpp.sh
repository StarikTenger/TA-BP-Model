echo "======== Building C++ program ========"

cd cpp_version
mkdir -p build
cd build
cmake ..
make

echo
echo "======== Running the model ========"

cd ..
./build/pipeline_model $1
cd ..
python3 diagram-diag.py cpp_version/out2.tmp >tmp/out.trd
echo "------------------------------------" >>tmp/out.trd
python3 diagram-diag.py cpp_version/out1.tmp >>tmp/out.trd