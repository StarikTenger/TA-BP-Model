# Executes C++ framework on a given input and generates a drawio diagram from the output.
# Usage: ./drawio-diagram.sh <input_file>

input=$1
diagram_file=$input".instr_compare.trd"

mkdir -p tmp
./cpp_version/build/compare_traces $input >$diagram_file
python3 drawio-diagram.py --outfile tmp/test.drawio $diagram_file
drawio -x tmp/test.drawio -s 2 -f png
