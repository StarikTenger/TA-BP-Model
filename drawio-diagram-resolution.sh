# Executes C++ framework on a given input and generates a drawio diagram from the output.
# Additionally runs a resolution procedure from which restores the causality graph.
# Usage: ./drawio-diagram-resolution.sh <input_file>

if [ $# -ne 1 ]; then
    echo "Usage: $0 <input_file>"
    exit 1
fi

input=$1
table_file=$input".event_table"
diagram_file=$input".instr_compare.trd"


cat $input >$table_file
echo >>$table_file
echo >>$table_file
./cpp_version/build/compare_traces $input >$diagram_file
./cpp_version/build/event_table $input >>$table_file
python3 drawio-diagram.py --graph $table_file --outfile $input.drawio $diagram_file
drawio -x $input.drawio -s 2 -f png
