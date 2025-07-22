input=$1

cat $input >tmp/event_table.tmp
./cpp_version/build/event_table $input >>tmp/event_table.tmp

python3 drawio-diagram.py --graph tmp/event_table.tmp --outfile tmp/test.drawio tmp/input.instr_compare.trd
drawio -x tmp/test.drawio -s 2 -f png
