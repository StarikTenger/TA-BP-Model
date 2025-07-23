input=$1

cat $input >event_table.tmp
./cpp_version/build/event_table $input >>event_table.tmp
python3 EventDiagram.py <event_table.tmp
# rm event_table.tmp