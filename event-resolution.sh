input="tmp/input.instr"

./cpp_version/build/event_table $input >event_table.tmp
python3 EventDiagram.py <event_table.tmp