import re
import sys

input_file = sys.argv[1]

file_format = input_file.split('.')[-1]

labels = []
current_labels = []

trace_limit = 10

with open(input_file, 'r') as file:
    lines = file.readlines()

    state_pattern = re.compile(r'State \d+:')
    label_pattern = re.compile(r'/\\ (.*?) = (.*)')

    cur_state = []
    for line in lines:
        if "Error: Invariant" in line:
            if current_labels:
                labels.append(current_labels)
                current_labels = []
        elif state_pattern.match(line):
            if cur_state:
                current_labels.append('\\n'.join(cur_state))
                cur_state = []
        else:
            match = label_pattern.match(line.strip())
            if match:
                key, value = match.groups()
                cur_state.append(f"{key} = {value}")

        if len(labels) >= trace_limit:
            break

    if current_labels:
        labels.append(current_labels)

def print_trace_pair(labels):
    tables = [{},{}]
    progs = ['', '']

    clock_cycle = 0
    for label in labels:
        lines = label.split('\\n')
        for line in lines:
            for i in range(2):
                if 'Prog' + str(i + 1) in line:
                    progs[i] = line.split('=')[1].strip()
                    continue
                if 'StageIF_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'idx\s*\|->\s*(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for idx in idx_matches:
                        tables[i][(int(idx), clock_cycle)] = 'IF'
                if 'StageID_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'(\{|, )(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for _, idx in idx_matches:
                        tables[i][(int(idx), clock_cycle)] = 'ID'
                if 'StageRS_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'(\{|, )(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for _, idx in idx_matches:
                        tables[i][(int(idx), clock_cycle)] = 'rs'
                if 'StageFU_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'(\w+)\s*\|->\s*\{\[idx\s*\|->\s*(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for fu, idx in idx_matches:
                        tables[i][(int(idx), clock_cycle)] = fu
                if 'ROB_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'(\<<|, )(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for _, idx in idx_matches:
                        if (int(idx), clock_cycle) not in tables[i]:
                            tables[i][(int(idx), clock_cycle)] = 'rob'
                if 'StageCOM_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'(\{|, )(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for _, idx in idx_matches:
                        tables[i][(int(idx), clock_cycle)] = 'COM'
                if 'Squashed_' + str(i + 1) in line:
                    idx_pattern = re.compile(r'(\{|, )(\d+)')
                    idx_matches = idx_pattern.findall(line)
                    for _, idx in idx_matches:
                        if (int(idx), clock_cycle - 1) in tables[i] and tables[i][(int(idx), clock_cycle - 1)] != '#squashed':
                            tables[i][(int(idx), clock_cycle)] = '#squashed'
        clock_cycle += 1

    def print_table(table):
        # Determine the maximum index and clock cycle for table dimensions
        max_idx = max(idx for idx, _ in table.keys())
        max_cycle = max(cycle for _, cycle in table.keys())

        # Print the header row
        header = "" + "".join(f"\t{cycle}" for cycle in range(1, max_cycle + 1))
        print(header)

        # Print each row
        for idx in range(1, max_idx + 1):
            row = f"{idx}"
            for cycle in range(1, max_cycle + 1):
                row += f"\t{table.get((idx, cycle), '')}"
            print(row)
        print('----' + '----' * max_cycle)

    def print_deps(prog):
        prog_pattern = re.compile(r'<<\[(.*?)\]>>')
        match = prog_pattern.search(prog)
        if match:
            dep_pattern = re.compile(r'idx\s*\|->\s*(\d+).*?data_deps\s*\|->\s*\{(.*?)\}')
            dep_matches = dep_pattern.findall(prog)
            for idx, deps in dep_matches:
                if deps.strip():
                    for dep in deps.split(','):
                        print(f"{dep.strip()} -> {idx}")
        else:
            print("No valid program format found.")

    # Print the tables for both programs
    print_table(tables[0])
    print_table(tables[1])

    # Print the dependencies for both programs
    print_deps(progs[0])

for i in range(0, len(labels)):
    print()
    print("====" * 10 + f" Trace {i} " +  "====" * 10)
    print()
    print_trace_pair(labels[i])