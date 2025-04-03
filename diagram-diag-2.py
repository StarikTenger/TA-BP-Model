import re
import sys

input_file = sys.argv[1]

file_format = input_file.split('.')[-1]

labels = []

if file_format == 'dot':
    with open(input_file, 'r') as file:
        lines = file.readlines()

    label_pattern = re.compile(r'label\s*=\s*"(.*?)"')

    for line in lines:
        match = label_pattern.search(line)
        if match:
            label = match.group(1)
            if label:
                labels.append(label)

elif file_format == 'txt':
    with open(input_file, 'r') as file:
        lines = file.readlines()

        state_pattern = re.compile(r'State \d+:')
        label_pattern = re.compile(r'/\\ (.*?) = (.*)')

        current_label = []
        for line in lines:
            if state_pattern.match(line):
                if current_label:
                    labels.append('\\n'.join(current_label))
                    current_label = []
            else:
                match = label_pattern.match(line.strip())
                if match:
                    key, value = match.groups()
                    current_label.append(f"{key} |-> {value}")
        if current_label:
            labels.append('\\n'.join(current_label))

tables = [{},{}]

clock_cycle = 0
for label in labels:
    lines = label.split('\\n')
    for line in lines:
        for i in range(2):
            if 'Prog1' in line or 'Prog2' in line:
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
                idx_pattern = re.compile(r'(\{|, )(\d+)')
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

# Print the tables for both programs
print_table(tables[0])
print_table(tables[1])