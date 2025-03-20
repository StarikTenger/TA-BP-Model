import re
import sys

input_file = sys.argv[1]
output_file = sys.argv[2]

with open(input_file, 'r') as file:
    lines = file.readlines()

label_pattern = re.compile(r'label\s*=\s*"(.*?)"')

labels = []

for line in lines:
    match = label_pattern.search(line)
    if match:
        label = match.group(1)
        if label:
            labels.append(label)

table = {}

clock_cycle = 0
for label in labels:
    lines = label.split('\\n')
    for line in lines:
        if 'StageIF' in line:
            idx_pattern = re.compile(r'idx\s*\|->\s*(\d+)')
            idx_matches = idx_pattern.findall(line)
            for idx in idx_matches:
                table[(int(idx), clock_cycle)] = 'IF'
        if 'StageID' in line:
            idx_pattern = re.compile(r'idx\s*\|->\s*(\d+)')
            idx_matches = idx_pattern.findall(line)
            for idx in idx_matches:
                table[(int(idx), clock_cycle)] = 'ID'
        if 'StageRS' in line:
            idx_pattern = re.compile(r'\d+')
            idx_matches = idx_pattern.findall(line)
            for idx in idx_matches:
                table[(int(idx), clock_cycle)] = 'RS'
        if 'StageFU' in line:
            idx_pattern = re.compile(r'(\w+)\s*\|->\s*\{\[idx\s*\|->\s*(\d+)')
            idx_matches = idx_pattern.findall(line)
            for fu, idx in idx_matches:
                table[(int(idx), clock_cycle)] = fu
    clock_cycle += 1

# Determine the maximum index and clock cycle for table dimensions
max_idx = max(idx for idx, _ in table.keys())
max_cycle = max(cycle for _, cycle in table.keys())

# Print the header row
header = "Idx/Cycle" + "".join(f"\t{cycle}" for cycle in range(max_cycle + 1))
print(header)

# Print each row
for idx in range(max_idx + 1):
    row = f"{idx}"
    for cycle in range(max_cycle + 1):
        row += f"\t{table.get((idx, cycle), '')}"
    print(row)
