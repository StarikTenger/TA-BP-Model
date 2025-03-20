import re
import sys

def process_dot_file(input_file, output_file):
    with open(input_file, 'r') as file:
        lines = file.readlines()

    label_pattern = re.compile(r'label\s*=\s*"(.*?)"')



    def reorder_label(label):
        order = ['PC', 'StageIF', 'StageID', 'StageRS', 'StageFU', 'ROB', 'StageCOM']
        lines = label.split('\\n')
        ordered_lines = sorted(lines, key=lambda x: order.index(next((o for o in order if o in x), len(order))))
        return '\\n'.join(ordered_lines)
    
    def substitude_label(label):
        label = label \
            .replace('<<', '⟨')     \
            .replace('>>', '⟩')     \
            .replace('|->', '↦')    \
            .replace('=', '\t=')    \
            .replace('\\n', '\l')
        return label + "\l"

    with open(output_file, 'w') as file:
        for line in lines:
            match = label_pattern.search(line)
            if match:
                label = match.group(1)
                if label:
                    reordered_label = substitude_label(reorder_label(label))
                    line = line.replace(label, reordered_label)
            file.write(line)

# Example usage
if len(sys.argv) != 3:
    print("Usage: python pretty-graph.py <input_file> <output_file>")
    sys.exit(1)

input_file = sys.argv[1]
output_file = sys.argv[2]
process_dot_file(input_file, output_file)