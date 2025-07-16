import re
import sys
import string

if len(sys.argv) < 2:
	print("Usage: python input-rewrite.py <filename>")
	sys.exit(1)

filename = sys.argv[1]

instructions = []
branch_variations = set()

line_count = 0
with open(filename, "r") as file:
    for line in file:
        match = re.match(r"^([ \t]*)(\w+)(?:\s+#(\w+))?(?:\s+(@[\w]+(?:\s+@[\w]+)*))?.*\[([\d|]+)\]\s*(\*?)", line)
        if match:
            indent = match.group(1)
            depth = indent.count('\t') + indent.count(' ') // 4
            type = match.group(2)
            label = match.group(3) if match.group(3) else None
            deps = [dep.lstrip('@') for dep in match.group(4).split()] if match.group(4) else []
            lats = []
            br_var = match.group(6) == '*'

            if match.group(5):
                lats = list(map(int, match.group(5).split("|")))
                lats.reverse()

                instructions.append({
                "depth": depth,
                "type": type,
                "label": label,
                "deps": deps,
                "lats": lats,
                "br_var": br_var
                })

            if match.group(6):
                branch_variations.add(line_count)
    
            line_count += 1


max_depth = max(instr["depth"] for instr in instructions)
print("\\begin{tabular}{" + "r" * (max_depth + 1) + "|" + "c" * (3) + "}")

# Header row
header =  [""] + [f"" for i in range(max_depth)] + ["Res", "Dep.", "Lat."]
print(" & ".join(header) + " \\\\ \\hline")


def idx_to_alpha(i):
    letters = ""
    i -= 1
    while True:
        letters = chr(ord('A') + (i % 26)) + letters
        i = i // 26 - 1
        if i < 0:
            break
    return letters

for idx, instruction in enumerate(instructions, start=1):
    label = "\\textit{" + ("*" if instruction["br_var"] else "") + idx_to_alpha(idx) + ":}"
    data_deps = {j for dep in instruction["deps"] if dep for j, instr in enumerate(instructions, start=1) if instr["label"] == dep}
    deps_alpha = [idx_to_alpha(j) for j in sorted(data_deps)] if data_deps else []
    deps_str = "" if len(deps_alpha) == 0 else "$\{" + ", ".join(deps_alpha) + "\}$"
    lats_str = "$" + "|".join(map(str, instruction['lats'])) + "$"
    # Prepare row: label, skip depth columns, then type, then fill, then deps, lats
    row = [] + [""] * instruction["depth"]
    row += [label]
    while len(row) < max_depth + 1:
        row.append("")
    row += [instruction["type"]]
    row += [deps_str, lats_str]
    print(" & ".join(row) + " \\\\")
print("\\end{tabular}")
