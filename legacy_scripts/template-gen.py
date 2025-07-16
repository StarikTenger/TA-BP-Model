# Generate TLA configuration from input file

import re
import sys
import argparse

parser = argparse.ArgumentParser(description="Generate TLA configuration from input file")
parser.add_argument("filename", help="Input file name")
parser.add_argument("--base", default=False, action="store_true", help="Enable base template generation")
parser.add_argument("--alt", default=False, action="store_true", help="Enable alternative template generation")
parser.add_argument("--name", default="Test", help="Specify benchmark name")
parser.add_argument("--time", type=int, default=0, help="Specify time bound")

args = parser.parse_args()

filename = args.filename
gen_base_template = args.base
gen_alt_template = args.alt
bench_name = args.name
time_bound = args.time

instructions = []
branch_variations = set()

line_count = 0
with open(filename, "r") as file:
    for line in file:
        match = re.match(r"^( *)(\w+)(?:\s+#(\w+))?(?:\s+@([\w,]+))?.*\[([\d|]+)\]\s*(\*?)", line)
        if match:
            depth = len(match.group(1))
            type = match.group(2)
            label = match.group(3) if match.group(3) else None
            deps = match.group(4).split(",") if match.group(4) else []
            lats = []

            if match.group(5):
                lats = list(map(int, match.group(5).split("|")))

                if gen_base_template:
                    lats = lats[0:1]
                elif gen_alt_template and len(lats) > 1:
                    lats = lats[1:2]

                instructions.append({
                "depth": depth,
                "type": type,
                "label": label,
                "deps": deps,
                "lats": lats
                })

            if match.group(6):
                branch_variations.add(line_count)

            line_count += 1


print(f"---- MODULE {bench_name} ----")
print("EXTENDS TLC, Pipeline")
print("const_prog == ⟨")

branch_stack = []
idx = 0
for instruction in instructions:
    idx += 1
    while branch_stack and branch_stack[-1][1] >= instruction["depth"]:
        branch_stack.pop()
    spec_of = ", ".join(str(idx + 1) for idx, _ in branch_stack)
    branch_stack.append((instructions.index(instruction), instruction["depth"]))
    lat_fu = ", ".join(map(str, instruction['lats']))
    data_deps = {idx for dep in instruction["deps"] if dep for idx, instr in enumerate(instructions, start=1) if instr["label"] == dep}
    data_deps = data_deps if data_deps else {}
    br_pred = "{}"
    if gen_alt_template:
        if (idx - 1) in branch_variations:
            br_pred = "{TRUE}"
        else:
            br_pred = "{FALSE}"
    print(
        (f"[idx |-> {idx}, "
        f"\ttype |-> \"{instruction['type']}\", "
        f"\tdata_deps |-> {data_deps}, "
        f"\tspec_of |-> {{{spec_of}}}, "
        f"\tLatIF |-> {{1}}, "
        f"\tbr_pred |-> {br_pred}, "
        f"\tLatFU |-> {{{lat_fu}}}]"
        + ("," if idx < len(instructions) else "")) \
        .expandtabs(4)
    )

print("⟩")
print("const_superscalar == 1")
if (gen_base_template):
    print("const_BranchDivergence == FALSE")
else:
    print("const_BranchDivergence == TRUE")
    
if time_bound > 0:
    print(f"TimeBounded == ¬TimeExceed({time_bound})")
else:
    print("TimeBounded == TRUE")

print("====")