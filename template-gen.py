import re
import sys
import argparse

parser = argparse.ArgumentParser(description="Generate TLA configuration from input file")
parser.add_argument("filename", help="Input file name")
parser.add_argument("--base", default=False, action="store_true", help="Enable base template generation")
parser.add_argument("--name", default="Test", help="Specify benchmark name")
parser.add_argument("--time", type=int, default=0, help="Specify time bound")

args = parser.parse_args()

filename = args.filename
gen_base_template = args.base
bench_name = args.name
time_bound = args.time

instructions = []

with open(filename, "r") as file:
    for line in file:
        match = re.match(r"^( *)(\w+)(?:\s+#(\w+))?(?:\s+@([\w,]+))?.*\[([\d|]+)\]", line)
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

                instructions.append({
                "depth": depth,
                "type": type,
                "label": label,
                "deps": deps,
                "lats": lats
                })


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
    if instruction["type"].startswith("BR"):
        branch_stack.append((instructions.index(instruction), instruction["depth"]))
    lat_fu = ", ".join(map(str, instruction['lats']))
    data_deps = {idx for dep in instruction["deps"] if dep for idx, instr in enumerate(instructions, start=1) if instr["label"] == dep}
    data_deps = data_deps if data_deps else {}
    print(
        (f"[idx |-> {idx}, "
        f"\ttype |-> \"{instruction['type']}\", "
        f"\tdata_deps |-> {data_deps}, "
        f"\tspec_of |-> {{{spec_of}}}, "
        f"\tLatIF |-> {{1}}, "
        f"\tLatFU |-> {{{lat_fu}}}]"
        + ("," if idx < len(instructions) else "")) \
        .expandtabs(8)
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