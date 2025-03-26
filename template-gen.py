import re
import sys

filename = sys.argv[1]

instructions = []

with open(filename, "r") as file:
    for line in file:
        match = re.match(r"^( *)(\w+).*?\[([\d|]+)\]", line)
        if match:
            depth = len(match.group(1))
            type = match.group(2)
            lats = []
            if match.group(3):
                lats = list(map(int, match.group(3).split("|")))
            instructions.append({
                "depth": depth,
                "type": type,
                "lats": lats
            })

branch_stack = []

idx = 0
for instruction in instructions:
    idx += 1
    while branch_stack and branch_stack[-1][1] >= instruction["depth"]:
        branch_stack.pop()
    if instruction["type"].startswith("BR"):
        branch_stack.append((instructions.index(instruction), instruction["depth"]))
    spec_of = ", ".join(str(idx + 1) for idx, _ in branch_stack)
    lat_fu = ", ".join(map(str, instruction['lats']))
    print(
        (f"[idx |-> {idx}, "
        f"\ttype |-> \"{instruction['type']}\", "
        f"\tdata_deps |-> {{}}, "
        f"\tspec_of |-> {{{spec_of}}}, "
        f"\tLatIF |-> {{1}}, "
        f"\tLatFU |-> {{{lat_fu}}}]"
        + ("," if idx < len(instructions) else "")) \
        .expandtabs(8)
    )

