import drawpyo
import os

file = drawpyo.File()
file.file_path = r"./"
file.file_name = "test.drawio"
# Add a page
page = drawpyo.Page(file=file)

def parse_table_and_deps_from_file(filepath):
    table = []
    deps = []
    with open(filepath, 'r') as f:
        lines = [line.rstrip('\n') for line in f if line.strip()]
    if not lines:
        return table, deps

    # Split table and deps sections
    table_lines = []
    deps_lines = []
    in_deps = False
    for line in lines:
        if line.strip().startswith("Deps:"):
            in_deps = True
            continue
        if in_deps:
            deps_lines.append(line)
        else:
            table_lines.append(line)

    # Parse table
    if table_lines:
        first_line = table_lines[0]
        if all(part.isdigit() for part in first_line.split()):
            table_lines = table_lines[1:]
        for line in table_lines:
            parts = line.split('\t')
            if parts and parts[0].isdigit():
                parts = parts[1:]
            table.append(parts)
        max_cols = max((len(row) for row in table), default=0)
        for row in table:
            while len(row) < max_cols:
                row.append('')

    # Parse deps
    for line in deps_lines:
        if '->' in line:
            left, right = line.split('->')
            left = left.strip()
            right = right.strip()
            if left.isdigit() and right.isdigit():
                deps.append((int(left), int(right)))

    return table, deps

# Example usage:
input_file = os.path.join(os.path.dirname(__file__), "input.tmp")
table, deps = parse_table_and_deps_from_file(input_file)

# Draw table
cell_width = 50
cell_height = 30
start_x = 100
start_y = 100

# Draw column labels (coordinates) on top
for col_idx in range(len(table[0]) if table else 0):
    label = str(col_idx + 1)
    obj = drawpyo.diagram.Object(
        page=page,
        value=label
    )
    obj.position = (start_x + col_idx * cell_width, start_y - cell_height)
    obj.geometry.width = cell_width
    obj.geometry.height = cell_height
    obj.text_format.fontSize = 16
    obj.apply_style_string("whiteSpace=wrap;rounded=0;dashed=1;fontSize=16;dashPattern=1 4;strokeColor=none;fillColor=none;fontStyle=2;align=center;verticalAlign=bottom;")

row_labels = []

# Draw row labels (coordinates) on the left
for row_idx in range(len(table)):
    label = "Instr " + str(row_idx + 1)
    obj = drawpyo.diagram.Object(
        page=page,
        value=label
    )
    obj.position = (start_x - cell_width, start_y + row_idx * cell_height)
    obj.geometry.width = cell_width
    obj.geometry.height = cell_height
    obj.text_format.fontSize = 16
    obj.apply_style_string("whiteSpace=wrap;rounded=0;dashed=1;fontSize=16;dashPattern=1 4;strokeColor=none;fillColor=none;fontStyle=2;align=center;")

    row_labels.append(obj)

# Draw dependency links between instructions based on deps
for src_idx, tgt_idx in deps:
    if 0 <= src_idx - 1 < len(row_labels) and 0 <= tgt_idx - 1 < len(row_labels):
        link = drawpyo.diagram.Edge(
            page=page,
            source=row_labels[src_idx - 1],
            target=row_labels[tgt_idx - 1],
            exitX=0,
            exitY=0.5,
            entryX=0,
            entryY=0.5,
            jettySize=15,
            waypoints="curved",
        )

style_table = {
    "IF": "fillColor=#fff2cc;",
    "ID": "fillColor=#ffe6cc;",
    "FU1": "fillColor=#d5e8d4;",
    "FU2": "fillColor=#dae8fc;",
    "COM": "fillColor=#fff2cc;",
    "rs": "fontStyle=2;",
    "rob": "fontStyle=2;",
}

# Draw table cells
for row_idx, row in enumerate(table):
    for col_idx, word in enumerate(row):
        obj = drawpyo.diagram.Object(
            page=page,
            value=""
        )
        obj.position = (start_x + col_idx * cell_width, start_y + row_idx * cell_height)
        obj.geometry.width = cell_width
        obj.geometry.height = cell_height
        obj.text_format.fontSize = 20
        obj.apply_style_string("whiteSpace=wrap;rounded=0;dashed=1;fontSize=20;dashPattern=1 4;strokeColor=light-dark(#8c8c8c, #ededed);")

        if word.strip():
            obj = drawpyo.diagram.Object(
                page=page,
                value=word.strip()
            )
            obj.position = (start_x + col_idx * cell_width, start_y + row_idx * cell_height)
            obj.geometry.width = cell_width
            obj.geometry.height = cell_height
            obj.text_format.fontSize = 20

            obj.apply_style_string("strokeColor=none;" + style_table.get(word.strip()))


file.write()