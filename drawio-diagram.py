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

row_offsets = []
for row in table:
    for col_idx, cell in enumerate(row):
        if cell.strip():
            row_offsets.append(col_idx + 1)
            break
    else:
        row_offsets.append(-1)

# Draw table
cell_width = 50
cell_height = 30
start_x = 100
start_y = 100

column_labels = []

# Draw column labels (coordinates) on top
for col_idx in range(len(table[0]) if table else 0):
    label = str(col_idx + 1)
    obj = drawpyo.diagram.Object(
        page=page,
        value=label
    )
    obj.geometry.width = cell_width
    obj.geometry.height = 20
    obj.position = (start_x + col_idx * cell_width, start_y - obj.geometry.height)
    obj.text_format.fontSize = 16
    obj.apply_style_string("whiteSpace=wrap;rounded=0;dashed=1;fontSize=16;dashPattern=1 4;strokeColor=none;fillColor=none;fontStyle=2;align=center;verticalAlign=bottom;fontFamily=Times New Roman;")
    column_labels.append(obj)

row_labels = []

# Draw row labels (coordinates) on the left
for row_idx in range(len(table)):
    label = chr(ord('A') + row_idx) + " "
    obj = drawpyo.diagram.Object(
        page=page,
        value=label
    )
    obj.geometry.width = 15
    obj.geometry.height = cell_height
    obj.position = (start_x - obj.geometry.width, start_y + row_idx * cell_height)
    obj.text_format.fontSize = 16
    obj.apply_style_string("whiteSpace=wrap;rounded=0;dashed=1;fontSize=16;dashPattern=1 4;strokeColor=none;fillColor=none;fontStyle=2;align=center;fontFamily=Times New Roman;")

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
    "#squashed": "fillColor=#f8cecc;",
}

# Draw table cells
for row_idx, row in enumerate(table):
    for col_idx, word in enumerate(row):
        if word.strip():
            obj = drawpyo.diagram.Object(
                page=page,
                value=word.strip()
            )
            obj.position = (start_x + col_idx * cell_width, start_y + row_idx * cell_height)
            obj.geometry.width = cell_width
            obj.geometry.height = cell_height
            obj.text_format.fontSize = 20

            if (word.strip() == "#squashed"):
                obj.value = "❌"

            obj.apply_style_string("strokeColor=none;fontFamily=Times New Roman;" + style_table.get(word.strip()))
        elif col_idx < row_offsets[row_idx]:
            obj = drawpyo.diagram.Object(
                page=page,
                value="."
            )
            obj.position = (start_x + col_idx * cell_width, start_y + row_idx * cell_height)
            obj.geometry.width = cell_width
            obj.geometry.height = cell_height
            obj.apply_style_string("strokeColor=none;fillColor=none;")

# Column separators
num_cols = len(table[0]) if table else 0
num_rows = len(table)
for col_idx in range(1, num_cols):
    x = start_x + col_idx * cell_width
    y1 = start_y
    y2 = start_y + num_rows * cell_height

    duplicate_label = drawpyo.diagram.Object(
        page=page,
        value=""
    )
    duplicate_label.position = (start_x + (col_idx - 1) * cell_width, y2)
    duplicate_label.geometry.width = cell_width
    duplicate_label.geometry.height = 1
    duplicate_label.apply_style_string("strokeColor=none;")

    sep = drawpyo.diagram.Edge(
        page=page,
        source=column_labels[col_idx - 1],
        target=duplicate_label,
        exitX=1,
        exitY=0,
        entryX=1,
        entryY=0,
        pattern="dashed_small",
        line_end_target="none",
        strokeColor="#6E6E6E",
        waypoints="straight",
    )

# Time axis
drawpyo.diagram.Edge(
    page=page,
    source=row_labels[0],
    target=column_labels[-1],
    exitX=0,
    exitY=0,
    entryX=1,
    entryY=1,
    pattern="solid",
    line_end_target="none",
    strokeColor="#000000",
    waypoints="straight",
)

# Instructions axis
drawpyo.diagram.Edge(
    page=page,
    source=column_labels[0],
    target=row_labels[-1],
    exitX=0,
    exitY=0,
    entryX=1,
    entryY=1,
    pattern="solid",
    line_end_target="none",
    strokeColor="#000000",
    waypoints="straight",
)

file.write()