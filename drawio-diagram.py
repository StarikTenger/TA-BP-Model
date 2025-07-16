import drawpyo
import os

file = drawpyo.File()
file.file_path = r"./"
file.file_name = "test.drawio"
# Add a page
page = drawpyo.Page(file=file)

def parse_tables_and_deps_from_file(filepath):
    tables = []
    deps = []
    with open(filepath, 'r') as f:
        lines = [line.rstrip('\n') for line in f if line.strip()]
    if not lines:
        return tables, deps

    # Split off deps section
    if any(line.strip().startswith("Deps:") for line in lines):
        deps_start = next(i for i, line in enumerate(lines) if line.strip().startswith("Deps:"))
        table_lines = lines[:deps_start]
        deps_lines = lines[deps_start + 1 :]
    else:
        table_lines = lines
        deps_lines = []

    # Split tables by dashed lines
    table_blocks = []
    current_block = []
    for line in table_lines:
        if set(line.strip()) == {"-"}:
            if current_block:
                table_blocks.append(current_block)
                current_block = []
        else:
            current_block.append(line)
    if current_block:
        table_blocks.append(current_block)

    # Parse each table
    for block in table_blocks:
        table = []
        last_idx = 0
        if block:
            first_line = block[0]
            if all(part.isdigit() for part in first_line.split()):
                block = block[1:]
            for line in block:
                parts = line.split('\t')
                cur_idx = parts[0] if parts else None
                if parts and parts[0].isdigit():
                    parts = parts[1:]
                if cur_idx:
                    cur_idx = int(cur_idx)
                    gap = cur_idx - last_idx
                    if gap > 1:
                        for _ in range(gap - 1):
                            table.append([])
                last_idx = cur_idx
                table.append(parts)
                
            # Remove empty elements from the end of each row
            for row in table:
                while row and (not row[-1].strip()):
                    row.pop()
            max_cols = max((len(row) for row in table), default=0)
            for row in table:
                while len(row) < max_cols:
                    row.append('')
        tables.append(table)

    # Parse deps
    for line in deps_lines:
        if '->' in line:
            left, right = line.split('->')
            left = left.strip()
            right = right.strip()
            if left.isdigit() and right.isdigit():
                deps.append((int(left), int(right)))

    return tables, deps

# Example usage:
input_file = os.path.join(os.path.dirname(__file__), "input.tmp")
tables, deps = parse_tables_and_deps_from_file(input_file)

start_y_offset = 0  # Track vertical offset for each table

tables = list(reversed(tables))

style_table = {
    "IF": "fillColor=#fff2cc;",
    "ID": "fillColor=#ffe6cc;",
    "FU1": "fillColor=#d5e8d4;",
    "FU2": "fillColor=#dae8fc;",
    "FU3": "fillColor=#e1d5e7;",
    "COM": "fillColor=#fff2cc;",
    "rs": "fontStyle=2;",
    "rs1": "fontStyle=2;fontColor=#C1C1C1;",
    "rs2": "fontStyle=2;fontColor=#C1C1C1;",
    "rob": "fontStyle=2;fontColor=#C1C1C1;",
    "#squashed": "fillColor=#f8cecc;",
}

label_style = "fontSize=30;rounded=0;fillColor=none;strokeColor=none;dashed=1;align=center;verticalAlign=bottom;fontFamily=Times New Roman;"

label_substyles = [
    "fontColor=light-dark(#00bfff, #ededed);",
    "fontColor=light-dark(#FF0303,#EDEDED);"
]

labels = ["α", "β", "α'", "β'"]

table_num = -1
for table in tables:
    table_num += 1

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
    start_y = 100 + start_y_offset  # Offset each table vertically

    # Draw table label
    table_label = drawpyo.diagram.Object(
        page=page,
        value=labels[table_num % len(labels)]
    )
    table_label.geometry.width = cell_height
    table_label.geometry.height = cell_height
    table_label.position = (start_x - cell_height, start_y - table_label.geometry.height)
    table_label.apply_style_string(label_style + label_substyles[table_num % len(label_substyles)])


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
        obj.apply_style_string("whiteSpace=wrap;rounded=0;dashed=1;fontSize=16;dashPattern=1 4;strokeColor=none;fontStyle=2;align=center;fontFamily=Times New Roman;")

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
                elif (word.strip() == "rs" or word.strip() == "rs1" or word.strip() == "rs2" or word.strip() == "rob"):                                                                                                                                                                                                                                                                                                         
                    obj.apply_style_string("strokeColor=none;fontFamily=Times New Roman;fontStyle=2;")
                else:                                                                                       
                    obj.apply_style_string("strokeColor=none;fontFamily=Times New Roman;")
                if word.strip() in style_table:                                                                                         
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

    # Update vertical offset for next table
    start_y_offset += (num_rows + 3) * cell_height  # 3 extra rows for spacing

file.write()