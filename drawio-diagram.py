import drawpyo
import os
import sys
import argparse


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


def draw_table(input_file, page):
    """Create a drawio diagram from parsed tables and dependencies."""
    

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
                # Set jettySize proportional to vertical distance between source and target
                vertical_distance = abs(src_idx - tgt_idx) * cell_height
                jetty_size = int(vertical_distance * 0.5)

                link = drawpyo.diagram.Edge(
                    page=page,
                    source=row_labels[src_idx - 1],
                    target=row_labels[tgt_idx - 1],
                    exitX=0,
                    exitY=0.5,
                    entryX=0,
                    entryY=0.5,
                    jettySize=jetty_size,
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

    
def parse_graph_file(filepath):
    """Parse graph file to extract edges and the last lookup table."""
    edges = []
    lookup_table = {}
    
    with open(filepath, 'r') as f:
        lines = [line.rstrip('\n') for line in f]
    
    if not lines:
        return edges, lookup_table
    
    # Extract edges from lines like {[3, FU_a]} -> [3, FU_r] or {[2, FU_r], [3, FU_r]} -> [4, FU_a]
    for line in lines:
        line = line.strip()
        if '->' in line and (line.startswith('{') or line.startswith('[')):
            # Parse edge format: {[row, col]} -> [row, col] or {[row, col], [row, col]} -> [row, col]
            try:
                # Split on '->'
                left_part, right_part = line.split('->', 1)
                left_part = left_part.strip()
                right_part = right_part.strip()
                
                # Parse sources (can be multiple)
                sources = []
                if left_part.startswith('{') and left_part.endswith('}'):
                    # Multiple sources: {[row, col], [row, col]}
                    inner_content = left_part[1:-1]  # Remove { and }
                    # Split by '], [' to get individual coordinate pairs
                    coord_parts = []
                    bracket_count = 0
                    current_part = ""
                    
                    for char in inner_content:
                        if char == '[':
                            bracket_count += 1
                        elif char == ']':
                            bracket_count -= 1
                        current_part += char
                        
                        if bracket_count == 0 and char == ']':
                            if current_part.strip():
                                coord_parts.append(current_part.strip())
                            current_part = ""
                    
                    for coord_part in coord_parts:
                        coord_part = coord_part.strip().strip(',').strip()
                        if coord_part.startswith('[') and coord_part.endswith(']'):
                            coord_content = coord_part[1:-1]  # Remove [ and ]
                            parts = [part.strip() for part in coord_content.split(',')]
                            if len(parts) >= 2:
                                row = int(parts[0])
                                col = parts[1]
                                sources.append((row, col))
                elif left_part.startswith('[') and left_part.endswith(']'):
                    # Single source: [row, col]
                    coord_content = left_part[1:-1]  # Remove [ and ]
                    parts = [part.strip() for part in coord_content.split(',')]
                    if len(parts) >= 2:
                        row = int(parts[0])
                        col = parts[1]
                        sources.append((row, col))
                
                # Parse destination
                destination = None
                if right_part.startswith('[') and right_part.endswith(']'):
                    coord_content = right_part[1:-1]  # Remove [ and ]
                    parts = [part.strip() for part in coord_content.split(',')]
                    if len(parts) >= 2:
                        row = int(parts[0])
                        col = parts[1]
                        destination = (row, col)
                
                # Create edges for each source to the destination
                if sources and destination:
                    # Create a single edge with multiple sources (multi-edge)
                    edges.append({
                        'from': sources,  # List of sources
                        'to': destination
                    })
                    
            except (ValueError, IndexError):
                # Skip malformed lines
                continue
    
    # Find and parse the last table
    # Look for lines that start with numbers followed by colon (table rows)
    table_lines = []
    current_table = []
    header_line = None
    
    for line in lines:
        line = line.strip()
        # Check if this is a table header (contains column names like IF_a, IF_r, etc.)
        if any(col in line for col in ['IF_a', 'IF_r', 'ID_a', 'ID_r', 'FU_a', 'FU_r', 'COM', 'Sq']):
            # If we have a previous table, save it
            if current_table and header_line:
                table_lines.append((header_line, current_table))
            # Start new table
            header_line = line
            current_table = []
        # Check if this is a table row (starts with number:)
        elif ':' in line and line.split(':')[0].strip().isdigit():
            if header_line:  # Only add rows if we have a header
                current_table.append(line)
    
    # Add the last table
    if current_table and header_line:
        table_lines.append((header_line, current_table))
    
    # Process the last table to create lookup table
    if table_lines:
        header, rows = table_lines[-1]  # Get the last table
        
        # Parse header to get column names
        header_parts = header.split('\t')
        # Remove empty parts and strip whitespace
        columns = [col.strip() for col in header_parts if col.strip()]
        
        # Parse each row
        for row_line in rows:
            if ':' in row_line:
                row_num_part, data_part = row_line.split(':', 1)
                try:
                    row_num = int(row_num_part.strip())
                    data_parts = data_part.split('\t')
                    # Remove empty parts and strip whitespace
                    values = [val.strip() for val in data_parts if val.strip()]
                    
                    # Create lookup entries for each column
                    for col_idx, col_name in enumerate(columns):
                        if col_idx < len(values):
                            try:
                                # Convert value to int if possible, otherwise keep as string
                                value = int(values[col_idx]) if values[col_idx].lstrip('-').isdigit() else values[col_idx]
                                lookup_table[(row_num, col_name)] = value
                            except ValueError:
                                lookup_table[(row_num, col_name)] = values[col_idx]
                                
                except ValueError:
                    continue
    
    return edges, lookup_table


def draw_graph(edges, lookup_table, page):
    cell_width = 50
    cell_height = 30
    start_x = 100 - cell_width / 2
    start_y = 100

    for edge in edges:
        to_coord = lookup_table.get(edge['to'])
        
        if not to_coord:
            continue
            
        # Handle both single and multi-edges
        sources = edge['from'] if isinstance(edge['from'], list) else [edge['from']]
        is_multi = len(sources) > 1
        
        if is_multi:
            # Multi-edge: create invisible junction and draw arrows accordingly
            shift_distance = 15
            to_col = edge['to'][1]
            to_offset = shift_distance if str(to_col).endswith("_a") else (-shift_distance if str(to_col).endswith("_r") else shift_distance)
            to_x = start_x + (to_coord if isinstance(to_coord, int) else 0) * cell_width + to_offset
            to_y = start_y + (edge['to'][0] - 1) * cell_height
            
            # Calculate mean position for junction
            source_positions = []
            for source in sources:
                from_coord = lookup_table.get(source)
                if from_coord:
                    from_col = source[1]
                    from_offset = shift_distance if str(from_col).endswith("_a") else (-shift_distance if str(from_col).endswith("_r") else shift_distance)
                    from_x = start_x + (from_coord if isinstance(from_coord, int) else 0) * cell_width + from_offset
                    from_y = start_y + (source[0] - 1) * cell_height
                    source_positions.append((from_x, from_y))
            
            if source_positions:
                # Calculate mean position of sources, then midpoint between mean and destination
                mean_source_x = sum(pos[0] for pos in source_positions) / len(source_positions)
                mean_source_y = sum(pos[1] for pos in source_positions) / len(source_positions)
                junction_x = (mean_source_x + to_x) / 2
                junction_y = (mean_source_y + to_y) / 2
                
                # Create invisible junction object
                junction_obj = drawpyo.diagram.Object(
                    page=page,
                    value=""
                )
                junction_obj.position = (junction_x + cell_width // 2 - 5, junction_y + cell_height // 2 - 5)
                junction_obj.geometry.width = 0
                junction_obj.geometry.height = 0
                junction_obj.apply_style_string("fillColor=none;strokeColor=none;")
                
                # Create destination object
                obj_to = drawpyo.diagram.Object(
                    page=page,
                    value=""
                )
                obj_to.position = (to_x + cell_width // 2 - 5, to_y + cell_height // 2 - 5)
                obj_to.geometry.width = 0
                obj_to.geometry.height = 0
                obj_to.apply_style_string("shape=ellipse;fillColor=#FF0000;strokeColor=#FF0000;strokeWidth=1;")
                
                # Draw arrows from each source to junction (no arrowhead)
                for source in sources:
                    from_coord = lookup_table.get(source)
                    if from_coord:
                        from_col = source[1]
                        from_offset = shift_distance if str(from_col).endswith("_a") else (-shift_distance if str(from_col).endswith("_r") else shift_distance)
                        from_x = start_x + (from_coord if isinstance(from_coord, int) else 0) * cell_width + from_offset
                        from_y = start_y + (source[0] - 1) * cell_height
                        
                        obj_from = drawpyo.diagram.Object(
                            page=page,
                            value=""
                        )
                        obj_from.position = (from_x + cell_width // 2 - 5, from_y + cell_height // 2 - 5)
                        obj_from.geometry.width = 0
                        obj_from.geometry.height = 0
                        obj_from.apply_style_string("shape=ellipse;fillColor=#FF0000;strokeColor=#FF0000;strokeWidth=1;")
                        
                        # Arrow from source to junction (no arrowhead)
                        drawpyo.diagram.Edge(
                            page=page,
                            source=obj_from,
                            target=junction_obj,
                            exitX=1,
                            exitY=0.5,
                            entryX=0,
                            entryY=0.5,
                            waypoints="straight",
                            shadow=True,
                            strokeWidth=4,
                            strokeColor="#b85450",
                            line_end_target="none"
                        )
                
                # Arrow from junction to destination (with arrowhead)
                drawpyo.diagram.Edge(
                    page=page,
                    source=junction_obj,
                    target=obj_to,
                    exitX=1,
                    exitY=0.5,
                    entryX=0,
                    entryY=0.5,
                    waypoints="straight",
                    shadow=True,
                    strokeWidth=4,
                    strokeColor="#b85450"
                )
        else:
            # Single edge: use original logic
            source = sources[0]
            from_coord = lookup_table.get(source)
            
            if from_coord and to_coord:
                shift_distance = 15

                # Determine x-offset based on suffix
                from_col = source[1]
                to_col = edge['to'][1]

                from_offset = shift_distance if str(from_col).endswith("_a") else (-shift_distance if str(from_col).endswith("_r") else shift_distance)
                to_offset = shift_distance if str(to_col).endswith("_a") else (-shift_distance if str(to_col).endswith("_r") else shift_distance)

                from_x = start_x + (from_coord if isinstance(from_coord, int) else 0) * cell_width + from_offset
                from_y = start_y + (source[0] - 1) * cell_height
                to_x = start_x + (to_coord if isinstance(to_coord, int) else 0) * cell_width + to_offset
                to_y = start_y + (edge['to'][0] - 1) * cell_height

                obj_from = drawpyo.diagram.Object(
                    page=page,
                    value=""
                )
                obj_from.position = (from_x + cell_width // 2 - 5, from_y + cell_height // 2 - 5)
                obj_from.geometry.width = 0
                obj_from.geometry.height = 0
                obj_from.apply_style_string("shape=ellipse;fillColor=#FF0000;strokeColor=#FF0000;strokeWidth=1;")

                obj_to = drawpyo.diagram.Object(
                    page=page,
                    value=""
                )
                obj_to.position = (to_x + cell_width // 2 - 5, to_y + cell_height // 2 - 5)
                obj_to.geometry.width = 0
                obj_to.geometry.height = 0
                obj_to.apply_style_string("shape=ellipse;fillColor=#FF0000;strokeColor=#FF0000;strokeWidth=1;")

                drawpyo.diagram.Edge(
                    page=page,
                    source=obj_from,
                    target=obj_to,
                    exitX=1,
                    exitY=0.5,
                    entryX=0,
                    entryY=0.5,
                    waypoints="straight",
                    shadow=True,
                    strokeWidth=4,
                    strokeColor="#b85450"
                )

def filter_edges(edges):
    """Filter edges to keep only the last one for each destination, removing all previous edges with same destination."""
    # Dictionary to store the last edge for each destination
    dest_to_edge = {}
    
    # Process edges in order, later edges will completely replace earlier ones for the same destination
    for edge in edges:
        dest = edge['to']
        dest_to_edge[dest] = edge
    
    # Return the filtered edges (only the last one for each destination)
    return list(dest_to_edge.values())

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate drawio diagram from input file.")
    parser.add_argument("inputfile", help="Input filename")
    parser.add_argument("--outfile", help="Output filename (default: inputfile + .drawio)")
    parser.add_argument("--graph", metavar="GRAPH_FILE", help="Parse and draw graph edges from specified graph file instead of tables")
    args = parser.parse_args()

    input_file = args.inputfile
    outfile = args.outfile if args.outfile else input_file + ".drawio"

    file = drawpyo.File()
    file.file_path = os.path.dirname(outfile)
    if file.file_path == "":
        file.file_path = "."
    file.file_name = os.path.basename(outfile)
    # Add a page
    page = drawpyo.Page(file=file)

    print(outfile)

    if args.graph:
        # Use graph parsing and drawing from the specified graph file
        edges, lookup_table = parse_graph_file(args.graph)
        draw_table(input_file, page)
        print(edges)
        print(lookup_table)
        edges = filter_edges(edges) # Filter edges to keep only the last one for each destination
        draw_graph(edges, lookup_table, page)
    else:
        # Use original table drawing from input file
        draw_table(input_file, page)

    file.write()