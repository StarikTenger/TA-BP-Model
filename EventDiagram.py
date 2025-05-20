import sys
import matplotlib.pyplot as plt
import re
import matplotlib.patches as mpatches

def parse_input_frames():
    content = sys.stdin.read()
    # Split meta and tables
    meta, *table_frames = content.strip().split('\n\n', 1)
    if table_frames:
        tables = table_frames[0]
        rest_frames = tables.split('\n\n')
    else:
        rest_frames = []
    # Parse meta
    fu_map = []
    for line in meta.strip().splitlines():
        m = re.search(r'FU(\d+)', line)
        if m:
            fu_map.append(int(m.group(1)))
        else:
            fu_map.append(None)
    # Parse tables
    parsed = []
    for frame in rest_frames:
        lines = [line.strip() for line in frame.splitlines() if line.strip()]
        if not lines:
            continue
        headers = lines[0].split()
        data = []
        for line in lines[1:]:
            parts = line.split(':', 1)[-1].strip().split()
            row = [int(x) for x in parts]
            data.append(row)
        parsed.append((headers, data))
    return fu_map, parsed

def get_fu_color(fu_num):
    palette = {
        1: "green",
        2: "blue",
        3: "purple"
    }
    return palette.get(fu_num, "gray")

def get_event_color(event_name, instr_idx, fu_map):
    if event_name.startswith("FU"):
        fu_num = fu_map[instr_idx] if instr_idx < len(fu_map) else None
        return get_fu_color(fu_num)
    if event_name.startswith("IF") or event_name == "COM":
        return "#baab27"
    elif event_name.startswith("ID"):
        return "orange"
    elif "sq" in event_name.lower():
        return "red"
    else:
        return "b"

def draw_wide_arrow(ax, x_start, x_end, y, color, label, va='bottom', arrow_height=0.18, alpha=0.5):
    ax.annotate(
        '', 
        xy=(x_end, y), xytext=(x_start, y),
        arrowprops=dict(
            arrowstyle='-|>,head_width=1.2,head_length=1.2',
            color=color,
            lw=10,
            alpha=alpha
        ),
        zorder=1
    )
    ax.text(
        (x_start + x_end) / 2, y + (arrow_height if va == 'bottom' else -arrow_height),
        label, color=color, fontsize=12, fontweight='bold',
        ha='center', va=va, alpha=0.9, zorder=2
    )

def draw_event(ax, plot_time, instr_idx, label, color):
    if "_r" in label:
        ax.annotate(
            '', xy=(plot_time, instr_idx + 0.4), xytext=(plot_time, instr_idx - 0.4),
            arrowprops=dict(arrowstyle='-|>', color=color, lw=2, shrinkA=0, shrinkB=0)
        )
    elif "_a" in label:
        ax.annotate(
            '', xy=(plot_time, instr_idx - 0.4), xytext=(plot_time, instr_idx + 0.4),
            arrowprops=dict(arrowstyle='-|>', color=color, lw=2, shrinkA=0, shrinkB=0)
        )
    else:
        ax.vlines(plot_time, instr_idx - 0.4, instr_idx + 0.4, color=color, linewidth=2)
        ax.text(plot_time, instr_idx + 0.45, label, rotation=90, va='bottom', ha='center', fontsize=8, color=color)

def plot_events(headers, data, ax, fu_map, change_arrows=None, will_change=None):
    import numpy as np
    num_instr = len(data)
    time_counts = [{time: row.count(time) for time in set(row) if time >= 0} for row in data]

    for instr_idx, row in enumerate(data):
        plotted_at_time = {}
        def get_time(label):
            try:
                idx = headers.index(label)
                t = row[idx]
                return t if t >= 0 else None
            except ValueError:
                return None

        IF_a_time, IF_r_time = get_time("IF_a"), get_time("IF_r")
        ID_a_time, ID_r_time = get_time("ID_a"), get_time("ID_r")
        FU_a_time, FU_r_time = get_time("FU_a"), get_time("FU_r")

        # Draw wide arrows for IF, ID, FU
        if IF_a_time is not None and IF_r_time is not None and IF_r_time > IF_a_time:
            draw_wide_arrow(ax, IF_a_time, IF_r_time, instr_idx, "#ffe066", "IF", va='bottom', arrow_height=0.18, alpha=0.5)
        if ID_a_time is not None and ID_r_time is not None and ID_r_time > ID_a_time:
            draw_wide_arrow(ax, ID_a_time, ID_r_time, instr_idx, "orange", "ID", va='bottom', arrow_height=0.18, alpha=0.4)
        if FU_a_time is not None and FU_r_time is not None and FU_r_time > FU_a_time:
            fu_color = get_fu_color(fu_map[instr_idx] if instr_idx < len(fu_map) else None)
            draw_wide_arrow(ax, FU_a_time, FU_r_time, instr_idx, fu_color, "FU", va='top', arrow_height=0.18, alpha=0.4)

        # Draw events
        for event_idx, time in enumerate(row):
            if time >= 0:
                count = time_counts[instr_idx][time]
                if count > 1:
                    idx_at_time = plotted_at_time.get(time, 0)
                    gap = 0.15
                    offset = (idx_at_time - (count - 1) / 2) * gap
                    plot_time = time + offset
                    plotted_at_time[time] = idx_at_time + 1
                else:
                    plot_time = time
                color = get_event_color(headers[event_idx], instr_idx, fu_map)
                draw_event(ax, plot_time, instr_idx, headers[event_idx], color)

                # Encircle if this event will change in the next frame
                if will_change and (instr_idx, event_idx) in will_change:
                    circle = mpatches.Circle((plot_time, instr_idx), 0.35, fill=False, color='crimson', linewidth=2, zorder=20)
                    ax.add_patch(circle)

    ax.set_yticks(range(num_instr))
    ax.set_yticklabels([f'Instr {i+1}' for i in range(num_instr)])
    ax.set_xlabel('Time')
    ax.set_ylabel('Instruction')
    ax.set_title('Event Diagram')
    ax.grid(True, axis='x', linestyle='--', alpha=0.5)
    ax.invert_yaxis()

    # Set x-axis ticks to show all integer times
    all_times = [time for row in data for time in row if time >= 0]
    if all_times:
        min_time = min(all_times)
        max_time = max(all_times)
        ax.set_xticks(range(min_time, max_time + 1))
        ax.set_xlim(min_time - 1, max_time + 1)  # Always show all timings with some margin

    # Always show all instructions
    ax.set_ylim(num_instr - 0.5, -0.5)  # Inverted y-axis, so -0.5 is top, num_instr-0.5 is bottom

    # Draw change arrows if provided, stacking them on different levels to avoid overlap
    if change_arrows:
        # Assign levels to arrows to avoid overlap
        level_height = 0.18  # vertical shift per level
        arrow_segments = []
        for (from_instr, from_event, from_time, to_instr, to_event, to_time, label) in change_arrows:
            key = (min(from_time, to_time), max(from_time, to_time), from_instr, to_instr)
            arrow_segments.append((key, (from_instr, from_event, from_time, to_instr, to_event, to_time, label)))
        arrow_segments.sort()  # Sort for deterministic stacking

        level_map = {}
        for seg_idx, (key, arrow) in enumerate(arrow_segments):
            # Find the lowest available level for this time range
            occupied = set()
            for prev_key, prev_level in level_map.items():
                if not (key[1] < prev_key[0] or key[0] > prev_key[1]):
                    occupied.add(prev_level)
            level = 0
            while level in occupied:
                level += 1
            level_map[key] = level

            from_instr, from_event, from_time, to_instr, to_event, to_time, label = arrow
            base_y_from = from_instr
            base_y_to = to_instr
            shift = (level - 0.5) * level_height
            y_from = base_y_from + shift
            y_to = base_y_to + shift

            # Draw the main movement arrow (gray dashed)
            ax.plot([from_time, to_time],
                    [y_from, y_to],
                    color='gray', linestyle='dashed', linewidth=2, alpha=0.8, zorder=10)
            ax.annotate(
                '', 
                xy=(to_time, y_to), xytext=(from_time, y_from),
                arrowprops=dict(
                    arrowstyle='->,head_width=1.2,head_length=1.2',
                    color='gray',
                    lw=2,
                    alpha=0.8,
                    linestyle='dashed'
                ),
                zorder=11
            )

            # Draw the previous position as a dotted vertical line or arrow, using the event's color and style
            prev_color = get_event_color(label, from_instr, fu_map)
            # To avoid overlap, shift each vertical line/arrow slightly horizontally based on its level
            x_shift = (level - 0.5) * 0.12  # 0.12 is a small horizontal offset per level
            shifted_from_time = from_time + x_shift

            if "_a" in label:
                ax.annotate(
                    '', xy=(shifted_from_time, y_from + 0.4), xytext=(shifted_from_time, y_from - 0.4),
                    arrowprops=dict(arrowstyle='-|>', color=prev_color, lw=2, linestyle='dotted', alpha=0.7, shrinkA=0, shrinkB=0),
                    zorder=9
                )
            elif "_r" in label:
                ax.annotate(
                    '', xy=(shifted_from_time, y_from - 0.4), xytext=(shifted_from_time, y_from + 0.4),
                    arrowprops=dict(arrowstyle='-|>', color=prev_color, lw=2, linestyle='dotted', alpha=0.7, shrinkA=0, shrinkB=0),
                    zorder=9
                )
            else:
                ax.vlines(shifted_from_time, y_from - 0.4, y_from + 0.4, color=prev_color, linestyle='dotted', linewidth=2, alpha=0.7, zorder=9)
            ax.text(shifted_from_time, y_from + 0.45, label, rotation=90, va='bottom', ha='center', fontsize=8, color=prev_color, alpha=0.7, zorder=9)

def find_changes_between_frames(headers, data_prev, data_next):
    """Finds changes between two frames and returns a list of arrows to draw and a set of events that will change."""
    arrows = []
    will_change = set()
    for instr_idx, (row_prev, row_next) in enumerate(zip(data_prev, data_next)):
        for event_idx, (val_prev, val_next) in enumerate(zip(row_prev, row_next)):
            if val_prev != val_next and val_prev >= 0 and val_next >= 0:
                arrows.append((
                    instr_idx, event_idx, val_prev,
                    instr_idx, event_idx, val_next,
                    headers[event_idx]
                ))
                will_change.add((instr_idx, event_idx))
    return arrows, will_change

def interactive_plot(fu_map, frames):
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(12, 6))
    plt.subplots_adjust(bottom=0.15)
    current = [0]

    def update(idx):
        ax.clear()
        headers, data = frames[idx]
        change_arrows = None
        will_change = None
        if idx + 1 < len(frames):
            headers_next, data_next = frames[idx + 1]
            if headers_next == headers and len(data_next) == len(data):
                _, will_change = find_changes_between_frames(headers, data, data_next)
        if idx > 0:
            headers_prev, data_prev = frames[idx-1]
            if headers_prev == headers and len(data_prev) == len(data):
                change_arrows, _ = find_changes_between_frames(headers, data_prev, data)
        plot_events(headers, data, ax, fu_map, change_arrows, will_change)
        ax.set_title(f"Event Diagram (Frame {idx+1}/{len(frames)})")
        fig.canvas.draw_idle()

    def on_key(event):
        if event.key == 'right':
            if current[0] < len(frames) - 1:
                current[0] += 1
                update(current[0])
        elif event.key == 'left':
            if current[0] > 0:
                current[0] -= 1
                update(current[0])

    fig.canvas.mpl_connect('key_press_event', on_key)
    update(0)
    plt.show()

if __name__ == "__main__":
    fu_map, frames = parse_input_frames()
    interactive_plot(fu_map, frames)