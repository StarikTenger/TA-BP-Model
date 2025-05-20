import sys
import matplotlib.pyplot as plt

def parse_input():
    lines = [line.strip() for line in sys.stdin if line.strip()]
    headers = lines[0].split()
    data = []
    for line in lines[1:]:
        parts = line.split(':', 1)[-1].strip().split()
        row = [int(x) for x in parts]
        data.append(row)
    return headers, data

def get_event_color(event_name):
    if event_name.startswith("IF") or event_name == "COM":
        return "#baab27"
    elif event_name.startswith("ID"):
        return "orange"
    elif event_name.startswith("FU"):
        return "green"
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
    # Draw arrow instead of vertical bar if needed
    if "_a" in label:
        ax.annotate(
            '', xy=(plot_time, instr_idx + 0.4), xytext=(plot_time, instr_idx - 0.4),
            arrowprops=dict(arrowstyle='-|>', color=color, lw=2, shrinkA=0, shrinkB=0)
        )
    elif "_r" in label:
        ax.annotate(
            '', xy=(plot_time, instr_idx - 0.4), xytext=(plot_time, instr_idx + 0.4),
            arrowprops=dict(arrowstyle='-|>', color=color, lw=2, shrinkA=0, shrinkB=0)
        )
    else:
        ax.vlines(plot_time, instr_idx - 0.4, instr_idx + 0.4, color=color, linewidth=2)
        ax.text(plot_time, instr_idx + 0.45, label, rotation=90, va='bottom', ha='center', fontsize=8, color=color)

def plot_events(headers, data):
    fig, ax = plt.subplots(figsize=(12, 6))
    num_instr = len(data)

    for instr_idx, row in enumerate(data):
        time_counts = {}
        for time in row:
            if time >= 0:
                time_counts[time] = time_counts.get(time, 0) + 1

        plotted_at_time = {}

        # Collect event times
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
            draw_wide_arrow(ax, FU_a_time, FU_r_time, instr_idx, "green", "FU", va='top', arrow_height=0.18, alpha=0.4)

        # Draw events
        for event_idx, time in enumerate(row):
            if time >= 0:
                count = time_counts[time]
                if count > 1:
                    idx_at_time = plotted_at_time.get(time, 0)
                    gap = 0.15
                    offset = (idx_at_time - (count - 1) / 2) * gap
                    plot_time = time + offset
                    plotted_at_time[time] = idx_at_time + 1
                else:
                    plot_time = time
                color = get_event_color(headers[event_idx])
                draw_event(ax, plot_time, instr_idx, headers[event_idx], color)

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

    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    headers, data = parse_input()
    plot_events(headers, data)