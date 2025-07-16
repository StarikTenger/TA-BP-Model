""" 
  ┌──────────────────────────────────────────────────────────────────────────┐
  │ Takes TLA+ output file as input and finds the maximum clock cycle.       │
  └──────────────────────────────────────────────────────────────────────────┘
 """

import re
import sys

def find_max_clock_cycle(file_path):
    max_cycle = None
    pattern = r"ClockCycle\s*=\s*(\d+)"
    
    with open(file_path, 'r') as file:
        for line in file:
            match = re.search(pattern, line)
            if match:
                cycle = int(match.group(1))
                if max_cycle is None or cycle > max_cycle:
                    max_cycle = cycle
    
    if max_cycle is not None:
        print(max_cycle)
    else:
        print("ERROR: No ClockCycle entries found.")
        sys.exit(1)

# Replace with the path to your file
if len(sys.argv) != 2:
    print("Usage: python calc-time.py <file_path>")
    sys.exit(1)

file_path = sys.argv[1]
find_max_clock_cycle(file_path)