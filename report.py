#!/usr/bin/env python3

import os

# Initialize counters for all .lean files
total_lines = 0
total_defs = 0
total_inductives = 0
total_abbrevs = 0

# Traverse all directories starting from the current folder
for root, dirs, files in os.walk("."):
    for file in files:
        if file.endswith(".lean"):
            filepath = os.path.join(root, file)
            try:
                with open(filepath, 'r') as f:
                    lines = f.readlines()
                    total_lines += len(lines)
                    total_defs += len(list(filter(lambda x: "def " in x, lines)))
                    total_inductives += len(list(filter(lambda x: "inductive " in x, lines)))
                    total_abbrevs += len(list(filter(lambda x: "abbrev " in x, lines)))
            except Exception as e:
                print(f"Error reading {filepath}: {e}")

f = open("build_log.txt")
lines = f.readlines()

errors = list(filter(lambda x: "error: " in x, lines))

# The number of lines containing the word "error"
errorcount = len(list(errors))

# The number of lines containing the word "warning"
warningcount = len(list(filter(lambda x: "warning: " in x, lines)))

# Remove anything before the string "error: " from each line
errors = list(map(lambda x: x[x.rfind(": ")+2:-1], errors))

# Create an array of unique errors plus their count from errors
errors = [[errors.count(x), x] for x in set(errors)]
errors.sort(reverse=True)

print(f"# Statistics\n")

print(f"Lines: {total_lines}  ")
print(f"Definitions: {total_defs}  ")
print(f"Inductive definitions: {total_inductives}  ")
print(f"Abbreviations: {total_abbrevs}  ")

print("")
print("# Warnings and Errors\n")

print(f"Errors found: {errorcount}  ")
print(f"Warnings found: {warningcount}  ")

print("")
print("## Error Classes\n")

for error in errors:
    print(f"- {error[0]}x {error[1]}")


