from pathlib import Path

file = Path(
    "examples/splinter-new/clean/manual-trigger/Splinter-CoordinationLayer-CoordinationSystemRefinement.i.dfy-Impl__CoordinationSystemRefinement.__default.CrashNext.smt2"
)

for line in file.read_text().splitlines(keepends=False):
    if "Set#" in line:
        continue

    print(line)
