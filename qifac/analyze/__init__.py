from io import StringIO
from typing import TextIO

from ..core import instances as core_instances
from ..instances import show as all_instances
from ..instances.compare import compare


def compare_files(unsat_file: TextIO, unknown_file: TextIO) -> TextIO:
    buffer = StringIO()

    unsat_forest = core_instances(unsat_file)
    unknown_forest = all_instances(unknown_file, with_proof=False)

    missing = compare(unsat_forest, unknown_forest)

    print(
        f"Missing {int(100*len(missing)/len(unsat_forest.nodes))}% of instantiations",
        file=buffer,
    )
    for node in missing:
        print(f"> {unsat_forest.nodes[node]}", file=buffer)

    buffer.seek(0)

    return buffer
