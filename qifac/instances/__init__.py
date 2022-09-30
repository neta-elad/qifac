import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Set, TextIO, Tuple

from qifac.parsing.instantiation_tree import Forest

from ..metadata import Metadata
from ..parsing.flat import Flat, parse_flat


def simple(smt_file: TextIO) -> Set[Flat]:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = dir_path / "input.smt2"

        with open(input_path, "w") as input_file:
            shutil.copyfileobj(smt_file, input_file)

        log_path = dir_path / "z3.log"
        args = [
            Metadata.default().z3,
            "trace=true",
            f"trace_file_name={log_path}",
            str(input_path),
        ]

        subprocess.run(
            args,
            capture_output=True,
            text=True,
        )

        instances_path = dir_path / "instances.txt"

        subprocess.run(
            [
                Metadata.default().z3tracer,
                "--skip-z3-version-check",
                "--skip-log-consistency-checks",
                "--flat-instantiations",
                str(instances_path),
                str(log_path),
            ],
            capture_output=True,
            text=True,
        )

        return parse_flat(instances_path.read_text())


def show(smt_file: TextIO, *, with_proof: bool) -> Forest:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = dir_path / "input.smt2"

        with open(input_path, "w") as input_file:
            shutil.copyfileobj(smt_file, input_file)

        log_path = dir_path / "z3.log"
        args = [
            Metadata.default().z3,
            "trace=true",
            "proof=true",
            f"trace_file_name={log_path}",
            str(input_path),
        ]
        if not with_proof:
            args.remove("proof=true")

        subprocess.run(
            args,
            capture_output=True,
            text=True,
        )

        # shutil.copyfile(log_path, "myz3.log")

        instances_path = dir_path / "instances.txt"

        subprocess.run(
            [
                Metadata.default().z3tracer,
                "--skip-z3-version-check",
                "--skip-log-consistency-checks",
                "--instantiation-tree",
                str(instances_path),
                str(log_path),
            ],
            capture_output=True,
            text=True,
        )

        return Forest.parse(instances_path.read_text().splitlines())


def count_qids(instances: Forest) -> List[Tuple[str, int]]:
    qids: Dict[str, int] = {}
    for node in instances.nodes.values():
        qids.setdefault(node.qid, 0)
        qids[node.qid] += 1

    return sorted(qids.items(), key=lambda item: item[1])
