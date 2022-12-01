import io
import re
import shutil
import subprocess
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator, List, TextIO, Tuple

import z3
from pysmt.smtlib.parser import Tokenizer

from qifac.parsing.instantiation_tree import Forest

from ..instances import show
from ..instances.instantiate import instantiate
from ..metadata import Metadata
from ..smt import dedup, filter_names, name, pysmt_prettify, skolemize
from ..smt.booleanize import booleanize
from ..z3_utils import run_z3


@contextmanager
def core_names(smt_file: TextIO) -> Iterator[Tuple[Path, List[str]]]:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        named_path = dir_path / "named.smt2"
        with open(input_path, "r") as input_smt, open(named_path, "w") as named_smt:
            shutil.copyfileobj(name(input_smt), named_smt)

        result = subprocess.run(
            [Metadata.default().z3, named_path], capture_output=True, text=True
        ).stdout

        if "unsat" not in result.splitlines()[0]:
            print("Not unsat")
            exit(-1)

        names_buffer = io.StringIO(result.splitlines()[-1])
        names = list(Tokenizer(names_buffer).generator)[1:-1]

        yield named_path, names


def find(smt_file: TextIO) -> TextIO:
    with core_names(smt_file) as (named_path, names):
        with open(named_path, "r") as named_smt:
            return filter_names(named_smt, names)


def instances(smt_file: TextIO) -> Forest:
    # assume skolemized?

    skolemized = skolemize(smt_file)
    pretty = pysmt_prettify(skolemized)
    deduped = dedup(pretty)

    # core_skolemized = find(deduped)

    core_skolemized = deduped

    all_instances = show(core_skolemized, with_proof=True)

    core_skolemized.seek(0)

    instantiated = instantiate(core_skolemized, all_instances)

    # cleaned = clean_errors(instantiated)

    # booleanized = booleanize(cleaned)
    booleanized = booleanize(instantiated)

    if run_z3(booleanized) != "unsat":
        print("Booleanized is not unsat")
        return Forest()

    booleanized.seek(0)

    nodes = set()

    with core_names(booleanized) as (path, names):
        for clause in names:
            match = re.match(r"(0x[^-]+)-", clause)
            if match is not None:
                ident = match[1]
                nodes.add(ident)

        with open("fully-instantiated.smt2", "w") as file, open(path, "r") as named_smt:
            shutil.copyfileobj(filter_names(named_smt, names), file)

    return all_instances.filter(nodes)


def find_core_with_api(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    # set options according to dafny generated smt2 files
    smt2_prelude = """
    (set-option :print-success false)
    (set-info :smt-lib-version |2.6|)
    (set-option :auto_config false)
    (set-option :type_check true)
    (set-option :smt.case_split 3)
    (set-option :smt.qi.eager_threshold 100)
    (set-option :smt.delay_units true)
    (set-option :smt.arith.solver 2)
    (set-option :smt.arith.nl false)
    (set-option :smt.mbqi false)
    (set-option :model.compact false)
    (set-option :model.v2 true)
    (set-option :pp.bv_literals false)
    """
    z3.set_param("auto_config", False)
    z3.set_param("type_check", True)
    z3.set_param("smt.case_split", 3)
    z3.set_param("smt.qi.eager_threshold", 100)
    z3.set_param("smt.delay_units", True)
    z3.set_param("smt.arith.solver", 2)
    z3.set_param("smt.arith.nl", False)
    z3.set_param("smt.mbqi", False)
    z3.set_param("model.compact", False)
    z3.set_param("model.v2", True)
    z3.set_param("pp.bv_literals", False)

    s = z3.Solver()
    smt_file_string = smt_file.read()
    s.from_string(smt_file_string)
    res = s.check()
    print(f"original file: {res}")
    if res == z3.unknown:
        print(f"    {s.reason_unknown()}")
    elif res == z3.unsat:
        assertions = s.assertions()
        s = z3.Solver()
        bools = [z3.Bool(f"__qifac___flag_{i}") for i in range(len(assertions))]
        s.add(*(z3.Implies(b, a) for a, b in zip(assertions, bools)))
        res = s.check(*bools)
        print(f"    with indicator variabes: {res}")
        if res == z3.unknown:
            print(f"        {s.reason_unknown()}")
        elif res == z3.unsat:
            unsat_core = list(s.unsat_core())
            ii = [int(str(b).split("_")[-1]) for b in unsat_core]
            unsat_core_assertions = [assertions[i] for i in ii]
            print(f"    found unsat core with {len(unsat_core_assertions)} assertions")
            s = z3.Solver()
            s.add(*unsat_core_assertions)
            res = s.check()
            print(
                f"    checking these {len(unsat_core_assertions)} assertions with a new solver: {res}"
            )
            if res == z3.unsat:
                print(f"    OK")
            elif res == z3.unknown:
                print(f"        {s.reason_unknown()}")

            # open(fn + '.qifac_unsat_core_to_smt2.smt2', 'w').write(smt2_prelude + s.to_smt2())
            # open(fn + '.qifac_unsat_core.dat', 'w').write(repr(ii))

            unsat_core_set = set(ii)
            lines = smt_file_string.splitlines()
            n = -1
            for i in range(len(lines)):
                if lines[i].startswith("(assert "):
                    n += 1
                    if n not in unsat_core_set:
                        lines[i] = "; not in unsat core; " + lines[i]
            buffer.write("\n".join(lines))

            buffer.seek(0)

    return buffer
