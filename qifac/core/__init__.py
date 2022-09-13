import io
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import TextIO

from pysmt.smtlib.parser import Tokenizer

from ..instances import show
from ..instances.instantiate import instantiate
from ..metadata import Metadata
from ..smt import filter_names, name, skolemize
from ..smt.cleaner import clean_errors


def find(smt_file: TextIO) -> TextIO:
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

        names_buffer = io.StringIO(result.splitlines()[-1])
        names = list(Tokenizer(names_buffer).generator)[1:-1]

        with open(named_path, "r") as named_smt:
            return filter_names(named_smt, names)


def instances(smt_file: TextIO) -> TextIO:
    # assume skolemized?

    skolemized = skolemize(smt_file)
    all_instances = show(skolemized)

    skolemized.seek(0)

    instantiated = instantiate(skolemized, all_instances)

    cleaned = clean_errors(instantiated)

    core_instantiated = find(cleaned)

    return core_instantiated
