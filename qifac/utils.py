import shutil
import signal
import sys
from contextlib import contextmanager
from pathlib import Path
from types import FrameType
from typing import Callable, Iterator, Optional, TextIO

import click


class TimeoutException(Exception):
    pass


@contextmanager
def time_limit(seconds: int) -> Iterator[None]:
    def signal_handler(signum: int, frame: Optional[FrameType]) -> None:
        raise TimeoutException("Timed out!")

    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)


def find_in_parent(path: Path) -> Path:
    if path.exists():
        return path

    resolved = path.parent.resolve()

    if resolved.parent == resolved:
        return path

    return find_in_parent(resolved.parent / path.name)


def smt_file_read_write(
    parent: click.Group, fun: Callable[[TextIO], TextIO], name: Optional[str] = None
) -> None:
    if name is None:
        name = fun.__name__

    @parent.command(name=name)
    @click.argument("smt_file", type=click.File("r"), default=sys.stdin)
    @click.argument("output", type=click.File("w"), default=sys.stdout)
    def wrapper(smt_file: TextIO, output: TextIO) -> None:
        shutil.copyfileobj(fun(smt_file), output)
