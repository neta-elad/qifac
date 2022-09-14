import signal
from contextlib import contextmanager
from types import FrameType
from typing import Iterator, Optional


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
