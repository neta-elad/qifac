from typing import TextIO
from ..script import SmtLibScript

class SmtLibParser:
    def get_script(self, script: TextIO) -> SmtLibScript: ...
