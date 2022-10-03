import re
from enum import Enum, auto

from qifac.metadata import Metadata


class Category(Enum):
    PRELUDE = auto()
    UNKNOWN = auto()
    FUN_TYPE = auto()
    BUILTIN = auto()
    LIB = auto()
    USER = auto()
    SAME_FILE = auto()

    @classmethod
    def parse(cls, qid: str, filename: str) -> "Category":
        for lib_qid in Metadata.default().lib_qids:
            if f"{lib_qid}idfy" in qid:
                return Category.LIB

        if "Preludebpl" in qid:
            return Category.PRELUDE
        elif "unknown." in qid:
            return Category.UNKNOWN
        elif "funType:" in qid:
            return Category.FUN_TYPE
        elif cls.clean_qid(filename) in qid:
            return Category.SAME_FILE
        elif re.search(r"\.\d+:\d+", qid) is not None:
            return Category.USER
        else:
            return Category.BUILTIN

    @classmethod
    def clean_qid(cls, filename: str) -> str:
        return filename.split(".i.dfy")[0].split("-")[-1] + "idfy"
