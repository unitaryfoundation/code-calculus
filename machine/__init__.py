import sys

if sys.version_info < (3, 10):
    raise RuntimeError(
        "code-calculus requires Python >= 3.10 "
        "(the machine package uses int.bit_count); "
        f"found {sys.version.split()[0]}"
    )
