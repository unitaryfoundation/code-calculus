"""Executable interval consumer (compatibility shim)."""

from machine.gf2 import *  # noqa: F401,F403
from machine.state import *  # noqa: F401,F403
from machine.connectivity import *  # noqa: F401,F403
from machine.layout import *  # noqa: F401,F403
from machine.tower_prices import *  # noqa: F401,F403
from machine.intervals import *  # noqa: F401,F403
from machine.constructors import *  # noqa: F401,F403
from machine.sequence import *  # noqa: F401,F403
from machine.entrypoints import *  # noqa: F401,F403

if __name__ == "__main__":
    from machine.entrypoints import _main
    raise SystemExit(_main())
