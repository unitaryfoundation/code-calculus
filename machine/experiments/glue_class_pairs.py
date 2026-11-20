#!/usr/bin/env python3
"""Re-export of the consumer helper.

The implementation lives in ``machine.glue_class_pairs``; this shim keeps the
experiment import path working.
"""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from machine.glue_class_pairs import *  # noqa: F401,F403

if __name__ == "__main__":
    raise SystemExit(main())
