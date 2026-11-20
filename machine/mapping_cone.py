"""Mapping-cone / chain-map constructor.

Re-exports the regression fixture in ``machine/experiments/mapping_cone.py``
and the judgment/conditional-price records.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "experiments"))

from mapping_cone import *  # noqa: F401,F403
