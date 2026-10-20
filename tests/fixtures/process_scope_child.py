"""A lifecycle fixture whose child deliberately leaves its parent's group."""
import os
from pathlib import Path
import signal
import sys

directory = Path(sys.argv[1])
child = os.fork()
if child == 0:
    os.setsid()
    (directory / "child-ready").write_text("ready\n")
else:
    (directory / "parent-ready").write_text("ready\n")
while True:
    signal.pause()
