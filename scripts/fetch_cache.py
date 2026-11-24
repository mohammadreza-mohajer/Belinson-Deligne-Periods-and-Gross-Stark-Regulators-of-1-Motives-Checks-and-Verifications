"""Fetch only the mathlib modules imported by this companion and their dependencies."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
modules = sorted({m for path in (root/"BD").glob("*.lean")
                  for m in re.findall(r"^import (Mathlib\.[\w.]+)$",path.read_text(encoding="utf-8"),re.M)})
subprocess.run(["lake","exe","cache","get",*modules],cwd=root,check=True)

