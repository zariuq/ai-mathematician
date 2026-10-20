"""Materialize pinned Python references for development comparisons only."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PYTHON_V4 = "5e73833790d43d066f72be1548be2ee0fcab192d"
UPSTREAM_V7 = "2a2be8d856d2d267fb49230ddd237f252d869cbe"
SOURCES = ("library.py", "sexpr_translate.py", "search.py", "atp.py",
           "itp.py", "prover.py", "induction.py", "llm.py")


def oracle_directory(revision=PYTHON_V4):
    """Keep an historical oracle unchanged when the application tracks upstream.

    The cache contains source files, not another checkout or runtime dependency.
    Missing history is an explicit development-setup failure. Original relative
    library/tool paths resolve to the same fixtures used by the comparison.
    """
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("an oracle revision must be a complete commit digest")
    cache = ROOT / ".cetta/python-oracles" / revision
    directory = cache / "phase1"
    directory.mkdir(parents=True, exist_ok=True)
    sources = SOURCES + (("smt_bridge.py",) if revision == UPSTREAM_V7 else ())
    for name in sources:
        ran = subprocess.run(["git", "-C", str(ROOT), "show",
                              f"{revision}:phase1/{name}"], capture_output=True, check=False)
        if ran.returncode:
            raise RuntimeError(f"missing pinned Python oracle {revision}:{name}; "
                               "fetch the reference commit before running comparisons")
        destination = directory / name
        if not destination.exists() or destination.read_bytes() != ran.stdout:
            destination.write_bytes(ran.stdout)
    for name in ("lib", "tools"):
        destination = cache / name
        if not destination.is_symlink():
            if destination.exists():
                raise RuntimeError(f"oracle fixture path is not a link: {destination}")
            destination.symlink_to(ROOT / name, target_is_directory=True)
        if destination.resolve() != (ROOT / name).resolve():
            raise RuntimeError(f"oracle fixture link has a different target: {destination}")
    return directory
