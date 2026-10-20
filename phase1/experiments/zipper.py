"""Zipperposition as a second ATP, for the goals Vampire cannot reach.

Vampire finds a proof for 680 of the 999 goals; on the other 319 it times
out, and that -- not Lean's reconstruction, which succeeds on 91% of what it
is handed -- is the pipeline's dominant failure. Vampire's higher-order
support is much newer than its first-order support, and this corpus is
higher-order throughout.

Zipperposition is the leading higher-order superposition prover (it has won
the CASC THF division repeatedly), so it fails differently. It reads the same
THF problem `atp.THF` already emits, and names the axioms it used directly in
its TPTP proof output, so the premise set comes back in the same shape
`run_vampire` returns.
"""
import os
import re
import subprocess
import tempfile

ZIPPER = os.environ.get(
    "ZIPPERPOSITION",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                 "tools", "zipperposition", "zipperposition.exe"))

# in the TPTP proof, an input axiom appears as `thf(c_add_nat_0R, axiom, ...)`
# while derived clauses are `zip_derived_cl<N>`
_AXIOM = re.compile(r"^(?:thf|tff|fof|cnf)\(\s*(c_\w+)\s*,\s*axiom\s*,", re.M)


def run_zipperposition(problem_text, timeout=30, mode=None):
    """(status, used_axiom_ids) -- same contract as atp.run_vampire."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as fh:
        fh.write(problem_text)
        path = fh.name
    try:
        # the default configuration is much weaker than the higher-order
        # modes the prover ships for the CASC THF division
        cmd = [ZIPPER, "--input", "tptp", "--output", "tptp",
               "--timeout", str(timeout)]
        if mode:
            cmd += ["--mode", mode]
        out = subprocess.run(
            cmd + [path],
            capture_output=True, text=True, timeout=timeout + 20).stdout
    except subprocess.TimeoutExpired:
        return "Timeout", set()
    except FileNotFoundError:
        return "NoBinary", set()
    finally:
        os.unlink(path)
    m = re.search(r"SZS status (\w+)", out)
    status = m.group(1) if m else "Unknown"
    if status not in ("Theorem", "Unsatisfiable", "ContradictoryAxioms"):
        return status, set()
    return "Theorem", set(_AXIOM.findall(out))
