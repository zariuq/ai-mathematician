"""Every library declaration's signature as Lean prints it, tidied for a
prompt: one line, bound variables renamed a b c ..., `set` for
`Megalodon.set`.

Why: in v8, with all the lemmas a human proof needs already in the prompt,
the model still failed about half the time, and the commonest error was
"Application type mismatch": the right lemma with its arguments in the
wrong order. The library's own text for a lemma is deeply nested
(`(forall x31928 : set, (forall x31929 : set, ((SNo x31928) -> ...`);
Lean's `#check` shows the same statement with the argument order plain:
`mul_SNo_distrL : ∀ (a b c : set), SNo a → SNo b → SNo c → ...`.

Built once (one Lean run) and cached in results/lean_sigs.json.
"""
import json
import os
import re
import subprocess
import tempfile

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
CACHE = os.path.join(ROOT, "results", "lean_sigs.json")
_LETTERS = [c for c in "abcdefghijklmnopqrstuvwxyz"] + [f"x{i}" for i in range(1, 60)]


def tidy(sig):
    s = " ".join(sig.split())
    s = s.replace("Megalodon.", "")
    names = []
    for v in re.findall(r"\bx\d{3,}\b", s):
        if v not in names:
            names.append(v)
    for i, v in enumerate(names):
        s = re.sub(rf"\b{v}\b", _LETTERS[i] if i < len(_LETTERS) else f"v{i}", s)
    return s


def build(names):
    from itp import LEAN, LIB
    src = ("import Bridge\nset_option pp.fieldNotation false\nopen Megalodon\n"
           + "".join(f"#check @{n}\n" for n in names))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir="/tmp") as fh:
        fh.write(src)
        path = fh.name
    try:
        out = subprocess.run([LEAN, path], capture_output=True, text=True,
                             env={**os.environ, "LEAN_PATH": LIB}, timeout=1800).stdout
    finally:
        os.unlink(path)
    sigs, cur = {}, None
    for line in out.splitlines():
        m = re.match(r"^([\w'.]+) : (.*)$", line)
        if m and not line.startswith(" "):
            cur = m.group(1).split(".")[-1]
            sigs[cur] = m.group(2)
        elif cur and line.startswith(" "):
            sigs[cur] += " " + line.strip()
    return {n: tidy(s) for n, s in sigs.items()}


_sigs = None


def get():
    global _sigs
    if _sigs is None:
        _sigs = json.load(open(CACHE)) if os.path.exists(CACHE) else {}
    return _sigs


if __name__ == "__main__":
    from library import load
    decls = load(os.path.join(ROOT, "data", "corpus.sexpr"))
    names = [d.name for d in decls if d.kind in ("THM", "AXIOM")]
    sigs = build(names)
    json.dump(sigs, open(CACHE, "w"), indent=0)
    print(f"{len(sigs)}/{len(names)} signatures -> {CACHE}")
    for n in ["mul_SNo_distrL", "SNoLt_tra", "nat_ind"]:
        print(" ", n, ":", sigs.get(n))
