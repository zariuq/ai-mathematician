"""Project optional source positions before the pinned Python algorithms.

Only the export envelope changes. Term/proof trees and all oracle algorithms
remain untouched, including declaration ordering and feature extraction.
"""

ARITIES = {"PARAM": 5, "AXIOM": 5, "DEF": 6, "PRIM": 5, "THM": 6, "PROOF": 3}


def accept_source_positions(library):
    if getattr(library, "_cetta_source_positions", False):
        return
    parse = library.parse_toplevel_forms

    def positioned_forms(text):
        forms = parse(text)
        result = []
        for form in forms:
            arity = ARITIES.get(form[0]) if isinstance(form, list) and form else None
            if arity is not None and len(form) == arity + 1:
                line = form[-1]
                if not isinstance(line, str) or not line.isascii() or not line.isdecimal():
                    raise ValueError(f"invalid source line: {line!r}")
                form = form[:-1]
            result.append(form)
        return result

    library.parse_toplevel_forms = positioned_forms
    library._cetta_source_positions = True
