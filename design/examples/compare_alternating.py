#!/usr/bin/env python3
"""Report source sizes for the alternating-group experiment; do not time proofs.

The proof-body measure counts nonblank lines in the current formatting.
Shared definitions, mathematical lemmas, and pattern-specific relations are
reported separately so moving work to helpers does not count as a saving.
"""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "ordinary Lean": ROOT / "lean/DesignExamples/Alternating.lean",
    "proposed patterns": ROOT / "pmop/DesignExamples/Alternating.pmop",
    "manual Lean elaboration": ROOT / "lean/DesignExamples/PatternStyle/Alternating.lean",
}


def code_lines(text: str) -> int:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return sum(bool(line.split("--", 1)[0].strip()) for line in text.splitlines())


def declaration(text: str, name: str) -> tuple[str, str]:
    text = text.split(f"theorem {name} ", 1)[1].split("\n\n", 1)[0]
    statement, separator, body = text.partition(":= by\n")
    if not separator:
        raise ValueError(f"Cannot locate the proof body of {name}")
    return " ".join(statement.split()), body


if __name__ == "__main__":
    expected_statement = None
    for label, path in SOURCES.items():
        text = path.read_text()
        statement, body = declaration(text, "contains_three")
        if expected_statement is None:
            expected_statement = statement
        elif statement != expected_statement:
            raise SystemExit(f"The theorem statement differs: {path}")
        print(f"{label}: contains_three body = {code_lines(body)} lines; "
              f"module = {code_lines(text)} lines")
    for name in ("Common", "Coverage", "Reductions", "Patterns"):
        path = ROOT / f"lean/DesignExamples/Alternating/{name}.lean"
        print(f"{name}: {code_lines(path.read_text())} lines")
    for name in ("alternating_simple", "a5_simple"):
        statements = {
            " ".join(path.read_text().split(f"theorem {name} ", 1)[1]
                     .split(":=", 1)[0].split())
            for path in SOURCES.values()
        }
        if len(statements) != 1:
            raise SystemExit(f"The theorem statement differs: {name}")
    print("All three versions have the same theorem statements. Counts depend on formatting.")
