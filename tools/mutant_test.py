#!/usr/bin/env python3
"""Run one unittest test (a dotted name, importable from the current directory) and print how it ended, as one JSON
object: {"outcomes": [[kind, message], ...]}, one per failure or error, where the kind is

- `kill`: an assertion failed (an expected exception not raised, values that differ, ...);
- `wording`: assertRaises*/assertRaisesRegex met the expected exception, and only its message did not match: the
  input is still refused, so nothing a test can see was lost (recognised where the check happens, not from text, so
  a message of several lines or a custom `msg` changes nothing);
- `twin`: a TwinDivergence (the rules kernel and its Python twin disagree);
- `crash`: any other error, which proves nothing.

Used by tools/run_mutants.py.

    python3 tools/mutant_test.py test_vars1.TestVars1Conformance.test_81_...
"""
from __future__ import annotations

import json
import os
import sys
import unittest
import unittest.case


class Wording(AssertionError):
    """The expected exception was raised; only its message differs from the pattern."""


_exit = unittest.case._AssertRaisesContext.__exit__


def _exit_marking_wording(self, exc_type, exc_value, tb):  # type: ignore[no-untyped-def]
    raised = exc_type is not None and issubclass(exc_type, self.expected)
    try:
        return _exit(self, exc_type, exc_value, tb)
    except self.test_case.failureException as e:
        if raised:  # the only failure left once the exception matched is its message
            raise Wording(str(e)) from None
        raise


unittest.case._AssertRaisesContext.__exit__ = _exit_marking_wording  # type: ignore[method-assign]


class Result(unittest.TestResult):
    def __init__(self) -> None:
        super().__init__()
        self.outcomes: list[tuple[str, str]] = []

    def _record(self, err) -> None:  # type: ignore[no-untyped-def]
        kind, value = err[0], err[1]
        if issubclass(kind, Wording):
            self.outcomes.append(("wording", str(value)))
        elif issubclass(kind, AssertionError):
            self.outcomes.append(("kill", str(value)))
        elif kind.__name__ == "TwinDivergence":
            self.outcomes.append(("twin", str(value)))
        else:
            self.outcomes.append(("crash", f"{kind.__name__}: {value}"))

    def addFailure(self, test, err):  # type: ignore[no-untyped-def]
        super().addFailure(test, err)
        self._record(err)

    def addError(self, test, err):  # type: ignore[no-untyped-def]
        super().addError(test, err)
        self._record(err)

    def addSubTest(self, test, subtest, err):  # type: ignore[no-untyped-def]
        super().addSubTest(test, subtest, err)
        if err is not None:
            self._record(err)


def main(argv: list[str]) -> int:
    sys.path.insert(0, os.getcwd())
    result = Result()
    unittest.defaultTestLoader.loadTestsFromName(argv[0]).run(result)
    print(json.dumps({"outcomes": [[k, m] for k, m in result.outcomes]}))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
