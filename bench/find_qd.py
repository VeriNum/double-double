#!/usr/bin/env python3
"""Locate the QD headers used by the evaluation harness."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
from typing import Iterable, Optional, Sequence, Tuple


SCRIPT_DIRECTORY = Path(__file__).resolve().parent
CONVENTIONAL_PREFIXES = (
    Path("/opt/homebrew/opt/qd"),
    Path("/usr/local/opt/qd"),
    Path("/usr/local"),
    Path("/usr"),
)
REQUIRED_HEADERS = (
    Path("include/qd/dd_real.h"),
    Path("include/qd/dd_inline.h"),
    Path("include/qd/inline.h"),
    Path("include/qd/qd_config.h"),
)


def canonical_path(value: str | os.PathLike[str]) -> Path:
    """Return an absolute path with symlinks and ``~`` resolved."""

    return Path(value).expanduser().resolve()


def validate_prefix(value: str | os.PathLike[str]) -> Tuple[Path, Tuple[str, ...]]:
    """Check that a prefix contains QD's double-double implementation headers."""

    prefix = canonical_path(value)
    if not prefix.is_dir():
        return prefix, ("directory does not exist",)

    problems = [
        "missing {}".format(relative)
        for relative in REQUIRED_HEADERS
        if not (prefix / relative).is_file()
    ]

    return prefix, tuple(problems)


def prefix_from_qd_config(command: str) -> Tuple[Optional[Path], Optional[str]]:
    """Run ``qd-config --prefix`` without invoking a shell."""

    command_path = Path(command).expanduser()
    if command_path.is_file():
        words = [str(command_path)]
    else:
        try:
            words = shlex.split(command)
        except ValueError as error:
            return None, "cannot parse qd-config command: {}".format(error)
    if not words:
        return None, "qd-config command is empty"

    executable = shutil.which(words[0])
    if executable is None:
        return None, "qd-config executable not found: {}".format(words[0])
    words[0] = executable

    try:
        completed = subprocess.run(
            words + ["--prefix"],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError) as error:
        return None, "cannot run qd-config: {}".format(error)

    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        suffix = ": {}".format(detail) if detail else ""
        return None, "qd-config --prefix exited with status {}{}".format(
            completed.returncode, suffix
        )

    lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    if len(lines) != 1:
        return None, "qd-config --prefix did not print exactly one prefix"
    return canonical_path(lines[0]), None


def _add_candidate(
    candidates: list[Tuple[str, Path]],
    seen: set[Path],
    source: str,
    value: str | os.PathLike[str],
) -> None:
    prefix = canonical_path(value)
    if prefix not in seen:
        seen.add(prefix)
        candidates.append((source, prefix))


def discover(
    *,
    artifact_root: Path = SCRIPT_DIRECTORY,
    search_path: Optional[str] = None,
    conventional_prefixes: Iterable[Path] = CONVENTIONAL_PREFIXES,
) -> Tuple[Optional[Path], Tuple[Tuple[str, Optional[Path], Tuple[str, ...]], ...]]:
    """Try automatic candidates in a deterministic order.

    The second result records each rejected candidate for diagnostics.
    """

    if search_path is None:
        search_path = os.environ.get("PATH", os.defpath)

    candidates: list[Tuple[str, Path]] = []
    rejected: list[Tuple[str, Optional[Path], Tuple[str, ...]]] = []
    seen: set[Path] = set()

    _add_candidate(
        candidates,
        seen,
        "artifact-local third_party/qd",
        artifact_root / "third_party" / "qd",
    )
    qd_config = shutil.which("qd-config", path=search_path)
    if qd_config is not None:
        prefix, error = prefix_from_qd_config(qd_config)
        if error is not None:
            rejected.append(("PATH qd-config", None, (error,)))
        elif prefix is not None:
            _add_candidate(candidates, seen, "PATH qd-config", prefix)

    for conventional in conventional_prefixes:
        _add_candidate(candidates, seen, "conventional prefix", conventional)

    for source, prefix in candidates:
        canonical, problems = validate_prefix(prefix)
        if not problems:
            return canonical, tuple(rejected)
        rejected.append((source, canonical, problems))

    return None, tuple(rejected)


def _print_requirements() -> None:
    print(
        "Required QD headers: include/qd/dd_real.h, dd_inline.h, inline.h, "
        "and qd_config.h.",
        file=sys.stderr,
    )
    print(
        "Set QD_PREFIX to the installation prefix, set QD_CONFIG to its "
        "qd-config executable, or pass the corresponding command-line option.",
        file=sys.stderr,
    )


def _report_invalid(source: str, prefix: Path, problems: Sequence[str]) -> None:
    print(
        "find_qd: {} is not a usable QD header installation: {}".format(
            source, prefix
        ),
        file=sys.stderr,
    )
    for problem in problems:
        print("  - {}".format(problem), file=sys.stderr)
    _print_requirements()


def argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--prefix-only",
        action="store_true",
        help="print only the canonical prefix on success",
    )
    explicit = parser.add_mutually_exclusive_group()
    explicit.add_argument(
        "--prefix",
        metavar="PREFIX",
        help="validate this QD installation only",
    )
    explicit.add_argument(
        "--qd-config",
        metavar="COMMAND",
        help="validate only the prefix reported by this qd-config command",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = argument_parser().parse_args(argv)

    if args.prefix is not None:
        prefix, problems = validate_prefix(args.prefix)
        if problems:
            _report_invalid("--prefix", prefix, problems)
            return 1
    elif args.qd_config is not None:
        prefix, error = prefix_from_qd_config(args.qd_config)
        if error is not None or prefix is None:
            print("find_qd: {}".format(error), file=sys.stderr)
            _print_requirements()
            return 1
        prefix, problems = validate_prefix(prefix)
        if problems:
            _report_invalid("--qd-config", prefix, problems)
            return 1
    else:
        prefix, rejected = discover()
        if prefix is None:
            print(
                "find_qd: no usable QD header installation was found.",
                file=sys.stderr,
            )
            for source, candidate, problems in rejected:
                location = " ({})".format(candidate) if candidate is not None else ""
                print("  {}{}: {}".format(source, location, "; ".join(problems)),
                      file=sys.stderr)
            _print_requirements()
            return 1

    # The Makefile consumes stdout, so it remains machine-readable in every mode.
    print(prefix)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
