#!/usr/bin/env python3
"""Update the benchmark build-configuration stamp when flags change."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile


SCRIPT_DIRECTORY = Path(__file__).resolve().parent
QD_IMPLEMENTATION_HEADERS = (
    "dd_real.h",
    "dd_inline.h",
    "inline.h",
    "qd_config.h",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--dd-cc", required=True)
    parser.add_argument("--dd-cflags", required=True)
    parser.add_argument("--clang-cc", required=True)
    parser.add_argument("--clang-cflags", required=True)
    parser.add_argument("--cxx", required=True)
    parser.add_argument("--cxxflags", required=True)
    parser.add_argument("--strict-fp-flags", required=True)
    parser.add_argument("--qd-prefix", required=True)
    parser.add_argument("--mpfr-cflags", required=True)
    parser.add_argument("--mpfr-libs", required=True)
    return parser.parse_args()


def file_identity(path: Path) -> dict[str, object]:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": digest.hexdigest(),
    }


def tool_identity(command: str, version_flag: str) -> dict[str, object]:
    words = shlex.split(command)
    if not words:
        return {"command": command, "error": "empty command"}
    executable = shutil.which(words[0])
    if executable is None:
        return {"command": command, "error": "executable not found"}
    path = Path(executable).resolve()
    record = {"command": command, **file_identity(path)}
    try:
        completed = subprocess.run(
            words + [version_flag], check=False, timeout=10,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace")
        record["version"] = completed.stdout.strip()[:8000]
        record["version_exit_code"] = completed.returncode
    except (OSError, subprocess.SubprocessError) as error:
        record["version_error"] = str(error)
    return record


def qd_identity(prefix: str) -> dict[str, object]:
    root = Path(prefix)
    headers = [
        file_identity(root / "include" / "qd" / name)
        for name in QD_IMPLEMENTATION_HEADERS
    ]
    return {
        "headers": headers,
        "policy": file_identity(SCRIPT_DIRECTORY / "qd_evaluation.hpp"),
    }


def main() -> int:
    args = parse_args()
    config = {
        "config_schema_version": 3,
        "clang_cc": args.clang_cc,
        "clang_cflags": args.clang_cflags,
        "cxx": args.cxx,
        "cxxflags": args.cxxflags,
        "dd_cc": args.dd_cc,
        "dd_cflags": args.dd_cflags,
        "mpfr_cflags": args.mpfr_cflags,
        "mpfr_libs": args.mpfr_libs,
        "qd_prefix": args.qd_prefix,
        "strict_fp_flags": args.strict_fp_flags,
        "tool_identities": {
            "clang_cc": tool_identity(args.clang_cc, "--version"),
            "cxx": tool_identity(args.cxx, "--version"),
            "dd_cc": tool_identity(args.dd_cc, "-version"),
            "qd": qd_identity(args.qd_prefix),
        },
    }
    content = json.dumps(config, indent=2, sort_keys=True) + "\n"

    output = args.output
    if output.exists() and output.read_text(encoding="utf-8") == content:
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    temporary_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=output.parent,
            prefix=f".{output.name}.",
            delete=False,
        ) as temporary:
            temporary.write(content)
            temporary.flush()
            os.fsync(temporary.fileno())
            temporary_name = temporary.name
        os.replace(temporary_name, output)
        temporary_name = None
    finally:
        if temporary_name is not None:
            Path(temporary_name).unlink(missing_ok=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
