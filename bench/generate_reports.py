#!/usr/bin/env python3
"""Generate validated Markdown, JSON, and LaTeX reports."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from reporting import ReportError, load_evaluation_run, render_all
from reporting import write_outputs_atomically


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Validate one evaluation run and derive all report artifacts."
    )
    parser.add_argument(
        "run_dir",
        type=Path,
        help="directory containing manifest.json (or run_manifest.json) and its TSV artifacts",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="output root (default: RUN_DIR/generated)",
    )
    parser.add_argument(
        "--template",
        type=Path,
        default=Path(__file__).with_name("results_template.md"),
        help="Markdown template (default: bench/results_template.md)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="do not write; fail if any generated artifact is missing or differs",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    run_dir = args.run_dir.resolve()
    output_dir = (args.output_dir or (run_dir / "generated")).resolve()
    try:
        template = args.template.read_text(encoding="utf-8")
        run = load_evaluation_run(run_dir)
        outputs = render_all(run, template)
        drift = write_outputs_atomically(output_dir, outputs, check=args.check)
    except (OSError, ReportError) as exc:
        print(f"generate_reports: {exc}", file=sys.stderr)
        return 2
    if drift:
        for message in drift:
            print(f"generate_reports: {message}", file=sys.stderr)
        return 1
    action = "verified" if args.check else "generated"
    print(f"{action} {len(outputs)} report artifacts under {output_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
