#!/usr/bin/env python3
"""Format benchmark analysis TSV files as LaTeX table rows."""

import csv
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from pathlib import Path
import os
import sys


OPERATIONS = (
    "two_sum",
    "fast_2sum",
    "fast_2mult",
    "dw_plus_fp",
    "dw_times_fp",
    "dw_div_fp",
    "dw_plus_dw",
    "dw_times_dw",
    "dw_div_dw",
)

COMPOSITE_OPERATIONS = OPERATIONS[3:]
ABSOLUTE_OPERATIONS = (
    "dw_times_fp",
    "dw_div_fp",
    "dw_times_dw",
    "dw_div_dw",
)

LABELS = {
    "two_sum": r"\textsc{TwoSum}",
    "fast_2sum": r"\textsc{Fast2Sum}",
    "fast_2mult": r"\textsc{Fast2Mult}",
    "dw_plus_fp": r"\textsc{DWPlusFP}",
    "dw_times_fp": r"\textsc{DWTimesFP}",
    "dw_div_fp": r"\textsc{DWDivFP}",
    "dw_plus_dw": r"\textsc{DWPlusDW}",
    "dw_times_dw": r"\textsc{DWTimesDW}",
    "dw_div_dw": r"\textsc{DWDivDW}",
}

RQ1_COLUMNS = {
    "operation",
    "implementation",
    "regime",
    "eligible_cases",
    "regime_cases",
    "finite_bound_ratio_mean",
    "finite_bound_ratio_max",
}

RQ2_COLUMNS = {
    "operation",
    "wrapper",
    "criterion",
    "rejected_cases",
    "qd_nonfinite",
    "qd_passed",
}

RQ3_COLUMNS = {
    "build",
    "operation",
    "measure",
    "input_count",
    "sample_count",
    "median",
    "iqr",
}

EM_DASH = r"\textemdash{}"


class FormatError(RuntimeError):
    pass


def read_table(path, key_columns, required_columns):
    try:
        file = path.open("r", encoding="utf-8", newline="")
    except OSError as error:
        raise FormatError(f"could not open {path}: {error}") from error

    with file:
        reader = csv.DictReader(file, delimiter="\t")
        if reader.fieldnames is None:
            raise FormatError(f"{path}: header is missing")
        if len(reader.fieldnames) != len(set(reader.fieldnames)):
            raise FormatError(f"{path}: header has a repeated column")
        missing = required_columns.difference(reader.fieldnames)
        if missing:
            names = ", ".join(sorted(missing))
            raise FormatError(f"{path}: required columns are missing: {names}")

        rows = {}
        for line_number, row in enumerate(reader, start=2):
            if None in row:
                raise FormatError(f"{path}:{line_number}: row has extra fields")
            key = tuple(row[name] for name in key_columns)
            if key in rows:
                raise FormatError(f"{path}:{line_number}: row is repeated: {key}")
            rows[key] = row
    return rows


def require_row(rows, key, path):
    try:
        return rows[key]
    except KeyError as error:
        raise FormatError(f"{path}: required row is missing: {key}") from error


def count(row, column):
    text = row[column]
    if not text.isdigit():
        raise FormatError(f"{column} is not a nonnegative integer: {text}")
    return int(text)


def number(row, column):
    text = row[column]
    if text == "-":
        raise FormatError(f"{column} has no value in a required row")
    try:
        value = Decimal(text)
    except InvalidOperation as error:
        raise FormatError(f"{column} is not a number: {text}") from error
    if not value.is_finite():
        raise FormatError(f"{column} is not finite: {text}")
    return value


def fixed(value, places):
    quantum = Decimal(1).scaleb(-places)
    rounded = value.quantize(quantum, rounding=ROUND_HALF_EVEN)
    return f"{rounded:.{places}f}"


def significant(value, digits=2):
    if value == 0:
        return "0"
    quantum = Decimal(1).scaleb(value.copy_abs().adjusted() - digits + 1)
    rounded = value.quantize(quantum, rounding=ROUND_HALF_EVEN)
    return format(rounded, "f")


def percentage(part, whole, places=2):
    if whole == 0:
        return EM_DASH
    value = Decimal(part) * Decimal(100) / Decimal(whole)
    return fixed(value, places) + r"\%"


def integer(value):
    return f"{value:,}".replace(",", "{,}")


def latex_row(*cells):
    return " & ".join(cells) + r" \\"


def rq1_rows(rows, path, regime, operations):
    result = ["% Generated from rq1.tsv; do not edit."]
    for operation in operations:
        fencedd = require_row(rows, (operation, "fenceDD", regime), path)
        qd = require_row(rows, (operation, "qd", regime), path)
        if (fencedd["eligible_cases"] != qd["eligible_cases"]
                or fencedd["regime_cases"] != qd["regime_cases"]):
            raise FormatError(
                f"{path}: FenceDD and QD populations differ for {operation} {regime}"
            )
        eligible = count(fencedd, "eligible_cases")
        regime_count = count(fencedd, "regime_cases")
        result.append(latex_row(
            LABELS[operation],
            percentage(regime_count, eligible),
            fixed(number(fencedd, "finite_bound_ratio_mean"), 4),
            fixed(number(fencedd, "finite_bound_ratio_max"), 4),
            fixed(number(qd, "finite_bound_ratio_mean"), 4),
            fixed(number(qd, "finite_bound_ratio_max"), 4),
        ))
    return "\n".join(result) + "\n"


def rq2_percentage(row, column):
    return percentage(count(row, column), count(row, "rejected_cases"))


def rq2_composite_rows(rows, path):
    result = ["% Generated from rq2.tsv; do not edit."]
    selected = {}
    for operation in COMPOSITE_OPERATIONS:
        for wrapper in ("default", "strong"):
            row = require_row(rows, (operation, wrapper), path)
            if row["criterion"] != "error_bound":
                raise FormatError(f"{path}: bad criterion for {operation} {wrapper}")
            selected[(operation, wrapper)] = row

    for wrapper, label in (("default", "Default"),
                           ("strong", "Alternative")):
        wrapper_rows = [
            selected[(operation, wrapper)]
            for operation in COMPOSITE_OPERATIONS
        ]
        rejected = sum(count(row, "rejected_cases") for row in wrapper_rows)
        nonfinite = sum(count(row, "qd_nonfinite") for row in wrapper_rows)
        passed = sum(count(row, "qd_passed") for row in wrapper_rows)
        result.append(latex_row(
            "All operations",
            label,
            integer(rejected),
            percentage(nonfinite, rejected, 1),
            percentage(passed, rejected, 1),
        ))

    result.append(r"\midrule")
    for operation in COMPOSITE_OPERATIONS:
        for wrapper, label in (("default", "Default"),
                               ("strong", "Alternative")):
            row = selected[(operation, wrapper)]
            result.append(latex_row(
                LABELS[operation],
                label,
                integer(count(row, "rejected_cases")),
                rq2_percentage(row, "qd_nonfinite"),
                rq2_percentage(row, "qd_passed"),
            ))
    return "\n".join(result) + "\n"


def rq2_transformation_rows(rows, path):
    result = ["% Generated from rq2.tsv; do not edit."]
    for operation in OPERATIONS[:3]:
        row = require_row(rows, (operation, "default"), path)
        if row["criterion"] != "exact_reconstruction":
            raise FormatError(f"{path}: bad criterion for {operation}")
        result.append(latex_row(
            LABELS[operation],
            EM_DASH,
            integer(count(row, "rejected_cases")),
            rq2_percentage(row, "qd_nonfinite"),
            rq2_percentage(row, "qd_passed"),
        ))
    return "\n".join(result) + "\n"


def timing_cell(rows, path, build, operation, measure):
    row = require_row(rows, (build, operation, measure), path)
    return (
        f'{significant(number(row, "median"))} '
        f'[{significant(number(row, "iqr"))}]'
    )


def rq3_rows(rows, path, strong):
    result = ["% Generated from rq3.tsv; do not edit."]
    operations = COMPOSITE_OPERATIONS if strong else OPERATIONS
    prefix = "strong" if strong else "default"
    for index, operation in enumerate(operations):
        if not strong and index == 3:
            result.append(r"\midrule")
        result.append(latex_row(
            LABELS[operation],
            timing_cell(rows, path, "compcert", operation,
                        prefix + "_over_kernel"),
            timing_cell(rows, path, "compcert", operation,
                        prefix + "_minus_kernel_ns"),
            timing_cell(rows, path, "clang", operation,
                        prefix + "_over_qd"),
        ))
    return "\n".join(result) + "\n"


def write_outputs(output_dir, outputs):
    output_dir.mkdir(parents=True, exist_ok=True)
    for name, text in outputs.items():
        path = output_dir / name
        partial = path.with_suffix(path.suffix + ".partial")
        try:
            partial.write_text(text, encoding="utf-8")
            os.replace(partial, path)
        except OSError as error:
            raise FormatError(f"could not write {path}: {error}") from error


def generate(analysis_dir, output_dir):
    rq1_path = analysis_dir / "rq1.tsv"
    rq2_path = analysis_dir / "rq2.tsv"
    rq3_path = analysis_dir / "rq3.tsv"
    rq1 = read_table(
        rq1_path, ("operation", "implementation", "regime"), RQ1_COLUMNS
    )
    rq2 = read_table(rq2_path, ("operation", "wrapper"), RQ2_COLUMNS)
    rq3 = read_table(rq3_path, ("build", "operation", "measure"), RQ3_COLUMNS)

    # Form every file before replacing any existing output.
    outputs = {
        "rq1-relative.tex": rq1_rows(
            rq1, rq1_path, "relative", COMPOSITE_OPERATIONS
        ),
        "rq1-absolute.tex": rq1_rows(
            rq1, rq1_path, "absolute", ABSOLUTE_OPERATIONS
        ),
        "rq2-composite.tex": rq2_composite_rows(rq2, rq2_path),
        "rq2-transformations.tex": rq2_transformation_rows(rq2, rq2_path),
        "rq3-default.tex": rq3_rows(rq3, rq3_path, False),
        "rq3-strong.tex": rq3_rows(rq3, rq3_path, True),
    }
    write_outputs(output_dir, outputs)


def main():
    if len(sys.argv) != 3:
        print(
            f"usage: {sys.argv[0]} analysis-directory output-directory",
            file=sys.stderr,
        )
        return 1
    try:
        generate(Path(sys.argv[1]), Path(sys.argv[2]))
    except FormatError as error:
        print(f"paper table generation failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
