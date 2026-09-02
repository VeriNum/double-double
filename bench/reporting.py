#!/usr/bin/env python3
"""Parse, validate, summarize, and render evaluation result files.

The benchmark executables deliberately emit simple, versioned TSV files.  This
module treats those files as untrusted input: it checks their complete schema,
all internal count identities, the manifest checksums, and the shared RQ1/RQ2
generated-input identity before producing any report text.

Only the Python standard library is used.  RQ1 values are kept as ``Decimal``
or as their original strings so values below the binary64 range are never
rounded through a Python ``float``.
"""

from __future__ import annotations

import csv
import datetime as _datetime
import gzip
import hashlib
import json
import math
import os
import platform
import re
import statistics
import tempfile
from collections import defaultdict
from dataclasses import dataclass, field
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from typing import Callable, Dict, Iterable, Iterator, List, Mapping, Optional
from typing import Sequence, Set, TextIO, Tuple


class ReportError(ValueError):
    """Raised when an input cannot support a trustworthy report."""


EFT_OPERATIONS: Tuple[str, ...] = (
    "two_sum",
    "fast_2sum",
    "fast_2mult",
)
COMPOSITE_OPERATIONS: Tuple[str, ...] = (
    "dw_plus_fp",
    "dw_times_fp",
    "dw_div_fp",
    "dw_plus_dw",
    "dw_times_dw",
    "dw_div_dw",
)
OPERATIONS: Tuple[str, ...] = EFT_OPERATIONS + COMPOSITE_OPERATIONS
DIVISION_OPERATIONS: Tuple[str, ...] = ("dw_div_fp", "dw_div_dw")
QD_IMPLEMENTATION_HEADERS: Tuple[str, ...] = (
    "dd_real.h",
    "dd_inline.h",
    "inline.h",
    "qd_config.h",
)

RQ1_INPUT_PAIR_TYPES: Tuple[str, ...] = ("fp_x_fp", "dw_x_fp", "dw_x_dw")
COVERAGE_METRICS: Tuple[str, ...] = (
    "cases",
    "first_bins_seen",
    "first_bins_total",
    "second_bins_seen",
    "second_bins_total",
    "first_positive",
    "second_positive",
    "first_zero_low",
    "second_zero_low",
)

RQ1_HEADER: Tuple[str, ...] = (
    "record",
    "operation",
    "implementation",
    "metric",
    "count",
    "maximum",
    "mean",
    "maximum_scaled",
    "mean_scaled",
    "flags",
    "flag_kind",
    "case_id",
    "result_hi_bits",
    "result_lo_bits",
    "reference",
    "absolute_error",
    "inputs",
)

RQ2_ACCEPTANCE_HEADER: Tuple[str, ...] = (
    "suite",
    "operation",
    "case_id",
    "first_exponent",
    "second_exponent",
    "default_outcome",
    "strong_outcome",
    "failure_mask",
    "failed_additional_conditions",
    "checked_exponents",
    "case_name",
    "inputs",
    "shared_result_equal",
    "qd_result_hi_bits",
    "qd_result_lo_bits",
    "qd_finite",
    "qd_valid_dw",
    "qd_within_bound",
    "qd_exact_reconstruction",
    "reference",
    "absolute_error",
    "bound",
    "expected_default_outcome",
    "expected_strong_outcome",
    "expected_failure_mask",
    "assertion_passed",
)

RQ3_PERFORMANCE_HEADER: Tuple[str, ...] = (
    "operation",
    "implementation",
    "interface",
    "trial",
    "ns_per_call",
)

OBSOLETE_REPORT_OUTPUTS: Tuple[Path, ...] = (
    Path("rq2-bins.tsv"),
    Path("rq2-acceptance.pdf"),
    Path("rq3-bins.tsv"),
    Path("rq3-acceptance.pdf"),
    Path("paper/generated/rq1_outcomes_rows.tex"),
    Path("paper/generated/rq1_comparison_rows.tex"),
    Path("paper/generated/rq1_bound_rows.tex"),
    Path("paper/generated/rq1_error_rows.tex"),
    Path("paper/generated/rq2_acceptance_rows.tex"),
    Path("paper/generated/rq2_failure_rows.tex"),
    Path("paper/generated/rq2-acceptance.pdf"),
    Path("paper/generated/rq2_performance_rows.tex"),
    Path("paper/generated/rq3_performance_rows.tex"),
    Path("paper/generated/rq3_compcert_rows.tex"),
    Path("paper/generated/rq3_clang_rows.tex"),
    Path("paper/generated/rq3_acceptance_rows.tex"),
    Path("paper/generated/rq3_failure_rows.tex"),
)

COUNT_METRICS: Tuple[str, ...] = (
    "generated",
    "input_check",
    "post_compute",
    "normal",
)
ERROR_METRICS: Tuple[str, ...] = (
    "relative_term_relative_error",
    "absolute_term_absolute_error",
)
BOUND_METRICS: Tuple[str, ...] = (
    "relative_term_bound_utilization",
    "absolute_term_bound_utilization",
)
BOUND_REGIMES: Tuple[str, ...] = (
    "relative_term_dominant",
    "absolute_term_dominant",
    "zero_bound",
)
BOUND_REGIME_LABELS: Mapping[str, str] = {
    "relative_term_dominant": "relative-term-dominant range",
    "absolute_term_dominant": "absolute-term-dominant range",
    "zero_bound": "zero-bound case",
}

# MPFR comparisons determine the flag. Decimal serialization is only a
# diagnostic representation and may round a value immediately around one.
BOUND_FLAG_SERIALIZATION_TOLERANCE = Decimal("1e-98")

HEX64_RE = re.compile(r"^0x[0-9a-fA-F]{16}$")
LOWER_FINGERPRINT_RE = re.compile(r"^0x[0-9a-f]{16}$")
LOWER_SEED_RE = re.compile(r"^0x[0-9a-f]+$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
HEX_MASK_RE = re.compile(r"^0x[0-9a-fA-F]{2}$")
SAFE_RUN_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")

FAILURE_BITS: Tuple[Tuple[int, str], ...] = (
    (0x01, "first_high_limit"),
    (0x02, "second_high_limit"),
    (0x04, "leading_product_limit"),
    (0x08, "nonzero_divisor"),
    (0x10, "leading_quotient_limit"),
)
ALLOWED_MASKS: Mapping[str, int] = {
    "dw_plus_fp": 0x01 | 0x02,
    "dw_times_fp": 0x04,
    "dw_div_fp": 0x01 | 0x08 | 0x10,
    "dw_plus_dw": 0x01 | 0x02,
    "dw_times_dw": 0x04,
    "dw_div_dw": 0x10,
}

# The boundary executable constructs and asserts this inventory in this order.
BOUNDARY_INVENTORY: Tuple[Tuple[str, str, str, str, int], ...] = (
    ("dw_plus_fp", "x_high_below_2^1022", "normal", "normal", 0x00),
    ("dw_plus_fp", "x_high_at_2^1022_nonzero_low", "normal", "normal", 0x00),
    ("dw_plus_fp", "x_high_above_2^1022", "normal", "input_check", 0x01),
    ("dw_plus_fp", "scalar_below_2^1022", "normal", "normal", 0x00),
    ("dw_plus_fp", "scalar_at_2^1022", "normal", "normal", 0x00),
    ("dw_plus_fp", "scalar_above_2^1022", "normal", "input_check", 0x02),
    ("dw_plus_fp", "large_exact_cancellation", "normal", "input_check", 0x03),
    ("dw_plus_fp", "post_compute_overflow", "post_compute", "input_check", 0x03),
    ("dw_times_fp", "leading_product_below_2^1023", "normal", "normal", 0x00),
    ("dw_times_fp", "leading_product_at_2^1023_nonzero_low", "normal", "input_check", 0x04),
    ("dw_times_fp", "leading_product_above_2^1023", "normal", "input_check", 0x04),
    ("dw_times_fp", "post_compute_overflow", "post_compute", "input_check", 0x04),
    ("dw_div_fp", "x_high_below_2^1022", "normal", "normal", 0x00),
    ("dw_div_fp", "x_high_at_2^1022_nonzero_low", "normal", "normal", 0x00),
    ("dw_div_fp", "x_high_above_2^1022", "normal", "input_check", 0x01),
    ("dw_div_fp", "x_high_below_2^-968", "input_check", "input_check", 0x00),
    ("dw_div_fp", "x_high_at_2^-968", "normal", "normal", 0x00),
    ("dw_div_fp", "x_high_above_2^-968", "normal", "normal", 0x00),
    ("dw_div_fp", "zero_dividend", "normal", "normal", 0x00),
    ("dw_div_fp", "leading_quotient_below_2^1022", "normal", "normal", 0x00),
    ("dw_div_fp", "leading_quotient_at_2^1022", "normal", "input_check", 0x10),
    ("dw_div_fp", "leading_quotient_above_2^1022", "normal", "input_check", 0x10),
    ("dw_div_fp", "zero_divisor_post_compute", "post_compute", "input_check", 0x08),
    ("dw_div_fp", "post_compute_overflow", "post_compute", "input_check", 0x10),
    ("dw_plus_dw", "first_high_below_2^1022", "normal", "normal", 0x00),
    ("dw_plus_dw", "first_high_at_2^1022_nonzero_low", "normal", "normal", 0x00),
    ("dw_plus_dw", "first_high_above_2^1022", "normal", "input_check", 0x01),
    ("dw_plus_dw", "second_high_below_2^1022", "normal", "normal", 0x00),
    ("dw_plus_dw", "second_high_at_2^1022_nonzero_low", "normal", "normal", 0x00),
    ("dw_plus_dw", "second_high_above_2^1022", "normal", "input_check", 0x02),
    ("dw_plus_dw", "large_exact_cancellation", "normal", "input_check", 0x03),
    ("dw_plus_dw", "post_compute_overflow", "post_compute", "input_check", 0x03),
    ("dw_times_dw", "leading_product_below_2^1023", "normal", "normal", 0x00),
    ("dw_times_dw", "leading_product_at_2^1023_nonzero_lows", "normal", "input_check", 0x04),
    ("dw_times_dw", "leading_product_above_2^1023", "normal", "input_check", 0x04),
    ("dw_times_dw", "post_compute_overflow", "post_compute", "input_check", 0x04),
    ("dw_div_dw", "leading_quotient_below_2^1022", "normal", "normal", 0x00),
    ("dw_div_dw", "leading_quotient_at_2^1022_nonzero_lows", "normal", "input_check", 0x10),
    ("dw_div_dw", "leading_quotient_above_2^1022", "normal", "input_check", 0x10),
    ("dw_div_dw", "divisor_high_below_2^-968", "input_check", "input_check", 0x00),
    ("dw_div_dw", "divisor_high_at_2^-968", "normal", "normal", 0x00),
    ("dw_div_dw", "divisor_high_above_2^-968", "normal", "normal", 0x00),
    ("dw_div_dw", "divisor_high_below_2^966", "normal", "normal", 0x00),
    ("dw_div_dw", "divisor_high_at_2^966", "normal", "normal", 0x00),
    ("dw_div_dw", "divisor_high_above_2^966", "input_check", "input_check", 0x00),
    ("dw_div_dw", "zero_dividend", "normal", "normal", 0x00),
    ("dw_div_dw", "zero_divisor", "input_check", "input_check", 0x00),
    ("dw_div_dw", "post_compute_overflow", "post_compute", "input_check", 0x10),
)

DISPLAY_NAMES: Mapping[str, str] = {
    "two_sum": "TwoSum",
    "fast_2sum": "Fast2Sum",
    "fast_2mult": "Fast2Mult",
    "dw_plus_fp": "DWPlusFP",
    "dw_times_fp": "DWTimesFP",
    "dw_div_fp": "DWDivFP",
    "dw_plus_dw": "DWPlusDW",
    "dw_times_dw": "DWTimesDW",
    "dw_div_dw": "DWDivDW",
}


@dataclass(frozen=True)
class InputShape:
    """Exponent ranges used to validate a complete set of generated inputs.

    Production code always uses ``DEFAULT_INPUT_SHAPE``.  Tests may inject a
    smaller shape while retaining every schema and count invariant.
    """

    dw_min: int = -969
    dw_max: int = 1022
    fp_min: int = -1074
    fp_max: int = 1023

    @property
    def dw_bins(self) -> int:
        return self.dw_max - self.dw_min + 1

    @property
    def fp_bins(self) -> int:
        return self.fp_max - self.fp_min + 1


DEFAULT_INPUT_SHAPE = InputShape()


def _error(path: Path, line: Optional[int], message: str) -> ReportError:
    location = str(path) if line is None else f"{path}:{line}"
    return ReportError(f"{location}: {message}")


def _parse_uint(text: str, context: str) -> int:
    if not text or not text.isdigit():
        raise ReportError(f"{context}: expected a nonnegative integer, got {text!r}")
    return int(text, 10)


def _parse_positive_uint(text: object, context: str) -> int:
    if isinstance(text, bool):
        raise ReportError(f"{context}: expected a positive integer")
    if isinstance(text, int):
        value = text
    elif isinstance(text, str) and text.isdigit():
        value = int(text, 10)
    else:
        raise ReportError(f"{context}: expected a positive integer")
    if value <= 0:
        raise ReportError(f"{context}: expected a positive integer")
    return value


def _parse_decimal(text: str, context: str) -> Decimal:
    try:
        value = Decimal(text)
    except InvalidOperation as exc:
        raise ReportError(f"{context}: invalid decimal {text!r}") from exc
    if not value.is_finite() or value < 0:
        raise ReportError(f"{context}: expected a finite nonnegative decimal")
    return value


def _parse_signed_decimal(text: str, context: str) -> Decimal:
    try:
        value = Decimal(text)
    except InvalidOperation as exc:
        raise ReportError(f"{context}: invalid decimal {text!r}") from exc
    if not value.is_finite():
        raise ReportError(f"{context}: expected a finite decimal")
    return value


def _decimal_close(actual: Decimal, expected: Decimal) -> bool:
    tolerance = max(abs(expected) * Decimal("2e-8"), Decimal("1e-9999"))
    return abs(actual - expected) <= tolerance


def _verified_bound_components(
    operation: str, reference: Decimal
) -> Tuple[Decimal, Decimal]:
    with localcontext() as decimal_context:
        decimal_context.prec = 200
        u = Decimal(2) ** -53
        u_squared = Decimal(2) ** -106
        eta = Decimal(2) ** -1074
        magnitude = abs(reference)
        relative = Decimal(0)
        absolute = Decimal(0)
        if operation == "dw_plus_fp":
            relative = Decimal(2) * u_squared * magnitude
        elif operation == "dw_plus_dw":
            relative = (
                Decimal(3) * u_squared * magnitude / (Decimal(1) - 4 * u)
            )
        elif operation == "dw_times_fp":
            relative = Decimal(2) * u_squared * magnitude
            absolute = Decimal(251) * eta / 100
        elif operation == "dw_times_dw":
            relative = Decimal(4) * u_squared * magnitude
            absolute = Decimal(5) * eta / 2
        elif operation == "dw_div_fp":
            relative = Decimal(3) * u_squared * magnitude
            absolute = eta
        elif operation == "dw_div_dw":
            relative = Decimal(98) * u_squared * magnitude / 10
            absolute = Decimal(5) * eta / 2
        else:
            raise ReportError(
                f"unknown operation for verified bound: {operation!r}"
            )
        return +relative, +absolute


def _verified_bound_value(operation: str, reference: Decimal) -> Decimal:
    relative, absolute = _verified_bound_components(operation, reference)
    with localcontext() as decimal_context:
        decimal_context.prec = 200
        return +(relative + absolute)


def _verified_bound_regime(operation: str, reference: Decimal) -> str:
    relative, absolute = _verified_bound_components(operation, reference)
    if reference == 0:
        return "absolute_term_dominant" if absolute > relative else "zero_bound"
    return (
        "relative_term_dominant"
        if relative >= absolute
        else "absolute_term_dominant"
    )


def _parse_finite_float(text: str, context: str, positive: bool = False) -> float:
    try:
        value = float(text)
    except ValueError as exc:
        raise ReportError(f"{context}: invalid floating-point value {text!r}") from exc
    if not math.isfinite(value) or (positive and not value > 0.0):
        qualifier = "positive " if positive else ""
        raise ReportError(f"{context}: expected a finite {qualifier}value")
    return value


def _parse_bool_token(text: str, context: str) -> bool:
    if text == "true":
        return True
    if text == "false":
        return False
    raise ReportError(f"{context}: expected 'true' or 'false', got {text!r}")


def _open_text(path: Path) -> TextIO:
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8", newline="")
    return path.open("r", encoding="utf-8", newline="")


def _read_tsv(
    path: Path,
    expected_header: Sequence[str],
    handle_row: Callable[[Mapping[str, str], int], None],
) -> Tuple[Dict[str, str], int]:
    """Stream a benchmark TSV and return its comment metadata and row count."""

    metadata: Dict[str, str] = {}
    header: Optional[Tuple[str, ...]] = None
    data_rows = 0
    footer_state = 0
    try:
        source = _open_text(path)
    except OSError as exc:
        raise ReportError(f"cannot open {path}: {exc}") from exc
    with source:
        for line_number, line in enumerate(source, 1):
            if line.startswith("#"):
                comment = line[1:].strip()
                if "=" not in comment:
                    raise _error(path, line_number, "metadata comment must be key=value")
                key, value = comment.split("=", 1)
                key = key.strip()
                value = value.strip()
                if not key or key in metadata:
                    raise _error(path, line_number, f"duplicate or empty metadata key {key!r}")
                if header is None:
                    if key in ("data_rows", "completed"):
                        raise _error(path, line_number, "footer metadata appeared before the header")
                elif key == "data_rows" and footer_state == 0:
                    footer_state = 1
                elif key == "completed" and footer_state == 1:
                    footer_state = 2
                else:
                    raise _error(
                        path,
                        line_number,
                        "only terminal data_rows then completed metadata may follow the header",
                    )
                metadata[key] = value
                continue
            if footer_state != 0:
                raise _error(path, line_number, "data appeared after the terminal footer began")
            if not line.strip():
                raise _error(path, line_number, "blank lines are not allowed")
            try:
                fields = next(csv.reader([line], delimiter="\t"))
            except csv.Error as exc:
                raise _error(path, line_number, f"invalid TSV row: {exc}") from exc
            if header is None:
                header = tuple(fields)
                if header != tuple(expected_header):
                    raise _error(
                        path,
                        line_number,
                        f"unexpected header {header!r}; expected {tuple(expected_header)!r}",
                    )
                continue
            if len(fields) != len(header):
                raise _error(
                    path,
                    line_number,
                    f"expected {len(header)} columns, found {len(fields)}",
                )
            handle_row(dict(zip(header, fields)), line_number)
            data_rows += 1
    if header is None:
        raise _error(path, None, "missing TSV header")
    if footer_state != 2 or metadata.get("completed") != "true":
        raise _error(path, None, "missing terminal metadata completed=true")
    declared_rows = _parse_uint(metadata.get("data_rows", ""), f"{path}: data_rows")
    if declared_rows != data_rows:
        raise _error(
            path,
            None,
            f"data_rows={declared_rows} but parsed {data_rows} rows",
        )
    return metadata, data_rows


def _require_metadata(
    path: Path,
    metadata: Mapping[str, str],
    required: Iterable[str],
) -> None:
    for key in required:
        if key not in metadata or metadata[key] == "":
            raise _error(path, None, f"missing metadata {key!r}")


def _require_exact_metadata(
    path: Path,
    metadata: Mapping[str, str],
    expected: Iterable[str],
) -> None:
    expected_keys = set(expected)
    actual_keys = set(metadata)
    if actual_keys != expected_keys:
        missing = sorted(expected_keys - actual_keys)
        extra = sorted(actual_keys - expected_keys)
        raise _error(
            path,
            None,
            f"metadata inventory mismatch; missing={missing}, extra={extra}",
        )


@dataclass(frozen=True)
class ManifestArtifact:
    key: str
    path: Path
    relative_path: str
    sha256: str
    byte_count: int
    uncompressed_sha256: Optional[str]
    uncompressed_byte_count: Optional[int]


@dataclass(frozen=True)
class RunManifest:
    path: Path
    run_dir: Path
    raw: Mapping[str, object]
    run_id: str
    profile_name: str
    profile_kind: str
    parameters: Mapping[str, int]
    artifacts: Mapping[str, ManifestArtifact]
    tsv_metadata: Mapping[str, Mapping[str, object]]


def _sha256_and_size(path: Path, decompress: bool = False) -> Tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    opener: Callable[..., TextIO]
    try:
        if decompress and path.suffix == ".gz":
            stream = gzip.open(path, "rb")
        else:
            stream = path.open("rb")
        with stream:
            while True:
                chunk = stream.read(1024 * 1024)
                if not chunk:
                    break
                digest.update(chunk)
                size += len(chunk)
    except (OSError, gzip.BadGzipFile) as exc:
        raise ReportError(f"cannot hash {path}: {exc}") from exc
    return digest.hexdigest(), size


def _require_mapping(value: object, context: str) -> Mapping[str, object]:
    if not isinstance(value, dict):
        raise ReportError(f"{context}: expected an object")
    return value


def _require_string(value: object, context: str) -> str:
    if not isinstance(value, str) or not value:
        raise ReportError(f"{context}: expected a nonempty string")
    return value


def _parse_iso8601(value: object, context: str) -> _datetime.datetime:
    text = _require_string(value, context)
    normalized = text[:-1] + "+00:00" if text.endswith("Z") else text
    try:
        parsed = _datetime.datetime.fromisoformat(normalized)
    except ValueError as exc:
        raise ReportError(f"{context}: expected an ISO-8601 timestamp") from exc
    if parsed.tzinfo is None:
        raise ReportError(f"{context}: timestamp must include a UTC offset")
    return parsed


def _validate_file_record(value: object, context: str) -> Mapping[str, object]:
    record = _require_mapping(value, context)
    _require_string(record.get("path"), f"{context}.path")
    digest = _require_string(record.get("sha256"), f"{context}.sha256")
    if not SHA256_RE.fullmatch(digest):
        raise ReportError(f"{context}.sha256 must be a lowercase SHA-256 digest")
    _parse_positive_uint(record.get("bytes"), f"{context}.bytes")
    return record


def _require_path_suffix(path_value: object, suffix: Tuple[str, ...], context: str) -> None:
    path = Path(_require_string(path_value, context))
    if len(path.parts) < len(suffix) or tuple(path.parts[-len(suffix):]) != suffix:
        raise ReportError(
            f"{context}: expected a path ending in {'/'.join(suffix)}")


def _validate_qd_identity(
    value: object, context: str
) -> Mapping[str, object]:
    identity = _require_mapping(value, context)
    if set(identity) != {"headers", "policy"}:
        raise ReportError(
            f"{context}: expected exactly headers and policy")
    headers = identity.get("headers")
    if not isinstance(headers, list) or len(headers) != len(QD_IMPLEMENTATION_HEADERS):
        raise ReportError(
            f"{context}.headers: expected exactly four QD implementation headers")
    for index, expected_name in enumerate(QD_IMPLEMENTATION_HEADERS):
        header_context = f"{context}.headers[{index}]"
        record = _validate_file_record(headers[index], header_context)
        _require_path_suffix(
            record.get("path"), ("include", "qd", expected_name),
            f"{header_context}.path")
    policy = _validate_file_record(identity.get("policy"), f"{context}.policy")
    _require_path_suffix(
        policy.get("path"), ("qd_evaluation.hpp",),
        f"{context}.policy.path")
    return identity


def _verify_run_checksums(run_dir: Path) -> None:
    checksum_path = run_dir / "checksums.sha256"
    try:
        lines = checksum_path.read_text(encoding="ascii").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ReportError(f"cannot read {checksum_path}: {exc}") from exc
    if not lines:
        raise ReportError(f"{checksum_path}: checksum inventory is empty")

    declared: List[str] = []
    for line_number, line in enumerate(lines, 1):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if match is None:
            raise _error(checksum_path, line_number, "malformed checksum entry")
        digest, relative = match.groups()
        relative_path = Path(relative)
        if (not relative_path.parts or relative_path.is_absolute()
                or ".." in relative_path.parts
                or relative_path.parts[0] == "generated"):
            raise _error(checksum_path, line_number, "invalid checksum path")
        if relative in declared:
            raise _error(checksum_path, line_number, "duplicate checksum path")
        path = (run_dir / relative_path).resolve()
        try:
            path.relative_to(run_dir)
        except ValueError as exc:
            raise _error(checksum_path, line_number, "checksum path escapes run") from exc
        actual_digest, _size = _sha256_and_size(path)
        if actual_digest != digest:
            raise _error(checksum_path, line_number, f"checksum mismatch for {relative}")
        declared.append(relative)

    if declared != sorted(declared):
        raise ReportError(f"{checksum_path}: entries are not in canonical order")
    expected = sorted(
        path.relative_to(run_dir).as_posix()
        for path in run_dir.rglob("*")
        if (path.is_file() and path != checksum_path
            and path.relative_to(run_dir).parts[0] != "generated")
    )
    if declared != expected:
        missing = sorted(set(expected) - set(declared))
        extra = sorted(set(declared) - set(expected))
        raise ReportError(
            f"{checksum_path}: checksum inventory mismatch; "
            f"missing={missing}, extra={extra}")


def load_manifest(run_dir: Path) -> RunManifest:
    """Load schema-5 run metadata and verify every declared artifact hash."""

    run_dir = run_dir.resolve()
    candidates = [run_dir / "manifest.json", run_dir / "run_manifest.json"]
    present = [path for path in candidates if path.is_file()]
    if len(present) != 1:
        raise ReportError(
            f"{run_dir}: expected exactly one of manifest.json or run_manifest.json"
        )
    manifest_path = present[0]
    try:
        raw = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ReportError(f"cannot read {manifest_path}: {exc}") from exc
    root = _require_mapping(raw, str(manifest_path))
    if root.get("manifest_schema_version") != 5:
        raise ReportError(f"{manifest_path}: manifest_schema_version must be 5")
    if root.get("status") != "complete":
        raise ReportError(f"{manifest_path}: status must be 'complete'")

    run_id = _require_string(root.get("run_id"), f"{manifest_path}: run_id")
    if not SAFE_RUN_ID_RE.fullmatch(run_id) or run_id in (".", ".."):
        raise ReportError(
            f"{manifest_path}: run_id must contain only letters, digits, dot, underscore, or dash"
        )
    profile = _require_mapping(root.get("profile"), f"{manifest_path}: profile")
    profile_name = _require_string(profile.get("name"), f"{manifest_path}: profile.name")
    profile_kind = _require_string(profile.get("kind"), f"{manifest_path}: profile.kind")
    if profile_kind not in ("smoke", "artifact"):
        raise ReportError(
            f"{manifest_path}: profile.kind must be smoke or artifact"
        )
    _validate_file_record(
        profile.get("source"), f"{manifest_path}: profile.source")

    started = _parse_iso8601(root.get("started_utc"), f"{manifest_path}: started_utc")
    completed = _parse_iso8601(root.get("completed_utc"), f"{manifest_path}: completed_utc")
    if completed < started:
        raise ReportError(f"{manifest_path}: completed_utc precedes started_utc")
    git = _require_mapping(root.get("git"), f"{manifest_path}: git")
    revision = git.get("revision")
    if revision is not None and not isinstance(revision, str):
        raise ReportError(f"{manifest_path}: git.revision must be a string or null")
    if not isinstance(git.get("dirty"), bool):
        raise ReportError(f"{manifest_path}: git.dirty must be boolean")
    if not isinstance(git.get("status"), str):
        raise ReportError(f"{manifest_path}: git.status must be a string")
    build = _require_mapping(root.get("build"), f"{manifest_path}: build")
    for key in (
        "dd_cc",
        "dd_cflags",
        "clang_cc",
        "clang_cflags",
        "cxx",
        "cxxflags",
        "strict_fp_flags",
        "qd_prefix",
    ):
        _require_string(build.get(key), f"{manifest_path}: build.{key}")
    configuration = _validate_file_record(
        build.get("configuration"), f"{manifest_path}: build.configuration")
    configuration_values = _require_mapping(
        configuration.get("values"),
        f"{manifest_path}: build.configuration.values")
    if configuration_values.get("config_schema_version") != 3:
        raise ReportError(
            f"{manifest_path}: build configuration schema must be 3")
    for key in (
        "dd_cc", "dd_cflags", "clang_cc", "clang_cflags", "cxx",
        "cxxflags", "strict_fp_flags", "qd_prefix",
    ):
        if configuration_values.get(key) != build[key]:
            raise ReportError(
                f"{manifest_path}: build.configuration.values.{key} "
                f"disagrees with build.{key}")
    tool_identities = _require_mapping(
        configuration_values.get("tool_identities"),
        f"{manifest_path}: build.configuration.values.tool_identities")
    if set(tool_identities) != {"clang_cc", "cxx", "dd_cc", "qd"}:
        raise ReportError(
            f"{manifest_path}: build tool identity inventory is incomplete")
    configuration_qd = _validate_qd_identity(
        tool_identities.get("qd"),
        f"{manifest_path}: build.configuration.values.tool_identities.qd")

    binaries = _require_mapping(
        build.get("binaries"), f"{manifest_path}: build.binaries")
    evaluation_keys = ("rq1", "rq2", "rq3_compcert", "rq3_clang")
    if set(binaries) != set(evaluation_keys):
        raise ReportError(
            f"{manifest_path}: build.binaries must contain exactly "
            "rq1, rq2, rq3_compcert, rq3_clang")
    for key, value in binaries.items():
        record = _validate_file_record(
            value, f"{manifest_path}: build.binaries.{key}")
        dependencies = record.get("dynamic_dependencies")
        if (not isinstance(dependencies, list)
                or any(not isinstance(item, str) for item in dependencies)):
            raise ReportError(
                f"{manifest_path}: build.binaries.{key}.dynamic_dependencies "
                "must be a list of strings")
    if "qd_config" in build or "qd_libraries" in build:
        raise ReportError(
            f"{manifest_path}: legacy linked-QD provenance fields are not allowed")
    top_level_qd = {
        "headers": build.get("qd_headers"),
        "policy": build.get("qd_policy"),
    }
    _validate_qd_identity(top_level_qd, f"{manifest_path}: build.qd")
    if top_level_qd != configuration_qd:
        raise ReportError(
            f"{manifest_path}: top-level QD provenance disagrees with the build configuration")

    environment = _require_mapping(root.get("environment"), f"{manifest_path}: environment")
    for key in (
        "os",
        "architecture",
        "cpu_model",
        "hostname",
        "python",
        "compcert",
        "clang",
        "cxx",
        "qd",
        "mpfr",
        "gmp",
        "compcert_executable",
        "clang_executable",
        "cxx_executable",
        "qd_config_executable",
        "pkg_config_executable",
    ):
        _require_string(environment.get(key), f"{manifest_path}: environment.{key}")
    _parse_positive_uint(environment.get("cpu_count"), f"{manifest_path}: environment.cpu_count")

    commands = root.get("commands")
    if not isinstance(commands, list) or len(commands) != 4:
        raise ReportError(
            f"{manifest_path}: commands must contain exactly RQ1, RQ2, "
            "RQ3 CompCert, and RQ3 Clang")
    command_evaluations: List[str] = []
    for index, command in enumerate(commands):
        context = f"{manifest_path}: commands[{index}]"
        record = _require_mapping(command, context)
        evaluation = _require_string(record.get("evaluation"), f"{context}.evaluation")
        if evaluation not in evaluation_keys:
            raise ReportError(f"{context}.evaluation is not a supported evaluation")
        command_evaluations.append(evaluation)
        argv = record.get("argv")
        if not isinstance(argv, list) or not argv:
            raise ReportError(f"{context}.argv must be a nonempty list")
        for argument_index, argument in enumerate(argv):
            _require_string(argument, f"{context}.argv[{argument_index}]")
        if record.get("exit_code") != 0:
            raise ReportError(f"{context}.exit_code must be zero in a complete run")
    if command_evaluations != list(evaluation_keys):
        raise ReportError(
            f"{manifest_path}: command order must be RQ1, RQ2, "
            "RQ3 CompCert, RQ3 Clang")

    parameters_raw = _require_mapping(root.get("parameters"), f"{manifest_path}: parameters")
    parameters: Dict[str, int] = {}
    expected_parameter_keys = {
        "rq1_samples", "rq2_samples", "rq3_inputs", "rq3_trials"
    }
    if set(parameters_raw) != expected_parameter_keys:
        raise ReportError(
            f"{manifest_path}: parameters must contain exactly "
            "rq1_samples, rq2_samples, rq3_inputs, and rq3_trials")
    for key in ("rq1_samples", "rq2_samples", "rq3_inputs", "rq3_trials"):
        parameters[key] = _parse_positive_uint(
            parameters_raw.get(key), f"{manifest_path}: parameters.{key}"
        )
    if parameters["rq1_samples"] % 40 or parameters["rq2_samples"] % 40:
        raise ReportError(f"{manifest_path}: RQ1/RQ2 samples must be multiples of 40")
    if parameters["rq3_trials"] % 24:
        raise ReportError(f"{manifest_path}: rq3_trials must be a multiple of 24")

    artifacts_raw = _require_mapping(root.get("artifacts"), f"{manifest_path}: artifacts")
    if set(artifacts_raw) != set(evaluation_keys):
        raise ReportError(
            f"{manifest_path}: artifacts must contain exactly rq1, rq2, "
            "rq3_compcert, rq3_clang")
    artifacts: Dict[str, ManifestArtifact] = {}
    for key in evaluation_keys:
        item = _require_mapping(artifacts_raw[key], f"{manifest_path}: artifacts.{key}")
        relative = _require_string(item.get("path"), f"{manifest_path}: artifacts.{key}.path")
        relative_path = Path(relative)
        if relative_path.is_absolute() or ".." in relative_path.parts:
            raise ReportError(f"{manifest_path}: artifact path must stay within the run directory")
        path = (run_dir / relative_path).resolve()
        try:
            path.relative_to(run_dir)
        except ValueError as exc:
            raise ReportError(f"{manifest_path}: artifact path escapes the run directory") from exc
        expected_hash = _require_string(
            item.get("sha256"), f"{manifest_path}: artifacts.{key}.sha256"
        )
        if not SHA256_RE.fullmatch(expected_hash):
            raise ReportError(f"{manifest_path}: artifacts.{key}.sha256 is malformed")
        expected_bytes = _parse_positive_uint(
            item.get("bytes"), f"{manifest_path}: artifacts.{key}.bytes"
        )
        actual_hash, actual_bytes = _sha256_and_size(path)
        if (actual_hash, actual_bytes) != (expected_hash, expected_bytes):
            raise ReportError(
                f"{manifest_path}: artifacts.{key} hash/size does not match {relative}"
            )
        uncompressed_hash_value = item.get("uncompressed_sha256")
        uncompressed_bytes_value = item.get("uncompressed_bytes")
        if (uncompressed_hash_value is None) != (uncompressed_bytes_value is None):
            raise ReportError(
                f"{manifest_path}: artifacts.{key} must provide both uncompressed fields"
            )
        uncompressed_hash: Optional[str] = None
        uncompressed_bytes: Optional[int] = None
        if uncompressed_hash_value is not None:
            uncompressed_hash = _require_string(
                uncompressed_hash_value,
                f"{manifest_path}: artifacts.{key}.uncompressed_sha256",
            )
            if not SHA256_RE.fullmatch(uncompressed_hash):
                raise ReportError(
                    f"{manifest_path}: artifacts.{key}.uncompressed_sha256 is malformed"
                )
            uncompressed_bytes = _parse_positive_uint(
                uncompressed_bytes_value,
                f"{manifest_path}: artifacts.{key}.uncompressed_bytes",
            )
            actual_uncompressed_hash, actual_uncompressed_bytes = _sha256_and_size(
                path, decompress=True
            )
            if (actual_uncompressed_hash, actual_uncompressed_bytes) != (
                uncompressed_hash,
                uncompressed_bytes,
            ):
                raise ReportError(
                    f"{manifest_path}: artifacts.{key} uncompressed hash/size mismatch"
                )
        if key == "rq2":
            if path.suffix != ".gz" or uncompressed_hash is None:
                raise ReportError(
                    f"{manifest_path}: RQ2 must be gzip-compressed with uncompressed provenance")
        elif path.suffix == ".gz" or uncompressed_hash is not None:
            raise ReportError(
                f"{manifest_path}: only RQ2 may be compressed")
        artifacts[key] = ManifestArtifact(
            key,
            path,
            relative,
            expected_hash,
            expected_bytes,
            uncompressed_hash,
            uncompressed_bytes,
        )

    tsv_metadata_raw = _require_mapping(
        root.get("tsv_metadata"), f"{manifest_path}: tsv_metadata"
    )
    if set(tsv_metadata_raw) != set(evaluation_keys):
        raise ReportError(
            f"{manifest_path}: tsv_metadata must contain rq1, rq2, "
            "rq3_compcert, rq3_clang")
    tsv_metadata: Dict[str, Mapping[str, object]] = {}
    for key in evaluation_keys:
        tsv_metadata[key] = _require_mapping(
            tsv_metadata_raw[key], f"{manifest_path}: tsv_metadata.{key}"
        )

    _verify_run_checksums(run_dir)

    return RunManifest(
        manifest_path,
        run_dir,
        root,
        run_id,
        profile_name,
        profile_kind,
        parameters,
        artifacts,
        tsv_metadata,
    )


def _metadata_text(value: object) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    return str(value)


def validate_manifest_tsv_metadata(
    manifest: RunManifest, key: str, actual: Mapping[str, str]
) -> None:
    declared = manifest.tsv_metadata[key]
    normalized = {
        metadata_key: _metadata_text(value)
        for metadata_key, value in declared.items()
    }
    if normalized != dict(actual):
        raise ReportError(
            f"{manifest.path}: tsv_metadata.{key} does not exactly match the TSV")


@dataclass(frozen=True)
class RQ1Metric:
    operation: str
    implementation: str
    name: str
    count: int
    maximum: str
    mean: str
    maximum_scaled: str
    mean_scaled: str
    flags: int
    flag_kind: str
    case_id: Optional[int]
    result_hi_bits: Optional[str]
    result_lo_bits: Optional[str]
    reference: Optional[str]
    absolute_error: Optional[str]
    inputs: Optional[str]


@dataclass(frozen=True)
class RQ1Witness:
    operation: str
    implementation: str
    name: str
    count: int
    case_id: int
    result_hi_bits: str
    result_lo_bits: str
    reference: str
    absolute_error: Optional[str]
    inputs: str


@dataclass(frozen=True)
class RQ1AboveBoundResult:
    operation: str
    implementation: str
    regime: str
    case_id: int
    result_hi_bits: str
    result_lo_bits: str
    reference: str
    absolute_error: str
    inputs: str


@dataclass
class RQ1Data:
    metadata: Dict[str, str]
    data_rows: int
    counts: Dict[Tuple[str, str, str], int]
    metrics: Dict[Tuple[str, str, str], RQ1Metric]
    witnesses: Dict[Tuple[str, str, str], RQ1Witness]
    above_bound_results: List[RQ1AboveBoundResult]
    coverage: Dict[str, Dict[str, int]]

    def count(self, operation: str, implementation: str, metric: str) -> int:
        key = (operation, implementation, metric)
        if key not in self.counts:
            raise ReportError(f"RQ1 is missing count row {key}")
        return self.counts[key]

    def metric(self, operation: str, implementation: str, metric: str) -> RQ1Metric:
        key = (operation, implementation, metric)
        if key not in self.metrics:
            raise ReportError(f"RQ1 is missing metric row {key}")
        return self.metrics[key]


def _require_dash_fields(row: Mapping[str, str], fields: Iterable[str], context: str) -> None:
    for name in fields:
        if row[name] != "-":
            raise ReportError(f"{context}: {name} must be '-' for this record")


def parse_rq1(path: Path, shape: InputShape = DEFAULT_INPUT_SHAPE) -> RQ1Data:
    counts: Dict[Tuple[str, str, str], int] = {}
    metrics: Dict[Tuple[str, str, str], RQ1Metric] = {}
    witnesses: Dict[Tuple[str, str, str], RQ1Witness] = {}
    above_bound_results: List[RQ1AboveBoundResult] = []
    coverage: Dict[str, Dict[str, int]] = defaultdict(dict)
    seen_records: Set[Tuple[object, ...]] = set()

    def handle(row: Mapping[str, str], line: int) -> None:
        context = f"{path}:{line}"
        record = row["record"]
        operation = row["operation"]
        implementation = row["implementation"]
        metric_name = row["metric"]
        record_key = (
            (record, operation, implementation, metric_name, row["case_id"])
            if record == "above_bound"
            else (record, operation, implementation, metric_name)
        )
        if record_key in seen_records:
            raise ReportError(f"{context}: duplicate record {record_key}")
        seen_records.add(record_key)

        if record in ("count", "coverage"):
            _require_dash_fields(
                row,
                (
                    "maximum",
                    "mean",
                    "maximum_scaled",
                    "mean_scaled",
                    "case_id",
                    "result_hi_bits",
                    "result_lo_bits",
                    "reference",
                    "absolute_error",
                    "inputs",
                ),
                context,
            )
            if row["flags"] != "0" or row["flag_kind"] != "none":
                raise ReportError(f"{context}: count/coverage rows cannot carry flags")
            value = _parse_uint(row["count"], f"{context}: count")
            if record == "coverage":
                if operation not in RQ1_INPUT_PAIR_TYPES:
                    raise ReportError(f"{context}: unknown input-pair type {operation!r}")
                if implementation != "inputs" or metric_name not in COVERAGE_METRICS:
                    raise ReportError(f"{context}: malformed coverage key")
                coverage[operation][metric_name] = value
            else:
                if operation not in COMPOSITE_OPERATIONS:
                    raise ReportError(f"{context}: unknown RQ1 operation {operation!r}")
                counts[(operation, implementation, metric_name)] = value
            return

        if record == "above_bound":
            if operation not in COMPOSITE_OPERATIONS:
                raise ReportError(
                    f"{context}: above-bound row on non-composite operation"
                )
            if implementation not in ("dd_lib", "QD"):
                raise ReportError(
                    f"{context}: unknown above-bound implementation"
                )
            if metric_name not in BOUND_REGIMES:
                raise ReportError(f"{context}: unknown above-bound regime")
            if row["count"] != "1":
                raise ReportError(f"{context}: above-bound count must be one")
            _require_dash_fields(
                row,
                ("maximum", "mean", "maximum_scaled", "mean_scaled"),
                context,
            )
            if row["flags"] != "0" or row["flag_kind"] != "none":
                raise ReportError(
                    f"{context}: above-bound rows cannot carry flags"
                )
            case_id = _parse_uint(row["case_id"], f"{context}: case_id")
            if (
                not HEX64_RE.fullmatch(row["result_hi_bits"])
                or not HEX64_RE.fullmatch(row["result_lo_bits"])
            ):
                raise ReportError(
                    f"{context}: above-bound result bits are malformed"
                )
            if not (
                _bits_are_finite(row["result_hi_bits"])
                and _bits_are_finite(row["result_lo_bits"])
            ):
                raise ReportError(
                    f"{context}: above-bound result must be finite"
                )
            for name in ("reference", "absolute_error", "inputs"):
                if row[name] in ("", "-"):
                    raise ReportError(
                        f"{context}: above-bound row is missing {name}"
                    )
            reference = _parse_signed_decimal(
                row["reference"], f"{context}: reference"
            )
            absolute_error = _parse_decimal(
                row["absolute_error"], f"{context}: absolute_error"
            )
            expected_regime = _verified_bound_regime(operation, reference)
            if metric_name != expected_regime:
                raise ReportError(
                    f"{context}: above-bound regime disagrees with reference"
                )
            bound = _verified_bound_value(operation, reference)
            if absolute_error < bound and not _decimal_close(
                absolute_error, bound
            ):
                raise ReportError(
                    f"{context}: recorded result is not above the bound"
                )
            if bound == 0 and absolute_error == 0:
                raise ReportError(
                    f"{context}: zero-bound result has zero error"
                )
            above_bound_results.append(
                RQ1AboveBoundResult(
                    operation,
                    implementation,
                    metric_name,
                    case_id,
                    row["result_hi_bits"].lower(),
                    row["result_lo_bits"].lower(),
                    row["reference"],
                    row["absolute_error"],
                    row["inputs"],
                )
            )
            return

        if record == "metric":
            if operation not in COMPOSITE_OPERATIONS:
                raise ReportError(f"{context}: metric row on non-composite operation")
            count = _parse_uint(row["count"], f"{context}: count")
            flags = _parse_uint(row["flags"], f"{context}: flags")
            if count == 0:
                for name in ("maximum", "mean", "maximum_scaled", "mean_scaled"):
                    if row[name] != "n/a":
                        raise ReportError(f"{context}: zero-count metric {name} must be n/a")
                _require_dash_fields(
                    row,
                    ("case_id", "result_hi_bits", "result_lo_bits", "reference", "absolute_error", "inputs"),
                    context,
                )
                case_id = None
                hi_bits = lo_bits = reference = absolute_error = inputs = None
            else:
                maximum_value = _parse_decimal(row["maximum"], f"{context}: maximum")
                mean_value = _parse_decimal(row["mean"], f"{context}: mean")
                if mean_value > maximum_value:
                    raise ReportError(f"{context}: metric mean exceeds its maximum")
                if metric_name in BOUND_METRICS:
                    if row["maximum_scaled"] != "n/a" or row["mean_scaled"] != "n/a":
                        raise ReportError(f"{context}: bound utilization has no scaled units")
                else:
                    maximum_scaled = _parse_decimal(
                        row["maximum_scaled"], f"{context}: maximum_scaled"
                    )
                    mean_scaled = _parse_decimal(
                        row["mean_scaled"], f"{context}: mean_scaled"
                    )
                    if mean_scaled > maximum_scaled:
                        raise ReportError(
                            f"{context}: scaled metric mean exceeds its maximum"
                        )
                case_id = _parse_uint(row["case_id"], f"{context}: case_id")
                if not HEX64_RE.fullmatch(row["result_hi_bits"]) or not HEX64_RE.fullmatch(row["result_lo_bits"]):
                    raise ReportError(f"{context}: metric witness has malformed result bits")
                hi_bits = row["result_hi_bits"].lower()
                lo_bits = row["result_lo_bits"].lower()
                for name in ("reference", "absolute_error", "inputs"):
                    if row[name] in ("", "-"):
                        raise ReportError(f"{context}: metric witness is missing {name}")
                reference = row["reference"]
                absolute_error = row["absolute_error"]
                inputs = row["inputs"]
                reference_value = _parse_signed_decimal(
                    reference, f"{context}: reference")
                absolute_error_value = _parse_decimal(
                    absolute_error, f"{context}: absolute_error")
                if metric_name in BOUND_METRICS:
                    bound_value = _verified_bound_value(operation, reference_value)
                    if bound_value == 0:
                        raise ReportError(
                            f"{context}: bound-utilization witness has a zero bound")
                    with localcontext() as decimal_context:
                        decimal_context.prec = 200
                        witness_metric_value = absolute_error_value / bound_value
                    if not _decimal_close(maximum_value, witness_metric_value):
                        raise ReportError(
                            f"{context}: bound maximum disagrees with its witness")
                elif metric_name in ERROR_METRICS:
                    if metric_name == "absolute_term_absolute_error":
                        witness_metric_value = absolute_error_value
                    else:
                        if reference_value == 0:
                            raise ReportError(
                                f"{context}: relative witness has zero reference")
                        with localcontext() as decimal_context:
                            decimal_context.prec = 100
                            witness_metric_value = (
                                absolute_error_value / abs(reference_value))
                    if not _decimal_close(maximum_value, witness_metric_value):
                        raise ReportError(
                            f"{context}: metric maximum disagrees with its witness")
                    unit_exponent = (
                        -106
                        if metric_name == "relative_term_relative_error"
                        else -1074
                    )
                    with localcontext() as decimal_context:
                        decimal_context.prec = 100
                        unit = Decimal(2) ** unit_exponent
                        expected_maximum_scaled = maximum_value / unit
                        expected_mean_scaled = mean_value / unit
                    if not _decimal_close(
                            maximum_scaled, expected_maximum_scaled):
                        raise ReportError(
                            f"{context}: maximum_scaled uses the wrong unit")
                    if not _decimal_close(mean_scaled, expected_mean_scaled):
                        raise ReportError(
                            f"{context}: mean_scaled uses the wrong unit")
            metrics[(operation, implementation, metric_name)] = RQ1Metric(
                operation,
                implementation,
                metric_name,
                count,
                row["maximum"],
                row["mean"],
                row["maximum_scaled"],
                row["mean_scaled"],
                flags,
                row["flag_kind"],
                case_id,
                hi_bits,
                lo_bits,
                reference,
                absolute_error,
                inputs,
            )
            return

        if record == "witness":
            if operation not in COMPOSITE_OPERATIONS:
                raise ReportError(f"{context}: unknown witness operation")
            count = _parse_uint(row["count"], f"{context}: count")
            if count == 0:
                raise ReportError(f"{context}: a witness must represent a nonzero count")
            _require_dash_fields(
                row,
                ("maximum", "mean", "maximum_scaled", "mean_scaled"),
                context,
            )
            if row["flags"] != "0" or row["flag_kind"] != "none":
                raise ReportError(f"{context}: witness rows cannot carry flags")
            case_id = _parse_uint(row["case_id"], f"{context}: case_id")
            if not HEX64_RE.fullmatch(row["result_hi_bits"]) or not HEX64_RE.fullmatch(row["result_lo_bits"]):
                raise ReportError(f"{context}: witness has malformed result bits")
            if row["reference"] in ("", "-") or row["inputs"] in ("", "-"):
                raise ReportError(f"{context}: witness lacks reference or inputs")
            absolute_error = None if row["absolute_error"] == "-" else row["absolute_error"]
            witnesses[(operation, implementation, metric_name)] = RQ1Witness(
                operation,
                implementation,
                metric_name,
                count,
                case_id,
                row["result_hi_bits"].lower(),
                row["result_lo_bits"].lower(),
                row["reference"],
                absolute_error,
                row["inputs"],
            )
            return

        raise ReportError(f"{context}: unknown record kind {record!r}")

    metadata, data_rows = _read_tsv(path, RQ1_HEADER, handle)
    rq1_metadata = (
        "rq1_schema_version",
        "generator",
        "seed",
        "input_fingerprint",
        "samples_per_exponent",
        "construction_precision_bits",
        "oracle_precision_bits",
        "division_recheck_precision_bits",
        "data_rows",
        "completed",
    )
    _require_metadata(path, metadata, rq1_metadata)
    _require_exact_metadata(path, metadata, rq1_metadata)
    if metadata["rq1_schema_version"] != "6":
        raise _error(path, None, "rq1_schema_version must be 6")
    if metadata["generator"] != "mpfr106-v1":
        raise _error(path, None, "generator must be mpfr106-v1")
    if not LOWER_SEED_RE.fullmatch(metadata["seed"]):
        raise _error(path, None, "seed must be lowercase hexadecimal with a 0x prefix")
    if metadata["seed"] != "0xc0ffee":
        raise _error(path, None, "seed must match the fixed input-generation seed")
    if not LOWER_FINGERPRINT_RE.fullmatch(metadata["input_fingerprint"]):
        raise _error(path, None, "input_fingerprint must contain 16 lowercase hexadecimal digits")
    samples = _parse_positive_uint(metadata["samples_per_exponent"], f"{path}: samples_per_exponent")
    if samples % 40:
        raise _error(path, None, "samples_per_exponent must be a multiple of 40")
    expected_precisions = {
        "construction_precision_bits": 256,
        "oracle_precision_bits": 2112,
        "division_recheck_precision_bits": 4224,
    }
    for key, expected in expected_precisions.items():
        actual = _parse_positive_uint(metadata[key], f"{path}: {key}")
        if actual != expected:
            raise _error(path, None, f"{key} must be {expected}")

    data = RQ1Data(
        metadata,
        data_rows,
        counts,
        metrics,
        witnesses,
        above_bound_results,
        dict(coverage),
    )
    _validate_rq1(data, shape)
    return data


def _expected_rq1_count_keys() -> Set[Tuple[str, str, str]]:
    expected: Set[Tuple[str, str, str]] = set()
    for operation in COMPOSITE_OPERATIONS:
        for metric in COUNT_METRICS:
            expected.add((operation, "dd_lib", metric))
        expected.update(
            {
                (operation, "QD", "nonfinite"),
                (operation, "QD", "invalid_double_word"),
                (operation, "dd_lib", "invalid_double_word"),
                (operation, "MPFR", "relative_term_references"),
                (operation, "MPFR", "absolute_term_references"),
                (operation, "MPFR", "zero_bound_reference"),
                (operation, "dd_lib", "zero_bound_error"),
                (operation, "QD", "zero_bound_error"),
                (operation, "QD", "zero_bound_nonfinite"),
            }
        )
        if operation in DIVISION_OPERATIONS:
            for metric in ("bound_rechecks", "bound_decision_changes"):
                expected.add((operation, "MPFR", metric))
    return expected


def _validate_rq1(data: RQ1Data, shape: InputShape) -> None:
    expected_counts = _expected_rq1_count_keys()
    if set(data.counts) != expected_counts:
        missing = sorted(expected_counts - set(data.counts))
        extra = sorted(set(data.counts) - expected_counts)
        raise ReportError(f"RQ1 count inventory mismatch; missing={missing}, extra={extra}")
    expected_coverage = set(RQ1_INPUT_PAIR_TYPES)
    if set(data.coverage) != expected_coverage:
        raise ReportError("RQ1 input-pair coverage inventory is incomplete")
    for input_type in RQ1_INPUT_PAIR_TYPES:
        if set(data.coverage[input_type]) != set(COVERAGE_METRICS):
            raise ReportError(f"RQ1 coverage metrics are incomplete for {input_type}")

    expected_metrics: Set[Tuple[str, str, str]] = set()
    for operation in COMPOSITE_OPERATIONS:
        for implementation in ("dd_lib", "QD"):
            for metric in ERROR_METRICS + BOUND_METRICS:
                expected_metrics.add((operation, implementation, metric))
    if set(data.metrics) != expected_metrics:
        raise ReportError("RQ1 metric inventory does not match the six composite operations")

    for operation in COMPOSITE_OPERATIONS:
        generated = data.count(operation, "dd_lib", "generated")
        input_check = data.count(operation, "dd_lib", "input_check")
        post_compute = data.count(operation, "dd_lib", "post_compute")
        normal = data.count(operation, "dd_lib", "normal")
        if generated != input_check + post_compute + normal:
            raise ReportError(f"RQ1 {operation}: outcome counts do not partition generated cases")
        dd_invalid = data.count(operation, "dd_lib", "invalid_double_word")
        if dd_invalid > normal:
            raise ReportError(
                f"RQ1 {operation}: invalid dd_lib double-word count exceeds normal returns")
        qd_nonfinite = data.count(operation, "QD", "nonfinite")
        qd_invalid = data.count(operation, "QD", "invalid_double_word")
        if qd_nonfinite > normal or qd_invalid > normal - qd_nonfinite:
            raise ReportError(
                f"RQ1 {operation}: invalid QD validity/nonfinite counts")

        relative_references = data.count(
            operation, "MPFR", "relative_term_references")
        absolute_references = data.count(
            operation, "MPFR", "absolute_term_references")
        zero_bound_references = data.count(
            operation, "MPFR", "zero_bound_reference")
        if relative_references + absolute_references + zero_bound_references != normal:
            raise ReportError(
                f"RQ1 {operation}: MPFR regimes do not partition normal returns")

        regime_inventory = (
            ("relative_term_relative_error",
             "relative_term_bound_utilization", relative_references),
            ("absolute_term_absolute_error",
             "absolute_term_bound_utilization", absolute_references),
        )
        qd_nonfinite_by_regime = 0
        for error_name, bound_name, references in regime_inventory:
            dd_error = data.metric(operation, "dd_lib", error_name)
            dd_bound = data.metric(operation, "dd_lib", bound_name)
            qd_error = data.metric(operation, "QD", error_name)
            qd_bound = data.metric(operation, "QD", bound_name)
            if dd_error.flag_kind != "none" or dd_error.flags != 0:
                raise ReportError(
                    f"RQ1 {operation}: dd_lib error metric carries flags")
            if qd_error.flag_kind != "qd_nonfinite_in_regime":
                raise ReportError(
                    f"RQ1 {operation}: QD error metric has the wrong flag kind")
            if dd_bound.flag_kind != "bound_ratio_above_one" \
                    or qd_bound.flag_kind != "bound_ratio_above_one":
                raise ReportError(
                    f"RQ1 {operation}: bound metric has the wrong flag kind")
            if dd_error.count != references or dd_bound.count != references:
                raise ReportError(
                    f"RQ1 {operation}: dd_lib regime counts disagree with MPFR")
            if qd_error.count != qd_bound.count \
                    or qd_error.count + qd_error.flags != references:
                raise ReportError(
                    f"RQ1 {operation}: QD finite/nonfinite regime counts disagree")
            qd_nonfinite_by_regime += qd_error.flags
            for implementation, bound_metric in (
                    ("dd_lib", dd_bound), ("QD", qd_bound)):
                if bound_metric.flags > bound_metric.count:
                    raise ReportError(
                        f"RQ1 {operation}/{implementation}: too many above-bound results")
                maximum = (
                    Decimal(bound_metric.maximum)
                    if bound_metric.count > 0 else Decimal(0))
                with localcontext() as decimal_context:
                    decimal_context.prec = 120
                    lower = Decimal(1) - BOUND_FLAG_SERIALIZATION_TOLERANCE
                    upper = Decimal(1) + BOUND_FLAG_SERIALIZATION_TOLERANCE
                if ((bound_metric.flags == 0 and maximum > upper)
                        or (bound_metric.flags > 0 and maximum < lower)):
                    raise ReportError(
                        f"RQ1 {operation}/{implementation}: bound maximum "
                        "and above-bound count disagree")

        qd_zero_nonfinite = data.count(
            operation, "QD", "zero_bound_nonfinite")
        if qd_nonfinite_by_regime + qd_zero_nonfinite != data.count(
                operation, "QD", "nonfinite"):
            raise ReportError(
                f"RQ1 {operation}: QD nonfinite regime counts do not sum")
        dd_zero_error = data.count(operation, "dd_lib", "zero_bound_error")
        qd_zero_error = data.count(operation, "QD", "zero_bound_error")
        if dd_zero_error > zero_bound_references:
            raise ReportError(f"RQ1 {operation}: too many dd_lib zero-bound errors")
        if qd_zero_nonfinite > zero_bound_references \
                or qd_zero_error > zero_bound_references - qd_zero_nonfinite:
            raise ReportError(f"RQ1 {operation}: invalid QD zero-bound counts")

        if operation in DIVISION_OPERATIONS:
            bound_rechecks = data.count(operation, "MPFR", "bound_rechecks")
            bound_changes = data.count(operation, "MPFR", "bound_decision_changes")
            finite_bound_ratios = sum(
                data.metric(operation, implementation, metric).count
                for implementation in ("dd_lib", "QD")
                for metric in BOUND_METRICS)
            if bound_rechecks > finite_bound_ratios or bound_changes > bound_rechecks:
                raise ReportError(f"RQ1 {operation}: invalid bound recheck counts")

    diagnostic_counts = (
        ("dd_lib", "invalid_double_word"),
        ("QD", "invalid_double_word"),
        ("dd_lib", "zero_bound_error"),
        ("QD", "zero_bound_error"),
        ("QD", "nonfinite"),
    )
    expected_witnesses = {
        (operation, implementation, metric)
        for operation in COMPOSITE_OPERATIONS
        for implementation, metric in diagnostic_counts
        if data.count(operation, implementation, metric) > 0
    }
    if set(data.witnesses) != expected_witnesses:
        raise ReportError("RQ1 diagnostic-witness inventory is inconsistent")
    for key, witness in data.witnesses.items():
        if witness.count != data.count(*key) \
                or witness.case_id >= data.count(
                    witness.operation, "dd_lib", "generated"):
            raise ReportError(f"RQ1 {key}: malformed diagnostic witness")
        reference = _parse_signed_decimal(
            witness.reference, f"RQ1 {key}: witness reference")
        finite_result = (
            _bits_are_finite(witness.result_hi_bits)
            and _bits_are_finite(witness.result_lo_bits)
        )
        if witness.name == "nonfinite":
            if witness.absolute_error != "inf" or finite_result:
                raise ReportError(
                    f"RQ1 {key}: nonfinite witness is inconsistent")
        elif witness.name == "invalid_double_word":
            if witness.absolute_error is not None or not finite_result:
                raise ReportError(
                    f"RQ1 {key}: invalid-DW witness is inconsistent")
        elif witness.name == "zero_bound_error":
            if witness.absolute_error is None or not finite_result:
                raise ReportError(
                    f"RQ1 {key}: zero-bound witness is inconsistent")
            if _verified_bound_value(witness.operation, reference) != 0:
                raise ReportError(
                    f"RQ1 {key}: zero-bound witness has a nonzero bound")
            if _parse_decimal(
                    witness.absolute_error,
                    f"RQ1 {key}: witness absolute_error") == 0:
                raise ReportError(
                    f"RQ1 {key}: zero-bound witness has zero error")

    observed_above_bound: Dict[Tuple[str, str, str], int] = defaultdict(int)
    above_bound_case_ids: Dict[Tuple[str, str, str], Set[int]] = defaultdict(set)
    seen_above_bound_cases: Set[Tuple[str, str, int]] = set()
    for result in data.above_bound_results:
        case_key = (result.operation, result.implementation, result.case_id)
        if case_key in seen_above_bound_cases:
            raise ReportError(
                f"RQ1 {case_key}: case is listed above bound more than once"
            )
        seen_above_bound_cases.add(case_key)
        if result.case_id >= data.count(
            result.operation, "dd_lib", "generated"
        ):
            raise ReportError(
                f"RQ1 {case_key}: above-bound case is out of range"
            )
        observed_above_bound[
            (result.operation, result.implementation, result.regime)
        ] += 1
        above_bound_case_ids[
            (result.operation, result.implementation, result.regime)
        ].add(result.case_id)

    for operation in COMPOSITE_OPERATIONS:
        for implementation in ("dd_lib", "QD"):
            expected_by_regime = {
                "relative_term_dominant": data.metric(
                    operation,
                    implementation,
                    "relative_term_bound_utilization",
                ).flags,
                "absolute_term_dominant": data.metric(
                    operation,
                    implementation,
                    "absolute_term_bound_utilization",
                ).flags,
                "zero_bound": data.count(
                    operation, implementation, "zero_bound_error"
                ),
            }
            for regime, expected in expected_by_regime.items():
                detail_key = (operation, implementation, regime)
                observed = observed_above_bound[detail_key]
                if observed != expected:
                    raise ReportError(
                        f"RQ1 {operation}/{implementation}/{regime}: "
                        f"above-bound detail count {observed} does not match "
                        f"aggregate count {expected}"
                    )
                if regime != "zero_bound" and expected:
                    metric_name = (
                        "relative_term_bound_utilization"
                        if regime == "relative_term_dominant"
                        else "absolute_term_bound_utilization"
                    )
                    maximum_case = data.metric(
                        operation, implementation, metric_name
                    ).case_id
                    if maximum_case not in above_bound_case_ids[detail_key]:
                        raise ReportError(
                            f"RQ1 {operation}/{implementation}/{regime}: "
                            "maximum-utilization case is missing from the "
                            "above-bound details"
                        )
    for metric in data.metrics.values():
        generated = data.count(metric.operation, "dd_lib", "generated")
        if metric.case_id is not None and metric.case_id >= generated:
            raise ReportError(f"RQ1 {metric.operation}: metric witness case is out of range")

    samples = int(data.metadata["samples_per_exponent"])
    expected_cases = {
        "fp_x_fp": shape.fp_bins * samples,
        "dw_x_fp": shape.dw_bins * samples,
        "dw_x_dw": shape.dw_bins * samples,
    }
    expected_bin_totals = {
        "fp_x_fp": (shape.fp_bins, shape.fp_bins),
        "dw_x_fp": (shape.dw_bins, shape.fp_bins),
        "dw_x_dw": (shape.dw_bins, shape.dw_bins),
    }
    for input_type, values in data.coverage.items():
        if values["cases"] != expected_cases[input_type]:
            raise ReportError(f"RQ1 {input_type}: case count disagrees with samples-per-exponent")
        first_total, second_total = expected_bin_totals[input_type]
        if values["first_bins_total"] != first_total or values["second_bins_total"] != second_total:
            raise ReportError(f"RQ1 {input_type}: exponent-bin total is wrong")
        if values["first_bins_seen"] > first_total or values["second_bins_seen"] > second_total:
            raise ReportError(f"RQ1 {input_type}: seen exponent bins exceed total")
        if values["first_bins_seen"] != first_total or values["second_bins_seen"] != second_total:
            raise ReportError(f"RQ1 {input_type}: exponent-bin coverage is incomplete")
        for name in ("first_positive", "second_positive", "first_zero_low", "second_zero_low"):
            if values[name] > values["cases"]:
                raise ReportError(f"RQ1 {input_type}: {name} exceeds case count")
        if values["first_positive"] * 2 != values["cases"]:
            raise ReportError(f"RQ1 {input_type}: first-operand signs are not balanced")
        if values["second_positive"] * 2 != values["cases"]:
            raise ReportError(f"RQ1 {input_type}: second-operand signs are not balanced")
    if data.coverage["fp_x_fp"]["first_zero_low"] != expected_cases["fp_x_fp"]:
        raise ReportError("RQ1 FP x FP first_zero_low must equal the case count")
    if data.coverage["fp_x_fp"]["second_zero_low"] != expected_cases["fp_x_fp"]:
        raise ReportError("RQ1 FP x FP second_zero_low must equal the case count")
    if data.coverage["dw_x_fp"]["second_zero_low"] != expected_cases["dw_x_fp"]:
        raise ReportError("RQ1 DW x FP second_zero_low must equal the case count")
    if data.coverage["dw_x_fp"]["first_zero_low"] * 20 != expected_cases["dw_x_fp"]:
        raise ReportError("RQ1 DW x FP ordinary-input share must be one twentieth")
    if data.coverage["dw_x_dw"]["first_zero_low"] * 20 != expected_cases["dw_x_dw"]:
        raise ReportError("RQ1 DW x DW first ordinary-input share must be one twentieth")
    if data.coverage["dw_x_dw"]["second_zero_low"] * 20 != expected_cases["dw_x_dw"]:
        raise ReportError("RQ1 DW x DW second ordinary-input share must be one twentieth")

    for operation in ("dw_plus_fp", "dw_times_fp", "dw_div_fp"):
        if data.coverage["dw_x_fp"]["cases"] != data.count(operation, "dd_lib", "generated"):
            raise ReportError(f"RQ1 mixed coverage does not match {operation}")
    for operation in ("dw_plus_dw", "dw_times_dw", "dw_div_dw"):
        if data.coverage["dw_x_dw"]["cases"] != data.count(operation, "dd_lib", "generated"):
            raise ReportError(f"RQ1 DW coverage does not match {operation}")


@dataclass(frozen=True)
class TimingRow:
    operation: str
    implementation: str
    interface: str
    trial: int
    ns_per_call: float


@dataclass(frozen=True)
class QuantileSummary:
    median: float
    first_quartile: float
    third_quartile: float

    @property
    def iqr(self) -> float:
        return self.third_quartile - self.first_quartile


@dataclass
class RQ3PerformanceData:
    build: str
    metadata: Dict[str, str]
    data_rows: int
    rows: Dict[Tuple[str, str, str], List[TimingRow]]
    summaries: Dict[Tuple[str, str, str], QuantileSummary]


def linear_quantile(values: Sequence[float], probability: float) -> float:
    if not values:
        raise ReportError("cannot summarize an empty timing sample")
    if not 0.0 <= probability <= 1.0:
        raise ReportError("quantile probability is outside [0,1]")
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = probability * (len(ordered) - 1)
    lower = int(math.floor(position))
    upper = int(math.ceil(position))
    fraction = position - lower
    return ordered[lower] + fraction * (ordered[upper] - ordered[lower])


def summarize_values(values: Sequence[float]) -> QuantileSummary:
    return QuantileSummary(
        linear_quantile(values, 0.5),
        linear_quantile(values, 0.25),
        linear_quantile(values, 0.75),
    )


def parse_rq3_performance(path: Path) -> RQ3PerformanceData:
    rows: Dict[Tuple[str, str, str], List[TimingRow]] = defaultdict(list)
    seen: Set[Tuple[str, str, str, int]] = set()

    def handle(row: Mapping[str, str], line: int) -> None:
        context = f"{path}:{line}"
        operation = row["operation"]
        implementation = row["implementation"]
        interface = row["interface"]
        if operation not in OPERATIONS:
            raise ReportError(f"{context}: unknown operation {operation!r}")
        if implementation == "QD":
            if interface != "reference":
                raise ReportError(f"{context}: QD interface must be 'reference'")
        elif implementation == "dd_lib":
            allowed = {"default", "kernel"}
            if operation in COMPOSITE_OPERATIONS:
                allowed.add("strong")
            if interface not in allowed:
                raise ReportError(
                    f"{context}: invalid dd_lib interface {interface!r} for {operation}")
        else:
            raise ReportError(f"{context}: invalid implementation {implementation!r}")
        trial = _parse_uint(row["trial"], f"{context}: trial")
        key = (operation, implementation, interface, trial)
        if key in seen:
            raise ReportError(f"{context}: duplicate timing row {key}")
        seen.add(key)
        ns_per_call = _parse_finite_float(
            row["ns_per_call"], f"{context}: ns_per_call", True)
        rows[(operation, implementation, interface)].append(
            TimingRow(
                operation,
                implementation,
                interface,
                trial,
                ns_per_call,
            )
        )

    metadata, data_rows = _read_tsv(path, RQ3_PERFORMANCE_HEADER, handle)
    rq3_metadata = (
        "rq3_schema_version",
        "build",
        "input_count",
        "trial_count",
        "composite_interfaces",
        "exact_transform_interface",
        "input_fingerprint",
        "quantile",
        "exact_schedule",
        "composite_schedule",
        "timer",
        "data_rows",
        "completed",
    )
    _require_metadata(path, metadata, rq3_metadata)
    _require_exact_metadata(path, metadata, rq3_metadata)
    if metadata["rq3_schema_version"] != "4":
        raise _error(path, None, "rq3_schema_version must be 4")
    build = metadata["build"]
    if build not in ("compcert", "clang"):
        raise _error(path, None, "build must be compcert or clang")
    if not LOWER_FINGERPRINT_RE.fullmatch(metadata["input_fingerprint"]):
        raise _error(path, None, "input_fingerprint must contain 16 lowercase hexadecimal digits")
    input_count = _parse_positive_uint(metadata["input_count"], f"{path}: input_count")
    trial_count = _parse_positive_uint(metadata["trial_count"], f"{path}: trial_count")
    if trial_count % 24:
        raise _error(path, None, "trial_count must be a multiple of 24")
    if metadata["composite_interfaces"] != "default:two-stage,strong:input-only":
        raise _error(path, None, "unsupported composite interface labels")
    if metadata["exact_transform_interface"] != "default:guarded":
        raise _error(path, None, "unsupported exact-transform interface label")
    if metadata["quantile"] != "linear_interpolation_p_times_n_minus_1":
        raise _error(path, None, "unsupported quantile rule")
    if metadata["exact_schedule"] != "all_six_permutations":
        raise _error(path, None, "unsupported exact-transform schedule")
    if metadata["composite_schedule"] != "all_twenty_four_permutations":
        raise _error(path, None, "unsupported composite schedule")
    if metadata["timer"] != "std_chrono_steady_clock":
        raise _error(path, None, "unsupported timer")
    del input_count  # Validated here and cross-checked against the manifest later.

    expected_series: Set[Tuple[str, str, str]] = set()
    for operation in OPERATIONS:
        expected_series.update({
            (operation, "dd_lib", "default"),
            (operation, "dd_lib", "kernel"),
            (operation, "QD", "reference"),
        })
        if operation in COMPOSITE_OPERATIONS:
            expected_series.add((operation, "dd_lib", "strong"))
    if set(rows) != expected_series:
        raise ReportError("RQ3 operation/interface inventory is incomplete")
    for key, series in rows.items():
        series.sort(key=lambda item: item.trial)
        if [item.trial for item in series] != list(range(trial_count)):
            raise ReportError(f"RQ3 {key}: trials must be contiguous from zero")

    summaries: Dict[Tuple[str, str, str], QuantileSummary] = {}
    for key, series in rows.items():
        summaries[key] = summarize_values([item.ns_per_call for item in series])
    return RQ3PerformanceData(build, metadata, data_rows, dict(rows), summaries)


def _rq3_paired_summary(
    data: RQ3PerformanceData,
    operation: str,
    numerator: Tuple[str, str],
    denominator: Tuple[str, str],
    combine: Callable[[float, float], float],
) -> QuantileSummary:
    left = data.rows[(operation, numerator[0], numerator[1])]
    right = data.rows[(operation, denominator[0], denominator[1])]
    if [item.trial for item in left] != [item.trial for item in right]:
        raise ReportError(f"RQ3 {data.build} {operation}: paired trials do not align")
    return summarize_values([
        combine(left_item.ns_per_call, right_item.ns_per_call)
        for left_item, right_item in zip(left, right)
    ])


def _rq3_ratio_to_kernel(
    data: RQ3PerformanceData, operation: str, interface: str
) -> QuantileSummary:
    return _rq3_paired_summary(
        data, operation, ("dd_lib", interface), ("dd_lib", "kernel"),
        lambda interface_ns, kernel_ns: interface_ns / kernel_ns,
    )


def _rq3_ratio_to_qd(
    data: RQ3PerformanceData, operation: str, interface: str
) -> QuantileSummary:
    return _rq3_paired_summary(
        data, operation, ("dd_lib", interface), ("QD", "reference"),
        lambda interface_ns, qd_ns: interface_ns / qd_ns,
    )


@dataclass
class PartitionCounts:
    generated: int = 0
    both_return: int = 0
    default_only: int = 0
    strong_only: int = 0
    neither_input: int = 0
    neither_post: int = 0

    @property
    def default_return(self) -> int:
        return self.both_return + self.default_only

    @property
    def strong_return(self) -> int:
        return self.both_return + self.strong_only

    def add(self, default: str, strong: str) -> None:
        self.generated += 1
        if default == "normal" and strong == "normal":
            self.both_return += 1
        elif default == "normal":
            self.default_only += 1
        elif strong == "normal":
            self.strong_only += 1
        elif default == "input_check":
            self.neither_input += 1
        elif default == "post_compute":
            self.neither_post += 1
        else:
            raise ReportError("invalid RQ2 outcome partition")


@dataclass
class EftOutcomeCounts:
    generated: int = 0
    input_check: int = 0
    normal: int = 0

    def add(self, outcome: str) -> None:
        self.generated += 1
        if outcome == "input_check":
            self.input_check += 1
        elif outcome == "normal":
            self.normal += 1
        else:
            raise ReportError("invalid RQ2 EFT outcome")


@dataclass
class DwRejectedCounts:
    rejected: int = 0
    qd_nonfinite: int = 0
    qd_finite_invalid_dw: int = 0
    qd_finite_valid_above_bound: int = 0
    qd_finite_valid_within_bound: int = 0

    def add(self, finite: bool, valid: bool, within_bound: bool) -> None:
        self.rejected += 1
        if not finite:
            self.qd_nonfinite += 1
        elif not valid:
            self.qd_finite_invalid_dw += 1
        elif not within_bound:
            self.qd_finite_valid_above_bound += 1
        else:
            self.qd_finite_valid_within_bound += 1

    def validate(self, context: str) -> None:
        classified = (
            self.qd_nonfinite + self.qd_finite_invalid_dw
            + self.qd_finite_valid_above_bound
            + self.qd_finite_valid_within_bound
        )
        if classified != self.rejected:
            raise ReportError(f"{context}: QD classes do not partition rejected inputs")


@dataclass
class EftRejectedCounts:
    rejected: int = 0
    qd_nonfinite: int = 0
    qd_finite_invalid_dw: int = 0
    qd_finite_valid_failed_reconstruction: int = 0
    qd_finite_valid_exact_reconstruction: int = 0

    def add(self, finite: bool, valid: bool, exact: bool) -> None:
        self.rejected += 1
        if not finite:
            self.qd_nonfinite += 1
        elif not valid:
            self.qd_finite_invalid_dw += 1
        elif not exact:
            self.qd_finite_valid_failed_reconstruction += 1
        else:
            self.qd_finite_valid_exact_reconstruction += 1

    def validate(self, context: str) -> None:
        classified = (
            self.qd_nonfinite + self.qd_finite_invalid_dw
            + self.qd_finite_valid_failed_reconstruction
            + self.qd_finite_valid_exact_reconstruction
        )
        if classified != self.rejected:
            raise ReportError(f"{context}: QD classes do not partition rejected inputs")


@dataclass
class ObservedExponentRange:
    minimum: Optional[int] = None
    maximum: Optional[int] = None
    saw_zero: bool = False
    saw_nonfinite: bool = False
    saw_not_evaluated: bool = False

    def add(self, value: str) -> None:
        if value == "zero":
            self.saw_zero = True
            return
        if value == "nonfinite":
            self.saw_nonfinite = True
            return
        if value == "not_evaluated":
            self.saw_not_evaluated = True
            return
        parsed = int(value, 10)
        self.minimum = parsed if self.minimum is None else min(self.minimum, parsed)
        self.maximum = parsed if self.maximum is None else max(self.maximum, parsed)


@dataclass(frozen=True)
class BoundaryObservation:
    case_id: int
    operation: str
    name: str
    default_outcome: str
    strong_outcome: str
    failure_mask: int


@dataclass(frozen=True)
class RQ2AboveBoundResult:
    operation: str
    case_id: int
    rejected_by: Tuple[str, ...]
    inputs: str
    result_hi_bits: str
    result_lo_bits: str
    reference: str
    absolute_error: str
    bound: str


@dataclass
class RQ2AcceptanceData:
    metadata: Dict[str, str]
    data_rows: int
    partitions: Dict[str, PartitionCounts]
    eft_outcomes: Dict[str, EftOutcomeCounts]
    dw_rejected: Dict[Tuple[str, str], DwRejectedCounts]
    eft_rejected: Dict[str, EftRejectedCounts]
    failure_counts: Dict[str, Dict[str, int]]
    default_only_ranges: Dict[str, Dict[str, ObservedExponentRange]]
    boundaries: List[BoundaryObservation]
    above_bound_results: List[RQ2AboveBoundResult]
    first_bins_seen: Dict[str, Set[int]]
    second_bins_seen: Dict[str, Set[int]]


def _canonical_failure_names(mask: int) -> str:
    names = [name for bit, name in FAILURE_BITS if mask & bit]
    return ",".join(names) if names else "-"


def _parse_mask(text: str, context: str) -> int:
    if not HEX_MASK_RE.fullmatch(text):
        raise ReportError(f"{context}: failure mask must be 0xNN")
    value = int(text, 16)
    if value & ~0x1F:
        raise ReportError(f"{context}: failure mask has unknown bits")
    return value


def _parse_log_exponent(text: str, minimum: int, maximum: int, context: str) -> int:
    try:
        value = int(text, 10)
    except ValueError as exc:
        raise ReportError(f"{context}: expected an integer exponent") from exc
    if value < minimum or value > maximum:
        raise ReportError(f"{context}: exponent {value} is outside [{minimum},{maximum}]")
    return value


def _validate_boundary_exponent(text: str, context: str) -> None:
    if text in ("zero", "nonfinite"):
        return
    try:
        int(text, 10)
    except ValueError as exc:
        raise ReportError(f"{context}: invalid boundary exponent {text!r}") from exc


CHECKED_EXPONENT_LABELS: Mapping[str, Tuple[str, ...]] = {
    "dw_plus_fp": ("first_high", "second_high"),
    "dw_times_fp": ("leading_product",),
    "dw_div_fp": ("first_high", "leading_quotient"),
    "dw_plus_dw": ("first_high", "second_high"),
    "dw_times_dw": ("leading_product",),
    "dw_div_dw": ("leading_quotient",),
}


def _parse_checked_exponents(
    operation: str, text: str, context: str
) -> Mapping[str, str]:
    if operation in EFT_OPERATIONS:
        if text != "not_applicable":
            raise ReportError(f"{context}: EFT checked_exponents must be not_applicable")
        return {}
    expected = CHECKED_EXPONENT_LABELS[operation]
    fields = text.split(",")
    if len(fields) != len(expected):
        raise ReportError(f"{context}: wrong checked-exponent inventory")
    parsed: Dict[str, str] = {}
    for field, expected_label in zip(fields, expected):
        if field.count("=") != 1:
            raise ReportError(f"{context}: malformed checked exponent {field!r}")
        label, value = field.split("=", 1)
        if label != expected_label or value == "":
            raise ReportError(f"{context}: malformed checked exponent {field!r}")
        if value not in ("zero", "nonfinite", "not_evaluated"):
            try:
                int(value, 10)
            except ValueError as exc:
                raise ReportError(
                    f"{context}: invalid checked exponent {value!r}") from exc
        parsed[label] = value
    return parsed


def _parse_yes_no(text: str, context: str) -> bool:
    if text == "yes":
        return True
    if text == "no":
        return False
    raise ReportError(f"{context}: expected yes or no, got {text!r}")


def _bits_are_finite(text: str) -> bool:
    return ((int(text, 16) >> 52) & 0x7FF) != 0x7FF


def _validate_not_evaluated_qd(row: Mapping[str, str], context: str) -> None:
    for name in ("qd_result_hi_bits", "qd_result_lo_bits", "reference",
                 "absolute_error", "bound"):
        if row[name] != "-":
            raise ReportError(f"{context}: unevaluated QD field {name} must be '-'")
    for name in ("qd_finite", "qd_valid_dw", "qd_within_bound",
                 "qd_exact_reconstruction"):
        if row[name] != "not_evaluated":
            raise ReportError(
                f"{context}: unevaluated QD field {name} must be not_evaluated")


def _parse_qd_assessment(
    row: Mapping[str, str], operation: str, context: str
) -> Tuple[bool, bool, bool]:
    for name in ("qd_result_hi_bits", "qd_result_lo_bits"):
        if not HEX64_RE.fullmatch(row[name]):
            raise ReportError(f"{context}: malformed {name}")
    finite = _parse_yes_no(row["qd_finite"], f"{context}: qd_finite")
    bits_finite = (
        _bits_are_finite(row["qd_result_hi_bits"])
        and _bits_are_finite(row["qd_result_lo_bits"])
    )
    if finite != bits_finite:
        raise ReportError(f"{context}: qd_finite disagrees with result bits")
    valid = _parse_yes_no(row["qd_valid_dw"], f"{context}: qd_valid_dw")
    if valid and not finite:
        raise ReportError(f"{context}: a nonfinite QD result cannot be a valid DW")
    _parse_signed_decimal(row["reference"], f"{context}: reference")

    if not finite:
        if row["absolute_error"] != "inf":
            raise ReportError(f"{context}: nonfinite QD result requires infinite error")
        if row["qd_within_bound"] != "not_applicable" \
                or row["qd_exact_reconstruction"] != "not_applicable":
            raise ReportError(f"{context}: nonfinite QD predicates must be not_applicable")
        if operation in EFT_OPERATIONS:
            if row["bound"] != "-":
                raise ReportError(f"{context}: EFT row cannot carry a bound")
        else:
            recorded_bound = _parse_decimal(row["bound"], f"{context}: bound")
            expected_bound = _verified_bound_value(
                operation, _parse_signed_decimal(
                    row["reference"], f"{context}: reference"))
            if not _decimal_close(recorded_bound, expected_bound):
                raise ReportError(f"{context}: recorded bound is incorrect")
        return finite, valid, False

    absolute_error = _parse_decimal(
        row["absolute_error"], f"{context}: absolute_error")
    if operation in EFT_OPERATIONS:
        if row["qd_within_bound"] != "not_applicable" or row["bound"] != "-":
            raise ReportError(f"{context}: EFT row has an inapplicable bound field")
        exact = _parse_yes_no(
            row["qd_exact_reconstruction"],
            f"{context}: qd_exact_reconstruction")
        if exact != (absolute_error == 0):
            raise ReportError(
                f"{context}: exact-reconstruction result disagrees with its error")
        return finite, valid, exact

    if row["qd_exact_reconstruction"] != "not_applicable":
        raise ReportError(f"{context}: DW row has an EFT reconstruction result")
    within = _parse_yes_no(
        row["qd_within_bound"], f"{context}: qd_within_bound")
    bound = _parse_decimal(row["bound"], f"{context}: bound")
    reference = _parse_signed_decimal(row["reference"], f"{context}: reference")
    expected_bound = _verified_bound_value(operation, reference)
    if not _decimal_close(bound, expected_bound):
        raise ReportError(f"{context}: recorded bound is incorrect")
    comparison_within = absolute_error <= bound
    if within != comparison_within and not _decimal_close(absolute_error, bound):
        raise ReportError(
            f"{context}: within-bound result disagrees with error and bound")
    return finite, valid, within


def parse_rq2_acceptance(
    path: Path,
    shape: InputShape = DEFAULT_INPUT_SHAPE,
) -> RQ2AcceptanceData:
    partitions = {operation: PartitionCounts() for operation in COMPOSITE_OPERATIONS}
    eft_outcomes = {operation: EftOutcomeCounts() for operation in EFT_OPERATIONS}
    dw_rejected = {
        (operation, wrapper): DwRejectedCounts()
        for operation in COMPOSITE_OPERATIONS
        for wrapper in ("default", "strong")
    }
    eft_rejected = {
        operation: EftRejectedCounts() for operation in EFT_OPERATIONS
    }
    failure_counts: Dict[str, Dict[str, int]] = {
        operation: {name: 0 for _, name in FAILURE_BITS}
        for operation in COMPOSITE_OPERATIONS
    }
    default_only_ranges: Dict[str, Dict[str, ObservedExponentRange]] = {
        operation: {
            label: ObservedExponentRange()
            for label in CHECKED_EXPONENT_LABELS[operation]
        }
        for operation in COMPOSITE_OPERATIONS
    }
    boundaries: List[BoundaryObservation] = []
    above_bound_results: List[RQ2AboveBoundResult] = []
    next_log_id = {operation: 0 for operation in OPERATIONS}
    next_boundary_id = 0
    first_bins_seen = {operation: set() for operation in OPERATIONS}
    second_bins_seen = {operation: set() for operation in OPERATIONS}

    def handle(row: Mapping[str, str], line: int) -> None:
        nonlocal next_boundary_id
        context = f"{path}:{line}"
        suite = row["suite"]
        operation = row["operation"]
        if operation not in OPERATIONS:
            raise ReportError(f"{context}: unknown RQ2 operation {operation!r}")
        case_id = _parse_uint(row["case_id"], f"{context}: case_id")
        default = row["default_outcome"]
        if default not in ("input_check", "post_compute", "normal"):
            raise ReportError(f"{context}: invalid default outcome")
        if not row["inputs"] or row["inputs"] == "-":
            raise ReportError(f"{context}: inputs must identify the case")
        checked = _parse_checked_exponents(
            operation, row["checked_exponents"], context)

        if operation in EFT_OPERATIONS:
            strong = "not_applicable"
            for name in ("strong_outcome", "failure_mask",
                         "failed_additional_conditions", "shared_result_equal"):
                if row[name] != "not_applicable":
                    raise ReportError(f"{context}: EFT {name} must be not_applicable")
            if default == "post_compute":
                raise ReportError(f"{context}: EFT cannot reject after computation")
            mask = 0
            default_only = False
        else:
            strong = row["strong_outcome"]
            if strong not in ("input_check", "normal"):
                raise ReportError(
                    f"{context}: strong interface cannot have outcome {strong!r}")
            mask = _parse_mask(row["failure_mask"], context)
            if mask & ~ALLOWED_MASKS[operation]:
                raise ReportError(
                    f"{context}: failure mask contains bits not used by {operation}")
            if row["failed_additional_conditions"] != _canonical_failure_names(mask):
                raise ReportError(f"{context}: failure names do not match failure_mask")
            both = default == "normal" and strong == "normal"
            default_only = default == "normal" and strong != "normal"
            expected_shared = "yes" if both else "not_applicable"
            if row["shared_result_equal"] != expected_shared:
                raise ReportError(f"{context}: shared-result marker is inconsistent")
            if default == "input_check" and mask != 0:
                raise ReportError(
                    f"{context}: weak input rejection cannot have a strong mask")
            if strong == "normal" and mask != 0:
                raise ReportError(
                    f"{context}: strong normal return has failed conditions")
            if default_only and mask == 0:
                raise ReportError(
                    f"{context}: default-only return lacks a failed strong condition")
            if default == "post_compute" and strong == "input_check" and mask == 0:
                raise ReportError(
                    f"{context}: post-computation rejection lacks a strong mask")

        if suite == "log_stratified":
            if case_id != next_log_id[operation]:
                raise ReportError(
                    f"{context}: {operation} log case IDs must be contiguous; expected {next_log_id[operation]}"
                )
            next_log_id[operation] += 1
            if row["case_name"] != "-":
                raise ReportError(f"{context}: log-stratified case_name must be '-'")
            for name in (
                "expected_default_outcome",
                "expected_strong_outcome",
                "expected_failure_mask",
                "assertion_passed",
            ):
                if row[name] != "-":
                    raise ReportError(f"{context}: log row {name} must be '-'")
            first = _parse_log_exponent(
                row["first_exponent"],
                shape.fp_min if operation in EFT_OPERATIONS else shape.dw_min,
                shape.fp_max if operation in EFT_OPERATIONS else shape.dw_max,
                f"{context}: first_exponent"
            )
            second_limits = (
                (shape.fp_min, shape.fp_max)
                if operation in EFT_OPERATIONS or operation.endswith("_fp")
                else (shape.dw_min, shape.dw_max)
            )
            second = _parse_log_exponent(
                row["second_exponent"], second_limits[0], second_limits[1],
                f"{context}: second_exponent",
            )
            first_bins_seen[operation].add(first)
            second_bins_seen[operation].add(second)
            rejected = default != "normal" or (
                operation in COMPOSITE_OPERATIONS and strong != "normal")
            if rejected:
                finite, valid, predicate = _parse_qd_assessment(
                    row, operation, context)
            else:
                _validate_not_evaluated_qd(row, context)
                finite = valid = predicate = False

            if operation in EFT_OPERATIONS:
                eft_outcomes[operation].add(default)
                if default != "normal":
                    eft_rejected[operation].add(finite, valid, predicate)
                return

            partitions[operation].add(default, strong)
            if default != "normal":
                dw_rejected[(operation, "default")].add(
                    finite, valid, predicate)
            if strong != "normal":
                dw_rejected[(operation, "strong")].add(
                    finite, valid, predicate)
            if finite and valid and not predicate:
                rejected_by = tuple(
                    wrapper
                    for wrapper, outcome in (
                        ("default", default),
                        ("strong", strong),
                    )
                    if outcome != "normal"
                )
                if not rejected_by:
                    raise ReportError(
                        f"{context}: above-bound QD result was not rejected"
                    )
                above_bound_results.append(
                    RQ2AboveBoundResult(
                        operation,
                        case_id,
                        rejected_by,
                        row["inputs"],
                        row["qd_result_hi_bits"].lower(),
                        row["qd_result_lo_bits"].lower(),
                        row["reference"],
                        row["absolute_error"],
                        row["bound"],
                    )
                )
            if default_only:
                for bit, name in FAILURE_BITS:
                    if mask & bit:
                        failure_counts[operation][name] += 1
                for label, value in checked.items():
                    default_only_ranges[operation][label].add(value)
            return

        if suite == "boundary":
            if case_id != next_boundary_id:
                raise ReportError(
                    f"{context}: boundary IDs must be contiguous; expected {next_boundary_id}"
                )
            next_boundary_id += 1
            if operation not in COMPOSITE_OPERATIONS:
                raise ReportError(f"{context}: boundary suite contains an EFT")
            _validate_boundary_exponent(
                row["first_exponent"], f"{context}: first_exponent")
            _validate_boundary_exponent(
                row["second_exponent"], f"{context}: second_exponent")
            if row["case_name"] in ("", "-"):
                raise ReportError(f"{context}: boundary case requires a name")
            if row["expected_default_outcome"] != default:
                raise ReportError(f"{context}: observed default outcome differs from expected")
            if row["expected_strong_outcome"] != strong:
                raise ReportError(f"{context}: observed strong outcome differs from expected")
            expected_mask = _parse_mask(row["expected_failure_mask"], context)
            if expected_mask != mask:
                raise ReportError(f"{context}: observed failure mask differs from expected")
            if row["assertion_passed"] != "yes":
                raise ReportError(f"{context}: boundary assertion did not pass")
            _validate_not_evaluated_qd(row, context)
            boundaries.append(
                BoundaryObservation(case_id, operation, row["case_name"], default, strong, mask)
            )
            return

        raise ReportError(f"{context}: unknown suite {suite!r}")

    metadata, data_rows = _read_tsv(path, RQ2_ACCEPTANCE_HEADER, handle)
    rq2_metadata = (
        "rq2_schema_version",
        "generator",
        "seed",
        "input_fingerprint",
        "samples_per_exponent",
        "oracle_precision_bits",
        "division_oracle_precision_bits",
        "qd_inline",
        "qd_fma",
        "data_rows",
        "completed",
    )
    _require_metadata(path, metadata, rq2_metadata)
    _require_exact_metadata(path, metadata, rq2_metadata)
    if metadata["rq2_schema_version"] != "5":
        raise _error(path, None, "rq2_schema_version must be 5")
    if metadata["generator"] != "mpfr106-v1":
        raise _error(path, None, "generator must be mpfr106-v1")
    if not LOWER_SEED_RE.fullmatch(metadata["seed"]):
        raise _error(path, None, "seed must be lowercase hexadecimal with a 0x prefix")
    if metadata["seed"] != "0xc0ffee":
        raise _error(path, None, "seed must match the fixed input-generation seed")
    if not LOWER_FINGERPRINT_RE.fullmatch(metadata["input_fingerprint"]):
        raise _error(path, None, "input_fingerprint must contain 16 lowercase hexadecimal digits")
    samples = _parse_positive_uint(metadata["samples_per_exponent"], f"{path}: samples_per_exponent")
    if samples % 40:
        raise _error(path, None, "samples_per_exponent must be a multiple of 40")
    expected_fixed_metadata = {
        "oracle_precision_bits": "2112",
        "division_oracle_precision_bits": "4224",
        "qd_inline": "1",
        "qd_fma": "std::fma",
    }
    for key, expected in expected_fixed_metadata.items():
        if metadata[key] != expected:
            raise _error(path, None, f"{key} must be {expected}")
    if metadata.get("suite_mode") == "boundary_only":
        raise _error(path, None, "a full report cannot use an RQ2 boundary-only TSV")
    for operation in OPERATIONS:
        expected_cases = (
            shape.fp_bins if operation in EFT_OPERATIONS else shape.dw_bins
        ) * samples
        observed_cases = (
            eft_outcomes[operation].generated
            if operation in EFT_OPERATIONS else partitions[operation].generated
        )
        if observed_cases != expected_cases:
            raise ReportError(
                f"RQ2 {operation}: expected {expected_cases} log rows, found {observed_cases}"
            )
        if next_log_id[operation] != expected_cases:
            raise ReportError(f"RQ2 {operation}: incomplete case-ID sequence")
        expected_first_bins = (
            shape.fp_bins if operation in EFT_OPERATIONS else shape.dw_bins)
        if len(first_bins_seen[operation]) != expected_first_bins:
            raise ReportError(f"RQ2 {operation}: first exponent coverage is incomplete")
        expected_second_bins = (
            shape.fp_bins
            if operation in EFT_OPERATIONS or operation.endswith("_fp")
            else shape.dw_bins)
        if len(second_bins_seen[operation]) != expected_second_bins:
            raise ReportError(f"RQ2 {operation}: second exponent coverage is incomplete")
        if operation in EFT_OPERATIONS:
            outcome = eft_outcomes[operation]
            if outcome.input_check + outcome.normal != outcome.generated:
                raise ReportError(f"RQ2 {operation}: EFT outcomes do not partition inputs")
            if eft_rejected[operation].rejected != outcome.input_check:
                raise ReportError(f"RQ2 {operation}: rejected QD population is incomplete")
            eft_rejected[operation].validate(f"RQ2 {operation}")
        else:
            partition = partitions[operation]
            if partition.strong_only != 0:
                raise ReportError(f"RQ2 {operation}: observed a strong-only return")
            expected_default_rejected = partition.neither_input + partition.neither_post
            expected_strong_rejected = expected_default_rejected + partition.default_only
            if dw_rejected[(operation, "default")].rejected != expected_default_rejected:
                raise ReportError(f"RQ2 {operation}: default-rejected population is incomplete")
            if dw_rejected[(operation, "strong")].rejected != expected_strong_rejected:
                raise ReportError(f"RQ2 {operation}: strong-rejected population is incomplete")
            for wrapper in ("default", "strong"):
                dw_rejected[(operation, wrapper)].validate(
                    f"RQ2 {operation}/{wrapper}")
                detailed = sum(
                    1
                    for result in above_bound_results
                    if result.operation == operation
                    and wrapper in result.rejected_by
                )
                aggregate = dw_rejected[
                    (operation, wrapper)
                ].qd_finite_valid_above_bound
                if detailed != aggregate:
                    raise ReportError(
                        f"RQ2 {operation}/{wrapper}: above-bound detail count "
                        f"{detailed} does not match aggregate count {aggregate}"
                    )
    observed_inventory = tuple(
        (
            item.operation,
            item.name,
            item.default_outcome,
            item.strong_outcome,
            item.failure_mask,
        )
        for item in boundaries
    )
    if observed_inventory != BOUNDARY_INVENTORY:
        raise ReportError("RQ2 boundary inventory/order does not match the asserted 48-case suite")
    return RQ2AcceptanceData(
        metadata,
        data_rows,
        partitions,
        eft_outcomes,
        dw_rejected,
        eft_rejected,
        failure_counts,
        default_only_ranges,
        boundaries,
        above_bound_results,
        first_bins_seen,
        second_bins_seen,
    )


@dataclass(frozen=True)
class EvaluationRun:
    manifest: RunManifest
    rq1: RQ1Data
    rq2: RQ2AcceptanceData
    rq3: Mapping[str, RQ3PerformanceData]


def load_evaluation_run(
    run_dir: Path, shape: InputShape = DEFAULT_INPUT_SHAPE
) -> EvaluationRun:
    manifest = load_manifest(run_dir)
    rq1 = parse_rq1(manifest.artifacts["rq1"].path, shape)
    rq2 = parse_rq2_acceptance(manifest.artifacts["rq2"].path, shape)
    rq3 = {
        "compcert": parse_rq3_performance(
            manifest.artifacts["rq3_compcert"].path),
        "clang": parse_rq3_performance(manifest.artifacts["rq3_clang"].path),
    }
    validate_manifest_tsv_metadata(manifest, "rq1", rq1.metadata)
    validate_manifest_tsv_metadata(manifest, "rq2", rq2.metadata)
    for build, data in rq3.items():
        key = f"rq3_{build}"
        validate_manifest_tsv_metadata(manifest, key, data.metadata)
        if data.build != build:
            raise ReportError(f"{key} artifact declares build {data.build!r}")
    _validate_cross_run(manifest, rq1, rq2, rq3)
    return EvaluationRun(manifest, rq1, rq2, rq3)


def _validate_cross_run(
    manifest: RunManifest, rq1: RQ1Data,
    rq2: RQ2AcceptanceData, rq3: Mapping[str, RQ3PerformanceData]
) -> None:
    for key in (
        "generator", "seed", "input_fingerprint", "samples_per_exponent",
        "oracle_precision_bits",
    ):
        if rq1.metadata[key] != rq2.metadata[key]:
            raise ReportError(f"RQ1/RQ2 shared generated-input metadata {key!r} does not match")
    if (rq1.metadata["division_recheck_precision_bits"]
            != rq2.metadata["division_oracle_precision_bits"]):
        raise ReportError(
            "RQ1/RQ2 division MPFR precision metadata does not match")
    parameter_checks = (
        ("rq1_samples", rq1.metadata["samples_per_exponent"]),
        ("rq2_samples", rq2.metadata["samples_per_exponent"]),
        ("rq3_inputs", rq3["compcert"].metadata["input_count"]),
        ("rq3_trials", rq3["compcert"].metadata["trial_count"]),
    )
    for key, actual_text in parameter_checks:
        if manifest.parameters[key] != int(actual_text):
            raise ReportError(f"manifest parameter {key} disagrees with TSV metadata")
    if manifest.parameters["rq1_samples"] != manifest.parameters["rq2_samples"]:
        raise ReportError("RQ1 and RQ2 must use the same samples-per-exponent")
    for key in ("input_count", "trial_count", "input_fingerprint"):
        if rq3["compcert"].metadata[key] != rq3["clang"].metadata[key]:
            raise ReportError(f"RQ3 CompCert/Clang metadata {key!r} does not match")

    for operation in COMPOSITE_OPERATIONS:
        partition = rq2.partitions[operation]
        # With a valid strong wrapper, strong-only is impossible.  Enforcing it
        # makes the aggregate default outcome categories recoverable from the
        # five-way partition and exposes any theorem/harness regression.
        if partition.strong_only != 0:
            raise ReportError(f"RQ2 {operation}: observed a strong-only return")
        rq2_input = partition.neither_input
        rq2_post = partition.neither_post
        rq2_normal = partition.default_return
        expected = (
            rq1.count(operation, "dd_lib", "generated"),
            rq1.count(operation, "dd_lib", "input_check"),
            rq1.count(operation, "dd_lib", "post_compute"),
            rq1.count(operation, "dd_lib", "normal"),
        )
        observed = (partition.generated, rq2_input, rq2_post, rq2_normal)
        if observed != expected:
            raise ReportError(
                f"RQ1/RQ2 {operation}: default outcome totals disagree; "
                f"RQ1={expected}, RQ2={observed}"
            )

    # Artifact reports cannot silently turn a failed checked guarantee into an
    # evaluation claim. QD is contextual and is not subject to these gates.
    if manifest.profile_kind == "artifact":
        for operation in COMPOSITE_OPERATIONS:
            if rq1.count(operation, "dd_lib", "invalid_double_word"):
                raise ReportError(
                    f"RQ1 {operation}: dd_lib returned an invalid double word")
            if rq1.count(operation, "dd_lib", "zero_bound_error"):
                raise ReportError(f"RQ1 {operation}: dd_lib failed a zero bound")
            for metric in BOUND_METRICS:
                if rq1.metric(operation, "dd_lib", metric).flags:
                    raise ReportError(
                        f"RQ1 {operation}: dd_lib bound has unresolved flags")


def _markdown_count(value: int) -> str:
    return f"{value:,}"


def _markdown_percent(numerator: int, denominator: int) -> str:
    if denominator == 0:
        return "n/a"
    return f"{_paper_percent_text(numerator, denominator)}%"


def _paper_float_text(value: object) -> str:
    """Render a measured value with two significant figures."""

    decimal_value = value if isinstance(value, Decimal) else Decimal(str(value))
    if decimal_value == 0:
        return "0"
    magnitude = decimal_value.copy_abs().adjusted()
    if -4 <= magnitude < 6:
        decimal_places = max(0, 1 - magnitude)
        return f"{decimal_value:.{decimal_places}f}"
    return f"{decimal_value:.1e}"


def _paper_percent_text(numerator: int, denominator: int) -> str:
    """Format a percentage without rounding a proper subset to 100%."""

    with localcontext() as context:
        context.prec = max(
            28,
            len(str(abs(numerator))) + len(str(abs(denominator))) + 5,
        )
        percentage = Decimal(100) * Decimal(numerator) / Decimal(denominator)
        rendered = _paper_float_text(percentage)
        if numerator < denominator and Decimal(rendered) == Decimal(100):
            decimal_places = 1
            while decimal_places < context.prec:
                rendered = f"{percentage:.{decimal_places}f}"
                if Decimal(rendered) < Decimal(100):
                    break
                decimal_places += 1
        return rendered


def _paper_decimal_text(text: str) -> str:
    """Round a parsed metric to two significant figures for presentation."""

    if text in ("n/a", "-"):
        return text
    value = _parse_decimal(text, "paper-facing numeric value")
    return _paper_float_text(value)


def _diagnostic_decimal_text(text: str, signed: bool = False) -> str:
    """Show enough digits to inspect a listed case without copying raw TSVs."""

    value = (
        _parse_signed_decimal(text, "case-detail numeric value")
        if signed
        else _parse_decimal(text, "case-detail numeric value")
    )
    return format(value, ".12g")


def _error_bound_ratio_text(absolute_error: str, bound: Decimal) -> str:
    if bound == 0:
        return "infinite (zero bound)"
    with localcontext() as decimal_context:
        decimal_context.prec = 200
        ratio = _parse_decimal(
            absolute_error, "above-bound absolute error"
        ) / bound
    return format(ratio, ".12g")


def _render_rq1_above_bound_results(rq1: RQ1Data) -> str:
    heading = "### Results above bound"
    if not rq1.above_bound_results:
        return heading + "\n\nNo finite result exceeded the bound."

    operation_order = {
        operation: index for index, operation in enumerate(COMPOSITE_OPERATIONS)
    }
    implementation_order = {"dd_lib": 0, "QD": 1}
    regime_order = {regime: index for index, regime in enumerate(BOUND_REGIMES)}
    results = sorted(
        rq1.above_bound_results,
        key=lambda result: (
            operation_order[result.operation],
            implementation_order[result.implementation],
            regime_order[result.regime],
            result.case_id,
        ),
    )
    lines = [
        heading,
        "",
        "Every finite result whose MPFR-measured error exceeded the bound is "
        "listed below. MPFR's direct comparison determines this classification; "
        "displayed decimal values are rounded, while the raw TSV retains full "
        "precision.",
    ]
    for result in results:
        reference = _parse_signed_decimal(
            result.reference, "RQ1 above-bound reference"
        )
        bound = _verified_bound_value(result.operation, reference)
        lines.extend(
            (
                "",
                f"- `{result.operation}`, {result.implementation}, "
                f"{BOUND_REGIME_LABELS[result.regime]}, case "
                f"`{result.case_id}`; error / bound: "
                f"{_error_bound_ratio_text(result.absolute_error, bound)}.",
                f"  Inputs: `{result.inputs}`",
                f"  Result bits: `({result.result_hi_bits}, "
                f"{result.result_lo_bits})`; MPFR reference: "
                f"{_diagnostic_decimal_text(result.reference, signed=True)}; "
                f"absolute error: "
                f"{_diagnostic_decimal_text(result.absolute_error)}; bound: "
                f"{_diagnostic_decimal_text(str(bound))}.",
            )
        )
    return "\n".join(lines)


def _render_rq2_above_bound_results(rq2: RQ2AcceptanceData) -> str:
    heading = "#### Results above bound"
    if not rq2.above_bound_results:
        return (
            heading
            + "\n\nNo finite, valid QD result exceeded the bound on an input "
            "rejected by either wrapper."
        )

    operation_order = {
        operation: index for index, operation in enumerate(COMPOSITE_OPERATIONS)
    }
    results = sorted(
        rq2.above_bound_results,
        key=lambda result: (operation_order[result.operation], result.case_id),
    )
    lines = [
        heading,
        "",
        "Each test case is listed once. “Rejected by” identifies every "
        "wrapper whose rejected population contains it. MPFR's direct "
        "comparison determines the classification; displayed decimal values "
        "are rounded, while the raw TSV retains full precision.",
    ]
    for result in results:
        bound = _parse_decimal(result.bound, "RQ2 above-bound bound")
        rejected_by = " and ".join(result.rejected_by)
        lines.extend(
            (
                "",
                f"- `{result.operation}`, case `{result.case_id}`; rejected by "
                f"{rejected_by}; error / bound: "
                f"{_error_bound_ratio_text(result.absolute_error, bound)}.",
                f"  Inputs: `{result.inputs}`",
                f"  QD result bits: `({result.result_hi_bits}, "
                f"{result.result_lo_bits})`; MPFR reference: "
                f"{_diagnostic_decimal_text(result.reference, signed=True)}; "
                f"absolute error: "
                f"{_diagnostic_decimal_text(result.absolute_error)}; bound: "
                f"{_diagnostic_decimal_text(result.bound)}.",
            )
        )
    return "\n".join(lines)


def _md_table(headers: Sequence[str], rows: Iterable[Sequence[object]], numeric_from: int = 0) -> str:
    header = "| " + " | ".join(headers) + " |"
    alignments = ["---" if index < numeric_from else "---:" for index in range(len(headers))]
    separator = "|" + "|".join(alignments) + "|"
    body = ["| " + " | ".join(str(value) for value in row) + " |" for row in rows]
    return "\n".join([header, separator] + body)


def _timing_cell(summary: QuantileSummary) -> str:
    return (
        f"{_paper_float_text(summary.median)} "
        f"[{_paper_float_text(summary.iqr)}]"
    )


def _render_configuration(run: EvaluationRun) -> str:
    manifest = run.manifest
    raw = manifest.raw
    environment = _require_mapping(raw["environment"], "manifest.environment")
    build = _require_mapping(raw["build"], "manifest.build")
    started = str(raw["started_utc"])
    if manifest.profile_kind == "smoke":
        kind_note = (
            "These are harness-validation results, not full evaluation "
            "measurements."
        )
    else:
        kind_note = "These results use the full artifact evaluation profile."
    return (
        f"{kind_note}\n\n"
        f"- Run: `{manifest.run_id}` ({manifest.profile_name}, {manifest.profile_kind})\n"
        f"- Started: `{started}`; git revision `{_require_mapping(raw['git'], 'git')['revision']}`\n"
        f"- Host: {environment['cpu_model']} ({environment['architecture']}, {environment['os']})\n"
        f"- Verified-library compiler: {environment['compcert']} with `{build['dd_cflags']}`\n"
        f"- Native ablation compiler: {environment['clang']} with `{build['clang_cflags']} {build['strict_fp_flags']}`\n"
        f"- Driver compiler: {environment['cxx']} with `{build['cxxflags']} {build['strict_fp_flags']}`\n"
        f"- QD: {environment['qd']}; MPFR: {environment['mpfr']}; GMP: {environment['gmp']}\n"
    )


def _render_generated_test_inputs(run: EvaluationRun) -> str:
    rows = []
    labels = {"fp_x_fp": "FP x FP", "dw_x_fp": "DW x FP", "dw_x_dw": "DW x DW"}
    for input_type in RQ1_INPUT_PAIR_TYPES:
        value = run.rq1.coverage[input_type]
        first_zero = "—" if input_type == "fp_x_fp" else _markdown_count(value["first_zero_low"])
        second_zero = "—" if input_type != "dw_x_dw" else _markdown_count(value["second_zero_low"])
        rows.append(
            (
                labels[input_type],
                _markdown_count(value["cases"]),
                f"{_markdown_count(value['first_bins_seen'])}/{_markdown_count(value['first_bins_total'])}",
                f"{_markdown_count(value['second_bins_seen'])}/{_markdown_count(value['second_bins_total'])}",
                _markdown_count(value["first_positive"]),
                _markdown_count(value["second_positive"]),
                first_zero,
                second_zero,
            )
        )
    return _md_table(
        (
            "Operand types",
            "Generated test cases",
            "First-operand exponent bins (covered/total)",
            "Second-operand exponent bins (covered/total)",
            "Positive first operands (count)",
            "Positive second operands (count)",
            "First DW operands with zero low word (count)",
            "Second DW operands with zero low word (count)",
        ),
        rows,
        1,
    )


def _render_rq1_test_basis(run: EvaluationRun) -> str:
    rq1 = run.rq1
    rows = (
        ("Samples per exponent", _markdown_count(
            int(rq1.metadata["samples_per_exponent"]))),
        ("Generated test cases per DW x FP operation", _markdown_count(
            rq1.coverage["dw_x_fp"]["cases"])),
        ("Generated test cases per DW x DW operation", _markdown_count(
            rq1.coverage["dw_x_dw"]["cases"])),
        ("MPFR reference precision (bits)", _markdown_count(
            int(rq1.metadata["oracle_precision_bits"]))),
        ("MPFR division recheck precision (bits)", _markdown_count(
            int(rq1.metadata["division_recheck_precision_bits"]))),
        ("Numerical-input fingerprint", f"`{rq1.metadata['input_fingerprint']}`"),
    )
    return (
        "### Test basis\n\n"
        + _md_table(("Quantity", "Value"), rows, 1)
        + "\n\nOperations with the same operand types use the same generated "
        "test cases. RQ1 and RQ2 use the same deterministic numerical "
        "inputs. Only cases returned normally by the default wrapper enter "
        "the RQ1 accuracy tables; MPFR and QD receive identical operands for "
        "those cases."
    )


def _render_rq2_test_basis(run: EvaluationRun) -> str:
    rq2 = run.rq2
    eft_counts = {
        rq2.eft_outcomes[operation].generated for operation in EFT_OPERATIONS
    }
    mixed_counts = {
        rq2.partitions[operation].generated
        for operation in ("dw_plus_fp", "dw_times_fp", "dw_div_fp")
    }
    dw_counts = {
        rq2.partitions[operation].generated
        for operation in ("dw_plus_dw", "dw_times_dw", "dw_div_dw")
    }
    if len(eft_counts) != 1 or len(mixed_counts) != 1 or len(dw_counts) != 1:
        raise ReportError("RQ2 generated test-case counts differ within an operand type")
    rows = (
        ("Samples per exponent", _markdown_count(
            int(rq2.metadata["samples_per_exponent"]))),
        ("Generated test cases per EFT operation", _markdown_count(
            next(iter(eft_counts)))),
        ("Generated test cases per DW x FP operation", _markdown_count(
            next(iter(mixed_counts)))),
        ("Generated test cases per DW x DW operation", _markdown_count(
            next(iter(dw_counts)))),
        ("Named boundary test cases (separate suite)", _markdown_count(
            len(rq2.boundaries))),
        ("MPFR reference precision (bits)", _markdown_count(
            int(rq2.metadata["oracle_precision_bits"]))),
        ("MPFR division precision (bits)", _markdown_count(
            int(rq2.metadata["division_oracle_precision_bits"]))),
        ("Numerical-input fingerprint (same as RQ1)",
         f"`{rq2.metadata['input_fingerprint']}`"),
    )
    return "### Test basis\n\n" + _md_table(("Quantity", "Value"), rows, 1)


def _render_rq3_test_basis(run: EvaluationRun) -> str:
    metadata = run.rq3["compcert"].metadata
    test_cases = int(metadata["input_count"])
    trials = int(metadata["trial_count"])
    rows = (
        ("Test cases per trial", _markdown_count(test_cases)),
        ("Trials per table cell", _markdown_count(trials)),
        ("Timed calls per table cell", _markdown_count(test_cases * trials)),
        ("Compiler blocks", _markdown_count(len(run.rq3))),
        ("Timing-input fingerprint", f"`{metadata['input_fingerprint']}`"),
    )
    return (
        "### Test basis\n\n"
        + _md_table(("Timing quantity", "Value"), rows, 1)
        + "\n\nEach time cell summarizes one per-trial observation for every "
        "trial; each observation is a full sweep of the timing test cases "
        "normalized to ns/call. Ratio cells use the corresponding paired "
        "observations. Every implementation of an operation uses the same "
        "timing test cases, and the two compiler blocks use bit-identical "
        "timing inputs. RQ3 uses a separate timing-input set from RQ1 and "
        "RQ2. Untimed preflight and warm-up calls are excluded from the "
        "timed-call count."
    )


def _render_rq1(run: EvaluationRun) -> str:
    rq1 = run.rq1
    outcome_rows = []
    relative_rows = []
    absolute_rows = []
    for operation in COMPOSITE_OPERATIONS:
        generated = rq1.count(operation, "dd_lib", "generated")
        rejected_by_input_check = rq1.count(
            operation, "dd_lib", "input_check")
        returned_normally = rq1.count(operation, "dd_lib", "normal")
        passed_input_check = generated - rejected_by_input_check
        outcome_rows.append(
            (
                f"`{operation}`",
                _markdown_percent(passed_input_check, generated),
                _markdown_percent(returned_normally, passed_input_check),
                _markdown_percent(returned_normally, generated),
            )
        )
        for implementation in ("dd_lib", "QD"):
            for rows, error_name, bound_name, reference_name in (
                (relative_rows, "relative_term_relative_error",
                 "relative_term_bound_utilization", "relative_term_references"),
                (absolute_rows, "absolute_term_absolute_error",
                 "absolute_term_bound_utilization", "absolute_term_references"),
            ):
                error = rq1.metric(operation, implementation, error_name)
                bound = rq1.metric(operation, implementation, bound_name)
                rows.append(
                    (
                        f"`{operation}`",
                        implementation,
                        _markdown_percent(
                            rq1.count(operation, "MPFR", reference_name),
                            returned_normally,
                        ),
                        _markdown_count(error.flags if implementation == "QD" else 0),
                        _paper_decimal_text(error.maximum_scaled),
                        _paper_decimal_text(error.mean_scaled),
                        _paper_decimal_text(bound.maximum),
                        _paper_decimal_text(bound.mean),
                        _markdown_count(bound.flags),
                    )
                )

    zero_bound_total = sum(
        rq1.count(operation, "MPFR", "zero_bound_reference")
        for operation in COMPOSITE_OPERATIONS)
    dd_zero_errors = sum(
        rq1.count(operation, "dd_lib", "zero_bound_error")
        for operation in COMPOSITE_OPERATIONS)
    qd_zero_errors = sum(
        rq1.count(operation, "QD", "zero_bound_error")
        for operation in COMPOSITE_OPERATIONS)
    qd_zero_nonfinite = sum(
        rq1.count(operation, "QD", "zero_bound_nonfinite")
        for operation in COMPOSITE_OPERATIONS)
    bound_definition = (
        r"For \(B = B_{\mathrm{relative}} + B_{\mathrm{absolute}}\), "
    )
    zero_note = (
        bound_definition
        + "zero-bound test cases among default-wrapper normal returns: 0."
        if zero_bound_total == 0 else
        bound_definition
        + "zero-bound test cases among default-wrapper normal returns: "
        f"{_markdown_count(zero_bound_total)}. Nonzero errors occurred for "
        f"`dd_lib` in {_markdown_count(dd_zero_errors)} cases and for finite QD "
        f"results in {_markdown_count(qd_zero_errors)} cases, with "
        f"{_markdown_count(qd_zero_nonfinite)} nonfinite QD results."
    )

    common_headers = (
        "Operation", "Implementation", "Test cases in range (%)",
        "Nonfinite results", None, None, "Maximum fraction of bound",
        "Mean fraction of bound", "Results above bound",
    )
    relative_headers = list(common_headers)
    relative_headers[4] = "Maximum relative error / u²"
    relative_headers[5] = "Mean relative error / u²"
    absolute_headers = list(common_headers)
    absolute_headers[4] = "Maximum absolute error / η"
    absolute_headers[5] = "Mean absolute error / η"
    return "\n\n".join(
        (
            _render_rq1_test_basis(run),
            "### Default-wrapper return rates\n\n"
            + "The output-finiteness-check pass rate is conditional on "
            "passing the input check; the other rates use all generated test "
            "cases as their denominator.\n\n"
            + _md_table(
                (
                    "Operation",
                    "Input-check pass rate",
                    "Output-finiteness-check pass rate",
                    "Normal-return rate",
                ),
                outcome_rows,
                1,
            ),
            "Both range tables include only test cases for which the `dd_lib` "
            "default wrapper returned normally. The test-cases-in-range "
            "column reports the percentage of those cases for each operation. "
            "MPFR supplies the reference and determines which term of the bound "
            "is larger. Here, "
            "`u = 2^-53` and `η = 2^-1074`. Means for QD exclude its "
            "nonfinite results.",
            "### Relative-term-dominant range\n\n"
            + _md_table(relative_headers, relative_rows, 2),
            "### Absolute-term-dominant range\n\n"
            + _md_table(absolute_headers, absolute_rows, 2),
            "QD's error is compared with the `dd_lib` bound only as context. QD "
            "may implement a different algorithm, so this is not a bound "
            "guaranteed for QD and matching bound utilization is not expected.",
            _render_rq1_above_bound_results(rq1),
            zero_note,
        )
    )


def _render_rq3_performance(run: EvaluationRun) -> str:
    rows = []
    for operation in OPERATIONS:
        for build in ("compcert", "clang"):
            data = run.rq3[build]
            kernel = data.summaries[(operation, "dd_lib", "kernel")]
            default = data.summaries[(operation, "dd_lib", "default")]
            default_ratio = _rq3_ratio_to_kernel(data, operation, "default")
            default_qd_ratio = _rq3_ratio_to_qd(data, operation, "default")
            qd = data.summaries[(operation, "QD", "reference")]
            if operation in COMPOSITE_OPERATIONS:
                strong = _timing_cell(
                    data.summaries[(operation, "dd_lib", "strong")])
                strong_ratio = _timing_cell(
                    _rq3_ratio_to_kernel(data, operation, "strong"))
                strong_qd_ratio = _timing_cell(
                    _rq3_ratio_to_qd(data, operation, "strong"))
            else:
                strong = "—"
                strong_ratio = "—"
                strong_qd_ratio = "—"
            rows.append((
                f"`{operation}`",
                "CompCert" if build == "compcert" else "Clang",
                _timing_cell(kernel),
                _timing_cell(default),
                _timing_cell(default_ratio),
                _timing_cell(default_qd_ratio),
                strong,
                strong_ratio,
                strong_qd_ratio,
                _timing_cell(qd),
            ))
    timing_results = (
        "CompCert and Clang form independent timing blocks. Time columns "
        "report median [IQR] in ns/call. Ratio columns report median [IQR] "
        "of per-trial paired ratios within the same block; a value greater "
        "than 1 means the `dd_lib` wrapper is slower than the denominator. "
        "QD time is measured directly in each block using the same inputs. "
        "The strong-precondition wrapper does not apply to the error-free "
        "transformations, so their strong columns contain em dashes. Clang "
        "is an unverified compiler ablation.\n\n"
        + _md_table(
            (
                "Operation",
                "`dd_lib` C compiler",
                "Kernel time (ns/call)",
                "Default time (ns/call)",
                "Default/kernel ratio",
                "Default/QD ratio",
                "Strong time (ns/call)",
                "Strong/kernel ratio",
                "Strong/QD ratio",
                "QD time (ns/call)",
            ),
            rows,
            2,
        )
    )
    return _render_rq3_test_basis(run) + "\n\n" + timing_results


def _render_rq2_acceptance(run: EvaluationRun) -> str:
    dw_rows = {"default": [], "strong": []}
    for operation in COMPOSITE_OPERATIONS:
        for wrapper in ("default", "strong"):
            value = run.rq2.dw_rejected[(operation, wrapper)]
            denominator = value.rejected
            cell = lambda count: (
                f"{_markdown_count(count)} "
                f"({_markdown_percent(count, denominator)})")
            dw_rows[wrapper].append((
                f"`{operation}`",
                _markdown_count(denominator),
                cell(value.qd_nonfinite),
                cell(value.qd_finite_invalid_dw),
                cell(value.qd_finite_valid_above_bound),
                cell(value.qd_finite_valid_within_bound),
            ))

    eft_rows = []
    for operation in EFT_OPERATIONS:
        value = run.rq2.eft_rejected[operation]
        denominator = value.rejected
        cell = lambda count: (
            f"{_markdown_count(count)} "
            f"({_markdown_percent(count, denominator)})")
        eft_rows.append((
            f"`{operation}`",
            _markdown_count(denominator),
            cell(value.qd_nonfinite),
            cell(value.qd_finite_invalid_dw),
            cell(value.qd_finite_valid_failed_reconstruction),
            cell(value.qd_finite_valid_exact_reconstruction),
        ))

    range_rows = []
    for operation in COMPOSITE_OPERATIONS:
        count = run.rq2.partitions[operation].default_only
        for label, observed in run.rq2.default_only_ranges[operation].items():
            if observed.minimum is None:
                finite_range = "—"
            elif observed.minimum == observed.maximum:
                finite_range = str(observed.minimum)
            else:
                finite_range = f"{observed.minimum} to {observed.maximum}"
            other_values = []
            if observed.saw_zero:
                other_values.append("`zero`")
            if observed.saw_nonfinite:
                other_values.append("`nonfinite`")
            if observed.saw_not_evaluated:
                other_values.append("`not_evaluated`")
            range_rows.append(
                (
                    f"`{operation}`",
                    _markdown_count(count),
                    f"`{label}`",
                    finite_range,
                    ", ".join(other_values) if other_values else "—",
                )
            )

    return "\n\n".join(
        (
            _render_rq2_test_basis(run),
            "QD is evaluated only on generated test cases rejected by the "
            "wrapper named in the table heading. For each row, percentages "
            "use that wrapper's rejected test cases as the denominator. The default- and "
            "strong-rejected populations "
            "overlap and must not be added. For QD, the bound is the `dd_lib` "
            "bound used as an empirical comparison threshold, not a QD guarantee.",
            "### Double-word operations\n\n"
            "#### Default weak-precondition wrapper\n\n"
            + _md_table(
                ("Operation", "Rejected test cases",
                 "QD nonfinite", "QD finite but invalid DW",
                 "QD finite, valid, above bound",
                 "QD finite, valid, within bound"),
                dw_rows["default"], 1)
            + "\n\n#### Strong-precondition wrapper\n\n"
            + _md_table(
                ("Operation", "Rejected test cases",
                 "QD nonfinite", "QD finite but invalid DW",
                 "QD finite, valid, above bound",
                 "QD finite, valid, within bound"),
                dw_rows["strong"], 1),
            _render_rq2_above_bound_results(run.rq2),
            "### Error-free transformations\n\n"
            + _md_table(
                ("Operation", "Rejected test cases", "QD nonfinite",
                 "QD finite but invalid DW",
                 "QD finite, valid, failed exact reconstruction",
                 "QD finite, valid, reconstructed exactly"),
                eft_rows, 1),
            f"Boundary-case assertions: {len(run.rq2.boundaries)} passed; "
            "0 failed. They are not included in the rejection-table "
            "denominators or checked-exponent summaries.",
            "### Checked exponents for log-stratified test cases returned by "
            "default and rejected by strong\n\n"
            + _md_table(
                (
                    "Operation",
                    "Test cases",
                    "Checked quantity",
                    "Integer exponent range",
                    "Other recorded values",
                ),
                range_rows,
                5,
            ),
        )
    )


def _render_provenance(run: EvaluationRun) -> str:
    rows = []
    labels = {
        "rq1": "RQ1",
        "rq2": "RQ2",
        "rq3_compcert": "RQ3 (CompCert)",
        "rq3_clang": "RQ3 (Clang)",
    }
    for key in ("rq1", "rq2", "rq3_compcert", "rq3_clang"):
        artifact = run.manifest.artifacts[key]
        rows.append((labels[key], f"`{artifact.relative_path}`",
                     f"`{artifact.sha256}`",
                     _markdown_count(artifact.byte_count)))
    return _md_table(("Artifact", "Path", "SHA-256", "Bytes"), rows, 3)


def render_markdown(run: EvaluationRun, template_text: str) -> str:
    replacements = {
        "CONFIGURATION": _render_configuration(run),
        "PROVENANCE": _render_provenance(run),
        "GENERATED_TEST_INPUTS": _render_generated_test_inputs(run),
        "RQ1": _render_rq1(run),
        "RQ2": _render_rq2_acceptance(run),
        "RQ3": _render_rq3_performance(run),
    }
    rendered = template_text
    for key, value in replacements.items():
        marker = "{{" + key + "}}"
        if rendered.count(marker) != 1:
            raise ReportError(f"report template must contain exactly one {marker}")
        rendered = rendered.replace(marker, value)
    leftovers = re.findall(r"\{\{[A-Z0-9_]+\}\}", rendered)
    if leftovers:
        raise ReportError(f"report template has unknown placeholders: {leftovers}")
    return rendered.rstrip() + "\n"


def _json_decimal_metric(metric: RQ1Metric) -> Mapping[str, object]:
    return {
        "count": metric.count,
        "maximum": metric.maximum,
        "mean": metric.mean,
        "maximum_scaled": metric.maximum_scaled,
        "mean_scaled": metric.mean_scaled,
        "flags": metric.flags,
        "flag_kind": metric.flag_kind,
        "case_id": metric.case_id,
    }


def build_summary(run: EvaluationRun) -> Mapping[str, object]:
    rq1_operations: Dict[str, object] = {}
    for operation in COMPOSITE_OPERATIONS:
        item: Dict[str, object] = {
            "outcomes": {
                "generated_input_pairs": run.rq1.count(
                    operation, "dd_lib", "generated"),
                "rejected_by_input_check": run.rq1.count(
                    operation, "dd_lib", "input_check"),
                "rejected_by_output_finiteness_check": run.rq1.count(
                    operation, "dd_lib", "post_compute"),
                "returned_normally": run.rq1.count(
                    operation, "dd_lib", "normal"),
            },
            "dd_lib_invalid_double_word": run.rq1.count(
                operation, "dd_lib", "invalid_double_word"),
            "qd_invalid_double_word": run.rq1.count(
                operation, "QD", "invalid_double_word"),
            "qd_nonfinite": run.rq1.count(operation, "QD", "nonfinite"),
            "zero_bound": {
                "input_pairs": run.rq1.count(
                    operation, "MPFR", "zero_bound_reference"),
                "dd_lib_nonzero_error": run.rq1.count(
                    operation, "dd_lib", "zero_bound_error"),
                "qd_nonzero_error": run.rq1.count(
                    operation, "QD", "zero_bound_error"),
                "qd_nonfinite": run.rq1.count(
                    operation, "QD", "zero_bound_nonfinite"),
            },
        }
        item["ranges"] = {}
        for range_name, reference_count, error_name, bound_name in (
            ("relative_term_dominant", "relative_term_references",
             "relative_term_relative_error",
             "relative_term_bound_utilization"),
            ("absolute_term_dominant", "absolute_term_references",
             "absolute_term_absolute_error",
             "absolute_term_bound_utilization"),
        ):
            range_item: Dict[str, object] = {
                "input_pairs": run.rq1.count(
                    operation, "MPFR", reference_count),
            }
            for implementation in ("dd_lib", "QD"):
                error = run.rq1.metric(operation, implementation, error_name)
                range_item[implementation] = {
                    "nonfinite": error.flags if implementation == "QD" else 0,
                    "error": _json_decimal_metric(error),
                    "bound_fraction": _json_decimal_metric(
                        run.rq1.metric(operation, implementation, bound_name)),
                }
            item["ranges"][range_name] = range_item
        if operation in DIVISION_OPERATIONS:
            item["higher_precision_bound_rechecks"] = {
                "rechecked": run.rq1.count(
                    operation, "MPFR", "bound_rechecks"),
                "decision_changes": run.rq1.count(
                    operation, "MPFR", "bound_decision_changes"),
            }
        rq1_operations[operation] = item

    rq3_operations: Dict[str, object] = {}
    def timing_json(value: QuantileSummary) -> Mapping[str, float]:
        return {
            "median": value.median,
            "first_quartile": value.first_quartile,
            "third_quartile": value.third_quartile,
            "iqr": value.iqr,
        }

    for operation in OPERATIONS:
        operation_builds: Dict[str, object] = {}
        for build in ("compcert", "clang"):
            data = run.rq3[build]
            interfaces: Dict[str, object] = {
                "kernel": timing_json(
                    data.summaries[(operation, "dd_lib", "kernel")]),
                "default": {
                    **timing_json(
                        data.summaries[(operation, "dd_lib", "default")]),
                    "paired_kernel_ratio": timing_json(
                        _rq3_ratio_to_kernel(data, operation, "default")),
                    "paired_qd_ratio": timing_json(
                        _rq3_ratio_to_qd(data, operation, "default")),
                },
                "reference": {
                    "implementation": "QD",
                    **timing_json(
                        data.summaries[(operation, "QD", "reference")]),
                },
            }
            if operation in COMPOSITE_OPERATIONS:
                interfaces["strong"] = {
                    **timing_json(
                        data.summaries[(operation, "dd_lib", "strong")]),
                    "paired_kernel_ratio": timing_json(
                        _rq3_ratio_to_kernel(data, operation, "strong")),
                    "paired_qd_ratio": timing_json(
                        _rq3_ratio_to_qd(data, operation, "strong")),
                }
            operation_builds[build] = interfaces
        rq3_operations[operation] = operation_builds

    rq2_dw_operations: Dict[str, object] = {}
    for operation in COMPOSITE_OPERATIONS:
        partition = run.rq2.partitions[operation]
        rejected_by_wrapper: Dict[str, object] = {}
        for wrapper in ("default", "strong"):
            value = run.rq2.dw_rejected[(operation, wrapper)]
            rejected_by_wrapper[wrapper] = {
                "rejected_input_pairs": value.rejected,
                "qd_nonfinite": value.qd_nonfinite,
                "qd_finite_invalid_double_word": value.qd_finite_invalid_dw,
                "qd_finite_valid_above_bound": value.qd_finite_valid_above_bound,
                "qd_finite_valid_within_bound": value.qd_finite_valid_within_bound,
            }
        range_json = {}
        for label, value in run.rq2.default_only_ranges[operation].items():
            range_json[label] = {
                "minimum": value.minimum,
                "maximum": value.maximum,
                "includes_zero": value.saw_zero,
                "includes_nonfinite": value.saw_nonfinite,
                "includes_not_evaluated": value.saw_not_evaluated,
            }
        rq2_dw_operations[operation] = {
            "wrapper_outcomes": {
                "generated": partition.generated,
                "both_return": partition.both_return,
                "default_only": partition.default_only,
                "strong_only": partition.strong_only,
                "neither_input": partition.neither_input,
                "neither_post": partition.neither_post,
                "default_return": partition.default_return,
                "strong_return": partition.strong_return,
            },
            "rejected_by_wrapper": rejected_by_wrapper,
            "failure_counts": run.rq2.failure_counts[operation],
            "default_only_checked_exponent_ranges": range_json,
        }

    rq2_eft_operations: Dict[str, object] = {}
    for operation in EFT_OPERATIONS:
        outcome = run.rq2.eft_outcomes[operation]
        value = run.rq2.eft_rejected[operation]
        rq2_eft_operations[operation] = {
            "outcomes": {
                "generated": outcome.generated,
                "input_check": outcome.input_check,
                "normal": outcome.normal,
            },
            "rejected_input_pairs": value.rejected,
            "qd_nonfinite": value.qd_nonfinite,
            "qd_finite_invalid_double_word": value.qd_finite_invalid_dw,
            "qd_finite_valid_failed_exact_reconstruction": (
                value.qd_finite_valid_failed_reconstruction),
            "qd_finite_valid_exact_reconstruction": (
                value.qd_finite_valid_exact_reconstruction),
        }

    rq1_above_bound_results = []
    for result in run.rq1.above_bound_results:
        reference = _parse_signed_decimal(
            result.reference, "RQ1 summary above-bound reference"
        )
        bound = _verified_bound_value(result.operation, reference)
        with localcontext() as decimal_context:
            decimal_context.prec = 200
            bound_fraction = (
                None
                if bound == 0
                else str(
                    _parse_decimal(
                        result.absolute_error,
                        "RQ1 summary above-bound absolute error",
                    )
                    / bound
                )
            )
        rq1_above_bound_results.append(
            {
                "operation": result.operation,
                "implementation": result.implementation,
                "range": result.regime,
                "case_id": result.case_id,
                "inputs": result.inputs,
                "result_hi_bits": result.result_hi_bits,
                "result_lo_bits": result.result_lo_bits,
                "reference": result.reference,
                "absolute_error": result.absolute_error,
                "bound": str(bound),
                "bound_fraction": bound_fraction,
            }
        )

    rq2_above_bound_results = []
    for result in run.rq2.above_bound_results:
        bound = _parse_decimal(result.bound, "RQ2 summary above-bound bound")
        with localcontext() as decimal_context:
            decimal_context.prec = 200
            bound_fraction = (
                None
                if bound == 0
                else str(
                    _parse_decimal(
                        result.absolute_error,
                        "RQ2 summary above-bound absolute error",
                    )
                    / bound
                )
            )
        rq2_above_bound_results.append(
            {
                "operation": result.operation,
                "case_id": result.case_id,
                "rejected_by": list(result.rejected_by),
                "inputs": result.inputs,
                "qd_result_hi_bits": result.result_hi_bits,
                "qd_result_lo_bits": result.result_lo_bits,
                "reference": result.reference,
                "absolute_error": result.absolute_error,
                "bound": result.bound,
                "bound_fraction": bound_fraction,
            }
        )

    return {
        "summary_schema_version": 6,
        "run_id": run.manifest.run_id,
        "profile": {"name": run.manifest.profile_name, "kind": run.manifest.profile_kind},
        "artifacts": {
            key: {
                "path": artifact.relative_path,
                "sha256": artifact.sha256,
                "bytes": artifact.byte_count,
            }
            for key, artifact in run.manifest.artifacts.items()
        },
        "rq1": {
            "metadata": run.rq1.metadata,
            "coverage": run.rq1.coverage,
            "operations": rq1_operations,
            "above_bound_results": rq1_above_bound_results,
            "diagnostic_witnesses": [
                {
                    "operation": witness.operation,
                    "implementation": witness.implementation,
                    "metric": witness.name,
                    "count": witness.count,
                    "case_id": witness.case_id,
                    "result_hi_bits": witness.result_hi_bits,
                    "result_lo_bits": witness.result_lo_bits,
                    "reference": witness.reference,
                    "absolute_error": witness.absolute_error,
                    "inputs": witness.inputs,
                }
                for _key, witness in sorted(run.rq1.witnesses.items())
            ],
        },
        "rq2": {
            "metadata": run.rq2.metadata,
            "double_word_operations": rq2_dw_operations,
            "error_free_transformations": rq2_eft_operations,
            "above_bound_results": rq2_above_bound_results,
            "boundary_cases_passed": len(run.rq2.boundaries),
        },
        "rq3": {
            "metadata": {
                build: data.metadata for build, data in run.rq3.items()
            },
            "operations": rq3_operations,
        },
    }


def render_summary_json(run: EvaluationRun) -> str:
    return json.dumps(build_summary(run), indent=2, sort_keys=True, allow_nan=False) + "\n"


def _latex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(character, character) for character in text)


def _latex_integer(value: int) -> str:
    return f"{value:,}".replace(",", "{,}")


def _latex_number(text: str) -> str:
    rendered = _paper_decimal_text(text)
    if rendered in ("n/a", "-"):
        return r"\textemdash{}"
    match = re.fullmatch(
        r"([+-]?[0-9]+(?:\.[0-9]+)?)[eE]([+-]?[0-9]+)", rendered)
    if match:
        exponent = int(match.group(2))
        return rf"${match.group(1)}\mathbin{{\times}}10^{{{exponent}}}$"
    return _latex_escape(rendered)


def _latex_count_percent(count: int, total: int) -> str:
    percentage = _markdown_percent(count, total)
    rendered_percentage = (
        r"\textemdash{}"
        if percentage == "n/a"
        else percentage.replace("%", r"\%")
    )
    return f"{_latex_integer(count)} ({rendered_percentage})"


def _latex_percent(numerator: int, denominator: int) -> str:
    percentage = _markdown_percent(numerator, denominator)
    if percentage == "n/a":
        return r"\textemdash{}"
    return percentage.replace("%", r"\%")


def render_latex_files(run: EvaluationRun) -> Mapping[str, str]:
    normal_return_count = sum(
        run.rq1.count(operation, "dd_lib", "normal")
        for operation in COMPOSITE_OPERATIONS
    )
    macros = [
        "% Generated by bench/generate_reports.py; do not edit.",
        rf"\newcommand{{\EvaluationRunID}}{{{_latex_escape(run.manifest.run_id)}}}",
        rf"\newcommand{{\RQOneInputFingerprint}}{{\texttt{{{_latex_escape(run.rq1.metadata['input_fingerprint'])}}}}}",
        rf"\newcommand{{\RQOneSamplesPerExponent}}{{{run.rq1.metadata['samples_per_exponent']}}}",
        rf"\newcommand{{\RQTwoBoundaryCases}}{{{len(run.rq2.boundaries)}}}",
        rf"\newcommand{{\RQThreeInputCount}}{{{_latex_integer(int(run.rq3['compcert'].metadata['input_count']))}}}",
        rf"\newcommand{{\RQThreeTrialCount}}{{{run.rq3['compcert'].metadata['trial_count']}}}",
        rf"\newcommand{{\RQOneNormalReturnCount}}{{{_latex_integer(normal_return_count)}}}",
    ]
    maximum_bound = max(
        (
            run.rq1.metric(operation, "dd_lib", metric_name)
            for operation in COMPOSITE_OPERATIONS
            for metric_name in BOUND_METRICS
        ),
        key=lambda metric: (
            Decimal(metric.maximum)
            if metric.maximum != "n/a"
            else Decimal("-1")
        ),
    )
    macros.append(rf"\newcommand{{\RQOneMaximumBoundRatio}}{{{_latex_number(maximum_bound.maximum)}}}")
    macros.append(rf"\newcommand{{\RQOneMaximumBoundOperation}}{{\textsc{{{DISPLAY_NAMES[maximum_bound.operation]}}}}}")
    maximum_bound_range = (
        "relative" if maximum_bound.name.startswith("relative_term_")
        else "absolute"
    )
    macros.append(
        rf"\newcommand{{\RQOneMaximumBoundRange}}{{{maximum_bound_range}}}")

    def maximum_bound_metric(range_name: str, implementation: str) -> RQ1Metric:
        return max(
            (
                run.rq1.metric(
                    operation,
                    implementation,
                    f"{range_name}_term_bound_utilization",
                )
                for operation in COMPOSITE_OPERATIONS
            ),
            key=lambda metric: (
                Decimal(metric.maximum)
                if metric.maximum != "n/a"
                else Decimal("-1")
            ),
        )

    relative_maximum = maximum_bound_metric("relative", "dd_lib")
    absolute_maximum = maximum_bound_metric("absolute", "dd_lib")
    relative_maximum_mean = max(
        (
            run.rq1.metric(
                operation, "dd_lib", "relative_term_bound_utilization"
            )
            for operation in COMPOSITE_OPERATIONS
        ),
        key=lambda metric: Decimal(metric.mean),
    )
    absolute_maximum_mean = max(
        (
            run.rq1.metric(
                operation, "dd_lib", "absolute_term_bound_utilization"
            )
            for operation in COMPOSITE_OPERATIONS
            if run.rq1.metric(
                operation, "dd_lib", "absolute_term_bound_utilization"
            ).mean != "n/a"
        ),
        key=lambda metric: Decimal(metric.mean),
    )
    qd_maximum = max(
        maximum_bound_metric("relative", "QD"),
        maximum_bound_metric("absolute", "QD"),
        key=lambda metric: Decimal(metric.maximum),
    )
    macros.extend(
        (
            rf"\newcommand{{\RQOneRelativeMaximumRatio}}{{{_latex_number(relative_maximum.maximum)}}}",
            rf"\newcommand{{\RQOneRelativeMaximumOperation}}{{\textsc{{{DISPLAY_NAMES[relative_maximum.operation]}}}}}",
            rf"\newcommand{{\RQOneAbsoluteMaximumRatio}}{{{_latex_number(absolute_maximum.maximum)}}}",
            rf"\newcommand{{\RQOneAbsoluteMaximumOperation}}{{\textsc{{{DISPLAY_NAMES[absolute_maximum.operation]}}}}}",
            rf"\newcommand{{\RQOneRelativeMaximumMean}}{{{_latex_number(relative_maximum_mean.mean)}}}",
            rf"\newcommand{{\RQOneAbsoluteMaximumMean}}{{{_latex_number(absolute_maximum_mean.mean)}}}",
            rf"\newcommand{{\RQOneQDMaximumRatio}}{{{_latex_number(qd_maximum.maximum)}}}",
            rf"\newcommand{{\RQOneQDExcessPercent}}{{{_paper_float_text((Decimal(qd_maximum.maximum) - Decimal(1)) * Decimal(100))}\%}}",
            rf"\newcommand{{\RQOneQDAboveBoundCount}}{{{_latex_integer(qd_maximum.flags)}}}",
        )
    )

    default_rejected = [
        run.rq2.dw_rejected[(operation, "default")]
        for operation in COMPOSITE_OPERATIONS
    ]
    strong_rejected = [
        run.rq2.dw_rejected[(operation, "strong")]
        for operation in COMPOSITE_OPERATIONS
    ]
    default_rejected_total = sum(value.rejected for value in default_rejected)
    double_word_generated_total = sum(
        run.rq1.count(operation, "dd_lib", "generated")
        for operation in COMPOSITE_OPERATIONS
    )
    default_nonfinite_total = sum(value.qd_nonfinite for value in default_rejected)
    default_within_total = sum(
        value.qd_finite_valid_within_bound for value in default_rejected
    )
    strong_rejected_total = sum(value.rejected for value in strong_rejected)
    strong_nonfinite_total = sum(value.qd_nonfinite for value in strong_rejected)
    strong_within_total = sum(
        value.qd_finite_valid_within_bound for value in strong_rejected
    )
    default_only_total = sum(
        run.rq2.partitions[operation].default_only
        for operation in COMPOSITE_OPERATIONS
    )
    fast_sum_rejected = run.rq2.eft_rejected["fast_2sum"]
    fast_mult_rejected = run.rq2.eft_rejected["fast_2mult"]
    macros.extend(
        (
            rf"\newcommand{{\RQTwoDefaultRejected}}{{{_latex_integer(default_rejected_total)}}}",
            rf"\newcommand{{\RQTwoDoubleWordInputCount}}{{{_latex_integer(double_word_generated_total)}}}",
            rf"\newcommand{{\RQTwoDefaultRejectedPercent}}{{{_latex_percent(default_rejected_total, double_word_generated_total)}}}",
            rf"\newcommand{{\RQTwoDefaultQDNonfinite}}{{{_latex_integer(default_nonfinite_total)}}}",
            rf"\newcommand{{\RQTwoDefaultQDNonfinitePercent}}{{{_latex_percent(default_nonfinite_total, default_rejected_total)}}}",
            rf"\newcommand{{\RQTwoDefaultQDWithin}}{{{_latex_integer(default_within_total)}}}",
            rf"\newcommand{{\RQTwoDefaultQDWithinPercent}}{{{_latex_percent(default_within_total, default_rejected_total)}}}",
            rf"\newcommand{{\RQTwoStrongRejected}}{{{_latex_integer(strong_rejected_total)}}}",
            rf"\newcommand{{\RQTwoStrongQDNonfinite}}{{{_latex_integer(strong_nonfinite_total)}}}",
            rf"\newcommand{{\RQTwoStrongQDWithin}}{{{_latex_integer(strong_within_total)}}}",
            rf"\newcommand{{\RQTwoStrongQDWithinPercent}}{{{_latex_percent(strong_within_total, strong_rejected_total)}}}",
            rf"\newcommand{{\RQTwoDefaultOnly}}{{{_latex_integer(default_only_total)}}}",
            rf"\newcommand{{\RQTwoFastSumRejected}}{{{_latex_integer(fast_sum_rejected.rejected)}}}",
            rf"\newcommand{{\RQTwoFastSumExact}}{{{_latex_integer(fast_sum_rejected.qd_finite_valid_exact_reconstruction)}}}",
            rf"\newcommand{{\RQTwoFastSumExactPercent}}{{{_latex_percent(fast_sum_rejected.qd_finite_valid_exact_reconstruction, fast_sum_rejected.rejected)}}}",
            rf"\newcommand{{\RQTwoFastMultRejected}}{{{_latex_integer(fast_mult_rejected.rejected)}}}",
            rf"\newcommand{{\RQTwoFastMultExact}}{{{_latex_integer(fast_mult_rejected.qd_finite_valid_exact_reconstruction)}}}",
            rf"\newcommand{{\RQTwoFastMultExactPercent}}{{{_latex_percent(fast_mult_rejected.qd_finite_valid_exact_reconstruction, fast_mult_rejected.rejected)}}}",
        )
    )

    compcert = run.rq3["compcert"]
    clang = run.rq3["clang"]

    def rq3_group_metrics(
        prefix: str, operations: Sequence[str], wrapper: str
    ) -> Tuple[List[Tuple[float, str]], List[Tuple[float, str]], List[Tuple[float, str]]]:
        kernel_ratios = [
            (_rq3_ratio_to_kernel(compcert, operation, wrapper).median, operation)
            for operation in operations
        ]
        qd_ratios = [
            (_rq3_ratio_to_qd(clang, operation, wrapper).median, operation)
            for operation in operations
        ]
        added_times = []
        for operation in operations:
            added = _rq3_paired_summary(
                compcert,
                operation,
                ("dd_lib", wrapper),
                ("dd_lib", "kernel"),
                lambda wrapper_ns, kernel_ns: wrapper_ns - kernel_ns,
            )
            added_times.append((added.median, operation))
        macros.extend(
            (
                rf"\newcommand{{\RQThree{prefix}MinimumKernelRatio}}{{{_paper_float_text(min(kernel_ratios)[0])}}}",
                rf"\newcommand{{\RQThree{prefix}MaximumKernelRatio}}{{{_paper_float_text(max(kernel_ratios)[0])}}}",
                rf"\newcommand{{\RQThree{prefix}MedianKernelRatio}}{{{_paper_float_text(statistics.median(value for value, _operation in kernel_ratios))}}}",
                rf"\newcommand{{\RQThree{prefix}MinimumAddedTime}}{{{_paper_float_text(min(added_times)[0])}}}",
                rf"\newcommand{{\RQThree{prefix}MaximumAddedTime}}{{{_paper_float_text(max(added_times)[0])}}}",
                rf"\newcommand{{\RQThree{prefix}MinimumQDRatio}}{{{_paper_float_text(min(qd_ratios)[0])}}}",
                rf"\newcommand{{\RQThree{prefix}MaximumQDRatio}}{{{_paper_float_text(max(qd_ratios)[0])}}}",
            )
        )
        return kernel_ratios, qd_ratios, added_times

    default_metrics = rq3_group_metrics(
        "Default", COMPOSITE_OPERATIONS, "default"
    )
    strong_metrics = rq3_group_metrics(
        "Strong", COMPOSITE_OPERATIONS, "strong"
    )
    transformation_metrics = rq3_group_metrics(
        "Transformation", EFT_OPERATIONS, "default"
    )

    all_kernel_ratios = (
        default_metrics[0] + strong_metrics[0] + transformation_metrics[0]
    )
    all_qd_ratios = default_metrics[1] + strong_metrics[1] + transformation_metrics[1]
    all_added_times = default_metrics[2] + strong_metrics[2] + transformation_metrics[2]
    macros.extend(
        (
            rf"\newcommand{{\RQThreeMinimumKernelRatio}}{{{_paper_float_text(min(all_kernel_ratios)[0])}}}",
            rf"\newcommand{{\RQThreeMaximumKernelRatio}}{{{_paper_float_text(max(all_kernel_ratios)[0])}}}",
            rf"\newcommand{{\RQThreeMinimumAddedTime}}{{{_paper_float_text(min(all_added_times)[0])}}}",
            rf"\newcommand{{\RQThreeMaximumAddedTime}}{{{_paper_float_text(max(all_added_times)[0])}}}",
            rf"\newcommand{{\RQThreeMinimumQDRatio}}{{{_paper_float_text(min(all_qd_ratios)[0])}}}",
            rf"\newcommand{{\RQThreeMaximumQDRatio}}{{{_paper_float_text(max(all_qd_ratios)[0])}}}",
        )
    )

    default_interface_rate_rows: List[str] = []
    relative_bound_rows: List[str] = []
    absolute_bound_rows: List[str] = []
    tightness_rows: List[str] = []
    for operation in COMPOSITE_OPERATIONS:
        name = rf"\textsc{{{DISPLAY_NAMES[operation]}}}"
        generated = run.rq1.count(operation, "dd_lib", "generated")
        rejected_by_input_check = run.rq1.count(
            operation, "dd_lib", "input_check")
        returned_normally = run.rq1.count(
            operation, "dd_lib", "normal")
        passed_input_check = generated - rejected_by_input_check
        default_interface_rate_rows.append(
            " & ".join(
                (
                    name,
                    _latex_percent(passed_input_check, generated),
                    _latex_percent(returned_normally, passed_input_check),
                    _latex_percent(returned_normally, generated),
                )
            ) + r" \\"
        )
        for implementation in ("dd_lib", "QD"):
            for rows, error_name, bound_name, reference_name in (
                (
                    relative_bound_rows,
                    "relative_term_relative_error",
                    "relative_term_bound_utilization",
                    "relative_term_references",
                ),
                (
                    absolute_bound_rows,
                    "absolute_term_absolute_error",
                    "absolute_term_bound_utilization",
                    "absolute_term_references",
                ),
            ):
                error = run.rq1.metric(operation, implementation, error_name)
                bound = run.rq1.metric(operation, implementation, bound_name)
                rows.append(
                    " & ".join(
                        (
                            name,
                            _latex_escape(implementation),
                            _latex_percent(
                                run.rq1.count(
                                    operation, "MPFR", reference_name),
                                returned_normally,
                            ),
                            _latex_integer(
                                error.flags if implementation == "QD" else 0),
                            _latex_number(error.maximum_scaled),
                            _latex_number(error.mean_scaled),
                            _latex_number(bound.maximum),
                            _latex_number(bound.mean),
                            _latex_integer(bound.flags),
                        )
                    ) + r" \\"
                )
        for implementation in ("dd_lib", "QD"):
            relative_bound = run.rq1.metric(
                operation, implementation, "relative_term_bound_utilization"
            )
            absolute_bound = run.rq1.metric(
                operation, implementation, "absolute_term_bound_utilization"
            )
            tightness_rows.append(
                " & ".join(
                    (
                        name,
                        _latex_escape(implementation),
                        _latex_percent(
                            run.rq1.count(
                                operation, "MPFR", "relative_term_references"
                            ),
                            returned_normally,
                        ),
                        _latex_number(relative_bound.mean),
                        _latex_number(relative_bound.maximum),
                        _latex_percent(
                            run.rq1.count(
                                operation, "MPFR", "absolute_term_references"
                            ),
                            returned_normally,
                        ),
                        _latex_number(absolute_bound.mean),
                        _latex_number(absolute_bound.maximum),
                        _latex_integer(relative_bound.flags + absolute_bound.flags),
                    )
                ) + r" \\"
            )

    timing_rows: List[str] = []
    for operation in OPERATIONS:
        compcert_data = run.rq3["compcert"]
        clang_data = run.rq3["clang"]
        compcert_kernel = compcert_data.summaries[
            (operation, "dd_lib", "kernel")
        ]
        clang_qd = clang_data.summaries[(operation, "QD", "reference")]
        wrappers = (
            (("", "default"),)
            if operation in EFT_OPERATIONS
            else (("Default", "default"), ("Strong", "strong"))
        )
        for index, (wrapper_label, wrapper) in enumerate(wrappers):
            compcert_wrapper = compcert_data.summaries[
                (operation, "dd_lib", wrapper)
            ]
            clang_wrapper = clang_data.summaries[
                (operation, "dd_lib", wrapper)
            ]
            compcert_kernel_ratio = _rq3_ratio_to_kernel(
                compcert_data, operation, wrapper
            )
            clang_qd_ratio = _rq3_ratio_to_qd(
                clang_data, operation, wrapper
            )
            timing_rows.append(
                " & ".join(
                    (
                        rf"\textsc{{{DISPLAY_NAMES[operation]}}}" if index == 0 else "",
                        wrapper_label,
                        f"{_paper_float_text(compcert_wrapper.median)} [{_paper_float_text(compcert_wrapper.iqr)}]",
                        f"{_paper_float_text(compcert_kernel.median)} [{_paper_float_text(compcert_kernel.iqr)}]",
                        f"{_paper_float_text(compcert_kernel_ratio.median)} [{_paper_float_text(compcert_kernel_ratio.iqr)}]",
                        f"{_paper_float_text(clang_wrapper.median)} [{_paper_float_text(clang_wrapper.iqr)}]",
                        f"{_paper_float_text(clang_qd.median)} [{_paper_float_text(clang_qd.iqr)}]",
                        f"{_paper_float_text(clang_qd_ratio.median)} [{_paper_float_text(clang_qd_ratio.iqr)}]",
                    )
                ) + r" \\"
            )
        if operation == EFT_OPERATIONS[-1]:
            timing_rows.append(r"\midrule")

    double_word_rejected_rows: Dict[str, List[str]] = {
        "default": [],
        "strong": [],
    }
    combined_double_word_rejected_rows: List[str] = []
    compact_double_word_rejected_rows: List[str] = []
    for operation in COMPOSITE_OPERATIONS:
        name = rf"\textsc{{{DISPLAY_NAMES[operation]}}}"
        for wrapper in ("default", "strong"):
            value = run.rq2.dw_rejected[(operation, wrapper)]
            result_cells = (
                _latex_integer(value.rejected),
                _latex_count_percent(value.qd_nonfinite, value.rejected),
                _latex_count_percent(
                    value.qd_finite_invalid_dw, value.rejected),
                _latex_count_percent(
                    value.qd_finite_valid_above_bound,
                    value.rejected,
                ),
                _latex_count_percent(
                    value.qd_finite_valid_within_bound,
                    value.rejected,
                ),
            )
            double_word_rejected_rows[wrapper].append(
                " & ".join((name, *result_cells)) + r" \\"
            )
            combined_double_word_rejected_rows.append(
                " & ".join(
                    (
                        name,
                        "Default" if wrapper == "default" else "Strong",
                        *result_cells,
                    )
                ) + r" \\"
            )
            compact_double_word_rejected_rows.append(
                " & ".join(
                    (
                        name,
                        "Default" if wrapper == "default" else "Strong",
                        _latex_integer(value.rejected),
                        _latex_percent(value.qd_nonfinite, value.rejected),
                        _latex_percent(
                            value.qd_finite_invalid_dw, value.rejected),
                        _latex_percent(
                            value.qd_finite_valid_above_bound,
                            value.rejected,
                        ),
                        _latex_percent(
                            value.qd_finite_valid_within_bound,
                            value.rejected,
                        ),
                    )
                ) + r" \\"
            )

    eft_rejected_rows: List[str] = []
    compact_eft_rejected_rows: List[str] = []
    for operation in EFT_OPERATIONS:
        name = rf"\textsc{{{DISPLAY_NAMES[operation]}}}"
        value = run.rq2.eft_rejected[operation]
        eft_rejected_rows.append(
            " & ".join(
                (
                    name,
                    _latex_integer(value.rejected),
                    _latex_count_percent(value.qd_nonfinite, value.rejected),
                    _latex_count_percent(
                        value.qd_finite_invalid_dw, value.rejected),
                    _latex_count_percent(
                        value.qd_finite_valid_failed_reconstruction,
                        value.rejected,
                    ),
                    _latex_count_percent(
                        value.qd_finite_valid_exact_reconstruction,
                        value.rejected,
                    ),
                )
            ) + r" \\"
        )
        compact_eft_rejected_rows.append(
            " & ".join(
                (
                    name,
                    _latex_integer(value.rejected),
                    _latex_percent(value.qd_nonfinite, value.rejected),
                    _latex_percent(
                        value.qd_finite_invalid_dw, value.rejected),
                    _latex_percent(
                        value.qd_finite_valid_failed_reconstruction,
                        value.rejected,
                    ),
                    _latex_percent(
                        value.qd_finite_valid_exact_reconstruction,
                        value.rejected,
                    ),
                )
            ) + r" \\"
        )

    def finish(lines: Sequence[str]) -> str:
        rows = list(lines)
        # The caller terminates the final row after \input.  This keeps
        # LaTeX's file hooks from appearing between \\ and booktabs' \noalign.
        if rows:
            row_terminator = r" \\"
            if not rows[-1].endswith(row_terminator):
                raise ReportError("generated LaTeX row lacks its terminator")
            rows[-1] = rows[-1][:-len(row_terminator)]
        return "% Generated by bench/generate_reports.py; do not edit.\n" + "\n".join(rows) + "\n"

    return {
        "evaluation_numbers.tex": "\n".join(macros) + "\n",
        "rq1_default_interface_rates_rows.tex": finish(
            default_interface_rate_rows),
        "rq1_relative_bound_rows.tex": finish(relative_bound_rows),
        "rq1_absolute_bound_rows.tex": finish(absolute_bound_rows),
        "rq1_tightness_rows.tex": finish(tightness_rows),
        "rq2_default_double_word_rejected_rows.tex": finish(
            double_word_rejected_rows["default"]),
        "rq2_strong_double_word_rejected_rows.tex": finish(
            double_word_rejected_rows["strong"]),
        # Retained for the current paper source, which still presents one
        # combined table with an explicit wrapper column.
        "rq2_double_word_rejected_rows.tex": finish(
            combined_double_word_rejected_rows),
        "rq2_double_word_compact_rows.tex": finish(
            compact_double_word_rejected_rows),
        "rq2_eft_rejected_rows.tex": finish(eft_rejected_rows),
        "rq2_eft_compact_rows.tex": finish(compact_eft_rejected_rows),
        "rq3_combined_rows.tex": finish(timing_rows),
    }


def render_all(run: EvaluationRun, template_text: str) -> Mapping[Path, bytes]:
    outputs: Dict[Path, bytes] = {
        Path("RESULTS.md"): render_markdown(run, template_text).encode("utf-8"),
        Path("summary.json"): render_summary_json(run).encode("utf-8"),
    }
    for name, content in render_latex_files(run).items():
        outputs[Path("paper") / "generated" / name] = content.encode("utf-8")
    return outputs


def write_outputs_atomically(
    output_dir: Path, outputs: Mapping[Path, bytes], check: bool = False
) -> List[str]:
    """Write reports atomically and retire known outputs from older schemas."""

    output_dir = output_dir.resolve()
    drift: List[str] = []
    if check:
        for relative, content in sorted(outputs.items(), key=lambda item: str(item[0])):
            target = output_dir / relative
            try:
                actual = target.read_bytes()
            except OSError:
                drift.append(f"missing {target}")
                continue
            if actual != content:
                drift.append(f"out of date {target}")
        for relative in OBSOLETE_REPORT_OUTPUTS:
            target = output_dir / relative
            if target.exists() or target.is_symlink():
                drift.append(f"obsolete {target}")
        return drift

    temporary_files: List[Tuple[Path, Path]] = []
    backup_files: List[Path] = []
    replaced: List[Tuple[Path, Optional[Path]]] = []
    try:
        for relative, content in sorted(outputs.items(), key=lambda item: str(item[0])):
            target = output_dir / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=f".{target.name}.", suffix=".tmp", dir=str(target.parent)
            )
            temporary = Path(temporary_name)
            try:
                with os.fdopen(descriptor, "wb") as stream:
                    stream.write(content)
                    stream.flush()
                    os.fsync(stream.fileno())
            except Exception:
                temporary.unlink(missing_ok=True)
                raise
            temporary_files.append((temporary, target))
        try:
            for temporary, target in temporary_files:
                backup: Optional[Path] = None
                if target.exists():
                    descriptor, backup_name = tempfile.mkstemp(
                        prefix=f".{target.name}.", suffix=".backup",
                        dir=str(target.parent))
                    os.close(descriptor)
                    backup = Path(backup_name)
                    backup_files.append(backup)
                    os.replace(target, backup)
                replaced.append((target, backup))
                os.replace(temporary, target)
            for relative in OBSOLETE_REPORT_OUTPUTS:
                target = output_dir / relative
                if not (target.exists() or target.is_symlink()):
                    continue
                if not (target.is_file() or target.is_symlink()):
                    raise ReportError(
                        f"obsolete report path is not a file: {target}")
                descriptor, backup_name = tempfile.mkstemp(
                    prefix=f".{target.name}.", suffix=".backup",
                    dir=str(target.parent))
                os.close(descriptor)
                backup = Path(backup_name)
                backup_files.append(backup)
                os.replace(target, backup)
                replaced.append((target, backup))
        except Exception:
            rollback_error: Optional[Exception] = None
            for target, backup in reversed(replaced):
                try:
                    target.unlink(missing_ok=True)
                    if backup is not None:
                        os.replace(backup, target)
                except Exception as exc:
                    if rollback_error is None:
                        rollback_error = exc
            if rollback_error is not None:
                raise ReportError(
                    f"report update failed and rollback was incomplete: "
                    f"{rollback_error}") from rollback_error
            raise
        for backup in backup_files:
            backup.unlink(missing_ok=True)
        return []
    finally:
        for temporary, _ in temporary_files:
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass
        for backup in backup_files:
            backup.unlink(missing_ok=True)
