#!/usr/bin/env python3
"""Test report parsing, validation, and rendering with a synthetic run fixture.

These tests exercise the reporting pipeline; they do not produce evaluation
results.
"""

from __future__ import annotations

import gzip
import hashlib
import json
import re
import sys
import tempfile
import unittest
from decimal import (
    Decimal,
    Inexact,
    ROUND_DOWN,
    ROUND_HALF_UP,
    ROUND_UP,
    Rounded,
    localcontext,
)
from pathlib import Path
from unittest import mock


BENCH = Path(__file__).resolve().parents[1]
FIXTURES = Path(__file__).resolve().parent / "fixtures" / "reporting"
sys.path.insert(0, str(BENCH))

import reporting  # noqa: E402


SHAPE = reporting.InputShape(dw_min=0, dw_max=1, fp_min=0, fp_max=1)
SAMPLES = 40
CASES = 80
FINGERPRINT = "0x0123456789abcdef"
SEED = "0xc0ffee"
GENERATOR = "mpfr106-v1"
FINITE_HI = "0x3ff0000000000000"
FINITE_LO = "0x0000000000000000"
INVALID_LO = "0x3ff0000000000000"
INFINITE_HI = "0x7ff0000000000000"

EXPECTED_MARKDOWN_PLACEHOLDERS = (
    "CONFIG_RUN_ID",
    "CONFIG_PROFILE_NAME",
    "CONFIG_PROFILE_KIND",
    "CONFIG_STARTED_UTC",
    "CONFIG_CPU_MODEL",
    "CONFIG_ARCHITECTURE",
    "CONFIG_OS",
    "CONFIG_COMPCERT",
    "CONFIG_DD_CFLAGS",
    "CONFIG_CLANG",
    "CONFIG_CLANG_FLAGS",
    "CONFIG_CXX",
    "CONFIG_CXX_FLAGS",
    "CONFIG_QD",
    "CONFIG_MPFR",
    "CONFIG_GMP",
    "PROVENANCE_ROWS",
    "GENERATED_TEST_INPUT_ROWS",
    "RQ1_SAMPLES_PER_EXPONENT",
    "RQ1_DW_FP_TEST_CASES",
    "RQ1_DW_DW_TEST_CASES",
    "RQ1_MPFR_REFERENCE_BITS",
    "RQ1_MPFR_DIVISION_RECHECK_BITS",
    "RQ1_INPUT_FINGERPRINT",
    "RQ1_RETURN_RATE_ROWS",
    "RQ1_RELATIVE_RANGE_ROWS",
    "RQ1_ABSOLUTE_RANGE_ROWS",
    "RQ1_ABOVE_BOUND_COUNT",
    "RQ1_ABOVE_BOUND_ITEMS",
    "RQ1_ZERO_BOUND_CASES",
    "RQ1_DDLIB_ZERO_BOUND_ERRORS",
    "RQ1_QD_ZERO_BOUND_ERRORS",
    "RQ1_QD_ZERO_BOUND_NONFINITE",
    "RQ2_SAMPLES_PER_EXPONENT",
    "RQ2_EFT_TEST_CASES",
    "RQ2_DW_FP_TEST_CASES",
    "RQ2_DW_DW_TEST_CASES",
    "RQ2_BOUNDARY_TEST_CASES",
    "RQ2_MPFR_REFERENCE_BITS",
    "RQ2_MPFR_DIVISION_BITS",
    "RQ2_INPUT_FINGERPRINT",
    "RQ2_DEFAULT_DW_ROWS",
    "RQ2_STRONG_DW_ROWS",
    "RQ2_ABOVE_BOUND_COUNT",
    "RQ2_ABOVE_BOUND_ITEMS",
    "RQ2_EFT_ROWS",
    "RQ2_BOUNDARY_PASSED",
    "RQ2_BOUNDARY_FAILED",
    "RQ2_CHECKED_EXPONENT_ROWS",
    "RQ3_TEST_CASES_PER_TRIAL",
    "RQ3_TRIALS_PER_CELL",
    "RQ3_TIMED_CALLS_PER_CELL",
    "RQ3_COMPILER_BLOCKS",
    "RQ3_INPUT_FINGERPRINT",
    "RQ3_PERFORMANCE_ROWS",
)


def _line(*fields: object) -> str:
    return "\t".join(str(field) for field in fields)


def _decimal(value: Decimal) -> str:
    return format(value, ".40e")


def _single_line(text: str) -> str:
    """Collapse Markdown source wrapping when checking fixed prose."""

    return " ".join(text.split())


def _rq1_text() -> tuple[str, dict[str, str]]:
    metadata = {
        "rq1_schema_version": "6",
        "generator": GENERATOR,
        "seed": SEED,
        "input_fingerprint": FINGERPRINT,
        "samples_per_exponent": str(SAMPLES),
        "construction_precision_bits": "256",
        "oracle_precision_bits": "2112",
        "division_recheck_precision_bits": "4224",
    }
    lines = [f"# {key}={value}" for key, value in metadata.items()]
    lines.append(_line(*reporting.RQ1_HEADER))
    data_rows = 0

    def count(operation: str, implementation: str, metric: str, value: int) -> None:
        nonlocal data_rows
        lines.append(
            _line(
                "count", operation, implementation, metric, value,
                "-", "-", "-", "-", 0, "none", "-", "-", "-", "-", "-", "-",
            )
        )
        data_rows += 1

    def coverage(input_type: str, metric: str, value: int) -> None:
        nonlocal data_rows
        lines.append(
            _line(
                "coverage", input_type, "inputs", metric, value,
                "-", "-", "-", "-", 0, "none", "-", "-", "-", "-", "-", "-",
            )
        )
        data_rows += 1

    def metric(
        operation: str,
        implementation: str,
        name: str,
        metric_count: int,
        maximum: Decimal,
        flags: int,
        flag_kind: str,
        reference: Decimal,
        case_id: int = 0,
    ) -> None:
        nonlocal data_rows
        if metric_count == 0:
            lines.append(
                _line(
                    "metric", operation, implementation, name, 0,
                    "n/a", "n/a", "n/a", "n/a", flags, flag_kind,
                    "-", "-", "-", "-", "-", "-",
                )
            )
            data_rows += 1
            return

        mean = maximum / 2
        if name.endswith("bound_utilization"):
            maximum_scaled = mean_scaled = "n/a"
            absolute_error = reporting._verified_bound_value(
                operation, reference
            ) * maximum
        elif name == "relative_term_relative_error":
            unit = Decimal(2) ** -106
            maximum_scaled = _decimal(maximum / unit)
            mean_scaled = _decimal(mean / unit)
            absolute_error = maximum * abs(reference)
        else:
            unit = Decimal(2) ** -1074
            maximum_scaled = _decimal(maximum / unit)
            mean_scaled = _decimal(mean / unit)
            absolute_error = maximum
        lines.append(
            _line(
                "metric", operation, implementation, name, metric_count,
                _decimal(maximum), _decimal(mean), maximum_scaled, mean_scaled,
                flags, flag_kind, case_id, FINITE_HI, FINITE_LO,
                _decimal(reference), _decimal(absolute_error),
                f"case={case_id} synthetic",
            )
        )
        data_rows += 1

    def above_bound(
        operation: str,
        implementation: str,
        regime: str,
        case_id: int,
        reference: Decimal,
        absolute_error: Decimal,
    ) -> None:
        nonlocal data_rows
        lines.append(
            _line(
                "above_bound", operation, implementation, regime, 1,
                "-", "-", "-", "-", 0, "none", case_id,
                FINITE_HI, FINITE_LO, _decimal(reference),
                _decimal(absolute_error), f"case={case_id} synthetic",
            )
        )
        data_rows += 1

    coverages = {
        "fp_x_fp": (CASES, 2, 2, 2, 2, 40, 40, CASES, CASES),
        "dw_x_fp": (CASES, 2, 2, 2, 2, 40, 40, 4, CASES),
        "dw_x_dw": (CASES, 2, 2, 2, 2, 40, 40, 4, 4),
    }
    for input_type in reporting.RQ1_INPUT_PAIR_TYPES:
        for name, value in zip(reporting.COVERAGE_METRICS, coverages[input_type]):
            coverage(input_type, name, value)

    u_squared = Decimal(2) ** -106
    eta = Decimal(2) ** -1074
    for operation in reporting.COMPOSITE_OPERATIONS:
        relative_references = 77 if operation.startswith("dw_plus") else 47
        absolute_references = 0 if operation.startswith("dw_plus") else 30
        for name, value in (
            ("generated", CASES),
            ("input_check", 2),
            ("post_compute", 1),
            ("normal", 77),
        ):
            count(operation, "dd_lib", name, value)
        count(operation, "QD", "nonfinite", 1)
        count(operation, "QD", "invalid_double_word", 0)
        count(operation, "dd_lib", "invalid_double_word", 0)
        count(operation, "MPFR", "relative_term_references", relative_references)
        count(operation, "MPFR", "absolute_term_references", absolute_references)
        count(operation, "MPFR", "zero_bound_reference", 0)
        count(operation, "dd_lib", "zero_bound_error", 0)
        count(operation, "QD", "zero_bound_error", 0)
        count(operation, "QD", "zero_bound_nonfinite", 0)

        lines.append(
            _line(
                "witness", operation, "QD", "nonfinite", 1,
                "-", "-", "-", "-", 0, "none", 0,
                INFINITE_HI, FINITE_LO, "1", "inf", "case=0 synthetic",
            )
        )
        data_rows += 1

        metric(
            operation, "dd_lib", "relative_term_relative_error",
            relative_references, u_squared, 0, "none", Decimal(1),
        )
        metric(
            operation, "QD", "relative_term_relative_error",
            relative_references - 1, u_squared, 1,
            "qd_nonfinite_in_regime", Decimal(1),
        )
        metric(
            operation, "dd_lib", "relative_term_bound_utilization",
            relative_references, Decimal("0.5"), 0,
            "bound_ratio_above_one", Decimal(1),
        )
        metric(
            operation, "QD", "relative_term_bound_utilization",
            relative_references - 1, Decimal("1.5"), 1,
            "bound_ratio_above_one", Decimal(1), 1,
        )
        above_bound(
            operation,
            "QD",
            "relative_term_dominant",
            1,
            Decimal(1),
            reporting._verified_bound_value(operation, Decimal(1))
            * Decimal("1.5"),
        )
        metric(
            operation, "dd_lib", "absolute_term_absolute_error",
            absolute_references, eta, 0, "none", Decimal(0),
        )
        metric(
            operation, "QD", "absolute_term_absolute_error",
            absolute_references, eta, 0,
            "qd_nonfinite_in_regime", Decimal(0),
        )
        metric(
            operation, "dd_lib", "absolute_term_bound_utilization",
            absolute_references, Decimal("0.5"), 0,
            "bound_ratio_above_one", Decimal(0),
        )
        metric(
            operation, "QD", "absolute_term_bound_utilization",
            absolute_references, Decimal("0.75"), 0,
            "bound_ratio_above_one", Decimal(0),
        )
        if operation in reporting.DIVISION_OPERATIONS:
            count(operation, "MPFR", "bound_rechecks", 0)
            count(operation, "MPFR", "bound_decision_changes", 0)

    metadata["data_rows"] = str(data_rows)
    metadata["completed"] = "true"
    lines.extend((f"# data_rows={data_rows}", "# completed=true"))
    return "\n".join(lines) + "\n", metadata


def _checked_exponents(operation: str, value: int = 0) -> str:
    if operation in reporting.EFT_OPERATIONS:
        return "not_applicable"
    return ",".join(
        f"{label}={value}"
        for label in reporting.CHECKED_EXPONENT_LABELS[operation]
    )


def _qd_assessment(operation: str, kind: str) -> tuple[str, ...]:
    if kind == "not_evaluated":
        return (
            "-", "-", "not_evaluated", "not_evaluated",
            "not_evaluated", "not_evaluated", "-", "-", "-",
        )
    if operation in reporting.EFT_OPERATIONS:
        if kind == "nonfinite":
            return (
                INFINITE_HI, FINITE_LO, "no", "no", "not_applicable",
                "not_applicable", "1", "inf", "-",
            )
        if kind == "invalid":
            return (
                FINITE_HI, INVALID_LO, "yes", "no", "not_applicable",
                "yes", "1", "0", "-",
            )
        if kind == "failed_exact":
            return (
                FINITE_HI, FINITE_LO, "yes", "yes", "not_applicable",
                "no", "1", "1e-100", "-",
            )
        if kind == "exact":
            return (
                FINITE_HI, FINITE_LO, "yes", "yes", "not_applicable",
                "yes", "1", "0", "-",
            )
        raise AssertionError(kind)

    bound = reporting._verified_bound_value(operation, Decimal(1))
    if kind == "nonfinite":
        return (
            INFINITE_HI, FINITE_LO, "no", "no", "not_applicable",
            "not_applicable", "1", "inf", _decimal(bound),
        )
    if kind == "invalid":
        return (
            FINITE_HI, INVALID_LO, "yes", "no", "yes",
            "not_applicable", "1", "0", _decimal(bound),
        )
    if kind == "above":
        return (
            FINITE_HI, FINITE_LO, "yes", "yes", "no",
            "not_applicable", "1", _decimal(2 * bound), _decimal(bound),
        )
    if kind == "within":
        return (
            FINITE_HI, FINITE_LO, "yes", "yes", "yes",
            "not_applicable", "1", _decimal(bound / 2), _decimal(bound),
        )
    raise AssertionError(kind)


def _rq2_text(fingerprint: str = FINGERPRINT) -> tuple[str, dict[str, str]]:
    metadata = {
        "rq2_schema_version": "5",
        "generator": GENERATOR,
        "seed": SEED,
        "input_fingerprint": fingerprint,
        "samples_per_exponent": str(SAMPLES),
        "oracle_precision_bits": "2112",
        "division_oracle_precision_bits": "4224",
        "qd_inline": "1",
        "qd_fma": "std::fma",
    }
    lines = [f"# {key}={value}" for key, value in metadata.items()]
    lines.append(_line(*reporting.RQ2_ACCEPTANCE_HEADER))
    data_rows = 0

    first_failure_bit = {
        operation: next(
            bit for bit, _name in reporting.FAILURE_BITS
            if reporting.ALLOWED_MASKS[operation] & bit
        )
        for operation in reporting.COMPOSITE_OPERATIONS
    }

    for operation in reporting.OPERATIONS:
        for case_id in range(CASES):
            first = case_id // 40
            second = case_id % 2
            if operation in reporting.EFT_OPERATIONS:
                default = "input_check" if case_id < 4 else "normal"
                strong = failure_mask = failed = shared = "not_applicable"
                qd_kind = (
                    ("nonfinite", "invalid", "failed_exact", "exact")[case_id]
                    if case_id < 4 else "not_evaluated"
                )
            else:
                bit = first_failure_bit[operation]
                if case_id < 2:
                    default, strong, mask = "input_check", "input_check", 0
                elif case_id == 2:
                    default, strong, mask = "post_compute", "input_check", bit
                elif case_id == 3:
                    default, strong, mask = "normal", "input_check", bit
                else:
                    default, strong, mask = "normal", "normal", 0
                failure_mask = f"0x{mask:02x}"
                failed = reporting._canonical_failure_names(mask)
                shared = "yes" if default == strong == "normal" else "not_applicable"
                qd_kind = (
                    ("nonfinite", "invalid", "above", "within")[case_id]
                    if case_id < 4 else "not_evaluated"
                )
            lines.append(
                _line(
                    "log_stratified", operation, case_id, first, second,
                    default, strong, failure_mask, failed,
                    _checked_exponents(operation, first), "-",
                    f"case={case_id} synthetic", shared,
                    *_qd_assessment(operation, qd_kind),
                    "-", "-", "-", "-",
                )
            )
            data_rows += 1

    for case_id, (
        operation, case_name, expected_default, expected_strong, expected_mask
    ) in enumerate(reporting.BOUNDARY_INVENTORY):
        shared = (
            "yes"
            if expected_default == expected_strong == "normal"
            else "not_applicable"
        )
        lines.append(
            _line(
                "boundary", operation, case_id, 0, 0,
                expected_default, expected_strong, f"0x{expected_mask:02x}",
                reporting._canonical_failure_names(expected_mask),
                _checked_exponents(operation), case_name,
                f"boundary={case_id}", shared,
                *_qd_assessment(operation, "not_evaluated"),
                expected_default, expected_strong, f"0x{expected_mask:02x}",
                "yes",
            )
        )
        data_rows += 1

    metadata["data_rows"] = str(data_rows)
    metadata["completed"] = "true"
    lines.extend((f"# data_rows={data_rows}", "# completed=true"))
    return "\n".join(lines) + "\n", metadata


def _rq3_text(build: str) -> tuple[str, dict[str, str]]:
    metadata = {
        "rq3_schema_version": "4",
        "build": build,
        "input_count": "64",
        "trial_count": "24",
        "composite_interfaces": "default:two-stage,strong:input-only",
        "exact_transform_interface": "default:guarded",
        "input_fingerprint": "0xfedcba9876543210",
        "quantile": "linear_interpolation_p_times_n_minus_1",
        "exact_schedule": "all_six_permutations",
        "composite_schedule": "all_twenty_four_permutations",
        "timer": "std_chrono_steady_clock",
    }
    lines = [f"# {key}={value}" for key, value in metadata.items()]
    lines.append(_line(*reporting.RQ3_PERFORMANCE_HEADER))
    row_count = 0
    for operation in reporting.OPERATIONS:
        interfaces = [("dd_lib", "kernel", 10.0), ("dd_lib", "default", 15.0)]
        if operation in reporting.COMPOSITE_OPERATIONS:
            interfaces.append(("dd_lib", "strong", 13.0))
        interfaces.append(("QD", "reference", 20.0))
        build_offset = 1.0 if build == "clang" else 0.0
        for implementation, interface, base in interfaces:
            for trial in range(24):
                lines.append(
                    _line(
                        operation, implementation, interface, trial,
                        format(base + build_offset + trial, ".17g"),
                    )
                )
                row_count += 1
    metadata["data_rows"] = str(row_count)
    metadata["completed"] = "true"
    lines.extend((f"# data_rows={row_count}", "# completed=true"))
    return "\n".join(lines) + "\n", metadata


def _digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _artifact(
    path: str, data: bytes, uncompressed: bytes | None = None
) -> dict[str, object]:
    record: dict[str, object] = {
        "path": path,
        "sha256": _digest(data),
        "bytes": len(data),
    }
    if uncompressed is not None:
        record["uncompressed_sha256"] = _digest(uncompressed)
        record["uncompressed_bytes"] = len(uncompressed)
    return record


def _manifest_base() -> dict[str, object]:
    build_values = {
        "dd_cc": "ccomp",
        "dd_cflags": "-O3",
        "clang_cc": "clang",
        "clang_cflags": "-O3",
        "cxx": "c++",
        "cxxflags": "-O3 -std=c++14",
        "strict_fp_flags": "-fno-fast-math -ffp-contract=off",
        "qd_prefix": "/test/qd",
    }
    qd_headers = [
        _artifact(f"/test/qd/include/qd/{name}", name.encode("ascii"))
        for name in ("dd_real.h", "dd_inline.h", "inline.h", "qd_config.h")
    ]
    qd_policy = _artifact("/test/bench/qd_evaluation.hpp", b"policy")
    qd_identity = {"headers": qd_headers, "policy": qd_policy}
    binaries = {
        key: {
            **_artifact(f"/test/bench/{executable}", key.encode("ascii")),
            "dynamic_dependencies": [],
        }
        for key, executable in (
            ("rq1", "rq1_accuracy"),
            ("rq2", "rq2_guard_acceptance"),
            ("rq3_compcert", "rq3_performance_compcert"),
            ("rq3_clang", "rq3_performance_clang"),
        )
    }
    commands = [
        {
            "evaluation": evaluation,
            "argv": argv,
            "exit_code": 0,
        }
        for evaluation, argv in (
            ("rq1", ["./rq1_accuracy", "40", "raw/rq1.tsv"]),
            ("rq2", ["./rq2_guard_acceptance", "40", "raw/rq2.tsv"]),
            (
                "rq3_compcert",
                ["./rq3_performance_compcert", "64", "24", "raw/rq3-compcert.tsv"],
            ),
            (
                "rq3_clang",
                ["./rq3_performance_clang", "64", "24", "raw/rq3-clang.tsv"],
            ),
        )
    ]
    return {
        "manifest_schema_version": 6,
        "status": "complete",
        "run_id": "synthetic-report-test",
        "profile": {
            "name": "unit test",
            "kind": "smoke",
            "source": _artifact("/test/evaluation_profiles.json", b"profile"),
        },
        "started_utc": "2026-08-31T12:00:00Z",
        "completed_utc": "2026-08-31T12:01:00Z",
        "build": {
            **build_values,
            "configuration": {
                **_artifact("/test/bench/.build/config.json", b"configuration"),
                "values": {
                    "config_schema_version": 3,
                    **build_values,
                    "tool_identities": {
                        "clang_cc": {},
                        "cxx": {},
                        "dd_cc": {},
                        "qd": qd_identity,
                    },
                },
            },
            "binaries": binaries,
            "qd_headers": qd_headers,
            "qd_policy": qd_policy,
        },
        "environment": {
            "os": "Test OS",
            "architecture": "test64",
            "cpu_model": "Synthetic CPU",
            "cpu_count": 1,
            "hostname": "test-host",
            "python": "Python 3",
            "compcert": "CompCert test",
            "clang": "Clang test",
            "cxx": "C++ test",
            "qd": "QD test with FMA",
            "mpfr": "MPFR test",
            "gmp": "GMP test",
            "compcert_executable": "/test/bin/ccomp",
            "clang_executable": "/test/bin/clang",
            "cxx_executable": "/test/bin/c++",
            "qd_config_executable": "/test/qd/bin/qd-config",
            "pkg_config_executable": "/test/bin/pkg-config",
        },
        "commands": commands,
        "parameters": {
            "rq1_samples": 40,
            "rq2_samples": 40,
            "rq3_inputs": 64,
            "rq3_trials": 24,
        },
        "artifacts": {},
        "tsv_metadata": {},
    }


def _write_checksums(root: Path) -> None:
    checksum_path = root / "checksums.sha256"
    paths = sorted(
        path for path in root.rglob("*")
        if (
            path.is_file()
            and path != checksum_path
            and path.relative_to(root).parts[0] != "generated"
        )
    )
    lines = [
        f"{_digest(path.read_bytes())}  {path.relative_to(root).as_posix()}"
        for path in paths
    ]
    checksum_path.write_text("\n".join(lines) + "\n", encoding="ascii")


def _set_profile_kind(root: Path, kind: str) -> None:
    manifest_path = root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["profile"]["name"] = kind
    manifest["profile"]["kind"] = kind
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    _write_checksums(root)


def _make_run(root: Path) -> None:
    manifest = _manifest_base()
    rq1_text, rq1_metadata = _rq1_text()
    rq2_text, rq2_metadata = _rq2_text()
    rq3_compcert_text, rq3_compcert_metadata = _rq3_text("compcert")
    rq3_clang_text, rq3_clang_metadata = _rq3_text("clang")
    raw = root / "raw"
    raw.mkdir()
    rq1 = rq1_text.encode("utf-8")
    rq2_uncompressed = rq2_text.encode("utf-8")
    rq2 = gzip.compress(rq2_uncompressed, compresslevel=9, mtime=0)
    rq3_compcert = rq3_compcert_text.encode("utf-8")
    rq3_clang = rq3_clang_text.encode("utf-8")
    (raw / "rq1.tsv").write_bytes(rq1)
    (raw / "rq2.tsv.gz").write_bytes(rq2)
    (raw / "rq3-compcert.tsv").write_bytes(rq3_compcert)
    (raw / "rq3-clang.tsv").write_bytes(rq3_clang)
    manifest["artifacts"] = {
        "rq1": _artifact("raw/rq1.tsv", rq1),
        "rq2": _artifact("raw/rq2.tsv.gz", rq2, rq2_uncompressed),
        "rq3_compcert": _artifact("raw/rq3-compcert.tsv", rq3_compcert),
        "rq3_clang": _artifact("raw/rq3-clang.tsv", rq3_clang),
    }
    manifest["tsv_metadata"] = {
        "rq1": rq1_metadata,
        "rq2": rq2_metadata,
        "rq3_compcert": rq3_compcert_metadata,
        "rq3_clang": rq3_clang_metadata,
    }
    (root / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    _write_checksums(root)


def _rewrite_artifact(
    root: Path,
    key: str,
    text: str,
    metadata: dict[str, str] | None = None,
) -> None:
    manifest_path = root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    record = manifest["artifacts"][key]
    path = root / record["path"]
    uncompressed = text.encode("utf-8")
    if path.suffix == ".gz":
        stored = gzip.compress(uncompressed, compresslevel=9, mtime=0)
        path.write_bytes(stored)
        record.update(_artifact(record["path"], stored, uncompressed))
    else:
        path.write_bytes(uncompressed)
        record.update(_artifact(record["path"], uncompressed))
    if metadata is not None:
        manifest["tsv_metadata"][key] = metadata
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    _write_checksums(root)


class ReportingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.run_dir = Path(self.temporary.name) / "run"
        self.run_dir.mkdir()
        _make_run(self.run_dir)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def load(self) -> reporting.EvaluationRun:
        return reporting.load_evaluation_run(self.run_dir, SHAPE)

    def template(self) -> str:
        return (BENCH / "results_template.md").read_text(encoding="utf-8")

    def render_markdown(
        self,
        run: reporting.EvaluationRun | None = None,
        template: str | None = None,
    ) -> str:
        return reporting.render_markdown(
            self.load() if run is None else run,
            self.template() if template is None else template,
        )

    def test_markdown_placeholder_inventory_is_exact(self) -> None:
        self.assertEqual(
            tuple(reporting.MARKDOWN_PLACEHOLDERS),
            EXPECTED_MARKDOWN_PLACEHOLDERS,
        )
        markers = re.findall(r"\{\{([A-Z0-9_]+)\}\}", self.template())
        self.assertEqual(tuple(markers), EXPECTED_MARKDOWN_PLACEHOLDERS)

    def test_markdown_template_rejects_missing_and_duplicate_placeholders(
        self,
    ) -> None:
        template = self.template()
        marker = "{{RQ1_RETURN_RATE_ROWS}}"
        self.assertEqual(template.count(marker), 1)
        for name, changed in (
            ("missing", template.replace(marker, "")),
            ("duplicate", template + "\n" + marker + "\n"),
        ):
            with self.subTest(name=name):
                with self.assertRaises(reporting.ReportError):
                    reporting.render_markdown(self.load(), changed)

    def test_markdown_template_rejects_unknown_and_malformed_placeholders(
        self,
    ) -> None:
        template = self.template()
        invalid_markers = (
            "{{UNKNOWN_PLACEHOLDER}}",
            "{{unknown_placeholder}}",
            "{{ RQ1_RETURN_RATE_ROWS }}",
            "{{RQ1_RETURN_RATE_ROWS}",
            "{RQ1_RETURN_RATE_ROWS}}",
        )
        for marker in invalid_markers:
            with self.subTest(marker=marker):
                with self.assertRaises(reporting.ReportError):
                    reporting.render_markdown(
                        self.load(), template + "\n" + marker + "\n"
                    )

    def test_markdown_replacements_have_only_the_declared_content_shapes(
        self,
    ) -> None:
        replacements = reporting._markdown_replacements(self.load())
        self.assertEqual(
            set(replacements), set(EXPECTED_MARKDOWN_PLACEHOLDERS)
        )

        row_widths = {
            "PROVENANCE_ROWS": 4,
            "GENERATED_TEST_INPUT_ROWS": 8,
            "RQ1_RETURN_RATE_ROWS": 4,
            "RQ1_RELATIVE_RANGE_ROWS": 9,
            "RQ1_ABSOLUTE_RANGE_ROWS": 9,
            "RQ2_DEFAULT_DW_ROWS": 6,
            "RQ2_STRONG_DW_ROWS": 6,
            "RQ2_EFT_ROWS": 6,
            "RQ2_CHECKED_EXPONENT_ROWS": 5,
            "RQ3_PERFORMANCE_ROWS": 10,
        }
        row_counts = {
            "PROVENANCE_ROWS": 4,
            "GENERATED_TEST_INPUT_ROWS": 3,
            "RQ1_RETURN_RATE_ROWS": 6,
            "RQ1_RELATIVE_RANGE_ROWS": 12,
            "RQ1_ABSOLUTE_RANGE_ROWS": 12,
            "RQ2_DEFAULT_DW_ROWS": 6,
            "RQ2_STRONG_DW_ROWS": 6,
            "RQ2_EFT_ROWS": 3,
            "RQ2_CHECKED_EXPONENT_ROWS": 9,
            "RQ3_PERFORMANCE_ROWS": 18,
        }
        for name, expected_width in row_widths.items():
            lines = replacements[name].splitlines()
            self.assertTrue(lines, name)
            self.assertEqual(len(lines), row_counts[name], name)
            for line in lines:
                with self.subTest(placeholder=name, line=line):
                    self.assertTrue(line.startswith("| "))
                    self.assertTrue(line.endswith(" |"))
                    self.assertEqual(
                        len(line.removeprefix("|").removesuffix("|").split("|")),
                        expected_width,
                    )
                    self.assertIsNone(
                        re.fullmatch(r"\|(?:\s*:?-+:?\s*\|)+", line)
                    )

        for name in ("RQ1_ABOVE_BOUND_ITEMS", "RQ2_ABOVE_BOUND_ITEMS"):
            lines = replacements[name].splitlines()
            self.assertTrue(lines, name)
            self.assertTrue(lines[0].startswith("- "), name)
            self.assertTrue(
                all(
                    not line or line.startswith(("- ", "  "))
                    for line in lines
                ),
                name,
            )

        structured = set(row_widths) | {
            "RQ1_ABOVE_BOUND_ITEMS",
            "RQ2_ABOVE_BOUND_ITEMS",
        }
        for name in set(EXPECTED_MARKDOWN_PLACEHOLDERS) - structured:
            with self.subTest(placeholder=name):
                self.assertNotIn("\n", replacements[name])
                self.assertFalse(replacements[name].startswith(("#", "|", "- ")))

    def test_rendered_markdown_tables_have_consistent_widths(self) -> None:
        lines = self.render_markdown().splitlines()
        separators = re.compile(r"^\|(?:\s*:?-+:?\s*\|)+$")
        table_count = 0
        for index, line in enumerate(lines):
            if not separators.fullmatch(line):
                continue
            table_count += 1
            self.assertGreater(index, 0)
            header_width = len(lines[index - 1].strip("|").split("|"))
            separator_width = len(line.strip("|").split("|"))
            self.assertEqual(separator_width, header_width)
            row_index = index + 1
            while row_index < len(lines) and lines[row_index].startswith("|"):
                self.assertEqual(
                    len(lines[row_index].strip("|").split("|")),
                    header_width,
                    lines[row_index],
                )
                row_index += 1
        self.assertEqual(table_count, reporting.MARKDOWN_TABLE_COUNT)

    def test_markdown_rejects_a_table_header_width_mismatch(self) -> None:
        template = self.template()
        header = "| Artifact | Path | SHA-256 | Bytes |"
        self.assertEqual(template.count(header), 1)
        malformed = template.replace(
            header,
            "| Artifact | Path | SHA-256 | Bytes | Unexpected |",
        )
        with self.assertRaises(reporting.ReportError):
            reporting.render_markdown(self.load(), malformed)

    def test_markdown_table_rows_escape_backslashes_and_pipes(self) -> None:
        row = reporting._md_rows(((r"left\|right", "value"),), 2, "test")
        self.assertEqual(
            len(reporting._split_markdown_table_row(row)),
            2,
        )

    def test_markdown_rejects_a_missing_table_separator(self) -> None:
        template = self.template()
        separator = "|---|---|---|---:|"
        self.assertEqual(template.count(separator), 1)
        malformed = template.replace(separator, "| Artifact data |", 1)
        with self.assertRaises(reporting.ReportError):
            reporting.render_markdown(self.load(), malformed)

    def test_markdown_rejects_a_misplaced_structured_placeholder(self) -> None:
        template = self.template()
        for marker in (
            "{{RQ1_RETURN_RATE_ROWS}}",
            "{{RQ1_ABOVE_BOUND_ITEMS}}",
        ):
            with self.subTest(marker=marker):
                malformed = template.replace(marker, "prefix " + marker)
                with self.assertRaises(reporting.ReportError):
                    reporting.render_markdown(self.load(), malformed)

    def test_rendered_markdown_heading_order_is_stable(self) -> None:
        headings = tuple(
            line
            for line in self.render_markdown().splitlines()
            if re.fullmatch(r"#{1,6} .+", line)
        )
        self.assertEqual(
            headings,
            (
                "# Evaluation results",
                "## Configuration",
                "## Input artifacts",
                "## Numerical test inputs used by RQ1 and RQ2",
                "## RQ1: Bound satisfaction and tightness",
                "### Test basis",
                "### Default-wrapper return rates",
                "### Relative-term-dominant range",
                "### Absolute-term-dominant range",
                "### Results above bound",
                "## RQ2: Usefulness of the wrappers",
                "### Test basis",
                "### Double-word operations",
                "#### Default wrapper",
                "#### Strong wrapper",
                "#### Results above bound",
                "### Error-free transformations",
                "### Checked exponents for log-stratified test cases returned by default and rejected by strong",
                "## RQ3: Runtime performance",
                "### Test basis",
            ),
        )

    def test_multiline_scalar_replacement_is_rejected(self) -> None:
        run = self.load()
        build = run.manifest.raw["build"]
        self.assertIsInstance(build, dict)
        build["dd_cflags"] = "-O3\nunexpected"
        with self.assertRaisesRegex(
            reporting.ReportError, "scalar Markdown replacement"
        ):
            reporting._markdown_replacements(run)

    def test_complete_run_renders_only_current_report_outputs(self) -> None:
        run = self.load()
        self.assertEqual(run.rq1.metadata["rq1_schema_version"], "6")
        self.assertEqual(run.rq2.metadata["rq2_schema_version"], "5")
        template = (BENCH / "results_template.md").read_text(encoding="utf-8")
        outputs = reporting.render_all(run, template)
        self.assertEqual(
            set(outputs),
            {
                Path("RESULTS.md"),
                Path("summary.json"),
                Path("paper/generated/evaluation_numbers.tex"),
                Path("paper/generated/rq1_default_interface_rates_rows.tex"),
                Path("paper/generated/rq1_relative_bound_rows.tex"),
                Path("paper/generated/rq1_absolute_bound_rows.tex"),
                Path("paper/generated/rq1_tightness_rows.tex"),
                Path("paper/generated/rq2_default_double_word_rejected_rows.tex"),
                Path("paper/generated/rq2_strong_double_word_rejected_rows.tex"),
                Path("paper/generated/rq2_double_word_rejected_rows.tex"),
                Path("paper/generated/rq2_double_word_compact_rows.tex"),
                Path("paper/generated/rq2_eft_rejected_rows.tex"),
                Path("paper/generated/rq2_eft_compact_rows.tex"),
                Path("paper/generated/rq3_combined_rows.tex"),
            },
        )
        self.assertNotIn(Path("rq2-bins.tsv"), outputs)
        self.assertNotIn(Path("paper/generated/rq2_acceptance_rows.tex"), outputs)
        self.assertNotIn(Path("paper/generated/rq2_failure_rows.tex"), outputs)

    def test_latex_rq3_rows_are_combined_and_grouped(self) -> None:
        rows = reporting.render_latex_files(self.load())[
            "rq3_combined_rows.tex"
        ]
        lines = rows.splitlines()
        two_sum = next(line for line in lines if r"\textsc{TwoSum}" in line)
        self.assertEqual(two_sum.count(" & "), 7)
        self.assertTrue(two_sum.endswith(r" \\"))
        self.assertEqual(rows.count(r"\textsc{"), len(reporting.OPERATIONS))
        self.assertEqual(rows.count(" & Default & "), len(reporting.COMPOSITE_OPERATIONS))
        self.assertEqual(rows.count(" & Strong & "), len(reporting.COMPOSITE_OPERATIONS))
        self.assertEqual(rows.count(r"\midrule"), 1)
        self.assertLess(rows.index(r"\textsc{Fast2Mult}"), rows.index(r"\midrule"))
        self.assertLess(rows.index(r"\midrule"), rows.index(r"\textsc{DWPlusFP}"))

    def test_markdown_has_rq1_ranges_and_rq2_tables(self) -> None:
        run = self.load()
        template = (BENCH / "results_template.md").read_text(encoding="utf-8")
        markdown = reporting.render_all(run, template)[Path("RESULTS.md")].decode()
        self.assertIn("## Numerical test inputs used by RQ1 and RQ2", markdown)
        self.assertNotIn("## Generated test inputs", markdown)
        self.assertEqual(markdown.count("### Test basis"), 3)
        self.assertIn("### Default-wrapper return rates", markdown)
        self.assertIn("Input-check pass rate", markdown)
        self.assertIn("Output-finiteness-check pass rate", markdown)
        self.assertIn("Normal-return rate", markdown)
        self.assertIn("### Relative-term-dominant range", markdown)
        self.assertIn("Test cases in range (%)", markdown)
        self.assertIn("Maximum relative error / u²", markdown)
        self.assertIn("### Absolute-term-dominant range", markdown)
        self.assertIn("Maximum absolute error / η", markdown)
        self.assertIn("### Results above bound", markdown)
        self.assertIn("### Double-word operations", markdown)
        self.assertIn("#### Default wrapper", markdown)
        self.assertIn("#### Strong wrapper", markdown)
        self.assertNotIn("Rejected by wrapper", markdown)
        self.assertIn("#### Results above bound", markdown)
        self.assertIn("QD finite, valid, above bound", markdown)
        self.assertIn("### Error-free transformations", markdown)
        self.assertIn("QD finite, valid, failed exact reconstruction", markdown)
        self.assertIn(
            "### Checked exponents for log-stratified test cases returned by "
            "default and rejected by strong",
            markdown,
        )
        prose = _single_line(markdown)
        self.assertIn("default- and strong-rejected populations overlap", prose)
        self.assertIn("Boundary-case assertions: 48 passed; 0 failed", prose)
        self.assertIn(
            "Each percentage is rounded independently to the nearest 0.01 "
            "percentage point; exact halfway cases use ties-to-even. "
            "Displayed categories may therefore not sum to exactly 100.00%; "
            "the integer counts are authoritative.",
            prose,
        )
        self.assertNotIn("Comparison with QD against MPFR", markdown)
        self.assertNotIn("Validity and nonzero-error diagnostics", markdown)

    def test_rq1_rates_use_the_documented_denominators(self) -> None:
        text = self.render_markdown()
        prose = _single_line(text)
        self.assertIn(
            "| Generated test cases per DW x FP operation | 80 |",
            text,
        )
        self.assertIn(
            "| Generated test cases per DW x DW operation | 80 |",
            text,
        )
        header = (
            "| Operation | Input-check pass rate | "
            "Output-finiteness-check pass rate | Normal-return rate |"
        )
        self.assertIn(header, text)
        self.assertNotIn(
            "| Operation | Generated test cases | Input-check pass rate",
            text,
        )
        self.assertIn(
            "| `dw_plus_fp` | 97.50% | 98.72% | 96.25% |",
            text,
        )
        self.assertLess(
            text.index("### Default-wrapper return rates"),
            text.index("### Relative-term-dominant range"),
        )
        self.assertIn(
            "output-finiteness-check pass rate is conditional on passing "
            "the input check",
            prose,
        )
        self.assertIn(
            r"For \(B = B_{\rm relative} + B_{\rm absolute}\), there were "
            "0 zero-bound test cases among default-wrapper normal returns.",
            prose,
        )

    def test_each_rq_reports_its_test_basis(self) -> None:
        run = self.load()
        markdown = self.render_markdown(run)
        prose = _single_line(markdown)

        rq1 = markdown
        self.assertIn("| Samples per exponent | 40 |", rq1)
        self.assertIn("| MPFR reference precision (bits) | 2,112 |", rq1)
        self.assertIn("| MPFR division precision (bits) | 4,224 |", rq1)
        self.assertIn(f"| Numerical-input fingerprint | `{FINGERPRINT}` |", rq1)
        self.assertIn(
            "RQ1 and RQ2 use the same deterministic numerical inputs", prose
        )

        rq2 = markdown
        self.assertIn("| Generated test cases per EFT operation | 80 |", rq2)
        self.assertIn(
            "| Generated test cases per DW x FP operation | 80 |", rq2
        )
        self.assertIn(
            "| Generated test cases per DW x DW operation | 80 |", rq2
        )
        self.assertIn("| Named boundary test cases (separate suite) | 48 |", rq2)
        self.assertIn(
            f"| Numerical-input fingerprint (same as RQ1) | `{FINGERPRINT}` |",
            rq2,
        )

        rq3 = markdown
        self.assertIn("| Test cases per trial | 64 |", rq3)
        self.assertIn("| Trials per table cell | 24 |", rq3)
        self.assertIn("| Timed calls per table cell | 1,536 |", rq3)
        self.assertIn("| Compiler blocks | 2 |", rq3)
        self.assertIn(
            "| Timing-input fingerprint | `0xfedcba9876543210` |", rq3
        )
        self.assertIn(
            "RQ3 uses a separate timing-input set from RQ1 and RQ2", prose
        )
        self.assertIn(
            "Untimed preflight and warm-up calls are excluded from the "
            "timed-call count",
            prose,
        )

    def test_rq1_range_tables_report_percent_of_normal_returns(self) -> None:
        text = self.render_markdown()
        self.assertIn(
            "test-cases-in-range column reports the percentage of those "
            "cases for each operation",
            _single_line(text),
        )
        self.assertIn(
            "| `dw_plus_fp` | dd_lib | 100.00% |",
            text,
        )
        self.assertIn(
            "| `dw_times_fp` | dd_lib | 61.04% |",
            text,
        )
        self.assertIn(
            "| `dw_times_fp` | QD | 61.04% |",
            text,
        )
        self.assertIn(
            "| `dw_times_fp` | dd_lib | 38.96% |",
            text,
        )
        self.assertNotIn(
            "| Operation | Implementation | Test cases in range |",
            text,
        )

    def test_rq1_presentation_rounds_without_changing_raw_values(self) -> None:
        source = "0." + "5123456789" * 10
        path = self.run_dir / "raw" / "rq1.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        prefix = (
            "metric\tdw_plus_fp\tdd_lib\t"
            "relative_term_bound_utilization\t"
        )
        index = next(
            i for i, line in enumerate(lines) if line.startswith(prefix)
        )
        fields = lines[index].split("\t")
        fields[5] = source
        with localcontext() as decimal_context:
            decimal_context.prec = 140
            fields[15] = format(
                reporting._verified_bound_value(
                    "dw_plus_fp", Decimal(fields[14])) * Decimal(source),
                ".120e",
            )
        lines[index] = "\t".join(fields)
        _rewrite_artifact(self.run_dir, "rq1", "\n".join(lines) + "\n")

        run = self.load()
        self.assertEqual(
            run.rq1.metric(
                "dw_plus_fp", "dd_lib",
                "relative_term_bound_utilization",
            ).maximum,
            source,
        )
        summary = json.loads(reporting.render_summary_json(run))
        self.assertEqual(
            summary["rq1"]["operations"]["dw_plus_fp"]["ranges"]
            ["relative_term_dominant"]["dd_lib"]["bound_fraction"]
            ["maximum"],
            source,
        )

        markdown = self.render_markdown(run)
        self.assertIn("0.51", markdown)
        self.assertNotIn(source, markdown)
        latex = reporting.render_latex_files(run)
        self.assertIn("0.51", latex["rq1_relative_bound_rows.tex"])
        self.assertIn(
            r"\newcommand{\RQOneMaximumBoundRatio}{0.51}",
            latex["evaluation_numbers.tex"],
        )

    def test_rq1_presentation_uses_decimal_scientific_notation(self) -> None:
        source = "1.2345678901234567890123456789e-123"
        self.assertEqual(reporting._paper_decimal_text(source), "1.2e-123")
        self.assertEqual(
            reporting._latex_number(source),
            r"$1.2\mathbin{\times}10^{-123}$",
        )

    def test_summary_v6_contains_clear_rq1_outcome_counts(self) -> None:
        summary = reporting.build_summary(self.load())
        self.assertEqual(summary["summary_schema_version"], 6)
        self.assertEqual(
            set(summary["rq1"]["operations"]),
            set(reporting.COMPOSITE_OPERATIONS),
        )
        self.assertNotIn("two_sum", summary["rq1"]["operations"])
        plus = summary["rq1"]["operations"]["dw_plus_fp"]
        self.assertEqual(
            plus["outcomes"],
            {
                "generated_input_pairs": 80,
                "rejected_by_input_check": 2,
                "rejected_by_output_finiteness_check": 1,
                "returned_normally": 77,
            },
        )
        self.assertEqual(
            plus["ranges"]["relative_term_dominant"]["input_pairs"], 77
        )
        self.assertEqual(
            summary["rq1"]["operations"]["dw_times_fp"]["ranges"]
            ["relative_term_dominant"]["input_pairs"],
            47,
        )
        self.assertEqual(
            summary["rq1"]["operations"]["dw_times_fp"]["ranges"]
            ["absolute_term_dominant"]["input_pairs"],
            30,
        )
        self.assertEqual(
            plus["ranges"]["relative_term_dominant"]["QD"]["nonfinite"], 1
        )
        self.assertEqual(
            plus["ranges"]["relative_term_dominant"]["QD"]
            ["bound_fraction"]["flags"],
            1,
        )
        self.assertEqual(len(summary["rq1"]["above_bound_results"]), 6)
        self.assertTrue(
            reporting._decimal_close(
                Decimal(
                    summary["rq1"]["above_bound_results"][0]
                    ["bound_fraction"]
                ),
                Decimal("1.5"),
            )
        )
        rq2 = summary["rq2"]
        self.assertEqual(rq2["boundary_cases_passed"], 48)
        self.assertEqual(len(rq2["above_bound_results"]), 6)
        self.assertEqual(
            rq2["above_bound_results"][0]["rejected_by"],
            ["default", "strong"],
        )
        self.assertEqual(
            set(rq2["double_word_operations"]),
            set(reporting.COMPOSITE_OPERATIONS),
        )
        self.assertEqual(
            set(rq2["error_free_transformations"]),
            set(reporting.EFT_OPERATIONS),
        )

    def test_latex_rq1_rate_rows_contain_only_percentages(self) -> None:
        rows = reporting.render_latex_files(self.load())[
            "rq1_default_interface_rates_rows.tex"
        ]
        self.assertIn(
            r"\textsc{DWPlusFP} & 97.50\% & 98.72\% & 96.25\%",
            rows,
        )
        self.assertNotIn("80", rows)
        self.assertNotIn("77", rows)

    def test_latex_rq1_range_rows_report_percent_of_normal_returns(self) -> None:
        latex = reporting.render_latex_files(self.load())
        relative = latex["rq1_relative_bound_rows.tex"]
        absolute = latex["rq1_absolute_bound_rows.tex"]
        self.assertIn(
            r"\textsc{DWPlusFP} & FenceDD & 100.00\% &",
            relative,
        )
        self.assertIn(
            r"\textsc{DWTimesFP} & FenceDD & 61.04\% &",
            relative,
        )
        self.assertIn(
            r"\textsc{DWTimesFP} & QD & 61.04\% &",
            relative,
        )
        self.assertIn(
            r"\textsc{DWTimesFP} & FenceDD & 38.96\% &",
            absolute,
        )

    def test_rq2_wrapper_populations_overlap_and_partition(self) -> None:
        run = self.load()
        for operation in reporting.COMPOSITE_OPERATIONS:
            default = run.rq2.dw_rejected[(operation, "default")]
            strong = run.rq2.dw_rejected[(operation, "strong")]
            self.assertEqual(default.rejected, 3)
            self.assertEqual(strong.rejected, 4)
            self.assertEqual(
                (
                    default.qd_nonfinite,
                    default.qd_finite_invalid_dw,
                    default.qd_finite_valid_above_bound,
                    default.qd_finite_valid_within_bound,
                ),
                (1, 1, 1, 0),
            )
            self.assertEqual(
                (
                    strong.qd_nonfinite,
                    strong.qd_finite_invalid_dw,
                    strong.qd_finite_valid_above_bound,
                    strong.qd_finite_valid_within_bound,
                ),
                (1, 1, 1, 1),
            )
            self.assertEqual(run.rq2.partitions[operation].default_only, 1)

    def test_rq2_eft_rejected_classes_partition(self) -> None:
        run = self.load()
        for operation in reporting.EFT_OPERATIONS:
            value = run.rq2.eft_rejected[operation]
            self.assertEqual(value.rejected, 4)
            self.assertEqual(
                (
                    value.qd_nonfinite,
                    value.qd_finite_invalid_dw,
                    value.qd_finite_valid_failed_reconstruction,
                    value.qd_finite_valid_exact_reconstruction,
                ),
                (1, 1, 1, 1),
            )

    def test_rq2_markdown_percentages_use_each_rejected_population(self) -> None:
        text = self.render_markdown()
        self.assertIn(
            "#### Default wrapper\n\n"
            "| Operation | Rejected test cases |",
            text,
        )
        self.assertIn(
            "| `dw_plus_fp` | 3 | 1 (33.33%) | 1 (33.33%) "
            "| 1 (33.33%) | 0 (0.00%) |",
            text,
        )
        self.assertIn(
            "#### Strong wrapper\n\n"
            "| Operation | Rejected test cases |",
            text,
        )
        self.assertIn(
            "| `dw_plus_fp` | 4 | 1 (25.00%) | 1 (25.00%) "
            "| 1 (25.00%) | 1 (25.00%) |",
            text,
        )
        self.assertIn(
            "| `two_sum` | 4 | 1 (25.00%) | 1 (25.00%) | 1 (25.00%) "
            "| 1 (25.00%) |",
            text,
        )

    def test_percentages_use_two_decimal_places(self) -> None:
        rejected = 41_945
        valid_not_exact = 41_830
        self.assertEqual(
            reporting._markdown_percent(valid_not_exact, rejected),
            "99.73%",
        )
        self.assertEqual(
            reporting._latex_count_percent(valid_not_exact, rejected),
            r"41{,}830 (99.73\%)",
        )
        self.assertEqual(
            reporting._markdown_percent(rejected, rejected),
            "100.00%",
        )
        self.assertEqual(
            reporting._markdown_percent(9_999, 10_000),
            "99.99%",
        )
        self.assertEqual(
            reporting._markdown_percent(999_999, 1_000_000),
            "100.00%",
        )

    def test_percentage_rounding_uses_explicit_ties_to_even(self) -> None:
        cases = (
            (1, 32, "3.12"),
            (3, 32, "9.38"),
            (19_997, 20_000, "99.98"),
            (19_999, 20_000, "100.00"),
            (9_898, 9_913, "99.85"),
        )
        for rounding in (ROUND_DOWN, ROUND_UP, ROUND_HALF_UP):
            with self.subTest(ambient_rounding=rounding):
                with localcontext() as context:
                    context.prec = 2
                    context.rounding = rounding
                    context.traps[Inexact] = True
                    context.traps[Rounded] = True
                    for numerator, denominator, expected in cases:
                        self.assertEqual(
                            reporting._paper_percent_text(
                                numerator, denominator
                            ),
                            expected,
                        )
                    self.assertEqual(
                        reporting._paper_percentage_value_text(
                            Decimal("12.341")
                        ),
                        "12.34",
                    )

    def test_rejection_percentages_round_to_two_decimal_places(self) -> None:
        run = self.load()
        value = run.rq2.dw_rejected[("dw_times_fp", "strong")]
        value.rejected = 9_913
        value.qd_nonfinite = 9_898
        value.qd_finite_invalid_dw = 0
        value.qd_finite_valid_above_bound = 0
        value.qd_finite_valid_within_bound = 15

        markdown = self.render_markdown(run)
        self.assertIn(
            "| `dw_times_fp` | 9,913 | 9,898 (99.85%) | 0 (0.00%) "
            "| 0 (0.00%) | 15 (0.15%) |",
            markdown,
        )

        latex = reporting.render_latex_files(run)[
            "rq2_strong_double_word_rejected_rows.tex"
        ]
        self.assertIn(
            r"\textsc{DWTimesFP} & 9{,}913 & 9{,}898 (99.85\%) "
            r"& 0 (0.00\%) & 0 (0.00\%) & 15 (0.15\%)",
            latex,
        )

    def test_all_rendered_percentages_have_two_decimal_places(self) -> None:
        markdown_percentages = re.findall(
            r"\d+(?:\.\d+)?%", self.render_markdown()
        )
        self.assertTrue(markdown_percentages)
        for percentage in markdown_percentages:
            with self.subTest(format="Markdown", percentage=percentage):
                self.assertRegex(percentage, r"^\d+\.\d{2}%$")

        latex = "\n".join(reporting.render_latex_files(self.load()).values())
        latex_percentages = re.findall(r"\d+(?:\.\d+)?\\?%", latex)
        self.assertTrue(latex_percentages)
        for percentage in latex_percentages:
            with self.subTest(format="LaTeX", percentage=percentage):
                self.assertRegex(percentage, r"^\d+\.\d{2}\\%$")
        self.assertIn(
            r"\newcommand{\RQOneQDExcessPercent}{50.00\%}",
            latex,
        )

    def test_latex_compact_rq2_rows_use_safe_percentages(self) -> None:
        run = self.load()
        fast_sum = run.rq2.eft_rejected["fast_2sum"]
        fast_sum.rejected = 41_945
        fast_sum.qd_nonfinite = 0
        fast_sum.qd_finite_invalid_dw = 12
        fast_sum.qd_finite_valid_failed_reconstruction = 41_830
        fast_sum.qd_finite_valid_exact_reconstruction = 103
        rows = reporting.render_latex_files(run)["rq2_eft_compact_rows.tex"]
        self.assertIn(
            r"\textsc{Fast2Sum} & 41{,}945 & 0.00\% & 0.03\% & 99.73\% & 0.25\%",
            rows,
        )

    def test_markdown_lists_every_rq1_above_bound_result(self) -> None:
        run = self.load()
        replacements = reporting._markdown_replacements(run)
        self.assertEqual(replacements["RQ1_ABOVE_BOUND_COUNT"], "6")
        self.assertEqual(
            replacements["RQ1_ABOVE_BOUND_ITEMS"].count("\n- ") + 1,
            6,
        )
        text = self.render_markdown(run)
        self.assertEqual(len(run.rq1.above_bound_results), 6)
        self.assertEqual(
            text.count("relative-term-dominant range, case `1`"), 6
        )
        self.assertEqual(text.count("Inputs: `case=1 synthetic`"), 6)
        self.assertIn("Result bits: `(0x3ff0000000000000,", text)
        self.assertIn("error / bound: 1.50000000000", text)

    def test_markdown_lists_each_rq2_above_bound_input_once(self) -> None:
        run = self.load()
        replacements = reporting._markdown_replacements(run)
        self.assertEqual(replacements["RQ2_ABOVE_BOUND_COUNT"], "6")
        self.assertEqual(
            replacements["RQ2_ABOVE_BOUND_ITEMS"].count("\n- ") + 1,
            6,
        )
        text = self.render_markdown(run)
        self.assertEqual(len(run.rq2.above_bound_results), 6)
        self.assertEqual(
            text.count("case `2`; rejected by default and strong"), 6
        )
        self.assertEqual(text.count("Inputs: `case=2 synthetic`"), 6)
        self.assertNotIn("case `2`; rejected by default;", text)
        self.assertIn("QD result bits: `(0x3ff0000000000000,", text)
        self.assertIn("error / bound: 2.00000000000", text)

    def test_zero_above_bound_results_use_counts_and_empty_item_lists(
        self,
    ) -> None:
        run = self.load()
        run.rq1.above_bound_results.clear()
        run.rq2.above_bound_results.clear()
        replacements = reporting._markdown_replacements(run)
        self.assertEqual(replacements["RQ1_ABOVE_BOUND_COUNT"], "0")
        self.assertEqual(replacements["RQ1_ABOVE_BOUND_ITEMS"], "")
        self.assertEqual(replacements["RQ2_ABOVE_BOUND_COUNT"], "0")
        self.assertEqual(replacements["RQ2_ABOVE_BOUND_ITEMS"], "")

        markdown = self.render_markdown(run)
        self.assertNotIn("No finite result exceeded the bound", markdown)
        self.assertNotIn(
            "No finite, valid QD result exceeded the bound", markdown
        )

    def test_zero_bound_ratio_is_a_value_not_conditional_prose(self) -> None:
        self.assertEqual(
            reporting._error_bound_ratio_text("1", Decimal(0)), "∞"
        )
        prose = _single_line(self.template())
        self.assertEqual(
            prose.count(
                "An error / bound value of ∞ denotes a positive error "
                "with a zero bound."
            ),
            2,
        )

    def test_rq2_latex_separates_default_and_strong_rows(self) -> None:
        latex = reporting.render_latex_files(self.load())
        default = latex["rq2_default_double_word_rejected_rows.tex"]
        strong = latex["rq2_strong_double_word_rejected_rows.tex"]
        combined = latex["rq2_double_word_rejected_rows.tex"]
        self.assertIn(
            r"\textsc{DWPlusFP} & 3 & 1 (33.33\%)",
            default,
        )
        self.assertIn(
            r"\textsc{DWPlusFP} & 4 & 1 (25.00\%)",
            strong,
        )
        self.assertNotIn("Default", default)
        self.assertNotIn("Strong", strong)
        self.assertEqual(default.count(r"\textsc{"), 6)
        self.assertEqual(strong.count(r"\textsc{"), 6)
        self.assertIn(
            r"\textsc{DWPlusFP} & Default & 3 & 1 (33.33\%)",
            combined,
        )
        self.assertIn(
            r"\textsc{DWPlusFP} & Strong & 4 & 1 (25.00\%)",
            combined,
        )

    def test_rq2_checked_exponents_are_presented_as_data(self) -> None:
        text = self.render_markdown()
        self.assertIn(
            "| Operation | Test cases | Checked quantity | "
            "Integer exponent range | Other recorded values |",
            text,
        )
        self.assertIn(
            "| `dw_plus_fp` | 1 | `first_high` | 0 | — |",
            text,
        )
        self.assertIn(
            "| `dw_div_dw` | 1 | `leading_quotient` | 0 | — |",
            text,
        )
        self.assertNotIn("marginal ranges", text)
        self.assertNotIn("The observed checked-exponent ranges", text)
        self.assertNotIn("- `dw_plus_fp`:", text)

    def test_rq2_checked_exponents_preserve_recorded_special_values(self) -> None:
        run = self.load()
        run.rq2.partitions["dw_div_fp"].default_only = 5
        observed = run.rq2.default_only_ranges["dw_div_fp"]["leading_quotient"]
        observed.minimum = -12
        observed.maximum = 1023
        observed.saw_zero = True
        observed.saw_nonfinite = True
        observed.saw_not_evaluated = True

        text = self.render_markdown(run)
        self.assertIn(
            "| `dw_div_fp` | 5 | `leading_quotient` | -12 to 1023 | "
            "`zero`, `nonfinite`, `not_evaluated` |",
            text,
        )

    def test_rq1_rejects_an_eft_record(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        footer = next(i for i, line in enumerate(lines) if line.startswith("# data_rows="))
        old_rows = int(lines[footer].split("=", 1)[1])
        lines.insert(
            footer,
            _line(
                "count", "two_sum", "dd_lib", "generated", 80,
                "-", "-", "-", "-", 0, "none", "-", "-", "-", "-", "-", "-",
            ),
        )
        lines[footer + 1] = f"# data_rows={old_rows + 1}"
        metadata = dict(self.load().rq1.metadata)
        metadata["data_rows"] = str(old_rows + 1)
        _rewrite_artifact(self.run_dir, "rq1", "\n".join(lines) + "\n", metadata)
        with self.assertRaisesRegex(reporting.ReportError, "unknown RQ1 operation"):
            self.load()

    def test_rq1_default_outcomes_must_partition_generated_inputs(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        text = path.read_text(encoding="utf-8").replace(
            "count\tdw_plus_fp\tdd_lib\tnormal\t77\t",
            "count\tdw_plus_fp\tdd_lib\tnormal\t76\t",
            1,
        )
        _rewrite_artifact(self.run_dir, "rq1", text)
        with self.assertRaisesRegex(reporting.ReportError, "do not partition"):
            self.load()

    def test_rq1_qd_nonfinite_counts_must_match_the_ranges(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        text = path.read_text(encoding="utf-8").replace(
            "count\tdw_plus_fp\tQD\tnonfinite\t1\t",
            "count\tdw_plus_fp\tQD\tnonfinite\t2\t",
            1,
        )
        _rewrite_artifact(self.run_dir, "rq1", text)
        with self.assertRaisesRegex(reporting.ReportError, "nonfinite regime counts"):
            self.load()

    def test_rq1_bound_above_one_requires_a_flag(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        prefix = "metric\tdw_plus_fp\tQD\trelative_term_bound_utilization\t"
        index = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[index].split("\t")
        fields[9] = "0"
        lines[index] = "\t".join(fields)
        _rewrite_artifact(self.run_dir, "rq1", "\n".join(lines) + "\n")
        with self.assertRaisesRegex(reporting.ReportError, "bound maximum.*disagree"):
            self.load()

    def test_rq1_requires_one_detail_row_per_above_bound_result(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        text = path.read_text(encoding="utf-8").replace(
            "metric\tdw_plus_fp\tQD\trelative_term_bound_utilization\t76\t"
            + _decimal(Decimal("1.5"))
            + "\t"
            + _decimal(Decimal("0.75"))
            + "\tn/a\tn/a\t1\t",
            "metric\tdw_plus_fp\tQD\trelative_term_bound_utilization\t76\t"
            + _decimal(Decimal("1.5"))
            + "\t"
            + _decimal(Decimal("0.75"))
            + "\tn/a\tn/a\t2\t",
            1,
        )
        _rewrite_artifact(self.run_dir, "rq1", text)
        with self.assertRaisesRegex(
            reporting.ReportError, "detail count 1 does not match aggregate count 2"
        ):
            self.load()

    def test_rq1_retains_multiple_above_bound_results(self) -> None:
        metadata = dict(self.load().rq1.metadata)
        path = self.run_dir / "raw" / "rq1.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        metric_prefix = (
            "metric\tdw_plus_fp\tQD\trelative_term_bound_utilization\t"
        )
        metric_index = next(
            i for i, line in enumerate(lines) if line.startswith(metric_prefix)
        )
        metric = lines[metric_index].split("\t")
        metric[9] = "2"
        lines[metric_index] = "\t".join(metric)
        detail_prefix = (
            "above_bound\tdw_plus_fp\tQD\trelative_term_dominant\t"
        )
        detail_index = next(
            i for i, line in enumerate(lines) if line.startswith(detail_prefix)
        )
        detail = lines[detail_index].split("\t")
        detail[11] = "2"
        detail[15] = _decimal(
            reporting._verified_bound_value("dw_plus_fp", Decimal(1))
            * Decimal("1.25")
        )
        detail[16] = "case=2 synthetic"
        footer = next(
            i for i, line in enumerate(lines) if line.startswith("# data_rows=")
        )
        old_rows = int(lines[footer].split("=", 1)[1])
        lines.insert(footer, "\t".join(detail))
        lines[footer + 1] = f"# data_rows={old_rows + 1}"
        metadata["data_rows"] = str(old_rows + 1)
        _rewrite_artifact(
            self.run_dir,
            "rq1",
            "\n".join(lines) + "\n",
            metadata,
        )
        run = self.load()
        results = [
            result
            for result in run.rq1.above_bound_results
            if result.operation == "dw_plus_fp"
            and result.implementation == "QD"
        ]
        self.assertEqual([result.case_id for result in results], [1, 2])
        text = self.render_markdown(run)
        self.assertIn("case `1`; error / bound: 1.50000000000", text)
        self.assertIn("case `2`; error / bound: 1.25000000000", text)

    def test_rq1_bound_flag_is_authoritative_at_serialized_one(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        tolerance = reporting.BOUND_FLAG_SERIALIZATION_TOLERANCE
        with localcontext() as decimal_context:
            decimal_context.prec = 130
            cases = (
                (
                    "metric\tdw_plus_fp\tQD\t"
                    "relative_term_bound_utilization\t",
                    Decimal(1) - tolerance / 2,
                    "1",
                ),
                (
                    "metric\tdw_plus_fp\tdd_lib\t"
                    "relative_term_bound_utilization\t",
                    Decimal(1) + tolerance / 2,
                    "0",
                ),
            )
            for prefix, maximum, expected_flag in cases:
                index = next(
                    i for i, line in enumerate(lines)
                    if line.startswith(prefix)
                )
                fields = lines[index].split("\t")
                self.assertEqual(fields[9], expected_flag)
                reference = Decimal(fields[14])
                fields[5] = format(maximum, ".105e")
                fields[15] = format(
                    reporting._verified_bound_value(
                        "dw_plus_fp", reference) * maximum,
                    ".105e",
                )
                lines[index] = "\t".join(fields)
                if expected_flag == "1":
                    detail_prefix = (
                        "above_bound\tdw_plus_fp\tQD\t"
                        "relative_term_dominant\t"
                    )
                    detail_index = next(
                        i for i, line in enumerate(lines)
                        if line.startswith(detail_prefix)
                    )
                    detail = lines[detail_index].split("\t")
                    detail[15] = format(
                        reporting._verified_bound_value(
                            "dw_plus_fp", Decimal(detail[14])
                        )
                        * maximum,
                        ".105e",
                    )
                    lines[detail_index] = "\t".join(detail)
        _rewrite_artifact(self.run_dir, "rq1", "\n".join(lines) + "\n")
        self.load()

    def test_rq1_division_screening_change_is_diagnostic(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        text = path.read_text(encoding="utf-8").replace(
            "count\tdw_div_fp\tMPFR\tbound_rechecks\t0\t",
            "count\tdw_div_fp\tMPFR\tbound_rechecks\t1\t",
            1,
        ).replace(
            "count\tdw_div_fp\tMPFR\tbound_decision_changes\t0\t",
            "count\tdw_div_fp\tMPFR\tbound_decision_changes\t1\t",
            1,
        )
        _rewrite_artifact(self.run_dir, "rq1", text)
        run = self.load()
        self.assertEqual(
            run.rq1.count("dw_div_fp", "MPFR", "bound_decision_changes"),
            1,
        )

    def test_artifact_profile_rejects_dd_lib_bound_failure(self) -> None:
        _set_profile_kind(self.run_dir, "artifact")
        metadata = dict(self.load().rq1.metadata)
        path = self.run_dir / "raw" / "rq1.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        prefix = "metric\tdw_plus_fp\tdd_lib\trelative_term_bound_utilization\t"
        index = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[index].split("\t")
        fields[5] = "1.5"
        fields[6] = "0.75"
        fields[9] = "1"
        fields[15] = _decimal(
            reporting._verified_bound_value("dw_plus_fp", Decimal(1))
            * Decimal("1.5")
        )
        lines[index] = "\t".join(fields)
        footer = next(
            i for i, line in enumerate(lines) if line.startswith("# data_rows=")
        )
        old_rows = int(lines[footer].split("=", 1)[1])
        lines.insert(
            footer,
            _line(
                "above_bound", "dw_plus_fp", "dd_lib",
                "relative_term_dominant", 1, "-", "-", "-", "-", 0,
                "none", 0, FINITE_HI, FINITE_LO, _decimal(Decimal(1)),
                _decimal(
                    reporting._verified_bound_value(
                        "dw_plus_fp", Decimal(1)
                    )
                    * Decimal("1.5")
                ),
                "case=0 synthetic",
            ),
        )
        lines[footer + 1] = f"# data_rows={old_rows + 1}"
        metadata["data_rows"] = str(old_rows + 1)
        _rewrite_artifact(
            self.run_dir,
            "rq1",
            "\n".join(lines) + "\n",
            metadata,
        )
        with self.assertRaisesRegex(reporting.ReportError, "bound has unresolved flags"):
            self.load()

    def test_rq2_rejects_inconsistent_within_bound_classification(self) -> None:
        path = self.run_dir / "raw" / "rq2.tsv.gz"
        lines = gzip.decompress(path.read_bytes()).decode().splitlines()
        prefix = "log_stratified\tdw_plus_fp\t2\t"
        index = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[index].split("\t")
        self.assertEqual(fields[17], "no")
        fields[17] = "yes"
        lines[index] = "\t".join(fields)
        _rewrite_artifact(self.run_dir, "rq2", "\n".join(lines) + "\n")
        with self.assertRaisesRegex(reporting.ReportError, "within-bound result disagrees"):
            self.load()

    def test_rq2_rejects_inconsistent_exact_reconstruction_classification(self) -> None:
        path = self.run_dir / "raw" / "rq2.tsv.gz"
        lines = gzip.decompress(path.read_bytes()).decode().splitlines()
        prefix = "log_stratified\ttwo_sum\t2\t"
        index = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[index].split("\t")
        self.assertEqual(fields[18], "no")
        fields[18] = "yes"
        lines[index] = "\t".join(fields)
        _rewrite_artifact(self.run_dir, "rq2", "\n".join(lines) + "\n")
        with self.assertRaisesRegex(
            reporting.ReportError, "exact-reconstruction result disagrees"
        ):
            self.load()

    def test_rq2_boundary_qd_fields_must_remain_excluded(self) -> None:
        path = self.run_dir / "raw" / "rq2.tsv.gz"
        lines = gzip.decompress(path.read_bytes()).decode().splitlines()
        index = next(i for i, line in enumerate(lines) if line.startswith("boundary\t"))
        fields = lines[index].split("\t")
        fields[15] = "yes"
        lines[index] = "\t".join(fields)
        _rewrite_artifact(self.run_dir, "rq2", "\n".join(lines) + "\n")
        with self.assertRaisesRegex(reporting.ReportError, "unevaluated QD field"):
            self.load()

    def test_cross_rq_input_fingerprint_mismatch_is_rejected(self) -> None:
        text, metadata = _rq2_text("0x1111111111111111")
        _rewrite_artifact(self.run_dir, "rq2", text, metadata)
        with self.assertRaisesRegex(reporting.ReportError, "shared generated-input metadata"):
            self.load()

    def test_cross_rq_default_outcome_mismatch_is_rejected(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        text = path.read_text(encoding="utf-8")
        text = text.replace(
            "count\tdw_plus_fp\tdd_lib\tinput_check\t2\t",
            "count\tdw_plus_fp\tdd_lib\tinput_check\t1\t",
            1,
        ).replace(
            "count\tdw_plus_fp\tdd_lib\tpost_compute\t1\t",
            "count\tdw_plus_fp\tdd_lib\tpost_compute\t2\t",
            1,
        )
        _rewrite_artifact(self.run_dir, "rq1", text)
        with self.assertRaisesRegex(reporting.ReportError, "default outcome totals disagree"):
            self.load()

    def test_rq3_compcert_and_clang_blocks_are_both_retained(self) -> None:
        run = self.load()
        self.assertEqual(
            run.rq3["compcert"].summaries[("two_sum", "dd_lib", "default")].median,
            26.5,
        )
        self.assertEqual(
            run.rq3["clang"].summaries[("two_sum", "dd_lib", "default")].median,
            27.5,
        )
        summary = reporting.build_summary(run)
        operation = summary["rq3"]["operations"]["two_sum"]
        self.assertEqual(set(operation), {"compcert", "clang"})
        self.assertNotIn("strong", operation["compcert"])
        self.assertAlmostEqual(
            operation["compcert"]["default"]["paired_qd_ratio"]["median"],
            0.8412298387096775,
        )
        self.assertAlmostEqual(
            operation["clang"]["default"]["paired_qd_ratio"]["median"],
            0.8461174242424243,
        )
        composite = summary["rq3"]["operations"]["dw_plus_fp"]
        self.assertAlmostEqual(
            composite["compcert"]["strong"]["paired_qd_ratio"]["median"],
            0.7777217741935484,
        )
        self.assertAlmostEqual(
            composite["clang"]["strong"]["paired_qd_ratio"]["median"],
            0.7845643939393939,
        )

    def test_rq3_markdown_reports_paired_qd_ratios(self) -> None:
        text = self.render_markdown()
        self.assertIn(
            "| Operation | `dd_lib` C compiler | Kernel time (ns/call) | "
            "Default time (ns/call) | Default/kernel ratio | "
            "Default/QD ratio | Strong time (ns/call) | "
            "Strong/kernel ratio | Strong/QD ratio | QD time (ns/call) |",
            text,
        )

        lines = text.splitlines()
        two_sum_compcert = next(
            line for line in lines
            if line.startswith("| `two_sum` | CompCert |")
        )
        two_sum_cells = [
            cell.strip() for cell in two_sum_compcert.strip("|").split("|")
        ]
        self.assertEqual(two_sum_cells[5], "0.84 [0.060]")
        self.assertEqual(two_sum_cells[6:9], ["—", "—", "—"])

        two_sum_clang = next(
            line for line in lines
            if line.startswith("| `two_sum` | Clang |")
        )
        two_sum_clang_cells = [
            cell.strip() for cell in two_sum_clang.strip("|").split("|")
        ]
        self.assertEqual(two_sum_clang_cells[5], "0.85 [0.056]")

        plus_compcert = next(
            line for line in lines
            if line.startswith("| `dw_plus_fp` | CompCert |")
        )
        plus_compcert_cells = [
            cell.strip() for cell in plus_compcert.strip("|").split("|")
        ]
        self.assertEqual(plus_compcert_cells[5], "0.84 [0.060]")
        self.assertEqual(plus_compcert_cells[8], "0.78 [0.084]")

        plus_clang = next(
            line for line in lines
            if line.startswith("| `dw_plus_fp` | Clang |")
        )
        plus_clang_cells = [
            cell.strip() for cell in plus_clang.strip("|").split("|")
        ]
        self.assertEqual(plus_clang_cells[5], "0.85 [0.056]")
        self.assertEqual(plus_clang_cells[8], "0.78 [0.079]")

    def test_rq3_rejects_nonpositive_timing(self) -> None:
        path = self.run_dir / "raw" / "rq3-compcert.tsv"
        text = path.read_text(encoding="utf-8").replace(
            "two_sum\tdd_lib\tdefault\t0\t15",
            "two_sum\tdd_lib\tdefault\t0\t0",
            1,
        )
        _rewrite_artifact(self.run_dir, "rq3_compcert", text)
        with self.assertRaisesRegex(reporting.ReportError, "ns_per_call"):
            self.load()

    def test_linear_quantile_matches_declared_rule(self) -> None:
        fixture = json.loads(
            (FIXTURES / "quantiles.json").read_text(encoding="utf-8")
        )
        summary = reporting.summarize_values(fixture["values"])
        self.assertEqual(summary.first_quartile, fixture["first_quartile"])
        self.assertEqual(summary.median, fixture["median"])
        self.assertEqual(summary.third_quartile, fixture["third_quartile"])
        self.assertEqual(summary.iqr, fixture["iqr"])

    def test_manifest_requires_v6_and_exact_tsv_metadata(self) -> None:
        manifest_path = self.run_dir / "manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        manifest["manifest_schema_version"] = 5
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        _write_checksums(self.run_dir)
        with self.assertRaisesRegex(reporting.ReportError, "manifest_schema_version must be 6"):
            self.load()

        second = Path(self.temporary.name) / "metadata-run"
        second.mkdir()
        _make_run(second)
        manifest_path = second / "manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        manifest["tsv_metadata"]["rq2"].pop("qd_fma")
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        _write_checksums(second)
        with self.assertRaisesRegex(reporting.ReportError, "does not exactly match"):
            reporting.load_evaluation_run(second, SHAPE)

    def test_manifest_rejects_git_metadata(self) -> None:
        manifest_path = self.run_dir / "manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        manifest["git"] = {
            "revision": "0123456789abcdef",
            "dirty": False,
            "status": "clean",
        }
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        _write_checksums(self.run_dir)
        with self.assertRaisesRegex(
            reporting.ReportError, r"manifest fields mismatch.*extra=\['git'\]"
        ):
            self.load()

    def test_artifact_hash_mismatch_is_rejected(self) -> None:
        path = self.run_dir / "raw" / "rq1.tsv"
        path.write_bytes(path.read_bytes() + b"# changed=true\n")
        with self.assertRaisesRegex(reporting.ReportError, "hash/size"):
            self.load()

    def test_atomic_writer_and_check_mode_detect_drift(self) -> None:
        output_dir = Path(self.temporary.name) / "generated"
        outputs = {Path("one.txt"): b"one\n", Path("nested/two.txt"): b"two\n"}
        self.assertEqual(reporting.write_outputs_atomically(output_dir, outputs), [])
        self.assertEqual(
            reporting.write_outputs_atomically(output_dir, outputs, check=True), []
        )
        (output_dir / "one.txt").write_text("changed\n", encoding="utf-8")
        drift = reporting.write_outputs_atomically(output_dir, outputs, check=True)
        self.assertEqual(len(drift), 1)
        self.assertIn("out of date", drift[0])

    def test_atomic_writer_reports_and_removes_obsolete_outputs(self) -> None:
        output_dir = Path(self.temporary.name) / "obsolete"
        outputs = {Path("RESULTS.md"): b"current\n"}
        self.assertEqual(reporting.write_outputs_atomically(output_dir, outputs), [])
        obsolete = output_dir / "rq2-bins.tsv"
        obsolete.write_bytes(b"old schema\n")

        drift = reporting.write_outputs_atomically(output_dir, outputs, check=True)
        self.assertEqual(drift, [f"obsolete {obsolete.resolve()}"])
        self.assertEqual(reporting.write_outputs_atomically(output_dir, outputs), [])
        self.assertFalse(obsolete.exists())
        self.assertEqual((output_dir / "RESULTS.md").read_bytes(), b"current\n")

    def test_atomic_writer_rolls_back_a_replacement_failure(self) -> None:
        output_dir = Path(self.temporary.name) / "rollback"
        output_dir.mkdir()
        (output_dir / "one.txt").write_bytes(b"old one\n")
        (output_dir / "two.txt").write_bytes(b"old two\n")
        outputs = {Path("one.txt"): b"new one\n", Path("two.txt"): b"new two\n"}
        real_replace = reporting.os.replace
        calls = 0

        def fail_fourth(source, target):
            nonlocal calls
            calls += 1
            if calls == 4:
                raise OSError("injected replacement failure")
            return real_replace(source, target)

        with mock.patch.object(reporting.os, "replace", side_effect=fail_fourth):
            with self.assertRaisesRegex(OSError, "injected"):
                reporting.write_outputs_atomically(output_dir, outputs)
        self.assertEqual((output_dir / "one.txt").read_bytes(), b"old one\n")
        self.assertEqual((output_dir / "two.txt").read_bytes(), b"old two\n")

    def test_repeated_render_is_byte_identical(self) -> None:
        run = self.load()
        template = (BENCH / "results_template.md").read_text(encoding="utf-8")
        self.assertEqual(
            reporting.render_all(run, template),
            reporting.render_all(run, template),
        )


if __name__ == "__main__":
    unittest.main()
