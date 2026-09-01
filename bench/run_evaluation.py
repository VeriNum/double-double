#!/usr/bin/env python3
"""Run the three evaluation drivers and finalize an immutable run directory."""

import argparse
import datetime as _datetime
import gzip
import hashlib
import json
import os
import pathlib
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import traceback


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
REPOSITORY_ROOT = SCRIPT_DIR.parent
PROFILE_FILE = SCRIPT_DIR / "evaluation_profiles.json"
RUN_ID_PATTERN = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}\Z")
EXPECTED_SCHEMAS = {
    "rq1": ("rq1", "6"),
    "rq2": ("rq2", "5"),
    "rq3_compcert": ("rq3", "4"),
    "rq3_clang": ("rq3", "4"),
}
DRIVER_NAMES = {
    "rq1": "rq1_accuracy",
    "rq2": "rq2_guard_acceptance",
    "rq3_compcert": "rq3_performance_compcert",
    "rq3_clang": "rq3_performance_clang",
}
RQ1_HEADER = [
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
]
RQ1_METADATA = {
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
}
RQ2_HEADER = [
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
]
RQ2_METADATA = {
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
}
RQ3_BUILDS = {
    "rq3_compcert": "compcert",
    "rq3_clang": "clang",
}
RQ3_HEADER = [
    "operation",
    "implementation",
    "interface",
    "trial",
    "ns_per_call",
]
RQ3_METADATA = {
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
}
RQ3_FIXED_METADATA = {
    "composite_interfaces": "default:two-stage,strong:input-only",
    "exact_transform_interface": "default:guarded",
    "quantile": "linear_interpolation_p_times_n_minus_1",
    "exact_schedule": "all_six_permutations",
    "composite_schedule": "all_twenty_four_permutations",
    "timer": "std_chrono_steady_clock",
}
RQ3_FINGERPRINT_PATTERN = re.compile(r"0x[0-9a-f]{16}\Z")
QD_IMPLEMENTATION_HEADERS = (
    "dd_real.h",
    "dd_inline.h",
    "inline.h",
    "qd_config.h",
)
QD_POLICY_FILE = SCRIPT_DIR / "qd_evaluation.hpp"


class EvaluationError(RuntimeError):
    """A failure that should be recorded in the run manifest."""


def utc_now():
    return (_datetime.datetime.now(_datetime.timezone.utc)
            .isoformat(timespec="seconds").replace("+00:00", "Z"))


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        while True:
            block = source.read(1024 * 1024)
            if not block:
                break
            digest.update(block)
    return digest.hexdigest()


def file_record(root, path):
    path = pathlib.Path(path)
    return {
        "path": path.relative_to(root).as_posix(),
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
    }


def absolute_file_record(path):
    path = pathlib.Path(path)
    return {
        "path": str(path.resolve()),
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
    }


def resolve_tool(command):
    candidate = pathlib.Path(command)
    if candidate.is_absolute() or candidate.parent != pathlib.Path("."):
        return str(candidate.resolve()) if candidate.exists() else command
    resolved = shutil.which(command)
    return resolved if resolved is not None else command


def capture_command(argv, timeout=10, empty_ok=False):
    try:
        completed = subprocess.run(
            argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace", timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.SubprocessError) as error:
        return "unavailable ({})".format(error)
    output = completed.stdout.strip()
    if completed.returncode != 0:
        if output:
            return "unavailable (exit {}: {})".format(
                completed.returncode, output[:1000])
        return "unavailable (exit {})".format(completed.returncode)
    if output:
        return output[:8000]
    return "" if empty_ok else "unavailable (empty output)"


def first_line(text):
    return text.splitlines()[0] if text else "unavailable"


def cpu_model():
    if platform.system() == "Darwin":
        value = capture_command(["sysctl", "-n", "machdep.cpu.brand_string"])
        if not value.startswith("unavailable"):
            return first_line(value)
    if platform.system() == "Linux":
        try:
            with open("/proc/cpuinfo", encoding="utf-8") as source:
                for line in source:
                    if line.lower().startswith("model name") and ":" in line:
                        return line.split(":", 1)[1].strip()
        except OSError:
            pass
    return platform.processor() or "unavailable"


def git_provenance(repository_root):
    git = shutil.which("git")
    if git is None:
        return {
            "revision": None,
            "dirty": True,
            "status": "git executable unavailable",
        }
    prefix = [git, "-C", str(repository_root)]
    revision = capture_command(prefix + ["rev-parse", "HEAD"])
    if revision.startswith("unavailable"):
        return {"revision": None, "dirty": True, "status": revision}
    status = capture_command(
        prefix + ["status", "--porcelain=v1", "--untracked-files=all"],
        empty_ok=True)
    if status.startswith("unavailable"):
        return {"revision": revision, "dirty": True, "status": status}
    return {
        "revision": revision,
        "dirty": bool(status),
        "status": status,
    }


def dynamic_dependencies(path):
    system = platform.system()
    if system == "Darwin" and shutil.which("otool"):
        output = capture_command(["otool", "-L", str(path)])
    elif system == "Linux" and shutil.which("ldd"):
        output = capture_command(["ldd", str(path)])
    else:
        return []
    return output.splitlines()


def binary_provenance(binary_directory):
    records = {}
    paths = {}
    for key, name in DRIVER_NAMES.items():
        path = (binary_directory / name).resolve()
        if not path.is_file():
            raise EvaluationError(
                "missing evaluation executable: {} (the runner does not build)"
                .format(path))
        if not os.access(str(path), os.X_OK):
            raise EvaluationError("evaluation executable is not executable: {}"
                                  .format(path))
        records[key] = {
            "path": str(path),
            "sha256": sha256_file(path),
            "bytes": path.stat().st_size,
            "dynamic_dependencies": dynamic_dependencies(path),
        }
        paths[key] = path
    return records, paths


def binary_identity(records):
    """Return stable fields; loader output may contain ASLR addresses."""
    return {
        key: {
            field: record[field]
            for field in ("path", "sha256", "bytes")
        }
        for key, record in records.items()
    }


def build_configuration(args):
    path = args.bin_dir / ".build" / "config.json"
    try:
        with open(path, encoding="utf-8") as source:
            document = json.load(source)
    except (OSError, ValueError) as error:
        raise EvaluationError(
            "cannot read benchmark build configuration {}: {} "
            "(run make prepare-evaluation first)".format(path, error))
    if document.get("config_schema_version") != 3:
        raise EvaluationError("unsupported benchmark build configuration")
    expected = {
        "dd_cc": args.dd_cc,
        "dd_cflags": args.dd_cflags,
        "clang_cc": args.clang_cc,
        "clang_cflags": args.clang_cflags,
        "cxx": args.cxx,
        "cxxflags": args.cxxflags,
        "strict_fp_flags": args.strict_fp_flags,
        "qd_prefix": args.qd_prefix_setting,
    }
    for key, value in expected.items():
        if document.get(key) != value:
            raise EvaluationError(
                "built configuration {}={!r}, but the runner was given {!r}; "
                "rebuild with make prepare-evaluation".format(
                    key, document.get(key), value))
    return {
        "path": str(path.resolve()),
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
        "values": document,
    }


def qd_build_records(qd_prefix):
    header_directory = qd_prefix / "include" / "qd"
    headers = [
        header_directory / name for name in QD_IMPLEMENTATION_HEADERS
    ]
    required = headers + [QD_POLICY_FILE]
    missing = [path for path in required if not path.is_file()]
    if missing:
        raise EvaluationError(
            "cannot record the header-only QD implementation; missing required "
            "provenance file(s): {}".format(
                ", ".join(str(path.resolve()) for path in missing)))
    return {
        "qd_headers": [absolute_file_record(path) for path in headers],
        "qd_policy": absolute_file_record(QD_POLICY_FILE),
    }


def environment_provenance(args):
    dd_cc = resolve_tool(args.dd_cc)
    clang_cc = resolve_tool(args.clang_cc)
    cxx = resolve_tool(args.cxx)
    qd_config = args.qd_prefix / "bin" / "qd-config"
    if qd_config.is_file():
        qd_executable = str(qd_config.resolve())
        qd_version = first_line(capture_command([qd_executable, "--version"]))
    else:
        qd_executable = "unavailable (missing {})".format(qd_config.resolve())
        qd_version = qd_executable
    pkg_config = resolve_tool(args.pkg_config)
    return {
        "os": platform.platform(),
        "architecture": platform.machine() or "unavailable",
        "cpu_model": cpu_model(),
        "cpu_count": os.cpu_count(),
        "hostname": platform.node() or "unavailable",
        "python": sys.version.splitlines()[0],
        "compcert_executable": dd_cc,
        "compcert": first_line(capture_command([dd_cc, "-version"])),
        "clang_executable": clang_cc,
        "clang": first_line(capture_command([clang_cc, "--version"])),
        "cxx_executable": cxx,
        "cxx": first_line(capture_command([cxx, "--version"])),
        "qd_config_executable": qd_executable,
        "qd": qd_version,
        "pkg_config_executable": pkg_config,
        "mpfr": first_line(capture_command(
            [pkg_config, "--modversion", "mpfr"])),
        "gmp": first_line(capture_command(
            [pkg_config, "--modversion", "gmp"])),
    }


def load_profile(path, name):
    try:
        with open(path, encoding="utf-8") as source:
            document = json.load(source)
    except (OSError, ValueError) as error:
        raise EvaluationError("cannot read evaluation profiles: {}".format(error))
    if document.get("profile_schema_version") != 3:
        raise EvaluationError("unsupported evaluation profile schema")
    profiles = document.get("profiles")
    if not isinstance(profiles, dict) or name not in profiles:
        raise EvaluationError("unknown evaluation profile: {}".format(name))
    profile = profiles[name]
    if not isinstance(profile, dict):
        raise EvaluationError("evaluation profile must be an object")
    if profile.get("kind") not in ("smoke", "artifact"):
        raise EvaluationError("profile kind must be smoke or artifact")
    if profile["kind"] == "artifact":
        required_build = profile.get("required_build")
        expected_keys = {
            "clang_cflags", "dd_cflags", "cxxflags", "strict_fp_flags",
        }
        if (not isinstance(required_build, dict)
                or set(required_build) != expected_keys
                or any(not isinstance(value, str) or not value
                       for value in required_build.values())):
            raise EvaluationError(
                "{} required_build must define exactly clang_cflags, "
                "dd_cflags, cxxflags, and strict_fp_flags".format(
                    profile["kind"]))
    return profile


def effective_parameters(args, profile):
    values = {}
    for name in ("rq1_samples", "rq2_samples", "rq3_inputs",
                 "rq3_trials"):
        override = getattr(args, name)
        value = profile.get(name) if override is None else override
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            raise EvaluationError("{} must be a positive integer".format(name))
        values[name] = value
    if values["rq1_samples"] % 40 != 0:
        raise EvaluationError("rq1_samples must be a multiple of 40")
    if values["rq2_samples"] % 40 != 0:
        raise EvaluationError("rq2_samples must be a multiple of 40")
    if values["rq3_trials"] % 24 != 0:
        raise EvaluationError("rq3_trials must be a multiple of 24")
    return values


class ExclusiveRunLock:
    def __init__(self, run_root):
        self.path = run_root / ".run_evaluation.lock"
        self.file_descriptor = None
        self.inode = None

    def __enter__(self):
        try:
            self.file_descriptor = os.open(
                str(self.path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        except FileExistsError:
            raise EvaluationError(
                "another evaluation holds {} (remove it only after confirming "
                "that no runner is active)".format(self.path))
        self.inode = os.fstat(self.file_descriptor).st_ino
        payload = json.dumps({
            "pid": os.getpid(),
            "hostname": platform.node(),
            "started_utc": utc_now(),
        }, sort_keys=True) + "\n"
        os.write(self.file_descriptor, payload.encode("utf-8"))
        os.fsync(self.file_descriptor)
        return self

    def __exit__(self, exc_type, exc_value, exc_traceback):
        if self.file_descriptor is not None:
            os.close(self.file_descriptor)
            self.file_descriptor = None
        try:
            if self.path.stat().st_ino == self.inode:
                self.path.unlink()
        except FileNotFoundError:
            pass


def parse_tsv(path, evaluation):
    try:
        schema_name, expected_schema = EXPECTED_SCHEMAS[evaluation]
    except KeyError:
        raise EvaluationError("unknown evaluation output: {}".format(evaluation))
    schema_key = "{}_schema_version".format(schema_name)
    metadata = {}
    header = None
    rows = 0
    tail = []
    try:
        source = open(path, encoding="utf-8", newline="")
    except OSError as error:
        raise EvaluationError("cannot open {} output: {}".format(
            evaluation, error))
    with source:
        for line_number, raw_line in enumerate(source, 1):
            line = raw_line.rstrip("\r\n")
            if not line:
                continue
            tail.append(line)
            if len(tail) > 2:
                tail.pop(0)
            if line.startswith("#"):
                if line.startswith("# ") and "=" in line:
                    key, value = line[2:].split("=", 1)
                    if not key or key in metadata:
                        raise EvaluationError(
                            "{} has duplicate or empty metadata at line {}"
                            .format(evaluation, line_number))
                    metadata[key] = value
                continue
            if header is None:
                header = line.split("\t")
                if len(header) < 2 or len(set(header)) != len(header):
                    raise EvaluationError(
                        "{} has an invalid TSV header".format(evaluation))
            else:
                if len(line.split("\t")) != len(header):
                    raise EvaluationError(
                        "{} has the wrong number of fields at line {}".format(
                            evaluation, line_number))
                rows += 1
    if header is None:
        raise EvaluationError("{} output has no TSV header".format(evaluation))
    if metadata.get(schema_key) != expected_schema:
        raise EvaluationError(
            "{} output has schema {}, expected {}".format(
                evaluation, metadata.get(schema_key),
                expected_schema))
    expected_footer = [
        "# data_rows={}".format(rows),
        "# completed=true",
    ]
    if tail != expected_footer:
        raise EvaluationError(
            "{} output lacks the required terminal data_rows/completed footer"
            .format(evaluation))
    try:
        recorded_rows = int(metadata.get("data_rows", ""), 10)
    except ValueError:
        raise EvaluationError("{} data_rows is not an integer".format(evaluation))
    if recorded_rows != rows:
        raise EvaluationError(
            "{} data_rows={}, but {} rows were written".format(
                evaluation, recorded_rows, rows))
    return metadata, header, rows


def require_metadata_integer(metadata, key, expected, evaluation):
    try:
        actual = int(metadata[key], 10)
    except (KeyError, ValueError):
        raise EvaluationError(
            "{} metadata {} is missing or invalid".format(evaluation, key))
    if actual != expected:
        raise EvaluationError(
            "{} metadata {}={}, expected {}".format(
                evaluation, key, actual, expected))


def validate_tsv(path, evaluation, parameters):
    metadata, header, rows = parse_tsv(path, evaluation)
    if evaluation == "rq1":
        if header != RQ1_HEADER:
            raise EvaluationError("rq1 has an invalid TSV header")
        if set(metadata) != RQ1_METADATA:
            raise EvaluationError("rq1 metadata does not match its schema")
        require_metadata_integer(
            metadata, "samples_per_exponent", parameters["rq1_samples"],
            evaluation)
        for key in ("generator", "seed", "input_fingerprint"):
            if not metadata.get(key):
                raise EvaluationError("rq1 metadata {} is missing".format(key))
        require_metadata_integer(
            metadata, "construction_precision_bits", 256, evaluation)
        require_metadata_integer(
            metadata, "oracle_precision_bits", 2112, evaluation)
        require_metadata_integer(
            metadata, "division_recheck_precision_bits", 4224,
            evaluation)
    elif evaluation == "rq2":
        if header != RQ2_HEADER:
            raise EvaluationError("rq2 has an invalid TSV header")
        if set(metadata) != RQ2_METADATA:
            raise EvaluationError("rq2 metadata does not match its schema")
        require_metadata_integer(
            metadata, "samples_per_exponent", parameters["rq2_samples"],
            evaluation)
        for key in ("generator", "seed", "input_fingerprint"):
            if not metadata.get(key):
                raise EvaluationError("rq2 metadata {} is missing".format(key))
        require_metadata_integer(
            metadata, "oracle_precision_bits", 2112, evaluation)
        require_metadata_integer(
            metadata, "division_oracle_precision_bits", 4224,
            evaluation)
        if metadata.get("qd_inline") != "1" or metadata.get("qd_fma") != "std::fma":
            raise EvaluationError("rq2 QD configuration metadata is invalid")
    elif evaluation in RQ3_BUILDS:
        if set(metadata) != RQ3_METADATA:
            missing = sorted(RQ3_METADATA - set(metadata))
            extra = sorted(set(metadata) - RQ3_METADATA)
            raise EvaluationError(
                "{} metadata does not match the RQ3 schema; missing={}, "
                "extra={}".format(evaluation, missing, extra))
        if header != RQ3_HEADER:
            raise EvaluationError(
                "{} has an invalid RQ3 TSV header".format(evaluation))
        expected_build = RQ3_BUILDS[evaluation]
        if metadata.get("build") != expected_build:
            raise EvaluationError(
                "{} metadata build={!r}, expected {!r}".format(
                    evaluation, metadata.get("build"), expected_build))
        for key, expected in RQ3_FIXED_METADATA.items():
            if metadata.get(key) != expected:
                raise EvaluationError(
                    "{} metadata {}={!r}, expected {!r}".format(
                        evaluation, key, metadata.get(key), expected))
        require_metadata_integer(
            metadata, "input_count", parameters["rq3_inputs"], evaluation)
        require_metadata_integer(
            metadata, "trial_count", parameters["rq3_trials"], evaluation)
        if rows != 33 * parameters["rq3_trials"]:
            raise EvaluationError(
                "{} wrote {} data rows; expected 33 per trial".format(
                    evaluation, rows))
        if not RQ3_FINGERPRINT_PATTERN.fullmatch(
                metadata.get("input_fingerprint", "")):
            raise EvaluationError(
                "{} input_fingerprint is invalid".format(evaluation))
    else:
        raise EvaluationError("unknown evaluation output: {}".format(evaluation))
    return metadata


def validate_shared_generated_inputs(rq1_metadata, rq2_metadata):
    for key in ("generator", "seed", "input_fingerprint",
                "samples_per_exponent"):
        if rq1_metadata.get(key) != rq2_metadata.get(key):
            raise EvaluationError(
                "RQ1 and RQ2 metadata disagree on {}".format(key))


def validate_shared_rq3_inputs(compcert_metadata, clang_metadata):
    for key in ("input_count", "trial_count", "input_fingerprint"):
        if compcert_metadata.get(key) != clang_metadata.get(key):
            raise EvaluationError(
                "CompCert and Clang RQ3 metadata disagree on {}".format(key))


def deterministic_gzip(source, destination):
    if destination.exists():
        raise EvaluationError("refusing to overwrite {}".format(destination))
    try:
        with open(source, "rb") as input_file, open(destination, "xb") as raw:
            with gzip.GzipFile(
                    filename="", mode="wb", fileobj=raw,
                    compresslevel=9, mtime=0) as compressed:
                shutil.copyfileobj(input_file, compressed, 1024 * 1024)
    except OSError as error:
        raise EvaluationError("cannot compress RQ2 output: {}".format(error))


def run_environment():
    environment = os.environ.copy()
    environment["LC_ALL"] = "C"
    environment["LANG"] = "C"
    environment["TZ"] = "UTC"
    recorded = {
        "LC_ALL": environment["LC_ALL"],
        "LANG": environment["LANG"],
        "TZ": environment["TZ"],
    }
    return environment, recorded


def run_driver(stage, evaluation, executable, arguments, environment,
               recorded_environment):
    log_directory = stage / "raw"
    stdout_path = log_directory / "{}.stdout.log".format(evaluation)
    stderr_path = log_directory / "{}.stderr.log".format(evaluation)
    argv = [str(executable)] + [str(value) for value in arguments]
    record = {
        "evaluation": evaluation,
        "argv": argv,
        "cwd": ".",
        "environment": recorded_environment,
        "started_utc": utc_now(),
        "completed_utc": None,
        "exit_code": None,
        "stdout": None,
        "stderr": None,
    }
    try:
        with open(stdout_path, "xb") as stdout_file, \
                open(stderr_path, "xb") as stderr_file:
            completed = subprocess.run(
                argv, cwd=str(stage), env=environment,
                stdout=stdout_file, stderr=stderr_file, check=False)
        record["exit_code"] = completed.returncode
    except OSError as error:
        record["launch_error"] = str(error)
    record["completed_utc"] = utc_now()
    record["stdout"] = file_record(stage, stdout_path)
    record["stderr"] = file_record(stage, stderr_path)
    return record


def write_json_atomic(path, value):
    temporary = path.with_name("." + path.name + ".tmp")
    with open(temporary, "x", encoding="utf-8", newline="\n") as output:
        json.dump(value, output, indent=2, sort_keys=True)
        output.write("\n")
        output.flush()
        os.fsync(output.fileno())
    os.replace(str(temporary), str(path))


def write_checksums(stage):
    checksum_path = stage / "checksums.sha256"
    paths = []
    for path in stage.rglob("*"):
        if path.is_file() and path != checksum_path:
            paths.append(path)
    paths.sort(key=lambda item: item.relative_to(stage).as_posix())
    with open(checksum_path, "x", encoding="ascii", newline="\n") as output:
        for path in paths:
            relative = path.relative_to(stage).as_posix()
            output.write("{}  {}\n".format(sha256_file(path), relative))
        output.flush()
        os.fsync(output.fileno())


def finalize_run_directory(stage, destination):
    if destination.exists():
        raise EvaluationError(
            "run directory already exists; refusing to overwrite {}"
            .format(destination))
    os.rename(str(stage), str(destination))


def base_manifest(args, profile, parameters, git):
    return {
        "manifest_schema_version": 5,
        "status": "running",
        "run_id": args.run_id,
        "profile": {
            "name": args.profile,
            "kind": profile["kind"],
            "source": {
                "path": str(args.profiles),
                "sha256": sha256_file(args.profiles),
                "bytes": args.profiles.stat().st_size,
            },
        },
        "started_utc": utc_now(),
        "completed_utc": None,
        "git": git,
        "build": {
            "dd_cc": args.dd_cc,
            "dd_cflags": args.dd_cflags,
            "clang_cc": args.clang_cc,
            "clang_cflags": args.clang_cflags,
            "cxx": args.cxx,
            "cxxflags": args.cxxflags,
            "strict_fp_flags": args.strict_fp_flags,
            "qd_prefix": args.qd_prefix_setting,
            "binaries": {},
        },
        "environment": {},
        "commands": [],
        "parameters": parameters,
        "artifacts": {},
        "tsv_metadata": {},
    }


def execute_run(args, profile, parameters, stage, manifest):
    profile_kind = profile["kind"]
    artifact_profile = profile_kind == "artifact"
    if artifact_profile:
        build_settings = {
            "clang_cflags": args.clang_cflags,
            "dd_cflags": args.dd_cflags,
            "cxxflags": args.cxxflags,
            "strict_fp_flags": args.strict_fp_flags,
        }
        for key, expected in profile["required_build"].items():
            if build_settings[key] != expected:
                raise EvaluationError(
                    "{} build setting {}={!r}, expected {!r} from the frozen "
                    "profile".format(
                        profile_kind, key, build_settings[key], expected))
        if args.profiles != PROFILE_FILE.resolve():
            raise EvaluationError(
                "{} runs must use the repository's frozen profile file".format(
                    profile_kind))
        overridden = [
            name for name in (
                "rq1_samples", "rq2_samples", "rq3_inputs",
                "rq3_trials")
            if getattr(args, name) is not None
        ]
        if overridden:
            raise EvaluationError(
                "{} profile parameters cannot be overridden: {}".format(
                    profile_kind, ", ".join(overridden)))

    initial_configuration = build_configuration(args)
    manifest["build"]["configuration"] = initial_configuration
    binaries, executable_paths = binary_provenance(args.bin_dir)
    manifest["build"]["binaries"] = binaries
    initial_qd_build = qd_build_records(args.qd_prefix)
    tool_identities = initial_configuration["values"].get("tool_identities")
    configured_qd = (
        tool_identities.get("qd")
        if isinstance(tool_identities, dict) else None)
    current_qd = {
        "headers": initial_qd_build["qd_headers"],
        "policy": initial_qd_build["qd_policy"],
    }
    if configured_qd != current_qd:
        raise EvaluationError(
            "current QD headers/policy do not match the benchmark build "
            "configuration; rebuild with make prepare-evaluation")
    manifest["build"].update(initial_qd_build)
    manifest["environment"] = environment_provenance(args)
    compcert_version = manifest["environment"]["compcert"].lower()
    if (artifact_profile
            and (compcert_version.startswith("unavailable")
                 or "compcert" not in compcert_version)):
        raise EvaluationError(
            "{} runs require DD_CC to resolve to CompCert".format(
                profile_kind))
    clang_version = manifest["environment"]["clang"].lower()
    if (artifact_profile
            and (clang_version.startswith("unavailable")
                 or "clang" not in clang_version)):
        raise EvaluationError(
            "{} runs require CLANG_CC to resolve to Clang".format(
                profile_kind))
    environment, recorded_environment = run_environment()
    raw_directory = stage / "raw"

    specifications = [
        ("rq1", [parameters["rq1_samples"],
                  "raw/.rq1-summary.tsv.partial"],
         raw_directory / ".rq1-summary.tsv.partial",
         raw_directory / "rq1-summary.tsv"),
        ("rq2", [parameters["rq2_samples"],
                  "raw/.rq2-cases.tsv.partial"],
         raw_directory / ".rq2-cases.tsv.partial",
         raw_directory / "rq2-cases.tsv"),
        ("rq3_compcert",
         [parameters["rq3_inputs"], parameters["rq3_trials"],
          "raw/.rq3-compcert-trials.tsv.partial"],
         raw_directory / ".rq3-compcert-trials.tsv.partial",
         raw_directory / "rq3-compcert-trials.tsv"),
        ("rq3_clang",
         [parameters["rq3_inputs"], parameters["rq3_trials"],
          "raw/.rq3-clang-trials.tsv.partial"],
         raw_directory / ".rq3-clang-trials.tsv.partial",
         raw_directory / "rq3-clang-trials.tsv"),
    ]

    for evaluation, driver_arguments, partial_path, final_path in specifications:
        command = run_driver(
            stage, evaluation, executable_paths[evaluation], driver_arguments,
            environment, recorded_environment)
        manifest["commands"].append(command)
        if command["exit_code"] != 0:
            raise EvaluationError(
                "{} exited with status {}".format(
                    evaluation, command["exit_code"]))
        metadata = validate_tsv(
            partial_path, evaluation, parameters)
        manifest["tsv_metadata"][evaluation] = metadata
        if evaluation != "rq2":
            os.replace(str(partial_path), str(final_path))
            manifest["artifacts"][evaluation] = file_record(stage, final_path)
        else:
            uncompressed_sha256 = sha256_file(partial_path)
            uncompressed_bytes = partial_path.stat().st_size
            compressed_path = raw_directory / "rq2-cases.tsv.gz"
            deterministic_gzip(partial_path, compressed_path)
            partial_path.unlink()
            record = file_record(stage, compressed_path)
            record["uncompressed_sha256"] = uncompressed_sha256
            record["uncompressed_bytes"] = uncompressed_bytes
            manifest["artifacts"][evaluation] = record

    validate_shared_generated_inputs(
        manifest["tsv_metadata"]["rq1"],
        manifest["tsv_metadata"]["rq2"])
    validate_shared_rq3_inputs(
        manifest["tsv_metadata"]["rq3_compcert"],
        manifest["tsv_metadata"]["rq3_clang"])

    final_configuration = build_configuration(args)
    final_binaries, _unused_paths = binary_provenance(args.bin_dir)
    final_qd_build = qd_build_records(args.qd_prefix)
    if final_configuration != initial_configuration:
        raise EvaluationError("benchmark build configuration changed during the run")
    if binary_identity(final_binaries) != binary_identity(binaries):
        raise EvaluationError("an evaluation executable changed during the run")
    if final_qd_build != initial_qd_build:
        raise EvaluationError("the QD build changed during the run")

    final_git = git_provenance(args.repo_root)
    manifest["git"] = final_git
    manifest["status"] = "complete"
    manifest["completed_utc"] = utc_now()
    return manifest


def finalize_stage(stage, manifest):
    write_json_atomic(stage / "manifest.json", manifest)
    write_checksums(stage)


def run(args):
    if not RUN_ID_PATTERN.fullmatch(args.run_id) or args.run_id in (".", ".."):
        raise EvaluationError(
            "run-id must contain only letters, digits, dot, underscore, or dash")
    args.profiles = args.profiles.resolve()
    profile = load_profile(args.profiles, args.profile)
    parameters = effective_parameters(args, profile)
    args.run_root = args.run_root.resolve()
    args.bin_dir = args.bin_dir.resolve()
    args.repo_root = args.repo_root.resolve()
    args.qd_prefix_setting = args.qd_prefix
    args.qd_prefix = pathlib.Path(args.qd_prefix).resolve()
    initial_git = git_provenance(args.repo_root)

    args.run_root.mkdir(parents=True, exist_ok=True)
    destination = args.run_root / args.run_id
    if destination.exists():
        raise EvaluationError(
            "run directory already exists; refusing to overwrite {}"
            .format(destination))

    with ExclusiveRunLock(args.run_root):
        if destination.exists():
            raise EvaluationError(
                "run directory already exists; refusing to overwrite {}"
                .format(destination))
        stage = pathlib.Path(tempfile.mkdtemp(
            prefix=".{}.staging-".format(args.run_id),
            dir=str(args.run_root)))
        (stage / "raw").mkdir()
        manifest = base_manifest(args, profile, parameters, initial_git)
        failure = None
        try:
            manifest = execute_run(
                args, profile, parameters, stage, manifest)
        except (Exception, KeyboardInterrupt) as error:
            failure = error
            manifest["status"] = "failed"
            manifest["completed_utc"] = utc_now()
            manifest["failure"] = {
                "type": type(error).__name__,
                "message": str(error),
            }
            failure_path = stage / "failure.txt"
            with open(failure_path, "x", encoding="utf-8", newline="\n") as output:
                traceback.print_exception(
                    type(error), error, error.__traceback__, file=output)
        finalize_stage(stage, manifest)
        finalize_run_directory(stage, destination)
        if failure is not None:
            raise EvaluationError(
                "evaluation failed; immutable failure record: {} ({})"
                .format(destination, failure))
    return destination


def argument_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", default="smoke")
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--profiles", type=pathlib.Path, default=PROFILE_FILE)
    parser.add_argument("--run-root", type=pathlib.Path,
                        default=SCRIPT_DIR / "runs")
    parser.add_argument("--bin-dir", type=pathlib.Path, default=SCRIPT_DIR)
    parser.add_argument("--repo-root", type=pathlib.Path,
                        default=REPOSITORY_ROOT)
    parser.add_argument("--rq1-samples", type=int)
    parser.add_argument("--rq2-samples", type=int)
    parser.add_argument("--rq3-inputs", type=int)
    parser.add_argument("--rq3-trials", type=int)
    parser.add_argument("--dd-cc", default=os.environ.get("DD_CC", "ccomp"))
    parser.add_argument("--dd-cflags",
                        default=os.environ.get("DD_CFLAGS", "-O3"))
    parser.add_argument("--clang-cc",
                        default=os.environ.get("CLANG_CC", "clang"))
    parser.add_argument("--clang-cflags", default=os.environ.get(
        "CLANG_CFLAGS", "-O3 -std=c11"))
    parser.add_argument("--cxx", default=os.environ.get("CXX", "g++"))
    parser.add_argument("--cxxflags", default=os.environ.get(
        "CXXFLAGS", "-O3 -std=c++14 -Wall"))
    parser.add_argument("--strict-fp-flags", default=os.environ.get(
        "STRICT_FP_FLAGS", "-fno-fast-math -ffp-contract=off"))
    parser.add_argument("--qd-prefix",
                        default=os.environ.get("QD_PREFIX", "/usr/local"))
    parser.add_argument("--pkg-config",
                        default=os.environ.get("PKG_CONFIG", "pkg-config"))
    return parser


def main(argv=None):
    args = argument_parser().parse_args(argv)
    try:
        destination = run(args)
    except EvaluationError as error:
        print("run_evaluation: {}".format(error), file=sys.stderr)
        return 1
    print("evaluation run completed at {}".format(destination))
    return 0


if __name__ == "__main__":
    sys.exit(main())
