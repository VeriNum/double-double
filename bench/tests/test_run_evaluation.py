#!/usr/bin/env python3
"""Self-tests for run validation, provenance checks, and atomic finalization.

They use temporary synthetic drivers, tools, and output files rather than
producing or assessing numerical evaluation results.
"""

import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


BENCH_DIRECTORY = Path(__file__).resolve().parents[1]
RUNNER = BENCH_DIRECTORY / "run_evaluation.py"
DRIVERS = (
    "rq1_accuracy",
    "rq2_guard_acceptance",
    "rq3_performance_compcert",
    "rq3_performance_clang",
)
QD_IMPLEMENTATION_HEADERS = (
    "dd_real.h",
    "dd_inline.h",
    "inline.h",
    "qd_config.h",
)


FAKE_DRIVER = r'''#!/usr/bin/env python3
import os
from pathlib import Path
import sys


name = Path(sys.argv[0]).name
order_path = os.environ.get("FAKE_ORDER_FILE")
if order_path:
    with open(order_path, "a", encoding="utf-8") as order:
        order.write(name + "\n")

print("stdout from " + name)
print("stderr from " + name, file=sys.stderr)

if name == "rq1_accuracy":
    samples = int(sys.argv[1])
    destination = Path(sys.argv[2])
    lines = [
        "# rq1_schema_version=6",
        "# generator=mpfr106-v1",
        "# seed=0xc0ffee",
        "# input_fingerprint=0x0123456789abcdef",
        "# samples_per_exponent={}".format(samples),
        "# construction_precision_bits=256",
        "# oracle_precision_bits=2112",
        "# division_recheck_precision_bits=4224",
        "record\toperation\timplementation\tmetric\tcount\tmaximum\tmean"
        "\tmaximum_scaled\tmean_scaled\tflags\tflag_kind\tcase_id"
        "\tresult_hi_bits\tresult_lo_bits\treference\tabsolute_error\tinputs",
        "count\tdw_plus_fp\tdd_lib\tgenerated\t1\t-\t-\t-\t-\t0\tnone"
        "\t-\t-\t-\t-\t-\t-",
        "# data_rows=1",
        "# completed=true",
    ]
elif name == "rq2_guard_acceptance":
    samples = int(sys.argv[1])
    destination = Path(sys.argv[2])
    fingerprint = ("0x1111111111111111" if
                   os.environ.get("MISMATCH_RQ2") else
                   "0x0123456789abcdef")
    lines = [
        "# rq2_schema_version=5",
        "# generator=mpfr106-v1",
        "# seed=0xc0ffee",
        "# input_fingerprint=" + fingerprint,
        "# samples_per_exponent={}".format(samples),
        "# oracle_precision_bits=2112",
        "# division_oracle_precision_bits=4224",
        "# qd_inline=1",
        "# qd_fma=std::fma",
        "suite\toperation\tcase_id\tfirst_exponent\tsecond_exponent"
        "\tdefault_outcome\tstrong_outcome\tfailure_mask"
        "\tfailed_additional_conditions\tchecked_exponents\tcase_name\tinputs"
        "\tshared_result_equal\tqd_result_hi_bits\tqd_result_lo_bits"
        "\tqd_finite\tqd_valid_dw\tqd_within_bound\tqd_exact_reconstruction"
        "\treference\tabsolute_error\tbound\texpected_default_outcome"
        "\texpected_strong_outcome\texpected_failure_mask\tassertion_passed",
        "log_stratified\tdw_plus_fp\t0\t0\t0\tnormal\tnormal\t0x00\t-\t-"
        "\t-\tcase=0\tyes\t-\t-\tnot_evaluated\tnot_evaluated"
        "\tnot_evaluated\tnot_applicable\t-\t-\t-\t-\t-\t-\t-",
        "# data_rows=1",
        "# completed=true",
    ]
elif name in ("rq3_performance_compcert", "rq3_performance_clang"):
    input_count = int(sys.argv[1])
    trial_count = int(sys.argv[2])
    destination = Path(sys.argv[3])
    build = ("compcert" if name.endswith("_compcert") else "clang")
    recorded_build = ("wrong-build" if
                      os.environ.get("MISMATCH_RQ3_BUILD") == name else build)
    fingerprint = ("0x2222222222222222" if
                   os.environ.get("MISMATCH_RQ3_INPUTS") == name else
                   "0xfedcba9876543210")
    lines = [
        "# rq3_schema_version=4",
        "# build=" + recorded_build,
        "# input_count={}".format(input_count),
        "# trial_count={}".format(trial_count),
        "# composite_interfaces=default:two-stage,strong:input-only",
        "# exact_transform_interface=default:guarded",
        "# input_fingerprint=" + fingerprint,
        "# quantile=linear_interpolation_p_times_n_minus_1",
        "# exact_schedule=all_six_permutations",
        "# composite_schedule=all_twenty_four_permutations",
        "# timer=std_chrono_steady_clock",
        "operation\timplementation\tinterface\ttrial\tns_per_call",
    ]
    exact_operations = ("two_sum", "fast_2sum", "fast_2mult")
    composite_operations = (
        "dw_plus_fp", "dw_times_fp", "dw_div_fp",
        "dw_plus_dw", "dw_times_dw", "dw_div_dw",
    )
    for trial in range(trial_count):
        for operation in exact_operations:
            for implementation, interface in (
                    ("dd_lib", "default"),
                    ("dd_lib", "kernel"),
                    ("QD", "reference")):
                lines.append("{}\t{}\t{}\t{}\t1".format(
                    operation, implementation, interface, trial))
        for operation in composite_operations:
            for implementation, interface in (
                    ("dd_lib", "default"),
                    ("dd_lib", "strong"),
                    ("dd_lib", "kernel"),
                    ("QD", "reference")):
                lines.append("{}\t{}\t{}\t{}\t1".format(
                    operation, implementation, interface, trial))
    data_rows = 33 * trial_count
    if os.environ.get("TRUNCATE_RQ3") == name:
        lines.pop()
        data_rows -= 1
    lines.extend((
        "# data_rows={}".format(data_rows),
        "# completed=true",
    ))
else:
    raise SystemExit("unexpected fake driver name: " + name)

destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text("\n".join(lines) + "\n", encoding="utf-8")
if os.environ.get("FAIL_DRIVER") == name:
    raise SystemExit(7)
if os.environ.get("MUTATE_BINARY") == name:
    with open(sys.argv[0], "a", encoding="utf-8") as executable:
        executable.write("# changed during run\n")
if os.environ.get("MUTATE_QD_HEADER_ON") == name:
    with open(os.environ["QD_HEADER_PATH"], "a", encoding="utf-8") as header:
        header.write("// changed during run\n")
'''


def sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for block in iter(lambda: source.read(65536), b""):
            digest.update(block)
    return digest.hexdigest()


def file_identity(path):
    path = Path(path)
    return {
        "path": str(path.resolve()),
        "sha256": sha256(path),
        "bytes": path.stat().st_size,
    }


class RunnerTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.bin_directory = self.root / "bin"
        self.bin_directory.mkdir()
        for name in DRIVERS:
            path = self.bin_directory / name
            path.write_text(FAKE_DRIVER, encoding="utf-8")
            path.chmod(0o755)
        build_directory = self.bin_directory / ".build"
        build_directory.mkdir()
        self.qd_prefix = self.root / "exact-qd-prefix-setting"
        qd_header_directory = self.qd_prefix / "include" / "qd"
        qd_header_directory.mkdir(parents=True)
        self.qd_headers = []
        for name in QD_IMPLEMENTATION_HEADERS:
            path = qd_header_directory / name
            path.write_text("// synthetic {}\n".format(name), encoding="utf-8")
            self.qd_headers.append(path)
        qd_identity = {
            "headers": [file_identity(path) for path in self.qd_headers],
            "policy": file_identity(BENCH_DIRECTORY / "qd_evaluation.hpp"),
        }
        (build_directory / "config.json").write_text(json.dumps({
            "config_schema_version": 3,
            "clang_cc": "exact-clang-setting",
            "clang_cflags": "-O2 exact-clang-flag",
            "dd_cc": "exact-ccomp-setting",
            "dd_cflags": "-O2 exact-dd-flag",
            "cxx": "exact-cxx-setting",
            "cxxflags": "-O2 exact-cxx-flag",
            "strict_fp_flags": "-fexact-strict-setting",
            "qd_prefix": "./exact-qd-prefix-setting",
            "mpfr_cflags": "test-mpfr-cflags",
            "mpfr_libs": "test-mpfr-libs",
            "tool_identities": {
                "clang_cc": {},
                "cxx": {},
                "dd_cc": {},
                "qd": qd_identity,
            },
        }, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        self.run_root = self.root / "runs"
        self.repository = self.root / "repository"
        self.repository.mkdir()
        self.order_file = self.root / "order.txt"

    def tearDown(self):
        self.temporary.cleanup()

    def invoke(self, run_id, profile="smoke", extra_arguments=(),
               extra_environment=None):
        command = [
            sys.executable,
            str(RUNNER),
            "--profile", profile,
            "--run-id", run_id,
            "--run-root", str(self.run_root),
            "--bin-dir", str(self.bin_directory),
            "--repo-root", str(self.repository),
        ] + list(extra_arguments)
        environment = os.environ.copy()
        environment.update({
            "PYTHONDONTWRITEBYTECODE": "1",
            "FAKE_ORDER_FILE": str(self.order_file),
            "DD_CC": "exact-ccomp-setting",
            "DD_CFLAGS": "-O2 exact-dd-flag",
            "CLANG_CC": "exact-clang-setting",
            "CLANG_CFLAGS": "-O2 exact-clang-flag",
            "CXX": "exact-cxx-setting",
            "CXXFLAGS": "-O2 exact-cxx-flag",
            "STRICT_FP_FLAGS": "-fexact-strict-setting",
            "QD_PREFIX": "./exact-qd-prefix-setting",
            "PKG_CONFIG": "missing-pkg-config-for-runner-test",
        })
        if extra_environment:
            environment.update(extra_environment)
        return subprocess.run(
            command, cwd=str(self.root), env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace", check=False)

    def read_manifest(self, run_id):
        path = self.run_root / run_id / "manifest.json"
        with open(path, encoding="utf-8") as source:
            return json.load(source)

    def verify_checksums(self, run_id):
        directory = self.run_root / run_id
        lines = (directory / "checksums.sha256").read_text(
            encoding="ascii").splitlines()
        self.assertTrue(lines)
        paths = []
        for line in lines:
            digest, relative = line.split("  ", 1)
            paths.append(relative)
            self.assertEqual(digest, sha256(directory / relative))
        self.assertEqual(paths, sorted(paths))
        self.assertNotIn("checksums.sha256", paths)

    def configure_frozen_build(self):
        compiler = self.root / "artifact-ccomp"
        compiler.write_text(
            "#!/bin/sh\necho 'CompCert synthetic test compiler'\n",
            encoding="utf-8")
        compiler.chmod(0o755)
        clang = self.root / "artifact-clang"
        clang.write_text(
            "#!/bin/sh\necho 'clang synthetic test compiler'\n",
            encoding="utf-8")
        clang.chmod(0o755)
        configuration_path = self.bin_directory / ".build" / "config.json"
        configuration = json.loads(
            configuration_path.read_text(encoding="utf-8"))
        configuration.update({
            "clang_cc": str(clang),
            "clang_cflags": "-O3 -std=c11",
            "dd_cc": str(compiler),
            "dd_cflags": "-O3",
            "cxxflags": "-O3 -std=c++14 -Wall",
            "strict_fp_flags": "-fno-fast-math -ffp-contract=off",
        })
        configuration_path.write_text(
            json.dumps(configuration, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        return {
            "CLANG_CC": str(clang),
            "CLANG_CFLAGS": "-O3 -std=c11",
            "DD_CC": str(compiler),
            "DD_CFLAGS": "-O3",
            "CXXFLAGS": "-O3 -std=c++14 -Wall",
            "STRICT_FP_FLAGS": "-fno-fast-math -ffp-contract=off",
        }

    def test_success_is_atomic_immutable_and_reproducibly_compressed(self):
        overrides = (
            "--rq1-samples", "80",
            "--rq2-samples", "80",
            "--rq3-inputs", "17",
            "--rq3-trials", "24",
        )
        first = self.invoke("success-one", extra_arguments=overrides)
        self.assertEqual(first.returncode, 0, first.stderr)
        manifest = self.read_manifest("success-one")
        self.assertEqual(manifest["manifest_schema_version"], 5)
        self.assertEqual(manifest["status"], "complete")
        self.assertEqual(manifest["profile"]["name"], "smoke")
        self.assertEqual(manifest["profile"]["kind"], "smoke")
        self.assertEqual(
            manifest["profile"]["source"]["sha256"],
            sha256(BENCH_DIRECTORY / "evaluation_profiles.json"))
        self.assertEqual(manifest["parameters"], {
            "rq1_samples": 80,
            "rq2_samples": 80,
            "rq3_inputs": 17,
            "rq3_trials": 24,
        })
        self.assertEqual(manifest["build"]["dd_cc"],
                         "exact-ccomp-setting")
        self.assertEqual(manifest["build"]["dd_cflags"],
                         "-O2 exact-dd-flag")
        self.assertEqual(manifest["build"]["clang_cc"],
                         "exact-clang-setting")
        self.assertEqual(manifest["build"]["clang_cflags"],
                         "-O2 exact-clang-flag")
        self.assertEqual(manifest["build"]["cxx"],
                         "exact-cxx-setting")
        self.assertEqual(manifest["build"]["cxxflags"],
                         "-O2 exact-cxx-flag")
        self.assertEqual(manifest["build"]["strict_fp_flags"],
                         "-fexact-strict-setting")
        self.assertEqual(manifest["build"]["qd_prefix"],
                         "./exact-qd-prefix-setting")
        self.assertEqual(manifest["build"]["configuration"]["values"]
                         ["strict_fp_flags"],
                         "-fexact-strict-setting")
        self.assertEqual(manifest["build"]["configuration"]["values"]
                         ["config_schema_version"], 3)
        self.assertIn(
            "clang_cc",
            manifest["build"]["configuration"]["values"]["tool_identities"])
        expected_qd_identity = {
            "headers": [file_identity(path) for path in self.qd_headers],
            "policy": file_identity(BENCH_DIRECTORY / "qd_evaluation.hpp"),
        }
        self.assertEqual(
            manifest["build"]["configuration"]["values"]
            ["tool_identities"]["qd"],
            expected_qd_identity)
        self.assertEqual(
            manifest["build"]["qd_headers"],
            expected_qd_identity["headers"])
        self.assertEqual(
            manifest["build"]["qd_policy"],
            expected_qd_identity["policy"])
        self.assertNotIn("qd_config", manifest["build"])
        self.assertNotIn("qd_libraries", manifest["build"])
        self.assertIn("compcert_executable", manifest["environment"])
        self.assertIn("clang_executable", manifest["environment"])
        self.assertIn("clang", manifest["environment"])
        self.assertIn("cxx_executable", manifest["environment"])
        self.assertIn("unavailable (missing", manifest["environment"]["qd"])
        for command in manifest["commands"]:
            self.assertEqual(
                command["environment"],
                {"LC_ALL": "C", "LANG": "C", "TZ": "UTC"})
        self.assertEqual(
            [entry["evaluation"] for entry in manifest["commands"]],
            ["rq1", "rq2", "rq3_compcert", "rq3_clang"])
        self.assertEqual(self.order_file.read_text(encoding="utf-8").splitlines(),
                         list(DRIVERS))
        self.assertEqual(manifest["artifacts"]["rq1"]["path"],
                         "raw/rq1-summary.tsv")
        self.assertEqual(manifest["artifacts"]["rq2"]["path"],
                         "raw/rq2-cases.tsv.gz")
        self.assertEqual(
            set(manifest["build"]["binaries"]),
            {"rq1", "rq2", "rq3_compcert", "rq3_clang"})
        self.assertEqual(
            set(manifest["artifacts"]),
            {"rq1", "rq2", "rq3_compcert", "rq3_clang"})
        self.assertEqual(
            set(manifest["tsv_metadata"]),
            {"rq1", "rq2", "rq3_compcert", "rq3_clang"})
        self.assertEqual(
            manifest["tsv_metadata"]["rq1"]["rq1_schema_version"], "6")
        self.assertEqual(manifest["artifacts"]["rq3_compcert"]["path"],
                         "raw/rq3-compcert-trials.tsv")
        self.assertEqual(manifest["artifacts"]["rq3_clang"]["path"],
                         "raw/rq3-clang-trials.tsv")
        self.assertEqual(
            manifest["tsv_metadata"]["rq3_compcert"]["build"], "compcert")
        self.assertEqual(
            manifest["tsv_metadata"]["rq3_clang"]["build"], "clang")
        self.assertEqual(
            manifest["tsv_metadata"]["rq3_compcert"]["input_fingerprint"],
            manifest["tsv_metadata"]["rq3_clang"]["input_fingerprint"])
        self.assertEqual(manifest["tsv_metadata"]["rq1"]
                         ["input_fingerprint"],
                         manifest["tsv_metadata"]["rq2"]
                         ["input_fingerprint"])

        first_gzip = self.run_root / "success-one" / "raw/rq2-cases.tsv.gz"
        first_bytes = first_gzip.read_bytes()
        self.assertEqual(first_bytes[4:8], b"\0\0\0\0")
        self.assertEqual(first_bytes[3] & 0x08, 0)
        uncompressed = gzip.decompress(first_bytes)
        rq2_record = manifest["artifacts"]["rq2"]
        self.assertEqual(rq2_record["sha256"], hashlib.sha256(
            first_bytes).hexdigest())
        self.assertEqual(rq2_record["uncompressed_sha256"], hashlib.sha256(
            uncompressed).hexdigest())
        self.assertEqual(rq2_record["uncompressed_bytes"], len(uncompressed))
        self.verify_checksums("success-one")
        self.assertFalse((self.run_root / ".run_evaluation.lock").exists())
        self.assertEqual(list(self.run_root.glob(".*.staging-*")), [])

        self.order_file.unlink()
        second = self.invoke("success-two", extra_arguments=overrides)
        self.assertEqual(second.returncode, 0, second.stderr)
        second_gzip = self.run_root / "success-two" / "raw/rq2-cases.tsv.gz"
        self.assertEqual(first_bytes, second_gzip.read_bytes())

        original_manifest = (self.run_root / "success-one" /
                             "manifest.json").read_bytes()
        repeated = self.invoke("success-one", extra_arguments=overrides)
        self.assertNotEqual(repeated.returncode, 0)
        self.assertIn("refusing to overwrite", repeated.stderr)
        self.assertEqual(original_manifest, (self.run_root / "success-one" /
                                             "manifest.json").read_bytes())

    def test_driver_failure_finalizes_logs_and_failure_manifest(self):
        completed = self.invoke(
            "driver-failure",
            extra_environment={"FAIL_DRIVER": "rq2_guard_acceptance"})
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("driver-failure")
        self.assertEqual(manifest["status"], "failed")
        self.assertIn("rq2 exited with status 7",
                      manifest["failure"]["message"])
        self.assertEqual(
            [entry["evaluation"] for entry in manifest["commands"]],
            ["rq1", "rq2"])
        self.assertEqual(manifest["commands"][-1]["exit_code"], 7)
        self.assertEqual(set(manifest["artifacts"]), {"rq1"})
        directory = self.run_root / "driver-failure"
        self.assertTrue((directory / "raw/rq2.stdout.log").is_file())
        self.assertTrue((directory / "raw/rq2.stderr.log").is_file())
        self.assertTrue((directory /
                         "raw/.rq2-cases.tsv.partial").is_file())
        self.assertTrue((directory / "failure.txt").is_file())
        self.verify_checksums("driver-failure")

    def test_generated_input_mismatch_is_a_recorded_failure(self):
        completed = self.invoke(
            "generated-inputs-mismatch",
            extra_environment={"MISMATCH_RQ2": "1"})
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("generated-inputs-mismatch")
        self.assertEqual(manifest["status"], "failed")
        self.assertIn("RQ1 and RQ2 metadata disagree on input_fingerprint",
                      manifest["failure"]["message"])
        self.assertEqual(
            set(manifest["artifacts"]),
            {"rq1", "rq2", "rq3_compcert", "rq3_clang"})
        self.assertEqual(len(manifest["commands"]), 4)

    def test_rq3_build_label_mismatch_is_a_recorded_failure(self):
        completed = self.invoke(
            "rq3-build-mismatch",
            extra_environment={
                "MISMATCH_RQ3_BUILD": "rq3_performance_compcert",
            })
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("rq3-build-mismatch")
        self.assertIn(
            "rq3_compcert metadata build='wrong-build', expected 'compcert'",
            manifest["failure"]["message"])
        self.assertEqual(
            [entry["evaluation"] for entry in manifest["commands"]],
            ["rq1", "rq2", "rq3_compcert"])
        self.assertEqual(set(manifest["artifacts"]), {"rq1", "rq2"})

    def test_rq3_input_mismatch_is_a_recorded_failure(self):
        completed = self.invoke(
            "rq3-inputs-mismatch",
            extra_environment={
                "MISMATCH_RQ3_INPUTS": "rq3_performance_clang",
            })
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("rq3-inputs-mismatch")
        self.assertIn(
            "CompCert and Clang RQ3 metadata disagree on input_fingerprint",
            manifest["failure"]["message"])
        self.assertEqual(len(manifest["commands"]), 4)
        self.assertEqual(
            set(manifest["artifacts"]),
            {"rq1", "rq2", "rq3_compcert", "rq3_clang"})

    def test_rq3_requires_thirty_three_series_per_trial(self):
        completed = self.invoke(
            "short-rq3",
            extra_environment={
                "TRUNCATE_RQ3": "rq3_performance_compcert",
            })
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("short-rq3")
        self.assertIn(
            "rq3_compcert wrote 791 data rows; expected 33 per trial",
            manifest["failure"]["message"])
        self.assertEqual(
            [entry["evaluation"] for entry in manifest["commands"]],
            ["rq1", "rq2", "rq3_compcert"])

    def test_rq3_trials_must_be_a_multiple_of_twenty_four(self):
        completed = self.invoke(
            "unbalanced-rq3", extra_arguments=("--rq3-trials", "6"))
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("rq3_trials must be a multiple of 24", completed.stderr)
        self.assertFalse((self.run_root / "unbalanced-rq3").exists())

    def test_binary_change_during_run_is_a_recorded_failure(self):
        completed = self.invoke(
            "binary-change",
            extra_environment={"MUTATE_BINARY": "rq3_performance_clang"})
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("binary-change")
        self.assertEqual(manifest["status"], "failed")
        self.assertIn("executable changed during the run",
                      manifest["failure"]["message"])
        self.assertEqual(len(manifest["commands"]), 4)

    def test_compcert_rq3_binary_change_during_run_is_recorded(self):
        completed = self.invoke(
            "compcert-binary-change",
            extra_environment={
                "MUTATE_BINARY": "rq3_performance_compcert",
            })
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("compcert-binary-change")
        self.assertIn("executable changed during the run",
                      manifest["failure"]["message"])
        self.assertEqual(len(manifest["commands"]), 4)

    def test_qd_header_change_since_build_prevents_execution(self):
        with self.qd_headers[0].open("a", encoding="utf-8") as header:
            header.write("// stale build\n")
        completed = self.invoke("stale-qd-build")
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("stale-qd-build")
        self.assertIn(
            "current QD headers/policy do not match",
            manifest["failure"]["message"])
        self.assertIn("rebuild", manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])
        self.assertFalse(self.order_file.exists())

    def test_missing_required_qd_header_prevents_execution(self):
        self.qd_headers[1].unlink()
        completed = self.invoke("missing-qd-header")
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("missing-qd-header")
        self.assertIn(
            "missing required provenance file",
            manifest["failure"]["message"])
        self.assertIn("dd_inline.h", manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])
        self.assertFalse(self.order_file.exists())

    def test_qd_header_change_during_run_is_a_recorded_failure(self):
        completed = self.invoke(
            "qd-header-change",
            extra_environment={
                "MUTATE_QD_HEADER_ON": "rq3_performance_clang",
                "QD_HEADER_PATH": str(self.qd_headers[2]),
            })
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("qd-header-change")
        self.assertIn(
            "QD build changed during the run",
            manifest["failure"]["message"])
        self.assertEqual(len(manifest["commands"]), 4)

    def test_selected_prefix_without_qd_config_does_not_fall_back_to_path(self):
        tools_directory = self.root / "path-tools"
        tools_directory.mkdir()
        unrelated = tools_directory / "qd-config"
        unrelated.write_text(
            "#!/bin/sh\necho unrelated-path-qd-config\n", encoding="utf-8")
        unrelated.chmod(0o755)
        completed = self.invoke(
            "no-qd-config-fallback",
            extra_environment={
                "PATH": str(tools_directory) + os.pathsep
                        + os.environ.get("PATH", ""),
            })
        self.assertEqual(completed.returncode, 0, completed.stderr)
        environment = self.read_manifest("no-qd-config-fallback")["environment"]
        self.assertIn("unavailable (missing", environment["qd"])
        self.assertNotIn("unrelated-path", environment["qd"])
        self.assertIn(
            str(self.qd_prefix / "bin" / "qd-config"),
            environment["qd_config_executable"])

    def test_existing_lock_prevents_execution(self):
        self.run_root.mkdir()
        lock = self.run_root / ".run_evaluation.lock"
        lock.write_text("occupied\n", encoding="utf-8")
        completed = self.invoke("locked")
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("another evaluation holds", completed.stderr)
        self.assertFalse((self.run_root / "locked").exists())
        self.assertFalse(self.order_file.exists())
        self.assertEqual(lock.read_text(encoding="utf-8"), "occupied\n")

    def test_build_configuration_mismatch_prevents_execution(self):
        path = self.bin_directory / ".build" / "config.json"
        configuration = json.loads(path.read_text(encoding="utf-8"))
        configuration["qd_prefix"] = "/different/qd"
        path.write_text(json.dumps(configuration), encoding="utf-8")
        completed = self.invoke("config-mismatch")
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("config-mismatch")
        self.assertEqual(manifest["status"], "failed")
        self.assertIn("built configuration qd_prefix",
                      manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])
        self.assertFalse(self.order_file.exists())

    def test_artifact_profile_runs_without_a_git_checkout(self):
        completed = self.invoke(
            "artifact-no-git", profile="artifact",
            extra_environment=self.configure_frozen_build())
        self.assertEqual(completed.returncode, 0, completed.stderr)
        manifest = self.read_manifest("artifact-no-git")
        self.assertEqual(manifest["status"], "complete")
        self.assertEqual(manifest["profile"]["kind"], "artifact")
        self.assertEqual(manifest["parameters"], {
            "rq1_samples": 40,
            "rq2_samples": 40,
            "rq3_inputs": 65536,
            "rq3_trials": 24,
        })
        self.assertIsNone(manifest["git"]["revision"])
        self.assertTrue(manifest["git"]["dirty"])
        self.assertEqual(len(manifest["commands"]), 4)

    def test_profile_inventory_has_one_full_artifact_path(self):
        profile_document = json.loads(
            (BENCH_DIRECTORY / "evaluation_profiles.json").read_text(
                encoding="utf-8"))
        self.assertEqual(profile_document["profile_schema_version"], 3)
        profiles = profile_document["profiles"]
        self.assertEqual(set(profiles), {"smoke", "artifact"})
        self.assertEqual(profiles["smoke"], {
            "kind": "smoke",
            "rq1_samples": 40,
            "rq2_samples": 40,
            "rq3_inputs": 4096,
            "rq3_trials": 24,
        })
        self.assertEqual(profiles["artifact"], {
            "kind": "artifact",
            "required_build": {
                "clang_cflags": "-O3 -std=c11",
                "dd_cflags": "-O3",
                "cxxflags": "-O3 -std=c++14 -Wall",
                "strict_fp_flags": "-fno-fast-math -ffp-contract=off",
            },
            "rq1_samples": 40,
            "rq2_samples": 40,
            "rq3_inputs": 65536,
            "rq3_trials": 24,
        })
        self.assertLess(
            profiles["smoke"]["rq3_inputs"],
            profiles["artifact"]["rq3_inputs"],
        )

    @unittest.skipUnless(shutil.which("git"), "git is required")
    def test_dirty_artifact_profile_runs_without_a_git_gate(self):
        git = shutil.which("git")
        subprocess.run([git, "init", "-q", str(self.repository)], check=True)
        subprocess.run(
            [git, "-C", str(self.repository), "config", "user.email",
             "runner-test@example.invalid"], check=True)
        subprocess.run(
            [git, "-C", str(self.repository), "config", "user.name",
             "Runner Test"], check=True)
        tracked = self.repository / "tracked.txt"
        tracked.write_text("initial\n", encoding="utf-8")
        subprocess.run(
            [git, "-C", str(self.repository), "add", "tracked.txt"],
            check=True)
        subprocess.run(
            [git, "-C", str(self.repository), "commit", "-q", "-m", "initial"],
            check=True)
        tracked.write_text("dirty\n", encoding="utf-8")

        completed = self.invoke(
            "dirty-artifact", profile="artifact",
            extra_environment=self.configure_frozen_build())
        self.assertEqual(completed.returncode, 0, completed.stderr)
        manifest = self.read_manifest("dirty-artifact")
        self.assertEqual(manifest["status"], "complete")
        self.assertEqual(manifest["profile"]["kind"], "artifact")
        self.assertTrue(manifest["git"]["dirty"])
        self.assertEqual(len(manifest["commands"]), 4)

    def test_artifact_profile_refuses_nonfrozen_build_flags(self):
        environment = self.configure_frozen_build()
        environment["DD_CFLAGS"] = "-O2"
        completed = self.invoke(
            "unsafe-artifact", profile="artifact",
            extra_environment=environment)
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("unsafe-artifact")
        self.assertEqual(manifest["status"], "failed")
        self.assertIn(
            "artifact build setting dd_cflags",
            manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])
        self.assertFalse(self.order_file.exists())

    def test_artifact_profile_refuses_nonfrozen_clang_flags(self):
        environment = self.configure_frozen_build()
        environment["CLANG_CFLAGS"] = "-O2 -std=c11"
        completed = self.invoke(
            "unsafe-clang-artifact", profile="artifact",
            extra_environment=environment)
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("unsafe-clang-artifact")
        self.assertIn(
            "artifact build setting clang_cflags",
            manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])

    def test_artifact_profile_refuses_parameter_overrides(self):
        completed = self.invoke(
            "artifact-override", profile="artifact",
            extra_arguments=("--rq1-samples", "40"),
            extra_environment=self.configure_frozen_build())
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("artifact-override")
        self.assertIn(
            "artifact profile parameters cannot be overridden",
            manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])

    def test_artifact_profile_refuses_an_alternate_profile_file(self):
        alternate = self.root / "copied-evaluation-profiles.json"
        alternate.write_bytes(
            (BENCH_DIRECTORY / "evaluation_profiles.json").read_bytes())
        completed = self.invoke(
            "artifact-alternate-profile", profile="artifact",
            extra_arguments=("--profiles", str(alternate)),
            extra_environment=self.configure_frozen_build())
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("artifact-alternate-profile")
        self.assertIn(
            "artifact runs must use the repository's frozen profile file",
            manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])

    def test_artifact_profile_rejects_unavailable_compcert_named_command(self):
        environment = self.configure_frozen_build()
        missing_compiler = self.root / "missing-compcert-command"
        configuration_path = self.bin_directory / ".build" / "config.json"
        configuration = json.loads(
            configuration_path.read_text(encoding="utf-8"))
        configuration["dd_cc"] = str(missing_compiler)
        configuration_path.write_text(
            json.dumps(configuration, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        environment["DD_CC"] = str(missing_compiler)

        completed = self.invoke(
            "artifact-missing-compcert", profile="artifact",
            extra_environment=environment)
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("artifact-missing-compcert")
        self.assertTrue(
            manifest["environment"]["compcert"].startswith("unavailable"))
        self.assertIn(
            "artifact runs require DD_CC to resolve to CompCert",
            manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])

    def test_artifact_profile_rejects_a_non_clang_compiler(self):
        environment = self.configure_frozen_build()
        clang = Path(environment["CLANG_CC"])
        clang.write_text(
            "#!/bin/sh\necho 'GCC synthetic test compiler'\n",
            encoding="utf-8")
        clang.chmod(0o755)

        completed = self.invoke(
            "artifact-non-clang", profile="artifact",
            extra_environment=environment)
        self.assertNotEqual(completed.returncode, 0)
        manifest = self.read_manifest("artifact-non-clang")
        self.assertEqual(manifest["environment"]["clang"],
                         "GCC synthetic test compiler")
        self.assertIn(
            "artifact runs require CLANG_CC to resolve to Clang",
            manifest["failure"]["message"])
        self.assertEqual(manifest["commands"], [])

    def test_unknown_profile_is_rejected(self):
        completed = self.invoke("unknown-profile", profile="not-a-profile")
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("unknown evaluation profile: not-a-profile", completed.stderr)
        self.assertFalse((self.run_root / "unknown-profile").exists())
        self.assertFalse(self.order_file.exists())


if __name__ == "__main__":
    unittest.main()
