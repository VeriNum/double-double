#!/usr/bin/env python3
"""Self-tests for QD installation discovery and header validation.

They use temporary synthetic QD prefixes and tools rather than producing or
assessing numerical evaluation results.
"""

from __future__ import annotations

import os
from pathlib import Path
import shlex
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


BENCH_DIRECTORY = Path(__file__).resolve().parents[1]
SCRIPT = BENCH_DIRECTORY / "find_qd.py"
sys.path.insert(0, str(BENCH_DIRECTORY))

import find_qd  # noqa: E402


def make_prefix(root: Path, *, omit: tuple[str, ...] = ()) -> Path:
    include = root / "include" / "qd"
    include.mkdir(parents=True)
    for name in ("dd_real.h", "dd_inline.h", "inline.h", "qd_config.h"):
        if name in omit:
            continue
        content = "/* #undef QD_FMA */\n/* #undef QD_FMS */\n" \
            if name == "qd_config.h" else "/* test QD header */\n"
        (include / name).write_text(content, encoding="utf-8")
    return root.resolve()


def make_qd_config(path: Path, prefix: Path, *, exit_code: int = 0) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "#!/bin/sh\n"
        "if [ \"$1\" != \"--prefix\" ]; then exit 64; fi\n"
        "printf '%s\\n' {}\n"
        "exit {}\n".format(shlex.quote(str(prefix)), exit_code),
        encoding="utf-8",
    )
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


class FindQdTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def invoke(self, *arguments: str, environment=None) -> subprocess.CompletedProcess:
        env = os.environ.copy()
        if environment is not None:
            env.update(environment)
        return subprocess.run(
            [sys.executable, str(SCRIPT), *arguments],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=env,
        )

    def test_explicit_prefix_prints_canonical_path(self) -> None:
        installation = make_prefix(self.root / "installation")
        alias = self.root / "alias"
        alias.symlink_to(installation, target_is_directory=True)

        completed = self.invoke("--prefix-only", "--prefix", str(alias))

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout, str(installation) + "\n")
        self.assertEqual(completed.stderr, "")

    def test_explicit_prefix_does_not_fall_back(self) -> None:
        invalid = make_prefix(self.root / "invalid", omit=("inline.h",))
        fallback = make_prefix(self.root / "fallback")
        config = make_qd_config(self.root / "bin" / "qd-config", fallback)

        completed = self.invoke(
            "--prefix", str(invalid), environment={"PATH": str(config.parent)}
        )

        self.assertNotEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout, "")
        self.assertIn("--prefix is not a usable", completed.stderr)
        self.assertIn("missing include/qd/inline.h", completed.stderr)

    def test_explicit_qd_config_validates_only_its_prefix(self) -> None:
        selected = make_prefix(self.root / "selected")
        config = make_qd_config(self.root / "bin" / "qd-config", selected)

        completed = self.invoke("--qd-config", str(config))

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout, str(selected) + "\n")

    def test_discovery_prefers_artifact_local_installation(self) -> None:
        artifact = self.root / "artifact"
        bundled = make_prefix(artifact / "third_party" / "qd")
        path_prefix = make_prefix(self.root / "path-prefix")
        config = make_qd_config(self.root / "bin" / "qd-config", path_prefix)

        discovered, rejected = find_qd.discover(
            artifact_root=artifact,
            search_path=str(config.parent),
            conventional_prefixes=(),
        )

        self.assertEqual(discovered, bundled)
        self.assertEqual(rejected, ())

    def test_home_local_installation_is_not_probed(self) -> None:
        artifact = self.root / "artifact"
        home = self.root / "home"
        make_prefix(home / ".local" / "qd-fma")

        with mock.patch.dict(os.environ, {"HOME": str(home)}):
            discovered, rejected = find_qd.discover(
                artifact_root=artifact,
                search_path=str(self.root / "empty-path"),
                conventional_prefixes=(),
            )

        self.assertIsNone(discovered)
        self.assertEqual(
            [entry[0] for entry in rejected],
            ["artifact-local third_party/qd"],
        )

    def test_discovery_uses_valid_path_qd_config(self) -> None:
        artifact = self.root / "artifact"
        path_prefix = make_prefix(self.root / "path-prefix")
        config = make_qd_config(self.root / "bin" / "qd-config", path_prefix)

        discovered, rejected = find_qd.discover(
            artifact_root=artifact,
            search_path=str(config.parent),
            conventional_prefixes=(),
        )

        self.assertEqual(discovered, path_prefix)
        self.assertEqual(
            [entry[0] for entry in rejected],
            ["artifact-local third_party/qd"],
        )

    def test_discovery_uses_conventional_prefix_after_path(self) -> None:
        artifact = self.root / "artifact"
        incomplete = make_prefix(
            self.root / "path-prefix", omit=("dd_inline.h",)
        )
        config = make_qd_config(self.root / "bin" / "qd-config", incomplete)
        conventional = make_prefix(self.root / "conventional")

        discovered, rejected = find_qd.discover(
            artifact_root=artifact,
            search_path=str(config.parent),
            conventional_prefixes=(conventional,),
        )

        self.assertEqual(discovered, conventional)
        self.assertEqual(
            [entry[0] for entry in rejected],
            ["artifact-local third_party/qd", "PATH qd-config"],
        )

    def test_non_fma_qd_configuration_is_accepted(self) -> None:
        prefix = make_prefix(self.root / "standard-qd")

        canonical, problems = find_qd.validate_prefix(prefix)

        self.assertEqual(canonical, prefix)
        self.assertEqual(problems, ())

    def test_missing_implementation_header_is_rejected(self) -> None:
        prefix = make_prefix(self.root / "incomplete", omit=("dd_inline.h",))

        canonical, problems = find_qd.validate_prefix(prefix)

        self.assertEqual(canonical, prefix)
        self.assertEqual(problems, ("missing include/qd/dd_inline.h",))

    def test_invalid_qd_config_has_actionable_diagnostic(self) -> None:
        invalid = make_prefix(self.root / "invalid", omit=("dd_inline.h",))
        config = make_qd_config(self.root / "bin" / "qd-config", invalid)

        completed = self.invoke("--qd-config", str(config))

        self.assertNotEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout, "")
        self.assertIn("--qd-config is not a usable", completed.stderr)
        self.assertIn("Required QD headers", completed.stderr)
        self.assertNotIn("libqd", completed.stderr)
        self.assertIn("Set QD_PREFIX", completed.stderr)


if __name__ == "__main__":
    unittest.main()
