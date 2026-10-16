#!/usr/bin/env python3
"""Reproduce the pinned submitted proof and preserve mechanical evidence."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PROOF_FILES = ("Erdos319.lean", "Submission.lean", "Audit.lean",
               "lean-toolchain", "lakefile.toml", "lake-manifest.json",
               "audit-targets.json")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(source: str) -> str:
    """Remove Lean line comments and nested block comments for a lead scan."""
    result = []
    depth = 0
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            result.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(result)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--setup", action="store_true", help="fetch pinned dependency cache")
    parser.add_argument("--clean", action="store_true", help="remove this project's build outputs")
    parser.add_argument("--no-kernel-replay", action="store_true",
                        help="skip replay; this is reported explicitly")
    args = parser.parse_args()
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("Lake is required; install elan and rerun in the repository.")

    output = ROOT / "verification" / "latest"
    output.mkdir(parents=True, exist_ok=True)
    expected_targets = json.loads((ROOT / "audit-targets.json").read_text(encoding="utf-8"))
    expected = set(expected_targets["declarations"])
    report = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "kind": "author self-check; not independent human review or award approval",
        "commands": [],
        "source_sha256": {name: digest(ROOT / name) for name in PROOF_FILES},
        "expected_axiom_targets": sorted(expected),
        "expected_mathlib_commit": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
        "allowed_axioms": sorted(STANDARD),
        "kernel_replay_requested": not args.no_kernel_replay,
    }

    def save() -> None:
        (output / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def run(label: str, command: list[str]) -> str:
        logfile = output / (label + ".log")
        start = time.monotonic()
        print("Running " + label, flush=True)
        with logfile.open("wb") as stream:
            process = subprocess.run(command, cwd=ROOT, stdout=stream,
                                     stderr=subprocess.STDOUT, check=False)
        report["commands"].append({
            "name": label, "command": command, "cwd": ".",
            "exit_code": process.returncode,
            "elapsed_seconds": time.monotonic() - start,
            "log": logfile.name,
        })
        save()
        text = logfile.read_text(encoding="utf-8", errors="replace")
        if process.returncode:
            raise RuntimeError(label + " failed: " + text[-6000:])
        return text

    try:
        if args.clean:
            build = ROOT / ".lake" / "build"
            # Never clean a shared dependency checkout or a redirected directory.
            if build.exists():
                if build.is_symlink() or build.resolve() != ROOT / ".lake" / "build":
                    raise RuntimeError("Refusing to clean a redirected build directory")
                shutil.rmtree(build)

        run("lean-version", [lake, "env", "lean", "--version"])
        run("lake-version", [lake, "--version"])
        if args.setup:
            run("dependency-cache", [lake, "exe", "cache", "get"])

        manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        packages = []
        for item in manifest["packages"]:
            package_path = ROOT / manifest["packagesDir"] / item["name"]
            actual = subprocess.check_output(
                ["git", "-C", str(package_path), "rev-parse", "HEAD"],
                text=True, encoding="utf-8").strip()
            packages.append({"name": item["name"], "expected": item["rev"], "actual": actual})
            if actual != item["rev"]:
                raise RuntimeError("Dependency revision mismatch: " + item["name"])
        report["dependency_revisions"] = packages

        for name in ("Erdos319.lean", "Submission.lean"):
            code = without_comments((ROOT / name).read_text(encoding="utf-8"))
            suspect = re.search(
                r"\b(?:sorry|admit|sorryAx|axiom|unsafe|implemented_by|extern|run_elab|run_meta)\b"
                r"|debug\.skipKernelTC", code)
            if suspect:
                raise RuntimeError("Trust-boundary scan requires review: " + name + ": " + suspect[0])

        run("proof-build", [lake, "build", "Erdos319", "Submission"])
        audit = run("axiom-audit", [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"])
        matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
        dependencies = {name: sorted({v.strip() for v in values.split(",") if v.strip()})
                        for name, values in matches}
        if len(matches) != len(expected) or set(dependencies) != expected:
            raise RuntimeError("Axiom audit omitted or duplicated expected declarations")
        if any(not set(values) <= STANDARD for values in dependencies.values()):
            raise RuntimeError("Nonstandard axiom dependency")
        report["axiom_dependencies"] = dependencies

        if not args.no_kernel_replay:
            for module in ("Erdos319", "Submission"):
                run("kernel-replay-" + module, [lake, "env", "leanchecker", "--verbose", module])
        report["kernel_replay_completed"] = not args.no_kernel_replay
        final_hashes = {name: digest(ROOT / name) for name in PROOF_FILES}
        if report["source_sha256"] != final_hashes:
            raise RuntimeError("Pinned proof inputs changed during verification")
        report["all_listed_checks_passed"] = True
        report["scope"] = (
            "Both submitted modules compiled from source, explicit integer-sign bridges checked, "
            "and all listed axiom closures checked. Replay, when requested, checks submitted "
            "modules against imported environments; dependencies are pinned and cache may be reused. "
            "No independent human review, discovery priority or award eligibility is established."
        )
        try:
            report["checked_git_commit"] = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            report["working_tree_status"] = subprocess.check_output(
                ["git", "status", "--porcelain", "--untracked-files=no"], cwd=ROOT, text=True)
        except subprocess.CalledProcessError:
            report["checked_git_commit"] = None
        print("All requested checks passed; evidence: verification/latest/results.json", flush=True)
        return 0
    except Exception as error:
        report["all_listed_checks_passed"] = False
        report["failure"] = str(error)
        print(str(error), file=sys.stderr, flush=True)
        return 1
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    raise SystemExit(main())
