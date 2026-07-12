#!/usr/bin/env python3
"""Generate revision and dependency metadata for the paper artifact."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def run(*args: str) -> str:
    process = subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if process.returncode != 0:
        detail = process.stderr.strip() or process.stdout.strip()
        raise RuntimeError(f"{' '.join(args)} failed: {detail}")
    return process.stdout.strip()


def package_by_name(manifest: dict, name: str) -> dict:
    matches = [item for item in manifest.get("packages", []) if item.get("name") == name]
    if len(matches) != 1:
        raise RuntimeError(f"manifest must contain exactly one package named {name!r}")
    return matches[0]


def required_by_name(lakefile: dict, name: str) -> dict:
    matches = [item for item in lakefile.get("require", []) if item.get("name") == name]
    if len(matches) != 1:
        raise RuntimeError(f"lakefile must contain exactly one requirement named {name!r}")
    return matches[0]


def collect(require_clean: bool = False) -> dict[str, object]:
    try:
        lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
        manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read package metadata: {error}") from error
    mathlib_req = required_by_name(lakefile, "mathlib")
    groebner_req = required_by_name(lakefile, "groebner")
    mathlib = package_by_name(manifest, "mathlib")
    groebner = package_by_name(manifest, "groebner")
    status = run("git", "status", "--porcelain")
    if require_clean and status:
        raise RuntimeError("working tree is dirty")
    branch = run("git", "branch", "--show-current") or "(detached HEAD)"
    license_text = (ROOT / "LICENSE").read_text(encoding="utf-8", errors="replace")
    if "Apache License" not in license_text or "Version 2.0" not in license_text:
        raise RuntimeError("LICENSE is not recognizable as Apache-2.0")
    return {
        "repository_remote_url": run("git", "remote", "get-url", "origin"),
        "current_branch": branch,
        "head_sha": run("git", "rev-parse", "HEAD"),
        "head_short_sha": run("git", "rev-parse", "--short", "HEAD"),
        "working_tree": "clean" if not status else "dirty",
        "lake_package_name": lakefile.get("name"),
        "package_version": lakefile.get("version"),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_version": run("lake", "env", "lean", "--version"),
        "requested_mathlib_revision": mathlib_req.get("rev"),
        "resolved_mathlib_commit": mathlib.get("rev"),
        "requested_groebner_revision": groebner_req.get("rev"),
        "resolved_groebner_commit": groebner.get("rev"),
        "license": "Apache-2.0",
        "principal_import": "MyProject.Determinantalideals.Groebner",
        "main_descriptive_theorem": (
            "Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder"
        ),
        "main_paper_number_alias": (
            "Determinantal.theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder"
        ),
        "ci_workflow_path": ".github/workflows/lean.yml",
    }


def markdown(metadata: dict[str, object]) -> str:
    labels = {
        "repository_remote_url": "Repository remote URL",
        "current_branch": "Current branch",
        "head_sha": "Full HEAD SHA",
        "head_short_sha": "Short HEAD SHA",
        "working_tree": "Working tree",
        "lake_package_name": "Lake package name",
        "package_version": "Package version",
        "lean_toolchain": "Lean toolchain",
        "lean_version": "Lean version",
        "requested_mathlib_revision": "Requested Mathlib revision",
        "resolved_mathlib_commit": "Resolved Mathlib commit",
        "requested_groebner_revision": "Requested groebner revision",
        "resolved_groebner_commit": "Resolved groebner commit",
        "license": "License",
        "principal_import": "Principal import",
        "main_descriptive_theorem": "Main descriptive theorem",
        "main_paper_number_alias": "Main paper-number alias",
        "ci_workflow_path": "CI workflow",
    }
    rows = ["| Artifact field | Value |", "| --- | --- |"]
    for key, label in labels.items():
        value = str(metadata.get(key, "")).replace("|", "\\|").replace("\n", "<br>")
        rows.append(f"| {label} | `{value}` |")
    return "\n".join(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--format", choices=("markdown", "json"), default="markdown")
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    try:
        metadata = collect(require_clean=args.require_clean)
    except (OSError, RuntimeError) as error:
        print(f"artifact metadata error: {error}", file=sys.stderr)
        return 2
    if not metadata["lake_package_name"] or not metadata["package_version"]:
        print("artifact metadata error: package name or version is missing", file=sys.stderr)
        return 2
    if args.format == "json":
        print(json.dumps(metadata, indent=2, ensure_ascii=False))
    else:
        print(markdown(metadata))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
