"""Validate committed LF policy, archive identity, and fresh bundle checkout cleanliness."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
import zipfile
from pathlib import Path


def require(value: bool, detail: str) -> None:
    if not value:
        raise ValueError(detail)


def run(args: list[str], *, cwd: Path) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(result.returncode == 0, result.stdout.decode("utf-8", errors="replace"))
    return result


def git(root: Path, *args: str) -> bytes:
    return run(["git", *args], cwd=root).stdout


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tracked_paths(root: Path, commit: str) -> list[str]:
    raw = git(root, "ls-tree", "-r", "--name-only", "-z", commit)
    return sorted(item.decode("utf-8") for item in raw.split(b"\0") if item)


def blob_policy(root: Path, commit: str, paths: list[str]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for path in (item for item in paths if item.endswith(".lean")):
        attributes = git(root, "check-attr", "--cached", "text", "eol", "--", path).decode("utf-8")
        require(f"{path}: text: set" in attributes and f"{path}: eol: lf" in attributes, f"LF attributes missing: {path}")
        data = git(root, "show", f"{commit}:{path}")
        require(b"\r\n" not in data, f"CRLF in LF-governed blob: {path}")
        rows.append({"bytes": len(data), "path": path, "sha256": sha256(data)})
    require(rows, "no governed Lean blobs")
    return rows


def archive_identity(root: Path, commit: str, paths: list[str], archive_path: Path, prefix: str) -> dict[str, object]:
    with zipfile.ZipFile(archive_path) as archive:
        require(archive.testzip() is None, "source archive CRC")
        members = {name: archive.read(name) for name in archive.namelist() if not name.endswith("/")}
    expected = {prefix + path for path in paths}
    require(set(members) == expected, "source archive path set differs from Git tree")
    for path in paths:
        require(members[prefix + path] == git(root, "show", f"{commit}:{path}"), f"archive/blob bytes differ: {path}")
    return {"file_count": len(paths), "path": os.fspath(archive_path), "sha256": sha256(archive_path.read_bytes()), "status": "PASS"}


def checkout_cleanliness(bundle: Path, commit: str) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="mathlibannex-fix1-checkout-") as temporary_name:
        checkout = Path(temporary_name) / "checkout"
        run(["git", "clone", "--no-checkout", os.fspath(bundle), os.fspath(checkout)], cwd=Path(temporary_name))
        git(checkout, "config", "core.autocrlf", "false")
        git(checkout, "config", "core.eol", "lf")
        git(checkout, "config", "core.safecrlf", "true")
        git(checkout, "checkout", "--detach", commit)
        tracked = git(checkout, "diff", "--exit-code")
        staged = git(checkout, "diff", "--cached", "--exit-code")
        porcelain = git(checkout, "status", "--porcelain=v1", "--untracked-files=all")
        require(not tracked and not staged and not porcelain, "fresh Linux-compatible checkout is dirty")
        return {
            "configuration": {"core.autocrlf": "false", "core.eol": "lf", "core.safecrlf": "true"},
            "porcelain_empty": True, "staged_diff_empty": True, "tracked_diff_empty": True,
            "status": "PASS",
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--commit", default="HEAD")
    parser.add_argument("--source-archive", type=Path)
    parser.add_argument("--bundle", type=Path)
    parser.add_argument("--archive-prefix", default="MathlibAnnex-0.2.0-rc.1/")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()
    commit = git(root, "rev-parse", args.commit).decode("ascii").strip()
    paths = tracked_paths(root, commit)
    value: dict[str, object] = {
        "blob_lf_policy": {"files": blob_policy(root, commit, paths), "status": "PASS"},
        "commit": commit,
        "schema": "mathlibannex.candidate-cleanliness-validation.v1",
        "status": "PASS",
    }
    if args.source_archive is not None or args.bundle is not None:
        require(args.source_archive is not None and args.bundle is not None, "archive and bundle are paired")
        value["source_archive_identity"] = archive_identity(root, commit, paths, args.source_archive.resolve(), args.archive_prefix)
        value["fresh_bundle_checkout"] = checkout_cleanliness(args.bundle.resolve(), commit)
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    print("PASS_MATHLIBANNEX_CANDIDATE_CLEANLINESS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
