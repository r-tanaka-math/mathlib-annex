"""Bounded failure diagnostics. Not a build/axiom/qualification verifier.

Integration helper only: never launches Lean, restores objects, or operates GitHub.
All paths are supplied by the worker. Source evidence is read-only.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

LIMIT = 120 * 1024

def snapshot(path: Path, label: str, keep: int = 5000) -> dict:
    if path.is_symlink() or not path.is_file():
        return {"path": label, "status": "MISSING_OR_LINK"}
    digest = hashlib.sha256()
    tail = b""
    count = 0
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(65536), b""):
            digest.update(block)
            count += len(block)
            tail = (tail + block)[-keep:]
    return {"path": label, "full_bytes": count, "sha256": digest.hexdigest(),
            "tail": tail.decode("utf-8", errors="replace"), "truncated": count > keep}

def small_json(path: Path, limit: int = 8 * 1024 * 1024):
    if path.is_symlink() or not path.is_file() or path.stat().st_size > limit:
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, OSError, UnicodeError):
        return None

def bounded_value(value, keep: int = 2048):
    """Bound a diagnostic value, not the source evidence; bind omitted text by hash."""
    if value is None or isinstance(value, (bool, int, float)):
        return value, None
    text = value if isinstance(value, str) else json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    raw = text.encode("utf-8", errors="replace")
    if len(raw) <= keep:
        return value, None
    return raw[-keep:].decode("utf-8", errors="ignore"), {
        "full_utf8_bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
        "truncated": True, "representation": "UTF8_TEXT" if isinstance(value, str) else "CANONICAL_JSON"}


def fit_budget(result: dict) -> dict:
    """JSON escaping can expand tails. Trim excerpts only, retaining full-file hashes."""
    result["diagnostic_tail_reductions"] = 0
    while max(len(json.dumps(result, ensure_ascii=ascii_mode, separators=(",", ":")).encode()) + 1
              for ascii_mode in (False, True)) > LIMIT:
        excerpts = [r for r in result["records"] if isinstance(r.get("tail"), str) and r["tail"]]
        if not excerpts:
            raise ValueError("Diagnostic metadata exceeds reserved budget; full evidence remains intact")
        record = max(excerpts, key=lambda r: len(r["tail"].encode("utf-8")))
        raw = record["tail"].encode("utf-8")
        keep = len(raw) // 2
        record["tail"] = raw[-keep:].decode("utf-8", errors="ignore") if keep else ""
        record["truncated"] = True
        result["diagnostic_tail_reductions"] += 1
    return result


def collect(evidence: Path, payload: Path) -> dict:
    for folder in (evidence, payload):
        if folder.is_symlink():
            raise ValueError("Linked evidence directory is not supported")
    records = []
    for name in ("identity-before-setup.json", "resource-blocked.json",
                 "resource-admissions.jsonl", "capacity.jsonl",
                 "actual-step-outcomes.json", "scope-native-import.json", "cache-get.json"):
        records.append(snapshot(evidence / name, name))
    stage_path = payload / "stage.json"
    stage = small_json(stage_path)
    stage_record = snapshot(stage_path, "payload/stage.json", 2000)
    if isinstance(stage, dict):
        stage_record["summary"] = {}
        stage_record["summary_value_bindings"] = {}
        for key in ("stage", "status", "failure", "failure_kind"):
            value, binding = bounded_value(stage.get(key))
            stage_record["summary"][key] = value
            if binding is not None:
                stage_record["summary_value_bindings"][key] = binding
        resource = stage.get("resource_failure")
        if isinstance(resource, dict):
            stage_record["resource_summary"] = {}
            for key in ("status", "reason", "target"):
                value, binding = bounded_value(resource.get(key))
                stage_record["resource_summary"][key] = value
                if binding is not None:
                    stage_record["summary_value_bindings"]["resource." + key] = binding
        mods = stage.get("modules", {})
        if isinstance(mods, dict):
            stage_record["recorded_module_count"] = len(mods)
            stage_record["recorded_names_sha256"] = hashlib.sha256(
                json.dumps(sorted(mods), separators=(",", ":")).encode()).hexdigest()
    records.append(stage_record)
    # Successful process exits are NOT converted to qualified results by this helper.
    failed = []
    for p in evidence.glob("*.command.json"):
        value = small_json(p)
        if isinstance(value, dict) and (value.get("exit_code") not in (0, None)
                                      or value.get("stop_reason")):
            failed.append((p.stat().st_mtime_ns, p.name, p, value))
    for _, name, path, command in sorted(failed, reverse=True)[:2]:
        records.append(snapshot(path, name, 12000))
        value = command.get("log")
        # Never follow an absolute path, traversal, or alternate-directory command locator.
        if isinstance(value, str) and value and Path(value).name == value and "\\" not in value:
            records.append(snapshot(evidence / value, value, 12000))
        else:
            records.append({"path": name + ":log", "status": "UNSAFE_OR_MISSING_LOCATOR"})
    result = {"status": "OBSERVATION_NOT_QUALIFICATION", "records": records,
              "failed_command_receipts_found": len(failed),
              "omitted_failed_command_receipts": max(0, len(failed)-2),
              "full_logs_preservation_required": True}
    # In particular ResourceBlocked may embed every resource sample in failure.
    # Neither that unbounded string nor escaped log tails may prevent a diagnosis.
    return fit_budget(result)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--payload", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    if args.out.exists() or args.out.is_symlink():
        raise ValueError("Refuse to overwrite existing diagnostics")
    result = collect(args.evidence, args.payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("x", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, separators=(",", ":"))
        f.write("\n")

if __name__ == "__main__":
    main()
