#!/usr/bin/env python3
"""Rebuild, kernel-check exported proofs, and audit reported axiom dependencies."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def main():
    started = time.monotonic()
    files = sorted(ROOT.glob("RichWords/*.lean")) + [ROOT / "RichWords.lean"]
    source_hashes = {}
    for path in files:
        text = path.read_text()
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", text):
            raise SystemExit("Disallowed proof mechanism in " + str(path))
        source_hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    commands = [["nice", "-n", "10", "lake", "build"]]
    commands += [
        ["nice", "-n", "10", "lake", "env", "lean", str(path.relative_to(ROOT))]
        for path in files if "#print axioms " in path.read_text()
    ]
    logs = []
    audit_outputs = []
    for command in commands:
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=600)
        logs.append("$ " + " ".join(command) + "\n" + result.stdout)
        if result.returncode:
            (ROOT / "verification.log").write_text("\n".join(logs))
            raise SystemExit(result.returncode)
        if command[3:6] == ["lake", "env", "lean"]:
            audit_outputs.append(result.stdout)
    output = "\n".join(audit_outputs)
    records = {}
    for line in output.splitlines():
        match = re.search(r"'(RichWords\.[^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", line)
        if not match:
            continue
        axioms = [a.strip() for a in (match.group(2) or "").split(",") if a.strip()]
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise SystemExit("Unexpected axioms: " + repr(unexpected))
        records[match.group(1)] = axioms
    all_proof_source = "\n".join(p.read_text() for p in files)
    declared = re.findall(r"^theorem (\w+)", all_proof_source, re.M)
    if set(records) != {"RichWords." + name for name in declared}:
        raise SystemExit("A declared theorem was not audited")
    exports = re.findall(r"^#print axioms (RichWords\.\w+)", all_proof_source, re.M)
    if set(records) != set(exports) or not exports:
        raise SystemExit("Missing axiom-audit output")
    report = {
        "status": "passed", "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "source_sha256": source_hashes, "axioms": records,
        "configuration_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify.py")
        },
        "dependency_revisions": {
            package["name"]: package["rev"]
            for package in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
        },
        "scope": "Lean definitions and theorems only; does not certify correspondence with every line of the paper or novelty",
    }
    (ROOT / "verification.log").write_text("\n".join(logs))
    (ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "audited_theorems": len(records),
                      "elapsed_seconds": report["elapsed_seconds"]}))

if __name__ == "__main__":
    main()
