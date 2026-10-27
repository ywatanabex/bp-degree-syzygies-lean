#!/usr/bin/env python3
"""Clean-build and audit this standalone Lean package.

Requires Python 3.9 or later and the pinned Lean toolchain through elan
(`lake` on PATH). Every input is resolved inside this repository: no sibling
checkout, no paper source and no Git commit is needed. Obtaining the pinned
dependency cache (`lake exe cache get`) needs network access unless the
dependencies are already present under `.lake/packages`.

Steps:
  1. preflight: public source inventory, no external research paths, every
     project import resolves to a file, no local path dependency, every
     dependency revision is a full commit hash;
  2. source audit: no `sorry`, no `axiom` declaration and no `native_decide`
     outside comments in the project sources;
  3. optional clean (`--clean` removes `.lake/build` of this package only);
  4. `lake build` of the default targets (`BPFixedPoints` and `PaperAudit`);
  5. `lake env lean PaperAudit.lean`, which re-runs the axiom audit of every
     declaration in the `BPFixedPoints` namespace and must print
     `Axiom audit PASS`;
  6. the source inventory and every file digest are taken before step 3 and
     again after step 5; the run fails if they differ, so the receipt
     describes exactly the sources that were built and audited.
A receipt with the toolchain, the dependency revisions, the Git commit at the
start and the end, the Git working-tree state of the package (modified and
untracked paths), the digests of the sources and the audit line is written to
the ignored `validation/` directory.

Scope of `--clean`: it removes `.lake/build` of this package only, so every
module of `BPFixedPoints` and `PaperAudit` is rebuilt; Mathlib and the other
dependencies are taken from `.lake/packages` (their pinned builds or the
cache) and are not rebuilt from source. `--skip-cache` only skips the cache
download; it does not make the build clean.
"""
import argparse
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB = "BPFixedPoints"
AUDIT = "PaperAudit"
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
VALIDATION = ROOT / "validation"


def project_files():
    """The public source inventory, excluding downloads and generated output."""
    files = list(ROOT.glob("*.lean"))
    files += list((ROOT / LIB).rglob("*.lean"))
    files += list((ROOT / "checks").glob("*.py"))
    files += list(ROOT.glob("*.md"))
    files += [p for p in (ROOT / "third_party").rglob("*") if p.is_file()]
    files += [ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "MANUSCRIPT.json", "LICENSE", "LICENSE-APACHE-2.0", ".gitignore", ".gitattributes")]
    files += list((ROOT / ".github" / "workflows").glob("*.yml"))
    return sorted(set(files))


def lean_sources():
    return sorted([ROOT / f"{LIB}.lean", ROOT / f"{AUDIT}.lean"] + list((ROOT / LIB).rglob("*.lean")))


def preflight(files):
    for path in files:
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"Public source is not a regular file: {path.relative_to(ROOT)}")
        data = path.read_text(encoding="utf-8")
        if not data.endswith("\n"):
            raise RuntimeError(f"Missing final newline: {path.relative_to(ROOT)}")
        if re.search(r"[ \t]+$", data, re.MULTILINE):
            raise RuntimeError(f"Trailing whitespace: {path.relative_to(ROOT)}")
        if re.search(r"/(?:Users|home)/[A-Za-z]", data):
            raise RuntimeError(f"External research path: {path.relative_to(ROOT)}")
    for path in lean_sources():
        for imported in re.findall(r"^import\s+([\w.]+)", path.read_text(encoding="utf-8"), re.MULTILINE):
            if imported.split(".")[0] in {LIB, AUDIT}:
                local = ROOT / (imported.replace(".", "/") + ".lean")
                if not local.is_file():
                    raise RuntimeError(f"Missing project module {imported} (imported by {path.relative_to(ROOT)})")
    config = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    if re.search(r"^\s*path\s*=", config, re.MULTILINE):
        raise RuntimeError("Lake configuration must not use a local path dependency")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            raise RuntimeError(f"Dependency {package['name']} is not pinned to a git commit")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if not re.fullmatch(r"leanprover/lean4:v[0-9][\w.\-]*", toolchain):
        raise RuntimeError(f"Unexpected toolchain specification: {toolchain}")
    return manifest, toolchain


def strip_comments(text):
    """Remove nested block comments and line comments from Lean source text."""
    out = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def source_audit():
    for path in lean_sources():
        code = strip_comments(path.read_text(encoding="utf-8"))
        rel = path.relative_to(ROOT)
        if re.search(r"\bsorry\b", code):
            raise RuntimeError(f"`sorry` outside comments in {rel}")
        if re.search(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*axiom\s", code, re.MULTILINE):
            raise RuntimeError(f"axiom declaration in {rel}")
        if re.search(r"\bnative_decide\b", code):
            raise RuntimeError(f"`native_decide` in {rel}")


def run(cmd, log_path, timeout=None):
    VALIDATION.mkdir(exist_ok=True)
    started = time.time()
    with open(log_path, "w", encoding="utf-8") as log:
        log.write("$ " + " ".join(cmd) + "\n")
        log.flush()
        proc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, text=True, timeout=timeout)
    return proc.returncode, time.time() - started


def digest(files):
    h = hashlib.sha256()
    per_file = {}
    for path in files:
        data = path.read_bytes()
        d = hashlib.sha256(data).hexdigest()
        per_file[str(path.relative_to(ROOT))] = d
        h.update(str(path.relative_to(ROOT)).encode() + b"\0" + data + b"\0")
    return h.hexdigest(), per_file


def git_head():
    try:
        out = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True)
        return out.stdout.strip() if out.returncode == 0 else None
    except OSError:
        return None


def git_status():
    """Modified and untracked paths of this package, relative to the package root."""
    try:
        out = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all", "--", "."],
                             cwd=ROOT, capture_output=True, text=True)
    except OSError:
        return None
    if out.returncode != 0:
        return None
    return [line for line in out.stdout.splitlines() if line.strip()]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--clean", action="store_true", help="remove .lake/build of this package before building")
    parser.add_argument("--skip-cache", action="store_true", help="do not run `lake exe cache get` even if the Mathlib build is absent")
    args = parser.parse_args()

    files = project_files()
    manifest, toolchain = preflight(files)
    source_audit()
    print(f"preflight OK: {len(files)} public files, {len(lean_sources())} Lean sources, toolchain {toolchain}")
    head_at_start = git_head()
    combined_at_start, per_file_at_start = digest(files)

    if args.clean:
        shutil.rmtree(ROOT / ".lake" / "build", ignore_errors=True)
        print("removed .lake/build")

    mathlib_built = (ROOT / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib").exists()
    if not mathlib_built and not args.skip_cache:
        code, seconds = run(["lake", "exe", "cache", "get"], VALIDATION / "cache.log")
        if code != 0:
            raise RuntimeError("`lake exe cache get` failed; see validation/cache.log")
        print(f"dependency cache obtained in {seconds:.0f}s")

    code, build_seconds = run(["lake", "build"], VALIDATION / "build.log")
    if code != 0:
        raise RuntimeError("`lake build` failed; see validation/build.log")
    print(f"lake build OK in {build_seconds:.0f}s")

    code, audit_seconds = run(["lake", "env", "lean", f"{AUDIT}.lean"], VALIDATION / "audit.log")
    audit_log = (VALIDATION / "audit.log").read_text(encoding="utf-8")
    passed = [line for line in audit_log.splitlines() if "Axiom audit PASS" in line]
    if code != 0 or not passed:
        raise RuntimeError("axiom audit failed; see validation/audit.log")
    audit_line = passed[0].split("info:", 1)[-1].strip() if "info:" in passed[0] else passed[0].strip()
    # Every `#print axioms` line of the audit must list only the allowed axioms.
    for line in audit_log.splitlines():
        m = re.search(r"depends on axioms: \[(.*)\]", line)
        if m:
            used = [a.strip() for a in m.group(1).split(",") if a.strip()]
            extra = [a for a in used if a not in ALLOWED_AXIOMS]
            if extra:
                raise RuntimeError(f"unexpected axioms in `#print axioms` output: {extra}")
    print(audit_line)

    files_at_end = project_files()
    if files_at_end != files:
        added = sorted(str(p.relative_to(ROOT)) for p in set(files_at_end) - set(files))
        removed = sorted(str(p.relative_to(ROOT)) for p in set(files) - set(files_at_end))
        raise RuntimeError(f"source inventory changed during validation: added {added}, removed {removed}")
    combined, per_file = digest(files)
    if combined != combined_at_start:
        changed = sorted(k for k in per_file if per_file[k] != per_file_at_start.get(k))
        raise RuntimeError(f"sources changed during validation: {changed}")
    head_at_end = git_head()
    if head_at_end != head_at_start:
        raise RuntimeError(f"Git HEAD changed during validation: {head_at_start} -> {head_at_end}")
    receipt = {
        "validated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "git_head": head_at_start,
        "git_status": git_status(),
        "sources_unchanged_during_run": True,
        "toolchain": toolchain,
        "dependencies": {p["name"]: p["rev"] for p in manifest["packages"]},
        "clean_build": args.clean,
        "build_seconds": round(build_seconds),
        "audit_seconds": round(audit_seconds),
        "audit": audit_line,
        "allowed_axioms": ALLOWED_AXIOMS,
        "lean_source_count": len(lean_sources()),
        "sources_sha256": combined,
        "files_sha256": per_file,
    }
    VALIDATION.mkdir(exist_ok=True)
    (VALIDATION / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"receipt written to {VALIDATION / 'receipt.json'}")


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"validation FAILED: {error}", file=sys.stderr)
        sys.exit(1)
