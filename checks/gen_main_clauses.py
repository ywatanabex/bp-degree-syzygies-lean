#!/usr/bin/env python3
"""Insert the Lean output of MainClauses.lean into MAIN_CLAUSES.md.

Usage: python3 -I checks/gen_main_clauses.py PACKAGE_ROOT OUTPUT_DIR (run after `lake build`)

Runs `lake env lean MainClauses.lean` (plain, saved to OUTPUT_DIR/main_clauses.out) and
`lake env lean --json MainClauses.lean`, maps every message to the command on its line, and
replaces the fenced block that follows each marker in MAIN_CLAUSES.md:

  <!-- lean-check: NAME ... -->    output of `#check @NAME`
  <!-- lean-axioms: NAME ... -->   output of `#print axioms NAME` (whitespace collapsed)
  <!-- lean-print: NAME ... -->    output of `#print NAME`
  <!-- lean-example: KEY -->       source of the `example` after `-- restate: KEY`
  <!-- lean-summary: -->           summary of the run

It fails if Lean reports an error or warning, if a command has no or several messages, or if
the markers and the commands of MainClauses.lean do not correspond one to one.
"""
import json
import os
import re
import subprocess
import sys

STANDARD = "depends on axioms: [propext, Classical.choice, Quot.sound]"


def die(msg):
    sys.exit("gen_main_clauses: " + msg)


def run(pkg, args):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    return subprocess.run(args, cwd=pkg, env=env, capture_output=True, text=True)


def parse_lean(path):
    commands = {}  # line -> (kind, name)
    examples = {}  # key -> (first line, last line, text)
    lines = open(path, encoding="utf-8").read().split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        n = i + 1
        m = re.fullmatch(r"#check @(\S+)", line)
        if m:
            commands[n] = ("check", m.group(1))
        m = re.fullmatch(r"#print axioms (\S+)", line)
        if m:
            commands[n] = ("axioms", m.group(1))
        m = re.fullmatch(r"#print (?!axioms )(\S+)", line)
        if m:
            commands[n] = ("print", m.group(1))
        m = re.fullmatch(r"-- restate: (\S+)", line)
        if m:
            j = i + 1
            body = []
            while j < len(lines) and lines[j].strip() != "":
                body.append(lines[j])
                j += 1
            if not body or not re.match(r"(noncomputable )?example ", body[0]):
                die("no example after line %d" % n)
            examples[m.group(1)] = (i + 2, j, "\n".join(body))
            i = j
            continue
        i += 1
    return commands, examples


def main():
    if len(sys.argv) != 3:
        die("usage: gen_main_clauses.py PACKAGE_ROOT OUTPUT_DIR")
    pkg, out_dir = sys.argv[1], sys.argv[2]
    lean_path = os.path.join(pkg, "MainClauses.lean")
    md_path = os.path.join(pkg, "MAIN_CLAUSES.md")

    plain = run(pkg, ["lake", "env", "lean", "MainClauses.lean"])
    with open(os.path.join(out_dir, "main_clauses.out"), "w", encoding="utf-8") as f:
        f.write(plain.stdout + plain.stderr)
    with open(os.path.join(out_dir, "main_clauses.exit"), "w") as f:
        f.write("%d\n" % plain.returncode)
    js = run(pkg, ["lake", "env", "lean", "--json", "MainClauses.lean"])
    if plain.returncode != 0 or js.returncode != 0 or js.stderr.strip():
        die("lean failed (exit %d / %d): %s" % (plain.returncode, js.returncode, js.stderr))

    commands, examples = parse_lean(lean_path)
    messages = [json.loads(l) for l in js.stdout.splitlines() if l.strip()]
    by_line = {}
    for msg in messages:
        if msg["severity"] != "information":
            die("%s at line %d: %s" % (msg["severity"], msg["pos"]["line"], msg["data"]))
        line = msg["pos"]["line"]
        if line not in commands:
            die("message at line %d without a command: %s" % (line, msg["data"][:200]))
        if line in by_line:
            die("several messages at line %d" % line)
        by_line[line] = msg["data"].rstrip("\n")
    for line, (kind, name) in commands.items():
        if line not in by_line:
            die("no output for %s %s (line %d)" % (kind, name, line))
    for key, (first, last, _) in examples.items():
        if any(first <= l <= last for l in by_line):
            die("message inside example %s" % key)

    out = {"check": {}, "axioms": {}, "print": {}}
    nonstandard = []
    for line, (kind, name) in sorted(commands.items()):
        text = by_line[line]
        if name in out[kind]:
            die("duplicate %s %s" % (kind, name))
        # Lean omits the `@` when the declaration has no implicit or instance arguments.
        prefixes = ("@" + name + " :", name + " :")
        if kind == "check" and not text.startswith(prefixes):
            die("unexpected #check output for %s" % name)
        if kind == "axioms":
            text = " ".join(text.split())
            if not text.startswith("'%s' " % name):
                die("unexpected axioms output for %s" % name)
            if text != "'%s' %s" % (name, STANDARD):
                nonstandard.append(text)
        out[kind][name] = text

    n_check, n_ax, n_print = len(out["check"]), len(out["axioms"]), len(out["print"])
    summary = "\n".join([
        "lake env lean MainClauses.lean: exit code %d, %d messages, no errors or warnings"
        % (plain.returncode, len(messages)),
        "#check: %d declarations; #print axioms: %d declarations; #print: %d definitions; "
        "restated examples: %d (checked, no messages)" % (n_check, n_ax, n_print, len(examples)),
        "#print axioms lines equal to [propext, Classical.choice, Quot.sound]: %d of %d"
        % (n_ax - len(nonstandard), n_ax),
    ] + ["NONSTANDARD: " + t for t in nonstandard])

    md = open(md_path, encoding="utf-8").read().split("\n")
    used = {"check": [], "axioms": [], "print": [], "example": []}
    result = []
    i = 0
    while i < len(md):
        line = md[i]
        result.append(line)
        m = re.fullmatch(r"<!-- lean-(check|axioms|print|example|summary):(.*?)-->", line.strip())
        if not m:
            i += 1
            continue
        kind, names = m.group(1), m.group(2).split()
        if i + 1 >= len(md) or not md[i + 1].startswith("```"):
            die("marker without a fenced block at line %d" % (i + 1))
        result.append(md[i + 1])
        j = i + 2
        while j < len(md) and md[j] != "```":
            j += 1
        if j >= len(md):
            die("unclosed block after line %d" % (i + 1))
        if kind == "summary":
            content = summary
        elif kind == "example":
            for key in names:
                if key not in examples:
                    die("unknown example %s" % key)
            content = "\n\n".join(examples[k][2] for k in names)
        else:
            for name in names:
                if name not in out[kind]:
                    die("no %s output for %s" % (kind, name))
            sep = "\n" if kind == "axioms" else "\n\n"
            content = sep.join(out[kind][n] for n in names)
        if kind != "summary":
            used[kind].extend(names)
        result.extend(content.split("\n"))
        result.append("```")
        i = j + 1

    for kind in ("check", "axioms", "print"):
        if sorted(used[kind]) != sorted(out[kind]):
            missing = set(out[kind]) - set(used[kind])
            extra = [n for n in used[kind] if used[kind].count(n) > 1]
            die("%s markers do not match the Lean file: missing %s, repeated %s"
                % (kind, sorted(missing), sorted(set(extra))))
    if sorted(used["example"]) != sorted(examples):
        die("example markers do not match the Lean file")

    with open(md_path, "w", encoding="utf-8") as f:
        f.write("\n".join(result))
    print(summary)


if __name__ == "__main__":
    main()
