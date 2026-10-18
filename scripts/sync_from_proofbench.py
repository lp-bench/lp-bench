#!/usr/bin/env python3
"""Regenerate this repository from a commit of the private ProofBench repository.

usage: scripts/sync_from_proofbench.py /path/to/ProofBench [--rev HEAD] [--build]

Only test-taker material is copied: the Lean project files, the statement-layer
library `ProofBench/Mathlib_Problems`, and per problem `Pxxx.lean` and (for open
problems) `Pxxx_DISPROVE.lean`.  Bounds, solutions, the proctor library
`ProofBench/Mathlib`, source papers and the full database stay behind.

A copied file may import only Mathlib, Matroid, `Archive.Sensitivity`, copied
`ProofBench.Mathlib_Problems.*` modules and other statement files.  A library
file that imports anything else is skipped and reported; a statement file that
does is an error.  `ProofBench/DATABASE/Database.json` keeps statement fields
only, and `SOURCE_COMMIT` records the exported commit.  `--build` compiles
every copied module with `lake build`.
"""

import argparse
import io
import json
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
PROJECT_FILES = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "ProofBench.lean"]
STATEMENT_FILE = re.compile(r"ProofBench/PROBLEMS/(P\d{3})/\1(_DISPROVE)?\.lean$")
EXTERNAL = re.compile(r"(Mathlib|Matroid)(\..+)?$|Archive\.Sensitivity$")
IMPORT = re.compile(r"^(?:public\s+)?import\s+(\S+)", re.M)
DB_FIELDS = ["id", "name", "difficulty", "msc", "informal_statement",
             "informal_statement_summary", "formal_statement"]
MANAGED = ["ProofBench", "SOURCE_COMMIT", *PROJECT_FILES]


def git(pb: Path, *args: str) -> bytes:
    return subprocess.run(["git", "-C", str(pb), *args], check=True, capture_output=True).stdout


def module(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("proofbench")
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--build", action="store_true")
    a = ap.parse_args()
    pb = Path(a.proofbench).resolve()
    commit = git(pb, "rev-parse", a.rev).decode().strip()
    paths = ["ProofBench/Mathlib_Problems", "ProofBench/PROBLEMS", "ProofBench/DATABASE/Database.json", *PROJECT_FILES]
    dirty = [l for l in git(pb, "status", "--porcelain", "--", *paths).decode().splitlines()
             if STATEMENT_FILE.search(l) or "Mathlib_Problems/" in l or not l.endswith(".lean")]

    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp)
        tarfile.open(fileobj=io.BytesIO(git(pb, "archive", commit, *paths))).extractall(src, filter="data")
        lean = {p.relative_to(src).as_posix(): p.read_text(encoding="utf-8") for p in src.rglob("*.lean")}
        statements = {p for p in lean if STATEMENT_FILE.match(p)}
        library = {p for p in lean if p.startswith("ProofBench/Mathlib_Problems/")}
        imports = {p: IMPORT.findall(t) for p, t in lean.items() if p in statements | library}

        # Drop library files whose imports leave the allowed set, until stable.
        visible = {module(p) for p in statements | library}
        skipped: dict[str, str] = {}
        changed = True
        while changed:
            changed = False
            for p in sorted(library - skipped.keys()):
                bad = [m for m in imports[p] if not (EXTERNAL.match(m) or m in visible)]
                if bad:
                    skipped[p] = bad[0]
                    visible.discard(module(p))
                    changed = True
        errors = [f"{p}: imports {m}" for p in sorted(statements) for m in imports[p]
                  if not (EXTERNAL.match(m) or m in visible)]
        if errors:
            sys.exit("statement files import non-statement material:\n  " + "\n  ".join(errors))

        for name in MANAGED:
            target = HERE / name
            if target.is_dir():
                shutil.rmtree(target)
            elif target.exists():
                target.unlink()
        for p in sorted(statements | (library - skipped.keys())):
            (HERE / p).parent.mkdir(parents=True, exist_ok=True)
            (HERE / p).write_text(lean[p], encoding="utf-8")
        for name in PROJECT_FILES:
            shutil.copyfile(src / name, HERE / name)
        db = json.loads((src / "ProofBench/DATABASE/Database.json").read_text(encoding="utf-8"))
        out = HERE / "ProofBench/DATABASE/Database.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps([{k: e.get(k, "") for k in DB_FIELDS} for e in db], indent=1, ensure_ascii=False) + "\n",
                       encoding="utf-8")
    (HERE / "SOURCE_COMMIT").write_text(commit + "\n")

    n_dis = sum(1 for p in statements if p.endswith("_DISPROVE.lean"))
    print(f"exported ProofBench {commit[:10]}: {len(statements) - n_dis} statements, {n_dis} DISPROVE, "
          f"{len(library) - len(skipped)} library files, {len(db)} database entries")
    for p, m in sorted(skipped.items()):
        print(f"skipped library file {p} (imports {m})")
    if dirty:
        print("uncommitted ProofBench changes NOT exported (commit them first):\n  " + "\n  ".join(dirty))
    if a.build:
        mods = sorted(module(p) for p in statements | (library - skipped.keys()))
        subprocess.run(["lake", "exe", "cache", "get"], cwd=HERE, check=True)
        subprocess.run(["lake", "build", *mods], cwd=HERE, check=True)


if __name__ == "__main__":
    main()
