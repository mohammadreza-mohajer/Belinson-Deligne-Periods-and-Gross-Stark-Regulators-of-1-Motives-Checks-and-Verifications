"""Rebuild every companion proof in a fresh module search path and compare the exact reports."""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from arithmetic import calculate
from correspondence import verify_ledger

ROOT = Path(__file__).resolve().parents[1]
BASE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULE_RE = re.compile(r"^import (BD(?:\.\w+)?)$", re.M)
DECL_RE = re.compile(r"^(theorem|lemma)\s+([\w']+)\b", re.M)


def checked(args, env, cwd=ROOT):
    p = subprocess.run([str(x) for x in args], cwd=cwd, env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
    if p.returncode:
        raise RuntimeError(f"Command failed ({p.returncode})\n{p.stdout}")
    return p.stdout.replace("\r\n", "\n")


def text_file(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def json_text(obj):
    return json.dumps(obj, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def toolchain(args):
    env = os.environ.copy()
    if args.mathlib is not None:
        if not args.lean:
            raise ValueError("--mathlib requires --lean pointing to the pinned compiler")
        mathlib = args.mathlib.resolve()
        p = json.loads((mathlib/"lake-manifest.json").read_text(encoding="utf-8"))
        pin = json.loads((ROOT/"lake-manifest.json").read_text(encoding="utf-8"))
        expected = {x["name"]:x["rev"] for x in pin["packages"] if x["name"]!="mathlib"}
        if {x["name"]:x["rev"] for x in p["packages"]} != expected:
            raise ValueError("dependency checkout has different transitive revision pins")
        if (mathlib/"lean-toolchain").read_text().strip() != (ROOT/"lean-toolchain").read_text().strip():
            raise ValueError("unexpected mathlib toolchain")
        if (mathlib/".git").exists():
            rev = checked(["git","rev-parse","HEAD"],env,cwd=mathlib).strip()
            if rev != next(x["rev"] for x in pin["packages"] if x["name"]=="mathlib"):
                raise ValueError("mathlib checkout is at a different revision")
        dirs = [mathlib] + [mathlib/".lake/packages"/x["name"] for x in p["packages"]]
        env["LEAN_PATH"] = os.pathsep.join(str(t/".lake/build/lib/lean") for t in dirs)
        lean = str(args.lean.resolve())
    else:
        exe = shutil.which("lake")
        if not exe:
            raise RuntimeError("Lake was not found. See the README for the pinned toolchain.")
        code = 'import os,json,shutil;print(json.dumps([os.environ["LEAN_PATH"],shutil.which("lean")]))'
        data = checked([exe, "env", sys.executable, "-c", code],env).strip().splitlines()[-1]
        env["LEAN_PATH"], lean = json.loads(data)
    raw = checked([lean,"--version"],env).strip()
    if not re.search(r"version 4\.19\.0[, )]",raw):
        raise ValueError(f"wrong Lean release: {raw}")
    return lean, env, raw


def sources():
    files = sorted((ROOT/"BD").glob("*.lean")) + [ROOT/"BD.lean"]
    texts = {str(f.relative_to(ROOT).with_suffix("")).replace(os.sep,"."):
             f.read_text(encoding="utf-8") for f in files}
    if set(MODULE_RE.findall(texts["BD"])) != set(texts) - {"BD"}:
        raise ValueError("BD.lean import list differs from module inventory")
    decls = {}
    for mod, src in texts.items():
        if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|Lean\.(ofReduceBool|trustCompiler)",src):
            raise ValueError(f"unreviewed proof escape in {mod}")
        if mod != "BD":
            ns = set(re.findall(r"^namespace\s+([\w.]+)",src,re.M))
            if len(ns)!=1:
                raise ValueError(f"ambiguous namespace in {mod}")
            for match in DECL_RE.finditer(src):
                line = src.count("\n",0,match.start()) + 1
                name = next(iter(ns))+"."+match[2]
                if name in decls:
                    raise ValueError(f"duplicate theorem {name}")
                decls[name] = (mod,line)
    return texts, decls


def audit_output(raw, decls):
    matches = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",raw)
    found = {n:sorted(s.strip() for s in deps.split(",") if s.strip()) for n,deps in matches}
    if len(matches)!=len(decls) or set(found)!=set(decls):
        raise ValueError("kernel axiom audit is missing declarations or contains duplicates")
    for n, used in found.items():
        if set(used) - BASE_AXIOMS:
            raise ValueError(f"{n} uses unexpected axioms {used}")
    return found


def negative_controls(lean, env, tree):
    cases = json.loads((ROOT/"inputs/negative-controls.json").read_text(encoding="utf-8"))
    # Each example must fail at the designated arithmetic assertion, never at import.
    src = tree/"NegativeControls.lean"
    prefix = ["import BD.Arithmetic","set_option maxRecDepth 20000","set_option maxHeartbeats 4000000"]
    text_file(src,"\n".join(prefix + ["example : "+c["proposition"]+" := by decide" for c in cases])+"\n")
    process = subprocess.run([lean,"-j","1",str(src)],cwd=ROOT,env=env,stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT,encoding="utf-8",errors="replace")
    errs = re.findall(r"NegativeControls\.lean:(\d+):\d+: error: ([\s\S]*?)(?=(?:[^\n]*NegativeControls\.lean:\d+:\d+: error:)|\Z)",
                      process.stdout)
    expected_lines = set(range(len(prefix)+1,len(prefix)+len(cases)+1))
    if process.returncode==0 or {int(n) for n,_ in errs}!=expected_lines or len(errs)!=len(cases):
        raise ValueError("negative controls did not fail at the expected source lines: "+process.stdout)
    for _,msg in errs:
        if "decide" not in msg or not ("is false" in msg or "isFalse" in msg):
            raise ValueError("unexpected reason for arithmetic rejection: "+msg)
    return [{"id":c["id"],"statement":c["proposition"],"outcome":"rejected as false"} for c in cases]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean",type=Path)
    p.add_argument("--mathlib",type=Path,help="use an already built, pinned dependency snapshot")
    p.add_argument("--output",type=Path,default=ROOT/"build/verification")
    p.add_argument("--jobs",type=int,default=2,choices=range(1,17),metavar="1..16")
    p.add_argument("--record",action="store_true",help="write the release reference reports")
    args = p.parse_args()
    lean, env, version = toolchain(args)
    texts, decls = sources()
    rows, equations = verify_ledger(ROOT, decls)
    print(version,flush=True)
    build = []
    with tempfile.TemporaryDirectory(prefix="bd-lean-") as temp:
        tree = Path(temp)
        (tree/"BD").mkdir()
        # Prepending a fresh BD directory prevents reuse of any project .olean.
        env["LEAN_PATH"] = str(tree)+os.pathsep+env["LEAN_PATH"]
        finished = set()

        def compile_one(mod):
            path = Path(*mod.split("."))
            result = checked([lean,"-j","1","-DwarningAsError=true","-o",tree/path.with_suffix(".olean"),
                              path.with_suffix(".lean")],env)
            if result.strip():
                raise ValueError(f"unexpected compiler diagnostics in {mod}: {result}")
            return mod

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while len(finished)!=len(texts):
                ready = sorted(mod for mod,src in texts.items() if mod not in finished
                               and set(MODULE_RE.findall(src))<=finished)
                if not ready:
                    raise ValueError("cyclic project dependencies")
                for mod in pool.map(compile_one,ready):
                    finished.add(mod)
                    build.append(f"PASS {mod}")
                    print(build[-1],flush=True)
        audit = tree/"AxiomReport.lean"
        text_file(audit,"import BD\n"+"\n".join("#print axioms "+n for n in sorted(decls))+"\n")
        raw = checked([lean,"-j","1","-DwarningAsError=true",audit],env)
        axioms = audit_output(raw,decls)
        signatures = tree/"PublicTypes.lean"
        text_file(signatures,"import BD\n" +
                  "\n".join("#check @"+n for n in sorted(decls))+"\n")
        formal_types = checked([lean,"-j","1","-DwarningAsError=true",signatures],env)
        named_types = re.findall(r"^@?(BD\.[\w.']+) :",formal_types,re.M)
        if len(named_types) != len(decls) or set(named_types) != set(decls):
            raise ValueError("incomplete public theorem signature report")
        calc_raw = checked([lean,"-j","1","--run","scripts/Compute.lean"],env)
        rejected = negative_controls(lean,env,tree)
    pairs = [line.split("=",1) for line in calc_raw.splitlines() if line]
    observed = dict(pairs)
    if len(observed)!=len(pairs):
        raise ValueError("duplicate arithmetic output key")
    expected = calculate(json.loads((ROOT/"inputs/arithmetic.json").read_text()))
    if observed != expected:
        raise ValueError(f"Lean/Python difference: {[(k,observed.get(k),expected.get(k)) for k in sorted(set(observed)|set(expected)) if observed.get(k)!=expected.get(k)]}")
    reports = {
        "kernel-build.txt":"\n".join(build)+"\n",
        "axioms.txt":raw.rstrip()+"\n",
        "axioms.json":json_text(axioms),
        "theorem-types.txt":formal_types.rstrip()+"\n",
        "negative-controls.json":json_text(rejected),
        "lean-calculations.txt":calc_raw.rstrip()+"\n",
        "arithmetic.json":json_text(observed),
        "verification.json":json_text({"lean":"4.19.0","modules":len(texts)-1,
            "public_theorems":len(decls),"numbered_items":rows,"labelled_equations":equations,
            "arithmetic_fields":len(observed),"negative_controls":len(rejected),"observed_kernel_axioms":sorted(set().union(*map(set,axioms.values()))),
            "mathlib_commit":"c44e0c8ee63ca166450922a373c7409c5d26b00b",
            "paper_sha256":hashlib.sha256((ROOT/"paper/manuscript.tex").read_bytes()).hexdigest(),
            "recompiled_all_project_modules":True,"python_agrees_with_lean":True})
    }
    for name, contents in reports.items():
        text_file(args.output/name,contents)
        ref=ROOT/"results"/name
        if args.record:
            text_file(ref,contents)
        elif ref.read_text(encoding="utf-8") != contents:
            raise ValueError(f"Release reference mismatch in {name}")
    text_file(args.output/"environment.txt",version+"\n")
    if args.record:
        text_file(ROOT/"results/recorded-environment.txt",version+"\n")
    print(f"PASS {len(decls)} public theorems; {len(observed)} arithmetic fields; {rows} numbered items; {equations} labelled equations.",flush=True)


if __name__=="__main__":
    main()

