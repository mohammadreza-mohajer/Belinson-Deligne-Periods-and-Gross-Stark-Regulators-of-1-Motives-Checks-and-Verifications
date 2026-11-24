"""Validate the complete statement and displayed-equation inventory against the paper source."""
import hashlib
import json
from pathlib import Path
import re

LABEL = re.compile(r"\\label\{([^}]+)\}")
EVENT = re.compile(r"^\\section\{|^\\begin\{(theorem|lemma|proposition|corollary|example|remark)\}")
UNLABELLED_PAGES = {"2.2":5,"3.2":8,"6.5":19}


def load(root):
    paper = (root/"paper/manuscript.tex").read_text(encoding="utf-8")
    anchors = json.loads((root/"paper/anchors.json").read_text(encoding="utf-8"))
    coverage = json.loads((root/"inputs/coverage.json").read_text(encoding="utf-8"))
    equations = json.loads((root/"inputs/equations.json").read_text(encoding="utf-8"))
    sec = number = 0
    index, lines = {}, {}
    for ln, line in enumerate(paper.splitlines(),1):
        for label in LABEL.findall(line):
            if label in lines:
                raise ValueError("duplicate manuscript label "+label)
            lines[label] = ln
        ev=EVENT.match(line)
        if not ev:
            continue
        if ev[1] is None:
            sec += 1
            number = 0
        else:
            number += 1
            key = f"{sec}.{number}"
            label = LABEL.search(line)
            if label:
                anchor = anchors[label[1]]
                if anchor["number"] != key:
                    raise ValueError("typeset and source theorem numbers disagree at "+key)
                pg = anchor["page"]
            else:
                pg = UNLABELLED_PAGES[key]
            index[key] = (ev[1], ln, pg)
    if len(coverage["numbered"])!=len(index) or {r["id"] for r in coverage["numbered"]}!=set(index):
        raise ValueError("the numbered-statement inventory differs from the manuscript")
    if set(anchors)!=set(lines):
        raise ValueError("typeset anchor inventory differs from source labels")
    eqs = {k for k in lines if k.startswith("eq:")}
    if len(equations)!=len(eqs) or {e["label"] for e in equations}!=eqs:
        raise ValueError("displayed-equation inventory differs from the manuscript")
    return index,lines,anchors,coverage,equations


def render(root,decls):
    index,lines,anchors,coverage,equations=load(root)
    doc = ["# Correspondence with the manuscript","",
           "Page numbers refer to the bundled PDF. Links open the exact source line. "
           "Each entry describes the scope of its Lean declarations and names the argument that still requires a mathematical input. "
           "The arithmetic constructions are stated in the accompanying manuscript.",""]
    def links(names):
        result=[]
        for name in names:
            mod,line = decls[name]
            result.append(f"[{name}](../{mod.replace('.', '/')}.lean#L{line})")
        return ", ".join(result)
    for row in coverage["numbered"]:
        nk=row["id"]; kind,line,page=index[nk]
        doc += [f"## {kind.capitalize()} {nk}. {row['title']}", "",
                f"[Manuscript, p. {page}](../paper/manuscript.pdf#page={page}) · [LaTeX statement](../paper/manuscript.tex#L{line})","",
                row["checked"],"",links(row["proofs"]),"","**Arithmetic or analytic scope.** "+row["boundary"],""]
    for row in coverage["additional"]:
        doc += ["## "+row["title"],"",row["checked"],"",links(row["proofs"]),"",
                "**Arithmetic or analytic scope.** "+row["boundary"],""]
    doc+=["## Labelled formulas","","| Formula | Page | Manuscript result | What the correspondence covers |",
          "| --- | ---: | --- | --- |"]
    for row in equations:
        k=row["label"]; a=anchors[k]; line=lines[k]
        doc.append(f"| [({a['number']})](../paper/manuscript.tex#L{line}) | {a['page']} | {row['target']} | {row['status']}. {row['detail']} |")
    return "\n".join(doc)+"\n"


def verify_ledger(root,decls):
    idx,lines,anchors,cov,eqs=load(root)
    hashes=json.loads((root/"paper/snapshot.json").read_text())
    for file,checksum in hashes.items():
        if hashlib.sha256((root/"paper"/file).read_bytes()).hexdigest()!=checksum:
            raise ValueError("paper snapshot mismatch: "+file)
    ids = set(idx) | {r["id"] for r in cov["additional"]}
    for row in cov["numbered"]+cov["additional"]:
        if not row["proofs"] or set(row["proofs"])-set(decls):
            raise ValueError("invalid Lean declaration in "+row["id"]+": "+str(set(row["proofs"])-set(decls)))
    if any(r["target"] not in ids for r in eqs):
        raise ValueError("orphan equation")
    text = (root/"docs/CORRESPONDENCE.md").read_text(encoding="utf-8")
    if text!=render(root,decls):
        raise ValueError("stale human-readable correspondence")
    return len(idx),len(eqs)

