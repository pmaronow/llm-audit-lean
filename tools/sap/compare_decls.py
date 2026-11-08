#!/usr/bin/env python3
"""compare_decls.py: for every credited row, compare the declaration's statement (from its keyword to the top-level `:=`,
comments removed, whitespace normalized) in llm-audit-lean (the base, ~/sap/repo) and self-audit-lean (~/sal/repo/lean,
the version the fidelity sweep checked). Writes ~/sap/reports/decl-equivalence.json and prints a summary.
Rows come from each repo's catalog (file, line, lean_name)."""
import json, glob, pathlib, re, collections
H = pathlib.Path.home()
LA = H / "sap/repo"; SA = H / "sal/repo"

def strip_comments(s):
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j
        elif s.startswith("/-", i):
            d, i = 1, i + 2
            while i < n and d:
                if s.startswith("/-", i): d += 1; i += 2
                elif s.startswith("-/", i): d -= 1; i += 2
                else: i += 1
        elif s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"': j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1]); i = j + 1
        else:
            out.append(s[i]); i += 1
    return "".join(out)

KW = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+(\S+)", re.M)

def signature(root, rel, line, name):
    p = root / rel
    if not p.exists(): return None, "file missing"
    lines = p.read_text().splitlines(keepends=True)
    last = name.split(".")[-1]
    # find the declaration line: given line first, else search by last name component
    cand = []
    if line and 0 < line <= len(lines): cand.append(line - 1)
    for i, l in enumerate(lines):
        m = KW.match(l)
        if m and m.group(2).split(".")[-1] == last: cand.append(i)
    for i in cand:
        m = KW.match(lines[i])
        if not m or m.group(2).split(".")[-1] != last: continue
        text = strip_comments("".join(lines[i:i + 400]))
        # cut at the first top-level ':=' or ' where' / '|' for definitions by pattern matching
        depth, j = 0, 0
        while j < len(text):
            c = text[j]
            if c in "([{⟨": depth += 1
            elif c in ")]}⟩": depth -= 1
            elif depth == 0 and text.startswith(":=", j): break
            j += 1
        return re.sub(r"\s+", " ", text[:j]).strip(), None
    return None, "declaration not found"

def rows(catalog_glob, key_file="file"):
    out = {}
    for f in sorted(glob.glob(catalog_glob)):
        w = json.load(open(f))
        for a in w.get("associations", []):
            if a.get("status") in ("proved", "counterexample_proved"):
                out[(a["target_id"], a["lean_name"])] = (a["file"], a.get("line"))
    return out

def rows_jsonl(path):
    out = {}
    for l in open(path):
        r = json.loads(l)
        if r.get("status") in ("proved", "counterexample_proved"):
            out[(r["target_id"], r["lean_name"])] = (r["file"], r.get("line"))
    return out
la = rows_jsonl(LA / "catalog/results.jsonl")
sa = rows_jsonl(SA / "catalog/results.jsonl")
res, cnt = [], collections.Counter()
for k in sorted(sa):
    if k not in la: cnt["missing_in_base"] += 1; res.append({"key": k, "result": "missing_in_base"}); continue
    fl, ll = la[k]; fs, ls = sa[k]
    rel_l = fl[len("lean/"):] if fl.startswith("lean/") else fl
    rel_s = fs[len("lean/"):] if fs.startswith("lean/") else fs
    a, ea = signature(LA, rel_l, ll, k[1]); b, eb = signature(SA / "lean", rel_s, ls, k[1])
    if a is None or b is None: r = f"unreadable ({ea or ''}/{eb or ''})"
    elif a == b: r = "identical"
    else: r = "different"
    cnt[r] += 1
    if r != "identical": res.append({"key": k, "result": r, "base": a, "checked": b, "base_file": fl, "checked_file": fs})
(H / "sap/reports").mkdir(parents=True, exist_ok=True)
json.dump({"counts": cnt, "non_identical": res}, open(H / "sap/reports/decl-equivalence.json", "w"), indent=1,
          default=list)
print(dict(cnt))
for r in res[:8]: print(r["key"], r["result"])
