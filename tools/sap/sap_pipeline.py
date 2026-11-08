#!/usr/bin/env python3
"""sap_pipeline.py [--enqueue U,U,... | --enqueue-all]: drive packaging units through
  arch (Sol architect) -> cert (strict run_comparator) -> ref (two blind Sol referees) -> [fix (resume architect with
  the reports) -> cert -> dref (resume referees with the revision)] (at most 2 referee rounds) -> final | stuck.
A failed certification resumes the architect with the failure (at most 3 times) before stuck.
Opus third rung (author 2026-11-04: "Use the API for any Opus tasks, until it runs out." / "If you run out of API
credits, don't use any more Opus agents."): a unit that would go stuck (referee issues after MAXREF rounds, or
certification failing more than MAXCERTFIX times) goes once to an Opus architect via ~/bin/opus_run.py (tag sap, cap 3,
API keys, key1 first) in tmux sapO-<UNIT>, then cert -> delta referees; still open -> stuck. When opus_run reports no
usable key (exit 6) the pipeline writes ~/sap/pipeline/NO_OPUS and every later such unit goes straight to stuck.
Declaration review (author 2026-11-04: "I want you to deploy two Sol agents on every Challenge declaration, and make sure
that all are faithful. We want to meet Palomar standards." then "just run one Sol agent per, not two. And I think you
can group declarations."): units named in ~/sap/pipeline/FW (or "all") go final -> fwprepq -> fwprep (tools/fw_prep.py:
fresh compile, Lean statement closures, per-declaration fingerprints) -> fw (ONE blind Sol reviewer per group of at
most FW_GROUP declarations, briefs/brief-fw.md / brief-fw-omit.md, tmux sapP-<U>-fr<round>g<k>) -> faithful when every
declaration's latest review on its CURRENT fingerprint is clean; otherwise fwfixq (architect resumed with the reports)
-> cert -> fwprepq (only declarations whose fingerprint changed or whose review is not clean are re-reviewed, in fresh
groups that see the earlier findings and the architect's reply) ... at most MAXFWFIX Sol fix rounds, then the Opus rung
(once per phase), then stuck.

Admission for every agent launch: fewer than ~/sap/pipeline/PARALLEL (default 20) live sapP-* agents; machine Codex
agents < 84; weekly quota remaining (last line of ~/dbl/logs/quota.log) > FLOOR (10.5). ~/sap/pipeline/STOP pauses new
launches. Agents run in tmux sessions sapP-<UNIT>-<ROLE> (Sol max, workspace-write, web search) with flag files;
certification runs in sapC-<UNIT>. One pipeline at a time (flock). State: ~/sap/pipeline/state.json (atomic)."""
import json, os, re, subprocess, sys, time, pathlib, fcntl, shutil, datetime
H = pathlib.Path.home(); P = H / "sap/pipeline"; P.mkdir(parents=True, exist_ok=True)
T = H / "sap/tools"; B = H / "sap/briefs"; TASKS = H / "sap/tasks"; WT = H / "sap/wt"; LOGS = H / "sap/logs"
STATE = P / "state.json"; FLOOR = 10.5; MAXCERTFIX = 3; MAXREF = 3
OPUS = "/home/ubuntu/bin/opus_run.py"; OPUS_CAP = 3
MAXFWFIX = 2; FWPREP_CAP = 10; FWU = H / "sap/fw/units"; FWPREP = H / "sap/fw/prep"
CLEAN = {"correct_whole", "correct_restricted", "omission_ok"}
sys.path.insert(0, str(H / "sal/fid/tools")); from pool import codex_agents  # same counting as the dbl queue
units = json.load(open(H / "sap/inputs/units.json"))

def now(): return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
def log(m):
    with open(P / "pipeline.log", "a") as f: f.write(f"{now()} {m}\n")
def save(st):
    tmp = STATE.with_suffix(".tmp"); tmp.write_text(json.dumps(st, indent=1)); os.replace(tmp, STATE)
def sh(cmd): return subprocess.run(cmd, shell=True, capture_output=True, text=True)
def tmux_alive(name): return sh(f"tmux has-session -t {name} 2>/dev/null").returncode == 0
def live_agents(): return [l for l in sh("tmux ls -F '#S' 2>/dev/null").stdout.split() if l.startswith("sapP-")]
CODEX_HOME = "/home/ubuntu/.codex-yale"   # Yale account for all new tasks (author, 2026-11-03); the gmail token is revoked
def quota_remaining():
    """Weekly allowance remaining on the Yale account: newest rate_limits event in its rollouts."""
    try:
        # only rollouts created on the Yale account: the file name carries the creation time; sessions copied from the
        # gmail home keep their older names (their mtimes are new), so filter and sort by the name, not the mtime
        files = sorted((f for f in pathlib.Path(CODEX_HOME).glob("sessions/*/*/*/rollout-*.jsonl")
                        if f.name[8:27] >= "2026-11-03T23-14-00"), key=lambda f: f.name[8:27])
        for f in reversed(files[-30:]):
            m = re.findall(r'"primary":\{"used_percent":([0-9.]+)', f.read_text(errors="ignore"))
            if m: return 100.0 - float(m[-1])
    except Exception: pass
    return None
AUTH_FAIL = re.compile(r"token_revoked|401 Unauthorized|invalidated oauth token")
def failed_on_auth(logfile):
    try: t = pathlib.Path(logfile).read_text(errors="ignore")
    except OSError: return False
    return bool(AUTH_FAIL.search(t.rsplit("=== sap launch", 1)[-1]))
def session_of(logfile):
    try: s = re.findall(r"session=([0-9a-f-]{20,})", pathlib.Path(logfile).read_text())
    except OSError: return None
    return s[-1] if s else None
DISK_MIN = 25e9   # author 2026-11-04: "Keep eye on disk usage."
def admit():
    if (P / "STOP").exists(): return False
    if shutil.disk_usage("/").free < DISK_MIN:
        if not (P / "DISK_LOW").exists():
            (P / "DISK_LOW").write_text(now()); log(f"DISK LOW: {shutil.disk_usage('/').free / 1e9:.0f} GB free; launches paused")
        return False
    (P / "DISK_LOW").unlink(missing_ok=True)
    # ~/sap/pipeline/FLOOR overrides the floor; "credits" = no floor (author 2026-11-03: "Let Yale go to credits")
    f = (P / "FLOOR").read_text().strip() if (P / "FLOOR").exists() else str(FLOOR)
    if f != "credits":
        q = quota_remaining()
        if q is None or q <= float(f): return False
    par = int((P / "PARALLEL").read_text().strip()) if (P / "PARALLEL").exists() else 20
    # machine-wide Codex agents (all campaigns); ~/sap/pipeline/MACHINE_CAP overrides 84 (author 2026-11-04: "I think you
    # can run more at once, no?"; 64 cores / 495 GB, load ~15 at 88 agents)
    mc = int((P / "MACHINE_CAP").read_text().strip()) if (P / "MACHINE_CAP").exists() else 84
    return len(live_agents()) < par and codex_agents() < mc

def launch(unit, role, cwd, prompt, logfile, flag, resume=None):
    name = f"sapP-{unit}-{role}"
    pathlib.Path(flag).unlink(missing_ok=True)
    if resume: cmd = f"python3 ~/bin/sol-retry.py max 1 -- resume {resume} -f {prompt} -e max --write --search"
    else: cmd = (f"python3 ~/bin/sol-retry.py max 1 -- run -f {prompt} -e max --write -C . --search "
                 f"--name {name} --timeout 14400")
    r = sh(f"tmux new-session -d -s {name} \"cd {cwd} && echo '=== sap launch {now()} ===' >> {logfile} && "
           f"CODEX_HOME={CODEX_HOME} {cmd} >> {logfile} 2>&1; touch {flag}\"")
    if r.returncode:   # V-ORCH-SAP2 MINOR 3: never advance state on a launch that did not happen
        log(f"{unit} LAUNCH FAILED {role}: {(r.stdout + r.stderr).strip()[:200]}"); return False
    log(f"{unit} launched {role}" + (f" (resume {resume})" if resume else "")); return True

def arch_dir(u): return WT / f"ARCH-{u}"
def start_arch(u):
    r = sh(f"cd ~/sap && python3 tools/make_arch.py {u}")
    if r.returncode: log(f"{u} packet failed: {(r.stdout + r.stderr)[-300:]}"); return False
    if not arch_dir(u).exists():
        r = sh(f"{T}/mkwt.sh ARCH-{u}")
        if r.returncode: log(f"{u} worktree failed: {r.stdout + r.stderr}"); return False
    d = arch_dir(u)
    shutil.copy(TASKS / f"ARCH-{u}/work.json", d / "work.json")
    (d / "brief.md").write_text((B / "brief-arch.md").read_text().replace("<WORK_ID>", units[u]["work"]).replace("<WORK>", u))
    ex = d / "examples"; ex.mkdir(exist_ok=True)
    for p in ("P022", "P010"):
        src = WT / f"ARCH-{p}/SAP/{p}"
        if src.exists() and not (ex / p).exists(): shutil.copytree(src, ex / p, ignore=shutil.ignore_patterns("verification"))
    launch(u, "arch", d, "brief.md", LOGS / f"ARCH-{u}.out", TASKS / f"ARCH-{u}/DONE"); return True

def start_cert(u):
    flag = TASKS / f"ARCH-{u}/CERT_RC"; flag.unlink(missing_ok=True)
    sh(f"tmux new-session -d -s sapC-{u} \"python3 {T}/run_comparator.py {arch_dir(u)} {u} > {LOGS}/CERT-{u}.out 2>&1; "
       f"echo \\$? > {flag}\"")
    log(f"{u} certification started")

def start_refs(u, st):
    sh(f"cd ~/sap && python3 tools/make_chfid.py {u}")
    for s in "ab":
        d = TASKS / f"CHFID-{u}-{s}"
        launch(u, f"ref{s}", d, "brief.md", d / "run.out", d / "DONE")
    st["ref_round"] = 1

def start_fix(u, st, reason_file):
    sess = session_of(LOGS / f"ARCH-{u}.out")
    if not sess: log(f"{u} no architect session; stuck"); st["stage"] = "stuck"; return False
    return launch(u, "arch", arch_dir(u), reason_file, LOGS / f"ARCH-{u}.out", TASKS / f"ARCH-{u}/DONE", resume=sess)

def start_drefs(u, st):
    A = arch_dir(u)
    for s in "ab":
        D = TASKS / f"CHFID-{u}-{s}"
        for part in ("Defs", "Challenge"):
            shutil.rmtree(D / f"SAP/{u}/{part}", ignore_errors=True)
            if (A / f"SAP/{u}/{part}").exists(): shutil.copytree(A / f"SAP/{u}/{part}", D / f"SAP/{u}/{part}")
            shutil.copy(A / f"SAP/{u}/{part}.lean", D / f"SAP/{u}/{part}.lean")
        ob = A / f".lake/build/lib/lean/SAP/{u}"; tb = D / f".lake/build/lib/lean/SAP/{u}"
        shutil.rmtree(tb, ignore_errors=True); tb.mkdir(parents=True)
        for f in ob.rglob("*"):
            rel = f.relative_to(ob)
            if f.is_file() and (rel.parts[0] in ("Defs", "Challenge") or rel.name.startswith(("Defs.", "Challenge."))):
                (tb / rel).parent.mkdir(parents=True, exist_ok=True); shutil.copy(f, tb / rel)
        man = json.load(open(A / f"SAP/{u}/manifest.json")); man = man if isinstance(man, list) else man.get("targets", man)
        json.dump([{k: m.get(k) for k in ("target_id", "decision", "theorem", "restriction", "rows_used", "rows_not_used")}
                   for m in man], open(D / f"record{st['ref_round'] + 1}.json", "w"), indent=1)
        shutil.copy(A / "REPORT.md", D / "architect-report.md")
        n = st["ref_round"] + 1
        (D / f"delta{n}.md").write_text((B / "chfid-delta.md").read_text().replace("<WORK>", u)
                                        .replace("record2.json", f"record{n}.json").replace("findings2.json", f"findings{n}.json")
                                        .replace("REPORT2.md", f"REPORT{n}.md"))
        (D / f"DONE{n}").unlink(missing_ok=True)
        launch(u, f"ref{s}", D, f"delta{n}.md", D / "delta.out", D / f"DONE{n}", resume=session_of(D / "run.out"))
    st["ref_round"] += 1

def findings_clean(u, rnd):
    issues = []
    for s in "ab":
        fn = TASKS / f"CHFID-{u}-{s}" / ("findings.json" if rnd == 1 else f"findings{rnd}.json")
        try: f = json.load(open(fn))
        except Exception as e: return None, [f"{s}: unreadable findings ({e})"]
        for x in f:
            if x.get("verdict") not in CLEAN or x.get("severity", "none") != "none": issues.append((s, x.get("target_id")))
    return not issues, issues

def ref_fix_prompt(u, rnd):
    A = arch_dir(u); dst = A / f"referees/round{rnd}"
    for s in "ab":
        D = TASKS / f"CHFID-{u}-{s}"; (dst / s).mkdir(parents=True, exist_ok=True)
        for fn in ([("findings.json", "findings.json"), ("REPORT.md", "REPORT.md"), ("reading.md", "reading.md")] if rnd == 1
                   else [(f"findings{rnd}.json", "findings.json"), (f"REPORT{rnd}.md", "REPORT.md")]):
            if (D / fn[0]).exists(): shutil.copy(D / fn[0], dst / s / fn[1])
    text = (B / "arch-revise-referees.md").read_text().replace("`referees/<a|b>/`", f"`referees/round{rnd}/<a|b>/`")
    pf = A / f"revise-ref{rnd}.md"; pf.write_text(text); return pf.name

def cert_fix_prompt(u, n):
    A = arch_dir(u); out = (LOGS / f"CERT-{u}.out").read_text()[-3000:]
    try: fr = json.load(open(A / f"SAP/{u}/verification/comparator-result.json")).get("failure", "")
    except Exception: fr = ""
    pf = A / f"revise-cert{n}.md"
    pf.write_text("Orchestrator update: the strict certification (`/home/ubuntu/sap/tools/run_comparator.py`: frozen snapshot, "
                  "fresh rebuild, complete manifest against your unit's targets, Lean-derived import closures, three-kernel "
                  f"Palomar Comparator) FAILED:\n\n{fr}\n\nLast output:\n```\n{out}\n```\n\nFix the cause within the brief's rules "
                  "(do not weaken a statement just to pass unless the brief allows it, and disclose any change), recompile "
                  "everything with sap-lean, update manifest.json/comparator.json/REPORT.md.")
    return pf.name

def live_opus(): return [l for l in sh("tmux ls -F '#S' 2>/dev/null").stdout.split() if l.startswith("sapO-")]
def opus_available(): return not (P / "NO_OPUS").exists()
def opus_flag(v): return "opus_fw" if v.get("phase") == "fw" else "opus"
def stuck_or_opus(u, v, why, msg):
    """The Opus third rung, once per unit and phase, while the API keys last; otherwise stuck."""
    if not v.get(opus_flag(v)) and opus_available():
        v["stage"] = "opusq"; v["opus_why"] = why; log(f"{u} {msg} -> Opus rung queued")
    else:
        v["stage"] = "stuck"
        log(f"{u} stuck: {msg}" + (" (after the Opus rung)" if v.get(opus_flag(v)) else " (no Opus: API credits exhausted)"))

def start_opus(u, v):
    A = arch_dir(u)
    if v.get("opus_why") == "ref":
        rnd = v["ref_round"]; ref_fix_prompt(u, rnd)   # copies the latest referee reports to referees/round<rnd>/
        items = ", ".join(f"{t} (referee {s})" for s, t in v.get("issues", [])) or "see the reports"
        why = (f"After {rnd} referee rounds, the two blind Sol referees still report open items: {items}. Their latest "
               f"reports are in `referees/round{rnd}/a/` and `referees/round{rnd}/b/` (findings.json, REPORT.md); earlier "
               f"rounds are in the other `referees/round*/` directories, and the Sol architect's replies are in REPORT.md.")
    elif v.get("opus_why") == "fw":
        rnd = v.get("fwfix", 0) + 1; items = fw_collect(u, v, rnd)
        why = (f"After {v.get('fwfix', 0)} fix rounds, the per-declaration reviews (a blind Sol reviewer for each Challenge "
               f"declaration, following every definition its statement depends on) still report open items:\n\n{items}\n\n"
               f"Their latest reports are in `fw/round{rnd}/<theorem>/<reviewer>/` (findings*.json, REPORT*.md, reading.md); "
               f"earlier rounds are in the other `fw/round*/` directories, and the Sol architect's replies are in REPORT.md.")
    else:
        n = v.get("certfix", 0); fn = cert_fix_prompt(u, n)
        why = (f"The strict certification failed {n} times after the Sol architect's fixes. The latest failure and the "
               f"runner's output are in `{fn}`.")
    rules = (B / "arch-revise-referees.md").read_text(); rules = rules[rules.index("1. **Clause"):]
    (A / "opus-rung.md").write_text((B / "opus-rung.md").read_text().replace("<WORK>", u).replace("<WHY>", why)
                                    .replace("<RULES>", rules))
    rcf = TASKS / f"ARCH-{u}/OPUS_RC"; rcf.unlink(missing_ok=True)
    sh(f"tmux new-session -d -s sapO-{u} \"cd {A} && echo '=== sap opus launch {now()} ===' >> {LOGS}/OPUS-{u}.out && "
       f"{OPUS} run -f opus-rung.md -C . --tag sap --name sap-{u}-opus -e xhigh --max-budget-usd 30 --timeout 14400 "
       f"--search >> {LOGS}/OPUS-{u}.out 2>&1; echo \\$? > {rcf}\"")
    log(f"{u} launched Opus rung ({v.get('opus_why')})")

# ---------- declaration review (FW) ----------
# Author 2026-11-04: two Sol agents per Challenge declaration, revised to "just run one Sol agent per, not two. And I
# think you can group declarations." One Sol reviewer per group of at most FW_GROUP declarations (FW_GROUP_OMIT omitted
# targets) of one unit. Validation and binding are shared with publication (tools/fw_common.py, V-ORCH-SAP2 delta
# D1-D3): an entry counts only if it passes validate_entry, its task dir still holds exactly the inputs it was given,
# and those inputs are the current version (same sources byte for byte, same review packet). A declaration passes when
# the reviews of its latest round bound to its CURRENT fingerprint are all clean.
import fw_common as FC
FW_GROUP = 5; FW_GROUP_OMIT = 8; FW_MAXMISS = 2
def fw_on(u):
    f = P / "FW"
    if not f.exists(): return False
    t = f.read_text().split(); return "all" in t or u in t
def fw_load(u): return json.load(open(FWU / f"{u}.json"))
def fw_save(u, uj):
    tmp = FWU / f"{u}.json.tmp"; tmp.write_text(json.dumps(uj, indent=1, ensure_ascii=False)); os.replace(tmp, FWU / f"{u}.json")
def fw_short(thm): return thm.rsplit(".", 1)[-1]
def fw_gdir(u, gid): return TASKS / f"FW-{u}-{gid}"
def fw_reviews(uj, t):
    r = uj.get("reviews", {}).get(t)
    if r is None: return []
    if isinstance(r, dict): return [dict(x, reviewer=k, round=x.get("round", x.get("n", 1))) for k, x in r.items()]
    return r
def fw_pass(uj, t):
    fp = uj["current"][t]["fp"]; rs = [r for r in fw_reviews(uj, t) if r.get("fp") == fp]
    if not rs: return False
    m = max(r["round"] for r in rs); return all(r["clean"] for r in rs if r["round"] == m)
def fw_open(uj): return [t for t in uj["current"] if not fw_pass(uj, t)]
def fw_add_review(uj, t, rec):
    lst = fw_reviews(uj, t); lst.append(rec); uj.setdefault("reviews", {})[t] = lst
def fw_manifest(u):
    man = json.load(open(arch_dir(u) / f"SAP/{u}/manifest.json")); return man if isinstance(man, list) else man.get("targets", man)

def fw_make_groups(u, v, thms, rnd):
    cur = fw_load(u)["current"]
    decl = [t for t in thms if not cur[t].get("omitted")]; om = [t for t in thms if cur[t].get("omitted")]
    gs = [decl[i:i + FW_GROUP] for i in range(0, len(decl), FW_GROUP)] + \
         [om[i:i + FW_GROUP_OMIT] for i in range(0, len(om), FW_GROUP_OMIT)]
    G = v.setdefault("fw_groups", {})
    for g in gs:
        k = 1 + sum(1 for x in G if x.startswith(f"r{rnd}g"))
        gid = f"r{rnd}g{k}"; G[gid] = {"thms": g, "round": rnd, "omit": bool(cur[g[0]].get("omitted"))}
        v.setdefault("fw_todo", []).append(gid)
    return len(gs)

def fw_package_group(u, gid, g):
    """Task dir for one reviewer of one group: the unit's current Defs/Challenge sources and fresh compiled outputs from
    ~/sap/fw/prep/<U>, closure.json, claims.json and record.json (exactly the review packets of fw_common.packet); from
    round 2, earlier.json and architect-report.md. Records the digests the binding check needs."""
    d = fw_gdir(u, gid); src = FWPREP / u; uj = fw_load(u); cur = uj["current"]
    shutil.rmtree(d, ignore_errors=True); (d / "scratch").mkdir(parents=True)
    for part in ("Defs", "Challenge"):
        if (src / f"SAP/{u}/{part}").exists(): shutil.copytree(src / f"SAP/{u}/{part}", d / f"SAP/{u}/{part}")
        shutil.copy(src / f"SAP/{u}/{part}.lean", d / f"SAP/{u}/{part}.lean")
    shutil.copytree(src / f".lake/build/lib/lean/SAP/{u}", d / f".lake/build/lib/lean/SAP/{u}")
    pk = json.load(open(TASKS / f"ARCH-{u}/work.json")); tg = {x["target_id"]: x for x in pk["targets"]}
    man = {m["target_id"]: m for m in fw_manifest(u)}
    targets, records, decls, earlier, pkts = [], [], [], [], {}
    for t in g["thms"]:
        c = cur[t]; pt = FC.packet(pk, tg[c["target_id"]], man[c["target_id"]], c.get("omitted"))
        pkts[t] = FC.packet_digest(pt); targets.append(pt["target"]); records.append(pt["record"])
        decls.append({"theorem": None if c.get("omitted") else t, "target_id": c["target_id"], "fingerprint": c["fp"],
                      "module": c["module"], "line": c["line"], "closure": c["closure"]})
        prev = fw_reviews(uj, t)
        if prev:
            last = max(r["round"] for r in prev)
            # only earlier reviews that raised issues: a clean earlier verdict adds nothing to check and invites anchoring
            earlier += [{"theorem": t, "target_id": c["target_id"], "round": r["round"], "verdict": r["verdict"],
                         "severity": r["severity"], "issues": r.get("issues")} for r in prev
                        if r["round"] == last and not r["clean"]]
    json.dump({"work_id": u, "citation": pk.get("citation"), "standing_assumptions": pk.get("standing_assumptions"),
               "targets": targets}, open(d / "claims.json", "w"), indent=1, ensure_ascii=False, default=str)
    json.dump(records, open(d / "record.json", "w"), indent=1, ensure_ascii=False, default=str)
    json.dump({"declarations": decls}, open(d / "closure.json", "w"), indent=1, ensure_ascii=False)
    brief = (B / ("brief-fw-omit.md" if g.get("omit") else "brief-fw.md")).read_text()
    if earlier:
        json.dump(earlier, open(d / "earlier.json", "w"), indent=1, ensure_ascii=False)
        shutil.copy(arch_dir(u) / "REPORT.md", d / "architect-report.md")
        brief += "\n" + (B / "fw-recheck.md").read_text()
    names = ", ".join(f"`{t}`" if not cur[t].get("omitted") else f"`{cur[t]['target_id']}` (omitted)" for t in g["thms"])
    (d / "brief.md").write_text(brief.replace("<WORK>", u).replace("<DECLS>", names))
    g["fps"] = {t: cur[t]["fp"] for t in g["thms"]}; g["pkt"] = pkts
    g["src_digest"] = FC.src_digest(d, u); g["binding"] = "fw_common v2"; g["base"] = uj["prep"]["base"]
    if g["src_digest"] != uj["prep"]["src_digest"]: raise RuntimeError(f"{u} {gid}: task copy differs from prep")
    return d

def start_fw_group(u, v, gid):
    g = v["fw_groups"][gid]; d = fw_package_group(u, gid, g)
    if not launch(u, f"f{gid}", d, "brief.md", d / "run.out", d / "DONE"): return False
    v.setdefault("fw_run", []).append(["G", gid]); return True

def fw_collect(u, v, rnd):
    """Copy the latest reviews of every open declaration into the architect worktree (fw/round<rnd>/) and list them."""
    uj = fw_load(u); items = []
    for t in fw_open(uj):
        rs = fw_reviews(uj, t); c = uj["current"][t]
        if not rs: items.append(f"- `{t}`: no review on the current text yet"); continue
        last = max(r["round"] for r in rs)
        for r in (r for r in rs if r["round"] == last):
            dst = arch_dir(u) / f"fw/round{rnd}/{fw_short(t)}/{r['reviewer']}"; dst.mkdir(parents=True, exist_ok=True)
            src = pathlib.Path(r["file"]).parent
            for a in (pathlib.Path(r["file"]), src / "REPORT.md", src / "reading.md"):
                if a.exists(): shutil.copy(a, dst / a.name)
            first = (r.get("issues") or [""])[0]
            items.append(f"- `{t}` ({c['target_id']}): {r['verdict']}/{r['severity']}" + (f" — {str(first)[:300]}" if first else ""))
    return "\n".join(items)

def fw_fix_prompt(u, v):
    n = v["fwfix"]; items = fw_collect(u, v, n)
    pf = arch_dir(u) / f"revise-fw{n}.md"
    pf.write_text((B / "fw-fix.md").read_text().replace("<N>", str(n)).replace("<ITEMS>", items))
    return pf.name

def fw_plan(u, v):
    uj = fw_load(u); todo = fw_open(uj)
    if not todo:
        v["stage"] = "faithful"; log(f"{u} FAITHFUL: all {len(uj['current'])} items reviewed clean on their current text"); return
    v["fw_round"] = v.get("fw_round", 0) + 1; v["fw_todo"] = []; v["fw_run"] = []
    n = fw_make_groups(u, v, todo, v["fw_round"]); v["stage"] = "fw"
    log(f"{u} declaration review round {v['fw_round']}: {len(todo)} items in {n} groups")

def fw_poll(u, v):
    still = []; uj = fw_load(u); G = v.setdefault("fw_groups", {}); miss = v.setdefault("fw_miss", {})
    cur = uj["current"]; man = {m["target_id"]: m for m in fw_manifest(u)}
    pk = json.load(open(TASKS / f"ARCH-{u}/work.json"))
    def missed(keys, why):
        again = []
        for t in keys:
            miss[t] = miss.get(t, 0) + 1
            if miss[t] <= FW_MAXMISS and t in cur: again.append(t)
            else: v["fw_broken"] = True
        if again: fw_make_groups(u, v, again, v.get("fw_round", 1))
        log(f"{u} review items without a valid result ({why}): {[fw_short(t) for t in keys]}"
            + ("; regrouped" if again else "; limit reached"))
    for e in v.get("fw_run", []):
        gid = e[1] if e[0] == "G" else None
        if gid is None: missed([e[0]], "pre-group legacy entry"); continue
        g = G[gid]; d = fw_gdir(u, gid)
        if not (d / "DONE").exists() or tmux_alive(f"sapP-{u}-f{gid}"): still.append(e); continue
        if failed_on_auth(d / "run.out"): v["fw_todo"].append(gid); log(f"{u} review group {gid} failed on auth; requeued"); continue
        keys = [t for t in g["thms"] if t in cur]
        if g.get("binding") == "fw_common v2" and FC.src_digest(d, u) != g["src_digest"]:
            missed(keys, "the reviewer's task copy no longer matches what it was given"); continue
        try:
            f = json.load(open(d / "findings.json"))
            items = {t: (cur[t]["target_id"], g["fps"][t]) for t in keys}
            by, probs = FC.index_findings(f, items)
        except Exception as ex:
            by, probs = {}, [f"unreadable findings ({ex})"]
        if probs: log(f"{u} review group {gid}: rejected entries: {probs[:4]}")
        for t in keys:
            if t not in by: continue
            x, clean = by[t]
            v2 = g.get("binding") == "fw_common v2"
            rec = {"round": g["round"], "reviewer": gid, "fp": None, "verdict": x["verdict"], "severity": x["severity"],
                   "clean": clean, "file": str(d / "findings.json"), "at": now(), "issues": x.get("issues") or [],
                   "resolved": x.get("resolved"), "binding": "v2" if v2 else "legacy",
                   "src_digest": g.get("src_digest") if v2 else None, "pkt": g.get("pkt", {}).get(t) if v2 else None,
                   "given_fp": g["fps"].get(t),
                   # v2 groups launched 11:36-12:20 did not record the base; it has not changed since the campaign began
                   "base": g.get("base") or (uj["prep"]["base"] if v2 else None)}
            # binding: the task's actual files (sources, reconstructed packet), base and fingerprint are the current ones
            bound, _, why = FC.review_bound(rec, t, cur[t]["target_id"], u, uj["prep"]["src_digest"],
                                            uj["prep"]["packets"][t], uj["prep"]["base"], cur[t]["fp"])
            rec["fp"] = cur[t]["fp"] if bound else None; rec["unbound"] = why or None
            fw_add_review(uj, t, rec)
            if not clean: log(f"{u} {fw_short(t)}: {x['verdict']}/{x['severity']}")
            if not bound: log(f"{u} {fw_short(t)}: review not bound to the current version ({why})")
        fw_save(u, uj)
        lost = [t for t in keys if t not in by]
        if lost: missed(lost, "missing or invalid entries")
    v["fw_run"] = still
    if still or v.get("fw_todo"): return
    if v.pop("fw_broken", False):
        v["stage"] = "stuck"; log(f"{u} stuck: a review item got no valid result after {FW_MAXMISS} retries"); return
    uj = fw_load(u); bad = fw_open(uj)
    unreviewed = [t for t in bad if not any(r.get("fp") == uj["current"][t]["fp"] for r in fw_reviews(uj, t))]
    if unreviewed:   # e.g. a review bound to an older version: review the current one before any fix
        fw_make_groups(u, v, unreviewed, v.get("fw_round", 1)); log(f"{u} {len(unreviewed)} items lack a review of the current version; regrouped"); return
    if not bad:
        v["stage"] = "faithful"; log(f"{u} FAITHFUL: all {len(uj['current'])} items reviewed clean on their current text")
    elif any(v.get("fw_item_fixes", {}).get(t, 0) < MAXFWFIX for t in bad):
        # fix budget per ITEM: an item with open findings gets up to MAXFWFIX Sol fix rounds (a re-review can open
        # new items in a unit whose earlier items used their rounds)
        v["stage"] = "fwfixq"; log(f"{u} declaration review: {len(bad)} items with open findings -> fix")
    else:
        stuck_or_opus(u, v, "fw", f"declaration review still open after {MAXFWFIX} fix rounds per item: "
                                   f"{sorted(fw_short(t) for t in bad)}")

def tick(st):
    for u, v in st.items():
        stg = v["stage"]
        if stg == "arch" and (TASKS / f"ARCH-{u}/DONE").exists() and not tmux_alive(f"sapP-{u}-arch"):
            if failed_on_auth(LOGS / f"ARCH-{u}.out"):
                v["stage"] = v.get("last_kind", "queued"); log(f"{u} architect failed on auth; requeued as {v['stage']}")
            else:
                v["stage"] = "certq"; log(f"{u} architect finished")
        elif stg == "cert" and (TASKS / f"ARCH-{u}/CERT_RC").exists() and not tmux_alive(f"sapC-{u}"):
            rc = (TASKS / f"ARCH-{u}/CERT_RC").read_text().strip()
            if rc == "0":
                log(f"{u} CERTIFIED")
                v["stage"] = "fwprepq" if v.get("phase") == "fw" else "refq" if v.get("ref_round", 0) == 0 else "drefq"
            else:
                v["certfix"] = v.get("certfix", 0) + 1; log(f"{u} certification failed ({v['certfix']})")
                if v.get(opus_flag(v)):   # Opus is the last rung of its phase: no Sol fix after it
                    v["stage"] = "stuck"; log(f"{u} stuck: certification failed after the Opus rung")
                elif v["certfix"] <= MAXCERTFIX: v["stage"] = "certfixq"
                else: stuck_or_opus(u, v, "cert", f"certification failed {v['certfix']} times")
        elif stg in ("ref", "dref"):
            rnd = v["ref_round"]; flags = [TASKS / f"CHFID-{u}-{s}" / ("DONE" if rnd == 1 else f"DONE{rnd}") for s in "ab"]
            if all(f.exists() for f in flags) and not any(tmux_alive(f"sapP-{u}-ref{s}") for s in "ab"):
                logs = [TASKS / f"CHFID-{u}-{s}" / ("run.out" if rnd == 1 else "delta.out") for s in "ab"]
                if any(failed_on_auth(l) for l in logs):
                    if stg == "dref": v["ref_round"] = rnd - 1
                    v["stage"] = "refq" if stg == "ref" else "drefq"; log(f"{u} referee failed on auth; requeued as {v['stage']}")
                    continue
                ok, issues = findings_clean(u, rnd)
                if ok: v["stage"] = "final"; log(f"{u} FINAL (referee round {rnd} clean)")
                elif ok is None: v["stage"] = "stuck"; log(f"{u} stuck: {issues}")
                elif rnd >= MAXREF:
                    v["issues"] = issues; stuck_or_opus(u, v, "ref", f"after {rnd} referee rounds: {issues[:6]}")
                else: v["stage"] = "reffixq"; v["issues"] = issues; log(f"{u} referee issues ({len(issues)}) -> fix")
    # declaration review: entry, prep completion, review completion
    for u, v in st.items():
        if v["stage"] == "final" and fw_on(u):
            v["stage"] = "fwprepq"; v["phase"] = "fw"; log(f"{u} declaration review queued")
        elif v["stage"] == "fwprep" and (TASKS / f"ARCH-{u}/FWPREP_RC").exists() and not tmux_alive(f"sapW-{u}"):
            rc = (TASKS / f"ARCH-{u}/FWPREP_RC").read_text().strip()
            if rc == "0": fw_plan(u, v)
            else: v["stage"] = "stuck"; log(f"{u} stuck: declaration-review preparation failed (logs/FWPREP-{u}.out)")
        elif v["stage"] == "fw":
            fw_poll(u, v)
    nprep = sum(1 for l in sh("tmux ls -F '#S' 2>/dev/null").stdout.split() if l.startswith("sapW-"))
    for u in sorted(st):
        v = st[u]
        if v["stage"] == "fwprepq" and not (P / "STOP").exists() and nprep < FWPREP_CAP:
            flag = TASKS / f"ARCH-{u}/FWPREP_RC"; flag.unlink(missing_ok=True)
            sh(f"tmux new-session -d -s sapW-{u} \"python3 {T}/fw_prep.py {u} > {LOGS}/FWPREP-{u}.out 2>&1; "
               f"echo \\$? > {flag}\"")
            v["stage"] = "fwprep"; nprep += 1
    # Opus third rung: completion
    for u, v in st.items():
        if v["stage"] == "opus" and (TASKS / f"ARCH-{u}/OPUS_RC").exists() and not tmux_alive(f"sapO-{u}"):
            rc = (TASKS / f"ARCH-{u}/OPUS_RC").read_text().strip()
            if rc == "6":
                (P / "NO_OPUS").write_text(f"{now()} opus_run: no usable API key (credits exhausted) at {u}\n")
                v["stage"] = "stuck"; log(f"{u} stuck: Opus rung impossible, API credits exhausted (NO_OPUS set)")
            elif rc in ("3", "4", "5"):
                v["stage"] = "opusq"; log(f"{u} Opus rung not started (opus_run rc {rc}); requeued")
            else:
                v[opus_flag(v)] = 1; v["stage"] = "certq"; log(f"{u} Opus rung finished (opus_run rc {rc})")
    # Opus third rung: launches (API keys, not Codex; own cap; STOP pauses them too)
    for u in sorted(st):
        v = st[u]
        if v["stage"] != "opusq": continue
        if (P / "STOP").exists() or len(live_opus()) >= OPUS_CAP: break
        if not opus_available():
            v["stage"] = "stuck"; log(f"{u} stuck: no Opus (API credits exhausted)"); continue
        start_opus(u, v); v["stage"] = "opus"; save(st)
    # non-agent step: certification jobs (CPU only)
    for u, v in st.items():
        if v["stage"] == "certq" and not (P / "STOP").exists():   # STOP also pauses new certification runs
            start_cert(u); v["stage"] = "cert"
    # agent launches: in-flight work first, then new architects
    order = ["certfixq", "reffixq", "fwfixq", "drefq", "refq", "queued"]
    for kind in order:
        for u in sorted(st):
            v = st[u]
            if v["stage"] != kind: continue
            need = 2 if kind in ("refq", "drefq") else 1
            if not admit() or (need == 2 and len(live_agents()) + 2 > int((P / "PARALLEL").read_text().strip()
                                                                       if (P / "PARALLEL").exists() else 20)):
                return
            v["last_kind"] = kind
            if kind == "queued":
                v["stage"] = "arch" if start_arch(u) else "stuck"
            elif kind == "certfixq":
                if start_fix(u, v, cert_fix_prompt(u, v["certfix"])): v["stage"] = "arch"
            elif kind == "reffixq":
                if start_fix(u, v, ref_fix_prompt(u, v["ref_round"])): v["stage"] = "arch"
            elif kind == "fwfixq":
                v["fwfix"] = v.get("fwfix", 0) + 1
                if start_fix(u, v, fw_fix_prompt(u, v)):
                    cnt = v.setdefault("fw_item_fixes", {})
                    for t in fw_open(fw_load(u)): cnt[t] = min(MAXFWFIX, cnt.get(t, 0) + 1)
                    v["stage"] = "arch"
            elif kind == "refq":
                start_refs(u, v); v["stage"] = "ref"
            elif kind == "drefq":
                start_drefs(u, v); v["stage"] = "dref"
            save(st)
    # declaration reviews: lowest priority, one agent per (declaration, reviewer)
    for u in sorted(st):
        v = st[u]
        if v["stage"] != "fw": continue
        while v.get("fw_todo"):
            if not admit(): return
            gid = v["fw_todo"].pop(0)
            try: ok = start_fw_group(u, v, gid)
            except Exception as ex: ok = False; log(f"{u} LAUNCH FAILED review group {gid}: packaging error {ex}")
            if not ok: v["fw_todo"].insert(0, gid); save(st); break
            save(st)

def main():
    lock = open(P / "pipeline.lock", "w")
    try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError: sys.exit("another pipeline is running")
    st = json.load(open(STATE)) if STATE.exists() else {}
    a = sys.argv[1:]
    add = [u for u in units if u not in ("P010", "P022")] if "--enqueue-all" in a else \
          (a[a.index("--enqueue") + 1].split(",") if "--enqueue" in a else [])
    for u in add:
        assert u in units, u
        st.setdefault(u, {"stage": "queued"})
    save(st); log(f"pipeline start: {sum(v['stage'] == 'queued' for v in st.values())} queued")
    while True:
        st = json.load(open(STATE)); tick(st); save(st)
        if all(v["stage"] in ("final", "stuck", "faithful") for v in st.values()):
            log("pipeline idle"); return
        time.sleep(30)

if __name__ == "__main__":
    main()
