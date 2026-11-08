# P025a independent semantic review

All eleven declarations are **faithful**, with severity **none**. No correction
is requested. This conclusion comes from comparing the source statements and
their complete source dependencies with the canonical claims. The supplied
accepted certificate establishes proof checking only; I did not use it as
evidence of semantic fidelity or rerun the Comparator.

| Declaration | Verdict | Severity | Record decision | Principal semantic check |
|---|---|---|---|---|
| `SAP.P025a.T1` | faithful | none | whole | Realizable two-unit sample; independent indicators; full-box residuals, range, and general zero-cut diagnosis |
| `SAP.P025a.T10` | faithful | none | whole | Actual six-unit design; unique real-box minimum; corrected cut and separate printed-display errors |
| `SAP.P025a.T11` | faithful | none | whole | Equal/strict boundary split; original-scale formulas; both pair identities; actual population class masses |
| `SAP.P025a.T2` | faithful | none | whole | Actual class totals and weights; independent Brewer replication; separation and full-box extrema |
| `SAP.P025a.T3` | faithful | none | whole | Corrected first cuts; prescribed optimizers; continuous feasible segment; complete interval and residual certificate |
| `SAP.P025a.T4` | faithful | none | whole | Positive class masses; original-scale optimizers; both partition and increment formulas; attained extrema |
| `SAP.P025a.T5` | faithful | none | whole | Normalized independent quota designs; actual unit marginals and every-draw counts/Hajek estimates; both directional counterexamples |
| `SAP.P025a.T6` | faithful | none | whole | Exact overlap thresholds; reweighted odds and product identity; common-cap consequence |
| `SAP.P025a.T7` | faithful | none | refuted | Counterexample contradicts the printed sample optimizer under its own hypotheses; valid upper half retained |
| `SAP.P025a.T8` | faithful | none | refuted | Realizable non-minimizer contradicts the printed class optimizer independently of the undefined display; upper half retained |
| `SAP.P025a.T9` | faithful | none | whole | Every-cut partition; corrected endpoint; exact two-class duplication error; explicit invalid-index convention |

The record's nine `whole` decisions and two `refuted` decisions are justified.
There are no declared restrictions. The docstrings describe the actual
statements accurately. In particular, T5 identifies the reading of the prose
that its examples refute; it does not declare the printed prose itself false.
T7 and T8 instead contradict mathematical assertions in the canonical printed
statements, so their `refuted` labels and docstrings are appropriate.

T11's saved claim-stage classification is `broader`: its pair algebra allows
any `0<a≤b`, while reciprocal probability bounds imply `1≤a≤b`. This is a
correct generalization containing every canonical case, so the record's
`whole` decision remains correct. No claim-stage conclusion was changed after
reading the record.

The printed reading for T7 is: every nonempty sorted sample with
`0<α≤β≤1` has the stated optimal threshold vectors and interval range at
the printed first cuts. Its refutation meets every relevant condition:

1. The sample `(0,1)` is real, sorted and nonempty; the valid cut range is
   exactly zero and one.
2. Bounds `α=1/2,β=1` are positive and ordered, with `γ=2`.
3. A two-unit population with equiprobable samples `{1}` and `{0,1}` has
   actual inclusions `(1/2,1)` and produces the full sample with probability
   `1/2`; its inclusion indicators are independent.
4. The printed lower cut is zero and has value `1/2`. Feasible original-scale
   weights `(2,1)` have value `1/3`, with denominator three. This contradicts
   lower optimality and the claimed range without any undefined quantity.

The printed reading for T8 is: the printed class first-cut vectors optimize
(6) and (7) in the finite-design/Brewer setting, with the stated endpoint
formulas. Its refutation also meets the conditions:

1. Six units with outcomes `(0,0,1,1,2,3)` give the four distinct sorted,
   nonempty outcome classes and sizes `(2,2,1,1)`.
2. Four equiprobable draws choose one unit from each of the first two pairs
   and always include the last two units. Actual inclusions are
   `(1/2,1/2,1/2,1/2,1,1)`, inside `[α,β]=[1/2,1]`; actual class totals
   are all one.
3. Independent repetitions exist by taking the countable product of this
   one-step finite law. No witness repeats one draw across replicates.
   All eight finite Assumption 2 comparisons also hold, although this
   optimizer refutation does not require that convergence condition.
4. The printed lower cut zero has value `3/2`; feasible weights
   `(2,2,1,1)` attain the genuine minimum `7/6` with positive denominator
   six. The invalid printed display at cut zero is a separate observation.
   Failure of the optimizer clause refutes the printed conjunction without
   needing a separate refutation of its sharpness sentence.

The definitions are ordinary finite ratios, reciprocal-probability boxes,
threshold vectors, actual finite-design marginal sums, class-fiber sums and
finite probability products. They neither encode optimality by definition
nor introduce conclusion-equivalent premises. Positive masses/weights and
nonempty finite index sets keep objective denominators positive and
attainable sets nonempty and bounded. The `Option`-valued lower display
records invalid one-based class indices as `none`; it does not use truncated
subtraction or real division by zero to manufacture a refutation. All uses
of natural subtraction and all square-root arguments are protected by
their hypotheses or concrete values. No problematic integral, conditional
law, limsup, or infinite-to-real conversion occurs.

Mathematical nonvacuity arguments are recorded separately for every target
in `findings.json`. They cover strict and equal bounds, singleton and tied
samples, positive class masses, the independent replication law, both quota
population pairs, the common-cap hypotheses, and both two-coordinate
branches. In particular, T3's extra conditional segment statement is paired
with unconditional existence of the cuts; its hypothesis is not being used
to replace the optimizer theorem.

The review followed the required order:

1. Read `brief.md`, verify the inventory without displaying claim contents,
   and read the Challenge/Defs sources and `closure.json` blind. Save
   `reading.md` before opening claims, record, or binding.
2. Read the canonical claims and standing assumptions; save and parse-check
   the eleven-entry `claim-stage.json` before opening record or binding.
3. Read `record.json` and then the binding metadata at the subsequent stage.
   Binding was used only for source/fingerprint identity checks, never as a
   semantic verdict. No referenced external production rows or build logs
   were opened.

All 341 closure entries were accounted for through their source expressions,
covering 216 distinct declarations, including 112 generated proof constants.
Every named source definition was read in full. Generated line-zero proof
constants were reviewed through their enclosing source expressions; their
compiled proof terms were not printed. No previous outcomes, handoff,
integration narrative, other campaign material, or old review was examined.
No web search, delegation, external messages, publication, commit, build,
production write, or `lake` invocation occurred.

The reproducible auxiliary check is `scratch/exact_audit.py`, with results
in `scratch/exact-audit.json`: **4,025 exact assertions passed**. It uses
Python `Fraction` arithmetic and exact binomial cardinalities. It checks
the concrete laws and residuals, independent finite-product instances,
Assumption 2 comparisons, threshold/increment/partition cases including
boundary data, quota marginals, population/estimator identities, rounding,
odds thresholds by exact squaring, and pair identities. The threshold grid
has 204 total cases, including 102 unit-mass sample cases and 42 strictly
ordered class cases. These finite checks corroborate the semantic analysis;
they do not prove universal real-box results, continuity, or countable
product independence. Those were assessed mathematically from the definitions.
No quota family of enormous cardinality was enumerated.

**No scratch Lean was compiled.** The provided local Lean executable exists,
but `LEAN_PATH` was unset, neither the packet build path nor the toolchain
contained `Mathlib.olean`, and the packet contained no dependency tree.
Authorized SSH preflight failed with `Operation not permitted` before remote
execution. No remote dependency path, free-space condition, remote hash, or
compilation is claimed. The exact blocked command, scoped for a parent/runtime
with network access, is:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 dbl-ws 'cd /home/ubuntu/sap/assure/independent-fw-20261105/P025a-doc-v2 && pwd && df -BG . && cat /home/ubuntu/sap/tools/sap-lean && cat /home/ubuntu/sap/tools/lean_path.txt'
```

No credentials, network route, or sandbox settings were changed. The brief
permits mathematical nonvacuity arguments when compilation is not feasible;
that is the basis of the per-target nonvacuity entries.

Final validation parses both JSON review outputs, requires exactly one entry
per closure target, compares every target ID and full fingerprint with
`closure.json`, and checks the verdict/severity/issues rules. All eleven
fingerprints also match binding metadata; all twelve binding source hashes
match the files and inventory. All 43 inventoried input hashes, plus the
inventory's own hash, remain unchanged. Only the four requested outputs and
the auxiliary files under `scratch/` were written.

Saved output SHA-256 values before this report:

```text
reading.md       9767736d865d7de9702a51a210f36a1a805ec1c0e5aab9fe8d6827a1f3bd8a76
claim-stage.json f48936dfef1a11c8301b0961f201fa4a5d66972d8db8252ed7e155b3502e069f
findings.json    e0e488aaf4d1680cd97bbd566af173e2f68a56bea22c3fa38339950305e18f6b
```

The final response supplies all four output hashes, including this report.
