P013b packages only the 13 targets assigned in `work.json`.

| Decision | Count |
| --- | ---: |
| whole | 11 |
| restricted | 1 |
| refuted | 1 |
| omitted | 0 |

All thirteen theorems, `SAP.P013b.T15`–`T27`, are proved in
`SAP/P013b/Solution.lean`. There are no omitted targets or open glue tasks.
T18 refutes a positive canonical assertion. T21, T23 and T25 establish canonical
claims that already specify counterexamples, so their decisions are `whole`.

P013-T20 is `whole`. Under independent exact-design-law replication, its theorem
retains both almost-sure matrix limits on one event, every exposure and entry, and
identity smoothing, including the same-exposure limit for `K = 1`. The usual
measure-theoretic conditions are assumed. The source row's `wrong_credit` status
is recorded only as proof provenance. The round-7 clarification supersedes the
previous source-based label; no mathematical statement or proof changes.

P013-T24 is `restricted`. It retains recorded-outcome expectations, lost-mean
identities, identification equivalences, the nonnegative-outcome sufficient
condition, exclusion identities, unequal Hajek factors, arithmetic and conditional
HT scaling. It omits verification of the reconstruction's actual 2050 students,
342 item nonrespondents, 151 survey nonrespondents and their zero coding; the
connection to the released orange-wristband indicator; reproduction of the twelve
rounded Table 2 estimates; and separate strictness of the sufficient-versus-necessary
loss condition. The scaling clause assumes cardinalities 2050, 1708 and 1899,
`item ⊆ S`, `survey ⊆ S`, positive weights and retention of every nonzero score
in both sets. It neither assumes nor establishes `item ⊆ survey`; containment of
survey nonrespondents among item nonrespondents is omitted. No assertion concerns
the authors' unavailable outcome file.

## Definitions and proof route

The shared-Defs route uses eleven numbered Defs parts and `Defs/WholeW1.lean`.
They import only Mathlib and earlier SAP definitions; the root imports them all.
Challenge and Solution share the same compiled definitions. Exact finite-design
moments are real weighted sums. Population observation encodes Conditions 1–2.
No project declaration is redefined under its original fully qualified name.

Bridge parts 1–4 use fieldwise adapters for designs, populations, experiments and
sequences. Finite sums and conditions reduce by definition; equality lemmas use
`rfl`, and condition equivalences use `Iff.rfl`. Part5's
[simulation_matrices_pair](/home/ubuntu/sap/wt/ARCH-P013b/SAP/P013b/Bridge/Part5.lean:19)
transports the existing IID matrix-limit theorem with an unused zero-outcome table.
`simulation_matrices_iid` collects the finitely many exposure labels on one event
using `ae_all_iff`. To cover the same-exposure limit even for `K = 1`, it relabels
exposures by `Fin.castSucc` into `Fin (K + 1)` and pairs each with the unused label
`Fin.last K`. Indicator agreement follows by `Fin.castSucc_inj`. This is
instantiation, transport and conjunction of the existing limits.

The remaining Solutions instantiate and conjoin existing results. Additional glue
rewrites exported numeric tables, evaluates finite Boolean cases and normalizes
fixed arithmetic. T22(f) instantiates `fixed_count_calibration` on a two-unit
example. T25 reuses the exact school marginals and joint probabilities, and T26
reuses T25's explicit support witness. The manifest records these sources.
The supplied `WH/W1` proofs remain an unused illustration of failure for perfectly
dependent replicates with correct marginal laws; they are not T20's proof.

The clause audit retains the full T21 errors and residuals, all six corrected T22
parts, the three-world T23 record and respondent comparison, and the school support,
joint-law and variance examples in T25–T26. T16 follows its enumerated finite
statements. T27 states the supplied formal wearing-outcome reading; contextual
empirical estimates and Hajek/WLS descriptions are not its conclusions. Its student
frame includes peers outside the analysed sample, and its undirected within-school
network assumptions are retained.

Marginal and population-size denominators have positive hypotheses where needed.
School supports are nonempty; abstract half-marginal premises exclude an empty
support. Variable variance inputs have positive denominators. T16 retains the
claim's express zero-count Hajek convention. T20's cross denominator is positive
for `R ≥ 1`; the initial `R = 0` value does not affect convergence. Wald levels
lie strictly between zero and one. T18's negative-variance convention and its
negligible effect on the source witness are disclosed below. The literal printed
dependency antecedent is preserved.

The comparator configuration lists all thirteen theorem names, an empty definition
list, the three permitted dependencies and the prescribed external kernels.
The supplied `verification/comparator-result.json` certifies an earlier snapshot;
it is not presented as a certificate for the current package.

## Referee round 1, revision 2

The following sections record decisions at each round. Round 7 supersedes T20's
earlier provenance-based classification.

Both reports were checked against the canonical statements and source signatures.

| Target | Both referees' verdict | Resolution |
| --- | --- | --- |
| T15 | correct_whole | All four mathematical clauses retained. |
| T16 | correct_whole | All enumerated finite clauses retained. |
| T17 | correct_whole | Both misspecified expectations retained. |
| T18 | correct_whole | Refutation retained, now labelled `refuted`. |
| T19 | correct_whole | Consistency claim retained. |
| T20 | omission_questionable | Superseded by the explicit reuse clarification and subsequent positive theorem. |
| T21 | correct_whole | Full three-unit certificate retained. |
| T22 | correct_whole | Six corrected parts and calibration retained. |
| T23 | correct_whole | Full three-world certificate retained. |
| T24 | restriction_inaccurate | Accepted: inter-set nesting is explicitly omitted. |
| T25 | correct_whole | Full school counterexample retained. |
| T26 | correct_whole | Counts, joint laws and student clauses retained. |
| T27 | correct_whole | Formal wearing-outcome reading retained. |

T24's disclosure was corrected because
[its premises](/home/ubuntu/sap/wt/ARCH-P013b/SAP/P013b/Defs/Part8.lean:116)
contain only the two subset relations into S. Nonnested respondent sets can satisfy
all of them. T20's initial omission treated `wrong_credit` as excluding all reuse;
the later explicit clarification permits exact-statement reuse as `restricted`.

## Declaration review round 1

Both minor docstring findings were accepted. T15 now attaches strictly positive
off-diagonal cross joints to the first covariance guarantee and its equality case;
the adjusted covariance and effect-variance guarantees allow arbitrary joints, as
[T15Statement](/home/ubuntu/sap/wt/ARCH-P013b/SAP/P013b/Defs/Part5.lean:16) requires.
T25 describes a 56-school population with exactly two nonzero hosted potential
outcomes, as specified by
[the school definitions](/home/ubuntu/sap/wt/ARCH-P013b/SAP/P013b/Defs/Part4.lean:15).
No mathematical statement changed in that round.

## Declaration review round 2

The T20 omission finding was accepted under the explicit reuse clarification.
The existing IID theorem was packaged as a restricted positive result using
`Defs/Part11.lean` and `Bridge/Part5.lean`. A subsequent supplied whole-version stage
introduced `Defs/WholeW1.lean` and the `WH/W1` repeated-draw certificate and temporarily
switched T20 to a refutation. Round 4 restored the positive IID theorem.

## Declaration review round 3

| Declaration/reviewer | Finding | Resolution |
| --- | --- | --- |
| T18 / r5g1 | faithful / none | Retained; source proof checked. |
| T18 / opus-o1 | junk_value / minor | Accepted disclosure issue; checked the actual witness bound. |
| T20 / r5g2 | faithful / none | Retained the supplied refutation in that round. |
| T20 / opus-o2 | not_faithful / major | Initially disagreed over the sampling reading; superseded by round 4. |

T18 counts a negative variance estimate as noncoverage. Its docstring now says so.
The source witness refutes coverage along even population sizes `N = 2k + 4`.
Its exported
[split-estimator identity](/home/ubuntu/sap/wt/ARCH-P013b/AronowAudit/P013/Wave1/PrintedWaldBlueprint.lean:283),
nonnegative ratio (`n14_proof`) and nonnegative true variance imply negative
estimates lie outside the all-split event. The exported
[complement bound](/home/ubuntu/sap/wt/ARCH-P013b/AronowAudit/P013/Wave1/PrintedWaldBlueprint.lean:227)
is `1/N`. The glue check
[scratch/T18DefinedIntervalCheck.lean](/home/ubuntu/sap/wt/ARCH-P013b/scratch/T18DefinedIntervalCheck.lean:14)
proves this bound from those facts and probability monotonicity, with the three
permitted dependencies. Changing the treatment of undefined intervals changes
coverage on this subsequence by at most `1/N`, which tends to zero; it cannot
remove the strict limiting gap in
[the source assembly](/home/ubuntu/sap/wt/ARCH-P013b/AronowAudit/P013/Wave1/PrintedWaldBlueprint.lean:360).
This implements the reviewer's minimal alternative without changing the definition
or adding a probabilistic proof.

The earlier T20 disagreement concerned the absence of an explicit independence
premise in the
[canonical quotation](/home/ubuntu/sap/wt/ARCH-P013b/work.json:872) and the
[precedence rule](/home/ubuntu/sap/wt/ARCH-P013b/brief.md:30) for diagnostic notes.
That round's retained marginal-law-only refutation and its proof credits were
superseded in round 4. `Defs/WholeW1.lean` was routed through the common root Defs;
Challenge parts import only that root. Both sides share the same compiled bodies.

## Declaration review round 4

T20 / r6g2, `not_faithful/major`: accepted the scope correction. The repeated-draw
witness is perfectly dependent and does not refute independent replication.
The four issue threads were addressed: T20 again states the positive
`T20Statement`; its Solution uses the existing IID row through the Bridge; its
docstring no longer calls the printed claim false; and the manifest credits the
positive row, not the unused counterexample.

The suggested `whole` label was not adopted under that round's reuse rule.
The later claim-relative clarification in round 7 supersedes that classification.
No new limit argument was written.

## Third-rung revision (Opus)

The supplied revision removed the misleading description of arbitrary dependent
couplings and the appendix's without-replacement wording as omitted canonical cases.
It also found that the previous common `d ≠ e` premise excluded the same-exposure
limit for `K = 1`. The strengthened T20Statement places both limits on one event for
every exposure and entry, requiring `d ≠ e` only for the cross limit. The Bridge
uses the relabelling described above. The existing theorem names were retained.
The supplied revision's type and dependency checks are in `scratch/third-rung-*`.
These mathematical definitions and proofs are unchanged in round 5.

## Declaration review round 5

| Reviewer / finding | Resolution at that round |
| --- | --- |
| r7g2 issue 1; r8g2 issue 1: `label_wrong/minor` | Accepted complete mathematical coverage, but kept `restricted` under the then-explicit reuse rule; superseded by round 7. |
| r7g2 issue 2: dependent sampling described as omitted canonical scope | Fixed in the supplied third-rung revision. |
| r8g2 earlier-issue 2: fixed | Agreed; neither appendix wording nor arbitrary dependent coupling was an omitted canonical case. |
| T21, T22, T23, T24: faithful / none | No changes. |

The docstring and manifest distinguished complete independent-replication coverage
from provenance; independence was no longer described as an added canonical
hypothesis. The earlier label followed
[revise-fw5.md:12](/home/ubuntu/sap/wt/ARCH-P013b/revise-fw5.md:12) and the
[source status](/home/ubuntu/sap/wt/ARCH-P013b/work.json:1038), not a missing limit.
Round-5 compilation, all thirteen permitted dependency lists and identical
Challenge/Solution types passed; see `scratch/declaration-round5-validation.json`.

## Declaration review round 6

| Declaration / finding | Resolution at that round |
| --- | --- |
| T20 / r9g2: `label_wrong/minor` | Accepted complete matrix-limit coverage, but retained the label required by the then-current reuse rule; superseded by round 7. |
| T21, T22, T23, T24: faithful / none | Retained without changes. |

The previous disagreement cited
[revise-fw6.md:12](/home/ubuntu/sap/wt/ARCH-P013b/revise-fw6.md:12), which expressly
required `restricted` for this source reuse. The proof note recorded that rationale.
No Lean source changed. All 25 SAP modules recompiled, all thirteen dependency lists
were permitted, and Challenge/Solution types matched; see
`scratch/declaration-round6-validation.json`.

## Declaration review round 7

| Declaration / finding | Resolution |
| --- | --- |
| T20 / r10g1: `label_wrong/minor` | Accepted: set `decision` to `whole` and `restriction` to null; revised the Challenge docstring and proof-credit note. |
| Earlier label issue: not fixed | Fixed by this revision. |

The finding, report and blind reading were checked against
[T20Statement](/home/ubuntu/sap/wt/ARCH-P013b/SAP/P013b/Defs/Part11.lean:21),
[the canonical claim](/home/ubuntu/sap/wt/ARCH-P013b/work.json:872) and the source
matrix-limit theorem. The statement retains both canonical limits with identity
smoothing, every exposure and entry on one probability-one event, and the
same-exposure limit when `K = 1`. Independent whole-design replication is the
printed reading being audited; independence remains an explicit substantive
hypothesis in Lean, rather than being classified as a measure-theoretic condition.
The docstring expressly says that the usual measure-theoretic conditions are
assumed. Its initial zero-replicate cross ratio remains irrelevant to convergence.

The clarified
[claim-relative label rule](/home/ubuntu/sap/wt/ARCH-P013b/revise-fw7.md:13) supersedes
the earlier provenance-based instruction. T20 is now `whole`; the manifest's
restriction is null. Its proof note separately records the
[source row's final credit status](/home/ubuntu/sap/wt/ARCH-P013b/work.json:1038)
and exact-statement reuse, as allowed by
[the clarified reuse rule](/home/ubuntu/sap/wt/ARCH-P013b/revise-fw7.md:12).
No canonical matrix-limit clause is dropped. T24 remains `restricted` for the
substantive omissions listed above, rather than for measure-theoretic conditions.
The manifest generator was updated, and the comparator configuration regenerated
with the same thirteen theorem names and required settings.

Only T20's Challenge docstring changed among the Lean sources. Every shared
definition, theorem statement, theorem name and proof remains unchanged. No new
mathematical argument was introduced.

Round-7 validation recompiled all 25 SAP modules in dependency order and reran
`#print axioms` for all thirteen targets. Every list is exactly `propext`,
`Classical.choice`, `Quot.sound`, matching the manifest. The only warnings are the
thirteen expected Challenge placeholders in `scratch/declaration-round7-build.log`.
Challenge and Solution have identical elaborated theorem types and universe lists
for all thirteen names, also unchanged from round 6; see the two
`scratch/declaration-round7-*-types.log` files. Both JSON files parse. Target and
row accounting, imports, required options, token checks and line limits pass.
Saved hashes confirm all shared definitions and proof sources are unchanged.
Structured results are in `scratch/declaration-round7-validation.json`.
No tracked project source changed. There are no open glue tasks.
