# P019b Challenge package

The current package covers exactly P019-T12 through P019-T22: **5 whole,
6 restricted, 0 refuted, 0 omitted**. All eleven Challenge theorems have
Solutions under the same fully qualified names. There are **0 open glue tasks**.

| Targets | Decision |
| --- | --- |
| T12, T13, T15, T17, T21 | whole |
| T14, T16, T18, T19, T20, T22 | restricted |

The current scope supersedes the earlier round-1 labels and the intermediate
whole-version switch recorded before round 2. In particular, T22 is a
restricted result, not a refutation of the printed assertion.

## Restricted targets

- **P019-T14:** All population conclusions (i)–(v) are retained on finite
  underlying probability spaces with arbitrary real atom masses. The truthful
  identities `Y = Q` and `X = R or Q` are pointwise. The extension to arbitrary
  measurable spaces with almost-sure truthful identities is not stated.
- **P019-T16:** Only the population contrast of the printed ceiling mechanism
  is retained, for the exact Binomial(4,2/5) baseline and an independently mixed
  affected share. The liar and false-confessor response rules, all rejection
  probabilities including the approximately 80% and 30% examples, the power
  curves, and their asserted dependence on sample size or violation share
  are omitted. A response-rule identity does not establish rejection power.
- **P019-T18:** The actual scaled variance limit and equation (3) are retained
  for every fixed empty-cell completion, only for iid draws on finite
  underlying probability spaces with arbitrary real atom masses. The extension
  to arbitrary measurable underlying spaces with bounded list counts is omitted.
- **P019-T19:** Positivity of the limiting variance, root-n tightness, the
  Gaussian limit, scaled plug-in consistency, and Wald coverage are retained
  for all fixed completions. They are stated only for iid draws on finite
  underlying probability spaces with arbitrary real atom masses. Arbitrary
  measurable underlying spaces with bounded list counts are omitted.
- **P019-T20:** Both actual scaled variance limits and their strict comparison
  are retained for all fixed cell and arm completions, only for iid draws on
  finite underlying probability spaces with arbitrary real atom masses. They
  are not stated on arbitrary measurable underlying spaces with bounded counts.
- **P019-T22:** The population identity under Assumption 3 and positive arms,
  and the studentized normal and p-value limits under Assumptions 3–4, are
  retained for finite underlying probability spaces with arbitrary real atom
  masses and fixed completions. The extension to arbitrary measurable spaces,
  the general randomized causal-effect interpretation, and the positive
  delayed-treatment design implication are not formalized. The additional
  finite protocol permits assignment disclosure before recording the direct
  answer and delays only physical list display. It establishes failure of
  independence under that display-only reading. It does not refute the
  printed delayed-treatment design assertion.

There are no omitted targets. T13's non-identification example is part of its
canonical claim and is not a claim that a printed mathematical theorem is false.

## Definitions, Bridges, and existing proofs

The shared-definition route is used. `Defs/Part1.lean` contains finite laws,
study data, assumptions, and population quantities. Part2 contains IID sampling
and completed sample statistics. Part3 contains Gaussian and convergence
notions and the finite CNN and ceiling witnesses. Parts4–5 contain the
original finite-law statement definitions.

`Defs/WholeW1.lean` contains the supplied arbitrary-space `WholeStudy`, almost
sure bounds and assumptions, finite observable encoding, population and beta
sampling correspondences, and the statement definitions used by T12, T13,
T17, T21, and T22. The name `T22WholeStatement` is retained for compatibility;
the manifest and docstring accurately classify its content as restricted.

The shared Defs modules import only Mathlib and earlier Defs. Challenge
imports only Defs. `Bridge.lean` adapts the finite law and study records to
the project structures, preserving every field. Its correspondences for
finite expectations, conditioning, assumptions, IID laws, estimators,
variances, convergence, normal quantities, and witnesses are proved by `rfl`
or `Iff.rfl`.

The supplied `WH/W1/P/T12_L1.lean` through `T12_L4.lean` already prove finite
observable encoding, population transport, independence transport, and beta
sample-law transport on arbitrary measurable spaces. `WH/W1/Leaves.lean`
assembles these into the existing T12, T17, and T21 general-space results;
it also assembles the complete CNN witness and the finite display protocol.
`WH/W1/Proofs/` supplies the proved wrappers used by Solution. These proof
extensions were present before this revision. This revision adds no
mathematical argument, proof leaf, or hypothesis.

The unchanged finite-space Solutions instantiate the credited project
results through Bridge. T14 also uses the existing `prob_false`,
`cell_probability`, `list_mean_identified`, and `mean_bit` helpers; its
additional excess and equality formulas are elementary algebra on exported
facts. T15 combines the existing two-tail result and pooled-variance identity.
Its n = 50 null example specializes the equality case, identifies the two
coincident tails as 1/40, and sums them to 1/20. No held null-example theorem
is used. T18–T20 do not export the additional sample-statistic transport
needed for their arbitrary-space conclusions.

All manifest rows have an explicit disposition. The duplicate unused entry
for `placebo_one_identity` in T21 was removed because the supplied whole
proof already lists it among used declarations. There are no open glue tasks.

## Defined quantities and sampling conventions

Positive probabilities guard population conditional quantities explicitly or
through nondegeneracy. The standing assumptions also give positive engagement
mass for the truth-rate denominator. Every quantile is used at an interior
normal probability; Gaussian measure values are finite. Bounded measurable
observables and bounded continuous Gaussian test functions have the required
integrability in the supplied general-space results.

All sample conclusions use the full IID law, including deficient samples.
Empty cell or arm means have arbitrary fixed real completions. A component
sample variance is zero below two observations; the entire estimated variance
has a fixed completion where its formula is undefined. A nonpositive estimated
variance gives studentized value zero and p-value one. These conventions
state limits of defined statistics and do not assert inference at an undefined
finite-sample ratio. No exact Monte Carlo percentage, R execution, or regenerated
figure is certified; T15 concerns analytic normal planning power.

Finite observable range makes a reduction mathematically possible, but does
not itself state an arbitrary-space theorem. The restrictions on T14 and
T18–T20 acknowledge the domain of the actual exported quantifiers.

## Declaration review round 1

The T21 `label_wrong`, major finding was accepted: its original finite
statement lacked the shifted conditional-distribution identity in canonical
`definitions_needed`. Round 1 marked it restricted and documented the omission.
See the [round-1 finding](fw/round1/T21/r1g2/findings.json) and
[report](fw/round1/T21/r1g2/REPORT.md:7).

Before round 2, supplied whole versions switched T12, T13, T17, T21, and T22
to their proved wrapper theorems. T21 now states the shifted-law identity
and its distributional-testing consequence on arbitrary measurable spaces,
together with the population and inferential conclusions, so its round-1
omission is resolved. T12, T13, and T17 also retain their supplied broader
versions. Round 2 specifically corrects the scope and interpretation below.

## Declaration review round 2

All five listed findings are accepted; there are no disagreements.

- **T14, `not_faithful`, major:** The quantifier in
  [T14Statement](SAP/P019b/Defs/Part4.lean:31) requires `Fintype`. Its
  canonical calculation imposes no finite underlying-space premise.
  Changed the manifest from whole to restricted and disclosed both the
  finite-space domain and pointwise truthful identities in the Challenge
  docstring. All numerical conclusions remain stated. See the
  [finding](fw/round2/T14/r5g1/findings.json) and the canonical claim in
  [work.json](work.json:147).
- **T18, `not_faithful`, major:**
  [T18Statement](SAP/P019b/Defs/Part5.lean:12) exports the actual variance
  limit only on finite spaces. Changed whole to restricted and disclosed the
  missing arbitrary-space extension in the manifest and Challenge docstring.
  See the [finding](fw/round2/T18/r5g2/findings.json) and
  [canonical claim](work.json:456).
- **T19, `not_faithful`, major:**
  [T19Statement](SAP/P019b/Defs/Part5.lean:17) contains all five inference
  clauses, only on finite spaces. Changed whole to restricted and disclosed
  that domain in both locations. See the
  [finding](fw/round2/T19/r5g2/findings.json) and
  [canonical claim](work.json:625).
- **T20, `not_faithful`, major:**
  [T20Statement](SAP/P019b/Defs/Part5.lean:29) contains both variance limits
  and the strict comparison, only on finite spaces. Changed whole to restricted
  and explicitly omitted their arbitrary-space extension. See the
  [finding](fw/round2/T20/r5g2/findings.json) and
  [canonical claim](work.json:767).
- **T22, `not_faithful`, major:** The
  [protocol](SAP/P019b/Defs/WholeW1.lean:251) discloses assignment at time 0,
  records an assignment-dependent direct answer at time 1, and displays the
  list at time 2. It does not establish that the direct answer precedes all
  assignment-dependent exposure. Withdrew the refuted label; changed the
  manifest to restricted; corrected both the Challenge and statement-definition
  docstrings. The valid null/inference bundle and all concrete protocol facts
  remain proved. The record now discloses the omitted general causal-effect
  interpretation, positive delayed-treatment design implication, and
  arbitrary-space inferential extension. See the
  [finding](fw/round2/T22/r5g3/findings.json),
  [review interpretation](fw/round2/T22/r5g3/REPORT.md), and
  [canonical claim](work.json:1095).

No theorem name, statement body, proof body, or shared mathematical definition
was changed in round 2. Four inherited files exceeded 300 lines:
`Defs/WholeW1.lean`, `WH/W1/Leaves.lean`, `WH/W1/P/T12_L2.lean`, and
`WH/W1/P/T12_L4.lean`. Comments, blank lines, and wrapped theorem headers
were compacted to restore the size limit. Comparing source tokens after
removing comments and whitespace confirms that all Lean mathematical content,
including all eleven Challenge types, is unchanged. No dependent declaration
acquires a new mathematical definition from this revision.

## Verification

All 21 SAP modules were recompiled sequentially with the supplied `sap-lean`
in dependency order; Lake was not run. Build order and output are preserved in
`scratch/P019bRound2BuildOrder.json` and `scratch/P019bRound2Build.log`.
`scratch/P019bAxioms.lean` reruns `#print axioms` for every Solution theorem;
all eleven report exactly `propext`, `Classical.choice`, and `Quot.sound`.
The output is in `scratch/P019bRound2Axioms.log`.

Both JSON files parse, the manifest covers exactly `unit_targets`, every
non-omitted theorem is proved, and the comparator lists exactly those eleven
names. Every SAP Lean file sets both implicit-variable options and is at most
300 lines. The only expected proof-placeholder warnings are in Challenge stubs.
No existing project source was edited.

The existing `verification/comparator-result.json` records an accepted
three-kernel comparison of the pre-round-2 snapshot. That historical record
is preserved; it does not certify the current revised source and metadata.
The regenerated `comparator.json` keeps the required modules, theorem names,
permitted foundations, and external-kernel commands. A fresh comparator run
is required for a current source certificate; this revision claims the full
Lean rebuild and dependency checks, not a newly run three-kernel certificate.
