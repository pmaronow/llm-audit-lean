# P001f packaging report

This unit contains only P001-T96 through P001-T114 from `unit_targets` in
`work.json`. Project sources, example units and referee packets were left intact.
The claim is the canonical statement plus definitions and standing assumptions;
audit notes add no hypotheses or conclusions.

| Decision | Targets |
| --- | ---: |
| whole | 7 |
| restricted | 9 |
| refuted | 2 |
| omitted | 1 |

There are 18 Challenge theorems, 18 proved Solution theorems, and no open glue
tasks. Whole targets are T96, T99, T100, T106, T109, T110 and T112. T96 and T99
state their canonical recorded counterexamples. T102 refutes a distributional
identification reading of PDA guidance and is restricted. T103 and T104
contradict assertions explicitly included in their canonical statements and
are refuted, with the partial scope below still disclosed. This classification
applies the latest [claim and refutation clarification](revise-ref2.md#L23).

## Scope restrictions and omission

- **T97 — restricted.** Starts from positive real arm masses and arbitrary real
  cell outcome sums with a positive common normalization. Omits part (i)'s
  raw-unit IPW regrouping and raw-data post-stratification identities and the
  transfer of the all-cell-sums quantifier to individual outcome vectors.
  Also omits Example 7.2.1 (p. 257), including its six-unit sample and its
  post-stratified estimate 4/9.

- **T98 — restricted.** Retains true-score conditional and unconditional
  mean-one arm-weight identities, positive-size sample-average expectation one,
  and strict expectation above one for the erroneous reciprocal weights. Omits
  the full stabilized outcome-estimator formula, fitted-score denominator
  convergence and efficiency claims. Binarity and the uniform two-sided bound
  are pointwise premises for every observation of an infinite iid sequence.

- **T101 — restricted.** Retains the corrected set-comprehension and
  intersection-with-complement identities. Omits the erroneous union formula's
  equality characterization, its covering/disjointness and complement-equality
  formulations, and all three numerical-example equalities. The ambient type
  supplies the universal set.

- **T102 — restricted.** Negates the reading that coordinate differentiability
  at every positive-density covariate value guarantees a common actual
  derivative at the covariate mean for all CEF versions, retaining the joint
  density premise. Retains the chosen-estimator plug-in formula with n > 0
  and differentiability at the sample mean. Omits the population-PDA definition
  identity for a fixed chosen CEF and the recommendation of discrete partial
  slopes. It does not deny the meaning of the derivative of a chosen extension.

- **T103 — refuted, with partial scope.** Refutes maximizer-existence assertion
  (A) for the actual unrestricted normal/lognormal/exponential mixture, even on
  positive samples. Omits (B)'s full-parameter consistency and asymptotic
  efficiency and any assessment of the plotted fit. Scales and rate are positive.

- **T104 — refuted, with partial scope.** Negates the unrestricted equivalence
  of equal positive-mass covariate supports and uniform two-sided positivity
  for countable joint-mass laws. Does not prove (A), separately isolate the
  directed failure in (B), resolve (C) under unspecified support conditions,
  or state Example 7.3.3's regional propensity values. Both arm masses are
  positive, joint masses are summable and normalized, and ratios are evaluated
  only on cells of positive total mass.

- **T105 — omitted.** The sole credited row negates a larger structural-rule
  contract for arbitrary real treatment. Its exported type lacks binary
  treatment and a predicate for the printed informational-completeness premise.
  Proof-only witness facts cannot strengthen that type by glue; no uncredited
  certificate was substituted.

- **T107 — restricted.** Retains only iterated expectation, Theorem 2.2.17.
  Drops total variance and every best-prediction component: the variance
  identity, MSE decomposition, nonnegative remainder, minimum-MSE inequality
  and residual-risk equality. The row for those components has final status
  wrong_credit and is excluded entirely.

- **T108 — restricted.** States the three formulas for positive-size initial
  segments of an infinite measurable iid sequence on the given space. Omits
  arbitrary fixed finite iid families and any transfer from such families.
  First-moment mean, second-moment variance and positive-variance Chebyshev
  scopes remain separate.

- **T111 — restricted.** Retains MCAR identification, discrete MAR identification
  with its summable weighted mean, vector MAR CEF identification and the worked
  estimates 3/4 and 7/9. Both MAR components explicitly retain population
  integrability of the respondent CEF m(X), instead of deriving it from MAR
  and overlap. Shared definitions supply the estimator formulas, evaluated only
  on the stated sample with nonzero denominators.

- **T113 — restricted.** Retains both double-robustness branches with the
  additional requirement that m(X) be integrable. Excludes correct-propensity
  cases where m(X) is nonintegrable but cancellation makes the combined score
  integrable. The canonical displayed expectations do not supply the separate
  nuisance moment; its diagnostic note adds no premise. See the referee response.

- **T114 — restricted.** Retains the population interval, width b-a, attainment
  of every interval value with identical observable joint law, and final sample
  ATE endpoints -2/6 and 4/6. Omits the four constituent potential-outcome sample
  estimates: upper E[Y(1)] = 5/6, lower E[Y(0)] = 1/6, lower E[Y(1)] = 3/6,
  upper E[Y(0)] = 5/6, and their individual imputation interpretations.
  Sharpness alternatives use the original space and unchanged treatment.

## Definitions, bridges and guards

The route is shared Mathlib-only definitions in `Defs/Part1.lean` through
`Part5.lean`. Challenge imports their root only; Solution imports the same
compiled root and Bridge and never imports Challenge. Every SAP Lean file
starts, after imports, with both required implicit-variable options disabled.

`Bridge/Part1.lean` gives correspondences for conditional means, eventwise
conditional independence, iid sequences, averages, densities, conditioning-event
means, finite-law operations, logistic likelihoods, the sample PDA formula and
mixture likelihoods/domains. These are definitional equalities or reflexive
equivalences, except finite event probabilities, whose identical finite sums
are compared by splitting on the same event predicate to accommodate different
decision procedures. Finite-law SAP statements use ordinary weight vectors;
the project structures occur only in Bridge.

`Bridge/Part2.lean` and `Part3.lean` transport the credited results. Additional
work is conjunction/projection, instantiation, cancellation of the positive
normalization in T97, finite arithmetic in T96 and T99, elementary algebra for
T100's weighted identities and equality case, the count-of-ones sum identity
in T110, and choosing the existing epsilon in T112. The PDA-reading contract
and countable overlap contract have explicit reflexive correspondences.
No substantive proof of a missing clause was added. All unused credited rows
and their reasons are recorded in `manifest.json`.

Probability-to-real conversions occur under probability measures. Conditioning
means have positive arm probabilities, averages have positive n, and cell
formulas have positive arm masses and interior propensities. The fixed ATT
law has masses 3/4 and 1/4. The missing-data sample has four respondents, three
and one in its two cells. T109 retains a square-integrable outcome so polynomial
prediction risks on its bounded interval are finite; minimizer existence and
approximation for every minimizing family are both asserted. T102 uses actual
derivative existence in its negation and guards the sample formula by actual
differentiability. Mixture scales are positive. No listed theorem uses a
nonintegrable mean, zero conditioning divisor or infinite probability conversion
as the value of a quantity the canonical claim presupposes exists.

## Round 1 findings and response

Both [A](referees/round1/a/findings.json) and
[B](referees/round1/b/findings.json) were checked. This table records the actions
at that stage; the round 2 classification clarification below supersedes the
three labels it identifies.

| Target | A | B | Action at round 1 |
| --- | --- | --- | --- |
| T96 | correct_whole | correct_whole | Counterexample retained; then labelled refuted. |
| T97 | correct_restricted | correct_restricted | Unchanged. |
| T98 | correct_restricted | correct_restricted | Unchanged. |
| T99 | correct_whole | correct_whole | Counterexample retained; then labelled refuted. |
| T100 | correct_whole | correct_whole | Unchanged. |
| T101 | correct_restricted | correct_restricted | Unchanged. |
| T102 | correct_whole | correct_whole | Negation retained; then labelled refuted. |
| T103 | correct_restricted | correct_restricted | Refuted label with partial scope retained. |
| T104 | correct_restricted | correct_restricted | Refuted label with partial scope retained. |
| T105 | omission_ok | omission_ok | Omission retained after checking the credited row. |
| T106 | correct_whole | correct_whole | Unchanged. |
| T107 | correct_restricted | correct_restricted | Unchanged; wrong_credit row excluded. |
| T108 | restriction_inaccurate | correct_whole | Accepted A: disclosed infinite-sequence restriction. |
| T109 | correct_whole | correct_whole | Unchanged. |
| T110 | correct_whole | correct_whole | Unchanged. |
| T111 | correct_restricted | correct_restricted | Unchanged. |
| T112 | correct_whole | correct_whole | Unchanged. |
| T113 | restriction_inaccurate | restriction_inaccurate | Declined whole relabelling; clarified extra nuisance moment. |
| T114 | correct_restricted | correct_restricted | Unchanged. |

T108's [canonical statement](work.json#L902) is for finite families, while
[IndependentCopies](SAP/P001f/Defs/Part1.lean#L34) demands an infinite sequence.
A fair Bernoulli observation on a two-atom space cannot be extended to a second
independent fair observation there. The restricted label and disclosure remain.

## Round 2 findings and current clarification

Read all findings and reports from [A](referees/round2/a/findings.json) and
[B](referees/round2/b/findings.json). No `reading.md` was staged in either
round 2 directory; their reports refer to the preserved round 1 readings,
which were consulted. Both accept the mathematical Lean propositions.

| Target | A | B | Current action |
| --- | --- | --- | --- |
| T96 | correct_whole | correct_whole | Full canonical counterexample retained; whole under latest claim rule. |
| T97 | correct_restricted | correct_restricted | Unchanged. |
| T98 | correct_restricted | correct_restricted | Unchanged. |
| T99 | correct_whole | correct_whole | Full canonical counterexample retained; whole under latest claim rule. |
| T100 | correct_whole | correct_whole | Unchanged. |
| T101 | correct_restricted | correct_restricted | Unchanged. |
| T102 | correct_whole | correct_whole | Restricted; docstring identifies distributional reading and omitted content. |
| T103 | correct_restricted | correct_restricted | Direct refutation and partial scope retained. |
| T104 | correct_restricted | correct_restricted | Direct refutation and partial scope retained. |
| T105 | omission_ok | omission_ok | Omission retained. |
| T106 | correct_whole | correct_whole | Unchanged. |
| T107 | correct_restricted | correct_restricted | Unchanged. |
| T108 | correct_restricted | correct_restricted | Accepted confirmation of fixed disclosure. |
| T109 | correct_whole | correct_whole | Unchanged. |
| T110 | correct_whole | correct_whole | Unchanged. |
| T111 | correct_restricted | correct_restricted | Unchanged. |
| T112 | correct_whole | correct_whole | Unchanged. |
| T113 | correct_restricted | restriction_inaccurate | Retained restricted; current governing instruction resolves B's premise. |
| T114 | correct_restricted | correct_restricted | Unchanged. |

**T113.** A withdraws its old objection. B still relies on the
[diagnostic note](work.json#L1329) and says the note-precedence rule was absent
from its review packet. The current governing instruction now expressly supplies
that rule in [What the claim is](revise-ref2.md#L23). The report now cites this
clarification directly, resolving the disputed review-context citation.
I disagree with B's proposed whole label: the [canonical formula](work.json#L1327)
and [definitions](work.json#L1328) require E[Y] and the complete-score expectation,
not E[m(X)]. The standing convention guards displayed expectations.
The [credited row](AronowAudit/P001/Wave1/MissingDr.lean#L29) separately assumes
population integrability of m(X), with final status narrower.

The cancellation example checks the distinction: independent uniforms X,U on
(0,1), Y=0, R=1 for X<1/2 and otherwise I(U<1/2), q=p equal to 1 below 1/2
and 1/2 above, and m(x)=1/x for 0<x<1/2, zero elsewhere. Both response arms
have positive mass (3/4, 1/4), MAR holds with lower bound 1/4, and the score is
identically zero. Its two displayed expectations exist, while the integral
of |m(X)| diverges. All score divisors are 1 or 1/2. This is a scope check,
not a new Lean proof or an assumption added from review history. Both referees
accept its calculation. The existing restricted statement and proof are kept.

**Classification under the latest clarification.** T96 and T99's canonical
statements themselves record the full counterexamples, including the asserted
numerical facts ([T96](work.json#L54), [T99](work.json#L285)). Their theorems
establish these assertions rather than contradict them, so they are whole;
the false-claim opening was removed. T102's [canonical guidance](work.json#L458)
and [support-domain definition](work.json#L459) do not explicitly assert a
common derivative for every global CEF extension. Its exported negation targets
that distributional identification reading. It is restricted, its docstring
names the reading, and it no longer announces that the printed claim is false.
This supersedes the round 2 referees' acceptance of those three earlier labels.

T103's [canonical assertion (A)](work.json#L551) explicitly asserts maximizer
existence for every sample; its negation directly contradicts that assertion.
T104's [canonical assertions (A) and (B)](work.json#L600) jointly imply the
countable overlap/positivity equivalence negated by its theorem. Those two
refuted labels and required opening notices remain, with all omissions listed.

## Declaration review round 1

Accepted the minor T97 finding in
[the declaration review](fw/round1/T97/r1g1/findings.json). Its two issues were
the same missing omission in the Challenge docstring and manifest restriction.
The six-unit illustration and post-stratified estimate 4/9 belong to the
canonical `definitions_needed`, not an audit note ([work.json:126](work.json#L126)).
`T97Statement` contains only the cell-sum characterization, so the illustration
is absent. Both restriction descriptions now explicitly omit Example 7.2.1
(p. 257), its six-unit sample and the 4/9 estimate; the scope list above agrees.
The decision remains restricted. No shared definition, theorem statement, proof,
or theorem name changed. Comparator configuration still lists all 18 proved
theorems, and all required compilation and dependency checks were repeated.

## Verification

Recompiled all five Defs parts and root, all three Bridge parts and root,
Challenge part and root, and Solution, in dependency order with
`/home/ubuntu/sap/tools/sap-lean`. All succeeded. Only documentation and metadata
changed; the mathematical contents and all 18 proved theorem names were retained.

- Reran `#print axioms` for all 18 proved theorems in `scratch/P001fAxioms.lean`.
  T101 has none; the other seventeen use exactly `propext`, `Classical.choice`
  and `Quot.sound`. The manifest records the refreshed results.
- Loaded separate Challenge and Solution environments with
  `scratch/P001fCompareTypes.lean`: all 18 theorem types/universe parameters and
  all 96 shared SAP declarations, including definition bodies, are identical.
- Parsed both JSON files; checked every target and credited row, theorem-list
  agreement, proof status, dependency whitelist, imports, the two initial options,
  stub placement, decision notices and the 300-line file limit.

Latest build log: `scratch/P001fDeclarationRound1Build.log`; expected placeholder warnings are
recorded without the reserved proof token. The staged
[Comparator result](SAP/P001f/verification/comparator-result.json) dated
20261103T212511Z reports acceptance of the earlier snapshot by all three kernels,
with its [log](SAP/P001f/verification/comparator.log). That record is preserved.
The current snapshot differs only in Challenge/Part1 documentation, the PDA
definition's comment, and manifest classifications/disclosures. All mathematical
sources are unchanged. The prior certificate is not a byte-identical certificate
of these revised files. No fresh external run was performed: the configured
kernel commands are absent from PATH. The current environment comparison is an
identity check. No open glue tasks remain.

## Whole versions (new proofs)

The following seven targets now use their supplied whole statements and proved
whole theorems. This section supersedes their earlier scope restrictions and
classification notes. Their Challenge stubs are in
`SAP/P001f/Challenge/Part1.lean`; their proved exports are in
`SAP/P001f/Solution.lean`. The resulting decisions are 14 whole,
2 restricted, 2 refuted and 1 omitted.

- **P001-T97 (`SAP.P001f.T97`) — whole.**
  Statement: `SAP.P001f.T97WholeStatement`; proof: `SAP.P001f.WH.W1.T97_whole`.
  Files: `SAP/P001f/Defs/WholeW1.lean`, `SAP/P001f/WH/W1/Leaves.lean`, `SAP/P001f/WH/W1/P/T97_L1.lean`, `SAP/P001f/WH/W1/P/T97_L2.lean`, `SAP/P001f/WH/W1/Proofs/T97.lean`.
  Removed restriction: Starts from positive real treated/control cell masses and arbitrary real cell outcome sums, with positive common sample-size normalization. Omits part (i): raw-unit regrouping of IPW and the raw-data post-stratification identity. Does not transport the all-cell-sums quantifier to individual outcome vectors. Also omits Example 7.2.1 (p. 257), including its six-unit sample and its post-stratified estimate 4/9.

- **P001-T101 (`SAP.P001f.T101`) — whole.**
  Statement: `SAP.P001f.T101WholeStatement`; proof: `SAP.P001f.WH.W1.T101_whole`.
  Files: `SAP/P001f/Defs/WholeW1.lean`, `SAP/P001f/WH/W1/Leaves.lean`, `SAP/P001f/WH/W1/Proofs/T101.lean`.
  Removed restriction: Retains only the corrected relative-complement/set-comprehension identity in the ambient universal type. Omits the characterization of the erroneous union identity, its covering/disjointness and complement-equality formulations, and all three numerical-example equalities.

- **P001-T107 (`SAP.P001f.T107`) — whole.**
  Statement: `SAP.P001f.T107WholeStatement`; proof: `SAP.P001f.WH.W1.T107_whole`.
  Files: `SAP/P001f/Defs/WholeW1.lean`, `SAP/P001f/WH/W1/Leaves.lean`, `SAP/P001f/WH/W1/P/T107_L1V2.lean`, `SAP/P001f/WH/W1/Proofs/T107.lean`.
  Removed restriction: Retains only Theorem 2.2.17 (iterated expectation). Drops the entire total-variance identity and all best-prediction conclusions: MSE decomposition, nonnegative remainder, minimum-MSE inequality, and residual-risk equality. The row credited for those components has final status wrong_credit and is not usable for this target.

- **P001-T108 (`SAP.P001f.T108`) — whole.**
  Statement: `SAP.P001f.T108WholeStatement`; proof: `SAP.P001f.WH.W1.T108_whole`.
  Files: `SAP/P001f/Defs/WholeW1.lean`, `SAP/P001f/WH/W1/Leaves.lean`, `SAP/P001f/WH/W1/Proofs/T108.lean`.
  Removed restriction: Assumes an infinite measurable iid sequence and proves the three formulas for positive-size initial segments. Does not state them for an arbitrary fixed finite iid family on its original probability space or provide a change-of-space transfer. The first-moment, second-moment, and positive-variance scopes remain separate.

- **P001-T111 (`SAP.P001f.T111`) — whole.**
  Statement: `SAP.P001f.T111WholeStatement`; proof: `SAP.P001f.WH.W1.T111_whole`.
  Files: `SAP/P001f/Defs/WholeW1.lean`, `SAP/P001f/WH/W1/Leaves.lean`, `SAP/P001f/WH/W1/P/T111_L1.lean`, `SAP/P001f/WH/W1/P/T111_L2.lean`, `SAP/P001f/WH/W1/Proofs/T111.lean`.
  Removed restriction: Both MAR components explicitly assume population integrability of the respondent CEF m(X), retaining that premise instead of deriving it from MAR and uniform overlap. MCAR, discrete MAR identification, vector MAR CEF identification, and the two worked estimator values are retained. Shared estimator definitions supply the printed formulas; their only evaluations here use the stated sample with nonzero denominators.

- **P001-T113 (`SAP.P001f.T113`) — whole.**
  Statement: `SAP.P001f.T113WholeStatement`; proof: `SAP.P001f.WH.W2.T113_whole`.
  Files: `SAP/P001f/Defs/WholeW2.lean`, `SAP/P001f/WH/W2/Leaves.lean`, `SAP/P001f/WH/W2/P/T113_L1.lean`, `SAP/P001f/WH/W2/P/T113_L2.lean`, `SAP/P001f/WH/W2/P/T113_L3.lean`, `SAP/P001f/WH/W2/Proofs/T113.lean`.
  Removed restriction: Retains Integrable (m composed with X) in both correctness branches. Relative to the canonical statement, definitions and standing finite-expectation convention, this excludes correct-propensity cases with nonintegrable nuisance regression but an integrable combined augmented score by cancellation. Finiteness of the outcome and combined-score expectations does not imply this separate premise; the diagnostic note adds no hypothesis. Uses measurable conditional-mean versions, a.e. correctness, and a.e. propensity bounds.

- **P001-T114 (`SAP.P001f.T114`) — whole.**
  Statement: `SAP.P001f.T114WholeStatement`; proof: `SAP.P001f.WH.W2.T114_whole`.
  Files: `SAP/P001f/Defs/WholeW2.lean`, `SAP/P001f/WH/W2/Leaves.lean`, `SAP/P001f/WH/W2/Proofs/T114.lean`.
  Removed restriction: Retains the population interval, width, every-value sharpness with identical observable joint law, and final six-unit ATE estimates -2/6 and 4/6. Omits the four separate potential-outcome bound estimates (upper E[Y(1)]=5/6, lower E[Y(0)]=1/6, lower E[Y(1)]=3/6, upper E[Y(0)]=5/6) and their individual-imputation interpretation.

Verification: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P001f`
rebuilt all 32 modules from scratch and passed its forbidden-token scan.
A scratch file importing `SAP.P001f.Solution` ran `#print axioms` for
all seven switched theorems; each uses exactly `propext`, `Classical.choice`
and `Quot.sound`. Their manifest axiom lists record these results.
The Challenge import whitelist and the absence of Challenge dependencies in
Solution were checked. All other target entries, declarations and proofs,
and all supplied whole statements, blueprints and proof files are unchanged.


## 2026-11-05 independently reviewed repair proposal

P001f Challenge T102 now uses the exact restricted PDF support and retains the current canonical work claim; T105 remains an omission. The definitional CompleteDescription statement makes the support restriction explicit. No WH or claim event is changed.

The source, accepted certificate, current canonical work packet, exact Defs/Challenge closure, and fresh normal full-unit declaration and omission reviews are bound in assure/remaining-repair-transactions-2026-11-05-v2/P001f/plan.json. Original adverse Opus findings and earlier review rows remain historical evidence. This entry does not accept a claim event, rewrite WH adjudication, enable whole promotion, perform A3 replay, collect, release, or push.
