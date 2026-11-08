# P011a packaging report, declaration review round 2

Scope: P011-T1 through P011-T14 only; namespace SAP.P011a. The canonical
claim text in work.json governs each mathematical claim.

Counts: 2 whole; 12 restricted; 0 refuted; 0 omitted.
All 14 theorem names and statements are retained with proved glue; no task is open.
T1 and T2 are restricted because they establish the canonical counterexamples
with the explicitly listed omissions. T11 establishes its whole canonical
counterexample. The declaration reviews below supersede the earlier refuted
labels. All other decisions and scope disclosures are retained.

## Restrictions and excluded clauses

- **P011-T1** (restricted): Retains the cycle laws, their hypotheses, singleton compatibility, exact variance and bias, finite moments, probability limits, exact all-alpha coverage formula, and negative-estimate example. Omits only the decimal coverage evaluation at alpha = 0.05 (about 0.805).

- **P011-T2** (restricted): Retains both path families, their assumptions, covariance and block moments, singleton compatibility, exact oracle expectations, probability and coverage limits, and OLS representation. Drops the sharper outcome bound 27/5, the pointwise S/L/Q polynomial expansions and the samplewise multiblock centering identity in (c), and the decimal coverage evaluation at alpha = 0.05.

- **P011-T3** (restricted): The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T4** (restricted): Retains the exact expectations under Scaling, linear variance bound, deterministic expansion, PSD sufficiency, clique characterization, and the iid-sign data-dependent failure. Drops the assertion that the PSD condition on M-(I+A) may be replaced by nonnegative traces against every admissible covariance, and the observation that only diagonal and true-edge entries contribute to that trace. The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T5** (restricted): The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T6** (restricted): The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T7** (restricted): Retains the finite identity, both finite comparison constants, variance conservativeness without bounded supplied degrees, and the unbounded-cap sign example with exact values and unscaled limits. Drops the characterization of maximizing graphs as the two residual-sign cliques in (d), and the confidence-interval consequence in (c); the variance result alone is stated here. The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T8** (restricted): The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T9** (restricted): Retains the zero means/covariances, root-n rates, finite perturbation inequality, both prediction-error convergence routes, misspecified-model limit, and the concrete unstable OLS model with its exact intercept variance, residual expectation, and failure of consistency. Drops (d)'s explicit slope weight representation, exact per-sample-size scaled true variance 2, pointwise residual sum formula, and its numeric n=4 and n=8 specializations. Measurability of the fitted-coefficient map is explicit. The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T10** (restricted): States the finite moments, full Scaling hypotheses, exact mixture identity, and both impossibility assertions for the displayed fixed-mean and mixture families and measurable statistics. Drops the separately quantified universal-estimator consequence in (ii), and (iv)'s assertions about unscaled consistency of zero and the possible existence of unbiased estimators with extra design information.

- **P011-T12** (restricted): The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

- **P011-T13** (restricted): Retains the finite feasibility test, existential mandatory/optional decomposition, optimal decoding and objective recovery for every supplied maximum matching, exact gadget counts and combinatorial size bounds, and both exact attained instances. Drops (a)'s equivalence with the paper's programs, (b)'s explicit uniqueness and separate optional-optimum identity, a general existence assertion for maximum matchings and an independently defined optimum-value identity in (c), and all runtime and complexity-class conclusions of (e). No encoded-bit-length conclusion is stated.

No target is omitted. T11 and T14 are the whole targets.

## Definition and bridge route

The six Defs parts import Mathlib and earlier Defs parts only. All definitions
live under SAP.P011a and are shared by Challenge and Solution. The numbered
statement definitions combine clauses of each claim; no proof helper is a
separate Challenge theorem. The SAP records are independent declarations,
not aliases for project records. The graph and unordered-edge subtypes use
ordinary Boolean adjacency functions and increasing pairs of finite indices.

- Bridge/Part1 adapts Model and Family records by preserving every field.
  Weighted outcomes, covariance, Scaling, estimator-class membership, concrete
  families and spectral clipping correspond by reflexivity.
- Bridge/Part2 instantiates each usable component theorem on those adapters.
  This is definitional transport, including the complete concrete probability
  laws, tail limits and coverage conclusions.
- Bridge/Part3 uses a plain sum of internal and external edge data for the
  matching gadget. The project's gadgetEdgeEquiv identifies those tags.
  Endpoints and weights agree by cases and reflexivity; mapping finite edge
  sets preserves matching, decoding and weight sums. The finite reduction,
  exact counts and attained examples then transport through this equivalence.
- Bridge/Part4 supplies the remaining glue: existing bounded-coordinate L2
  facts instantiate the exact quadratic expectation; multiplication of the
  affine identity by a nonnegative square transfers maximization; an existing
  finite-maximization declaration supplies comparison maximizers; the already
  proved mean-bias criteria specialize the corrected class to equal means and
  clique unions. The homoskedastic display uses the existing covariance-sum
  identity, equality of marginal variances, and scalar algebra. Doubled LP
  objective values and the inadequate-zero-feasible-point example use the
  exported gap witnesses and arithmetic. Sign-model facts, the spectral
  difference formula, and the named six-unit witness are existing declarations.
  Alternating-estimator identities use the empty-graph identity and arithmetic
  on the exported moments. None of these steps supplies a new statistical or
  asymptotic argument.

## Review handling and scope concerns

The two rows with final_status wrong_credit are excluded from target credit:
cycle_clipped_entries and corrected_polynomial_size_matching_reduction.
The narrower corrected_asymptotic row is used only for its actual norm,
domination and tail-limit conclusions. The credited corrected_finite and
corrected_matrix_majorant rows supply the separate finite assertions.

T6 uses the usable cycle-counterexample row from T1 for its exact
scaled true variance, filling the review's missing identity. T8 combines
the revised-corollary row with the usable mean/clique rows from T3 and the
actual counterexamples from T1/T2. Supporting declarations and these cross-target
uses are recorded explicitly. rows_not_used means not invoked separately in
SAP; such a helper may remain an internal dependency of an imported proof.

All sample-size divisions in probabilistic claims concern positive sample
sizes. The finite clique and corrected/spectral estimator clauses explicitly
require a positive sample size. The finite exact expectation requires L2
coordinates, obtained from Scaling's bounded weighted outcomes for its use
under Scaling. Raw-coordinate integrability is explicit in MeanModel.
Uniform finite laws are probability measures. Normal quantiles in coverage
are only used with 0 < alpha < 1, and intervals use the maximum of variance
and zero. Limiting bias criteria retain Scaling, which bounds the bias
sequence; event probabilities lie in [0,1]. Spectral formulas require
symmetry or use symmetric oracle matrices. Matching denominators are lcms of
positive rational denominators, including the empty lcm of one.

T13 is deliberately a finite result. It neither uses the rejected complexity
row as a premise nor assumes a matching algorithm or a published runtime
theorem. Its universal decoding conclusion is conditional on the supplied
matching being maximum; no choice of a maximum on every instance is asserted.

## Round 1 referee findings and revision 2 actions

I checked each finding from [referee A](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json) and [referee B](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/b/findings.json) against the canonical text
and the actual SAP definitions. No substantive finding is rejected.

The observed-graph objection is valid. The [canonical standing assumptions S2/S5](/home/ubuntu/sap/wt/ARCH-P011a/work.json:37) distinguish the
full dependency graph from its observed induced subgraph and nest the full
graphs. They do not require successive observed subsets to be nested.
In contrast, [Nested and Scaling](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part1.lean:119) require nondecreasing observed sizes and an
injection preserving every adjacency Boolean, hence both edges and nonedges.
A nested full matching with independent signs can have edgeless observed
graphs at odd sample sizes and one observed edge at even sample sizes.
The bounds and positive limiting variance remain valid, but the even graph
cannot embed into the next edgeless graph. This verifies the scope loss
without asserting a counterexample to any conclusion under the Lean premise.
Removing that premise would require stronger general theorems; the revision
therefore discloses it and preserves the existing proofs.

| Finding | Check and action |
| --- | --- |
| [A / P011-T3](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:23) | Changed whole to restricted and disclosed the exact observed induced-nesting premise. |
| [A / P011-T4](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:36) | Kept the existing excluded clauses and added the exact observed induced-nesting premise. |
| [A / P011-T5](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:49) | Changed whole to restricted and disclosed the exact observed induced-nesting premise. |
| [A / P011-T6](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:62) | Changed whole to restricted and disclosed the exact observed induced-nesting premise. |
| [A / P011-T7](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:75) | Kept the existing excluded clauses and added the exact observed induced-nesting premise. |
| [A / P011-T8](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:88) | Changed whole to restricted and disclosed the exact observed induced-nesting premise. |
| [A / P011-T9](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:101) | Kept the existing excluded clauses and added the exact observed induced-nesting premise. |
| [A / P011-T12](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/a/findings.json:134) | Changed whole to restricted and disclosed the exact observed induced-nesting premise. |
| [B / P011-T1](/home/ubuntu/sap/wt/ARCH-P011a/referees/round1/b/findings.json:3) | The exact coverage formula contains no certified decimal bound at alpha = 0.05. Disclosed that single excluded evaluation; used refuted under revision 2 rule 2. |

For T1, [canonical clause (f)](/home/ubuntu/sap/wt/ARCH-P011a/work.json:46) includes the approximate number 0.805, whereas
[the exact all-alpha coverage statement](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part3.lean:68) gives only the exact formula and strict undercoverage.
No existing credited declaration certifies a decimal enclosure. The revised
restriction therefore records that omission; no numerical proof was added.
This follows B's scope finding despite A's whole verdict. Conversely, B's
whole verdicts for the general results do not remove A's independently
verified nesting objection; the canonical S2/S5 and SAP definitions cited
above explain why those whole verdicts are not retained.

Both reports found no false or vacuous theorem and no additional defect from
totalized quantities. I rechecked positive sample-size guards, probability
mass one, bounded weighted-coordinate moments under Scaling, raw-mean
integrability in MeanModel, the interior-alpha quantile condition, bounded
bias/coverage sequences for real liminfs, feasible residual capacities, and
positive rational denominator lcms. No new hypothesis or mathematical proof
was needed. Fixed counterexample families assert their own nesting facts;
they do not restrict a universally quantified class of models by assumption.

At revision 2, T2, T10, T11, T13 and T14 kept the mathematical scopes accepted
by both referees; the declaration review below corrects T11's label. Existing dropped
clauses for T4, T7 and T9 remain listed together with their added-premise
disclosures. Every mathematical theorem statement and every proof module is
byte-for-byte unchanged; the source hashes are in scratch/revision2-review.json.

## Declaration review round 1

The only open declaration finding is **SAP.P011a.T11 / P011-T11,
label_wrong, minor**, with two related issues in the
[reviewer's entry](/home/ubuntu/sap/wt/ARCH-P011a/fw/round1/T11/r1g3/findings.json:3).
Both are accepted; there is no disagreement.

| Finding | Check and action |
| --- | --- |
| T11 was labelled refuted although its canonical claim already asserts the counterexample. | Changed manifest.json's decision to whole. The [canonical T11 statement](/home/ubuntu/sap/wt/ARCH-P011a/work.json:1482) asserts failure of the printed and intended readings. [T11Statement](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part6.lean:28) establishes that assertion, including the exact moments and retained one-sided conservativeness. |
| T11's docstring opening did not distinguish the quoted auxiliary proof step from the canonical counterexample. | Replaced it with the reviewer's proposed text, explicitly identifying the printed < epsilon display and intended > epsilon consistency reading. |

I compared canonical clauses (a)–(f) with
[AlternatingCounterexample](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part4.lean:238),
[AlternatingMoments](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part5.lean:17)
and the estimator identities in T11Statement. These state the concrete family
and assumptions, finite decomposition and moments, limit at one, both failure
limits with the even-size bounds, and Proposition 2's one-sided conclusion.
The empty-graph identities identify the auxiliary estimator with V2 and its
scaled value with the sample variance. Thus the corrected whole label requires
no new mathematical argument or extra assumption.

All shared definitions, bridge lemmas, theorem statements and Solution proofs
are unchanged. The same 14 fully qualified theorem names remain in comparator.json,
whose configuration was regenerated and validated. Hash checks against the
previous revision record confirm that only the T11 docstring changed among
Lean source files. The review record is scratch/declaration-review-round1.json.
The reviewer also covered T12–T14 in the same findings file; their entries
report no open issue and require no change.

## Declaration review round 2

Both open findings are accepted. I checked the entry for each requested
declaration in its own findings file; the additional faithful entries in the
same reports require no changes.

| Finding | Check and action |
| --- | --- |
| [T1: label_wrong, major](/home/ubuntu/sap/wt/ARCH-P011a/fw/round2/T1/r2g2/findings.json:3) | Changed the decision from refuted to restricted. [Canonical T1](/home/ubuntu/sap/wt/ARCH-P011a/work.json:46) asserts the four-cycle counterexample, and [T1Statement](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part5.lean:229) affirms it. Retained the exclusion of the decimal coverage evaluation at alpha = 0.05. |
| [T2: label_wrong, major](/home/ubuntu/sap/wt/ARCH-P011a/fw/round2/T2/r2g2/findings.json:16) | Changed the decision from refuted to restricted. [Canonical T2](/home/ubuntu/sap/wt/ARCH-P011a/work.json:228) asserts both path-law counterexamples, and [T2Statement](/home/ubuntu/sap/wt/ARCH-P011a/SAP/P011a/Defs/Part5.lean:238) establishes them with their block moments and OLS representation. Retained every previously disclosed omitted clause. |

The witnesses contradict the paper propositions quoted in the canonical
claims; they establish the canonical counterexample assertions themselves.
Their omitted clauses preclude whole labels. The revised docstring openings
now identify them as establishing the canonical cycle and path counterexamples,
while preserving the exact restriction text. No finding is rejected.

No shared definition, mathematical statement, bridge lemma or proof changed.
All 14 fully qualified theorem names remain in the regenerated comparator
configuration. Hash checks against declaration review round 1 confirm that
only the Challenge comments changed among Lean sources. The accepted findings,
fingerprints and source hashes are in scratch/declaration-review-round2.json.
The clarified permission for wrong_credit rows does not require adding one:
the existing restricted package continues to use its previous declarations.

## Validation

All Defs, Bridge, Challenge and Solution modules were recompiled in dependency
order with sap-lean after declaration review round 2.
All 14 Solution dependency checks returned exactly propext, Classical.choice
and Quot.sound. Both JSON files parse, and all package source checks pass.

Final compilation and dependency checks are recorded in scratch/validation.json.
The fresh compiler run, complete dependency order and compiled source hashes
are recorded in scratch/declaration-review-round2-compilation.json.
The scratch dependency check imports Solution only and prints all 14 theorem
dependencies. Observed permitted dependencies are recorded individually in
manifest.json and scratch/axioms-results.json.

The package is configured for the Palomar Comparator. No comparator tool or
external-kernel executables were available in the current session, so this
report does not claim three-kernel certification. Challenge and Solution use
the same statements from the same compiled Defs modules; their names and
statements are additionally checked in the local validation script.

## Whole versions (new proofs)
The following targets now use the whole statements and generated proofs supplied in `switch.json`. Their restrictions are removed; the existing definitions and proof modules are unchanged.

**P011-T12 — `SAP.P011a.T12`.** `SAP.P011a.T12WholeStatement` is proved by `SAP.P011a.WH.W1.T12_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW1.lean`, `SAP/P011a/WH/W1/Leaves.lean`, `SAP/P011a/WH/W1/Proofs/T12.lean`, `SAP/P011a/WH/W1/P/T12_L1.lean`.

Old restriction removed: The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T6 — `SAP.P011a.T6`.** `SAP.P011a.T6WholeStatement` is proved by `SAP.P011a.WH.W1.T6_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW1.lean`, `SAP/P011a/WH/W1/Leaves.lean`, `SAP/P011a/WH/W1/Proofs/T6.lean`, `SAP/P011a/WH/W1/P/T6_L1.lean`.

Old restriction removed: The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T7 — `SAP.P011a.T7`.** `SAP.P011a.T7WholeStatement` is proved by `SAP.P011a.WH.W1.T7_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW1.lean`, `SAP/P011a/WH/W1/Leaves.lean`, `SAP/P011a/WH/W1/Proofs/T7.lean`, `SAP/P011a/WH/W1/P/T6_L1.lean`, `SAP/P011a/WH/W1/P/T7_L1.lean`, `SAP/P011a/WH/W1/P/T7_L2.lean`, `SAP/P011a/WH/W1/P/T7_L3.lean`, `SAP/P011a/WH/W1/P/T7_L4.lean`.

Old restriction removed: Retains the finite identity, both finite comparison constants, variance conservativeness without bounded supplied degrees, and the unbounded-cap sign example with exact values and unscaled limits. Drops the characterization of maximizing graphs as the two residual-sign cliques in (d), and the confidence-interval consequence in (c); the variance result alone is stated here. The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T8 — `SAP.P011a.T8`.** `SAP.P011a.T8WholeStatement` is proved by `SAP.P011a.WH.W1.T8_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW1.lean`, `SAP/P011a/WH/W1/Leaves.lean`, `SAP/P011a/WH/W1/Proofs/T8.lean`, `SAP/P011a/WH/W1/P/T6_L1.lean`, `SAP/P011a/WH/W1/P/T7_L1.lean`, `SAP/P011a/WH/W1/P/T7_L3.lean`, `SAP/P011a/WH/W1/P/T7_L4.lean`, `SAP/P011a/WH/W1/P/T8_L1.lean`.

Old restriction removed: The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T9 — `SAP.P011a.T9`.** `SAP.P011a.T9WholeStatement` is proved by `SAP.P011a.WH.W2.T9_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW2.lean`, `SAP/P011a/WH/W2/Leaves.lean`, `SAP/P011a/WH/W2/Proofs/T9.lean`, `SAP/P011a/WH/W2/P/T9_L1.lean`.

Old restriction removed: Retains the zero means/covariances, root-n rates, finite perturbation inequality, both prediction-error convergence routes, misspecified-model limit, and the concrete unstable OLS model with its exact intercept variance, residual expectation, and failure of consistency. Drops (d)'s explicit slope weight representation, exact per-sample-size scaled true variance 2, pointwise residual sum formula, and its numeric n=4 and n=8 specializations. Measurability of the fitted-coefficient map is explicit. The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T10 — `SAP.P011a.T10`.** `SAP.P011a.T10WholeStatement` is proved by `SAP.P011a.WH.W2.T10_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW2.lean`, `SAP/P011a/WH/W2/Leaves.lean`, `SAP/P011a/WH/W2/Proofs/T10.lean`, `SAP/P011a/WH/W2/P/T10_L1.lean`.

Old restriction removed: States the finite moments, full Scaling hypotheses, exact mixture identity, and both impossibility assertions for the displayed fixed-mean and mixture families and measurable statistics. Drops the separately quantified universal-estimator consequence in (ii), and (iv)'s assertions about unscaled consistency of zero and the possible existence of unbiased estimators with extra design information.

**P011-T1 — `SAP.P011a.T1`.** `SAP.P011a.T1WholeStatement` is proved by `SAP.P011a.WH.W2.T1_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW2.lean`, `SAP/P011a/WH/W2/Leaves.lean`, `SAP/P011a/WH/W2/Proofs/T1.lean`, `SAP/P011a/WH/W2/P/T1_L1.lean`.

Old restriction removed: Retains the cycle laws, their hypotheses, singleton compatibility, exact variance and bias, finite moments, probability limits, exact all-alpha coverage formula, and negative-estimate example. Omits only the decimal coverage evaluation at alpha = 0.05 (about 0.805).

**P011-T2 — `SAP.P011a.T2`.** `SAP.P011a.T2WholeStatement` is proved by `SAP.P011a.WH.W2.T2_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW2.lean`, `SAP/P011a/WH/W2/Leaves.lean`, `SAP/P011a/WH/W2/Proofs/T2.lean`, `SAP/P011a/WH/W2/P/T2_L1.lean`.

Old restriction removed: Retains both path families, their assumptions, covariance and block moments, singleton compatibility, exact oracle expectations, probability and coverage limits, and OLS representation. Drops the sharper outcome bound 27/5, the pointwise S/L/Q polynomial expansions and the samplewise multiblock centering identity in (c), and the decimal coverage evaluation at alpha = 0.05.

**P011-T3 — `SAP.P011a.T3`.** `SAP.P011a.T3WholeStatement` is proved by `SAP.P011a.WH.W2.T3_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW2.lean`, `SAP/P011a/WH/W2/Leaves.lean`, `SAP/P011a/WH/W2/Proofs/T3.lean`, `SAP/P011a/WH/W2/P/T3_L1.lean`, `SAP/P011a/WH/W2/P/T3_L2.lean`.

Old restriction removed: The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T4 — `SAP.P011a.T4`.** `SAP.P011a.T4WholeStatement` is proved by `SAP.P011a.WH.W3.T4_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW3.lean`, `SAP/P011a/WH/W3/Leaves.lean`, `SAP/P011a/WH/W3/Proofs/T4.lean`, `SAP/P011a/WH/W3/Analytic.lean`, `SAP/P011a/WH/W3/Finite.lean`, `SAP/P011a/WH/W3/Signs.lean`.

Old restriction removed: Retains the exact expectations under Scaling, linear variance bound, deterministic expansion, PSD sufficiency, clique characterization, and the iid-sign data-dependent failure. Drops the assertion that the PSD condition on M-(I+A) may be replaced by nonnegative traces against every admissible covariance, and the observation that only diagonal and true-edge entries contribute to that trace. The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

**P011-T5 — `SAP.P011a.T5`.** `SAP.P011a.T5WholeStatement` is proved by `SAP.P011a.WH.W3.T5_whole`.

Files: `SAP/P011a/Challenge/Part1.lean`, `SAP/P011a/Solution.lean`, `SAP/P011a/manifest.json`, `SAP/P011a/Defs/WholeW3.lean`, `SAP/P011a/WH/W3/Leaves.lean`, `SAP/P011a/WH/W3/Proofs/T5.lean`, `SAP/P011a/WH/W3/Analytic.lean`, `SAP/P011a/WH/W3/Finite.lean`, `SAP/P011a/WH/W3/Signs.lean`.

Old restriction removed: The general assertions under Scaling additionally require the observed sample sizes n_k to be nondecreasing and, for every k, an injection e_k from the n_k observed vertices to the n_(k+1) observed vertices such that G_k(i,j)=G_(k+1)(e_k(i),e_k(j)) for every i,j. This is induced nesting of the observed dependency graphs, an additional condition not implied by nesting of the full graphs when the observed subsets may change.

Dependent Solution proofs: no repairs were needed. T11, T13 and T14 do not use any switched theorem; their statements, docstrings, proofs and manifest entries remain unchanged.

Validation for these switches: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P011a` rebuilt all 50 modules from scratch and reported a clean token scan. The Solution-only scratch file `scratch/whole-switch-axioms.lean` ran `#print axioms` on every switched theorem; every result was exactly `propext`, `Classical.choice`, and `Quot.sound`. The compiler output is saved in `scratch/whole-switch-axioms.out`. Lean compilation was serial; no `lake` command was run. Per-target results are in `switched.json`.
