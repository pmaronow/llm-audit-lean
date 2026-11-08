P001g packages 13 of the 14 unit targets from `work.json`. All 13 Challenge
theorems have proved Solutions under the same names, with no open glue tasks.
T120 and the earlier tied-maximizer result remain auxiliary Solution theorems.

| Decision | Count | Targets |
|---|---:|---|
| whole | 7 | T115, T116, T117, T125, T126, T127, T130 |
| restricted | 3 | T119, T128, T129 |
| refuted | 3 | T118, T121, T124 |
| omitted | 1 | T120 |

The restrictions are:

- **P001-T119**, Definition 4.3.9, pp. 168–169: refutes only the specified
  population integrated squared-risk interpretation. It does not refute the
  book's undefined regional, pointwise or prediction-measure consistency.
  The target-authorized squared-residual correction is used; the literal
  unsquared argmin is not addressed. The usual measure-theoretic conditions
  include finite population squared errors in the canonical BLP setting,
  enforced by `MemLp (Y 0) 2 μ`. The universe-zero domain, density positive
  exactly on a nondegenerate compact interval, literal `ContDiff ℝ ⊤` CEF
  premise and both degree limits are retained. Fits have no measurability
  premise, and risk-event probabilities use measure outer values.
- **P001-T128**, Theorem 3.4.2, pp. 125–126: proves limiting coverage at least
  1-alpha for the displayed open sets under the nonnegative variance-estimator
  and n-scale consistency assumptions. Omits footnote 34's requirement that
  endpoints be strictly ordered almost surely at every positive sample size.
  The sets may be empty at finite sample sizes. No additional positivity
  premise or proper-random-interval assertion is introduced.
- **P001-T129**, Theorem 5.2.6 and its lemma, pp. 193–194: actual-product MLE
  consistency requires compactness, finite observed logs, parameterwise almost
  sure observed-density positivity, continuity, unique expected-log maximization,
  and a finite envelope dominating empirical-log error at every sample size,
  sample point and parameter, converging in probability to zero. This extra
  uniform condition is not credited to the printed pointwise WLLN. A separate
  domain retains the expected-log maximum and density-equality characterization
  under a true normalized model, support domination and finite logs. The
  separate product-log/sample-average identity, unique sample-maximizer assertion,
  pointwise WLLN conclusion and derivation of the uniform envelope from informal
  regularities are omitted. Any measurable product maximizer is allowed.

The omitted target is:

- **P001-T120**, Theorem 5.2.8, p. 195: the sole credited row negates a
  consistency assertion without the true-model premise carried by canonical
  [Definitions 5.2.1–5.2.2](work.json:408). Its common-Bernoulli witness cannot
  reproduce conditional success rates 1/4 and 3/4 at two positive-mass covariates,
  even up to density null sets. Thus it supplies no counterexample on the
  canonical domain or positive restricted clause. Declaring the alternative
  negation `restricted` did not correct that logical gap. The proved
  `SAP.P001g.T120` is retained in Solution only as an auxiliary result.
T120 has no Challenge declaration or Comparator entry; its manifest `theorem`
and `proof_status` are null. The earlier tied-maximizer result is uncredited
under `SAP.P001g.T121_tiedAuxiliary`. T121's restored Challenge uses the
separate unique-maximizer statement described below.

The whole positive statements retain all these clauses:

- T115: population random-assignment identification, every selection-bias
  decomposition equality, both empirical arm means and their difference.
- T116: discrete ATE sum, conditional ATE and its expectation, balance,
  conditional independence and propensity-score positivity, with a separate
  score domain free of outcome-moment premises.
- T117: population IPW and both double-robustness alternatives; only the
  complete augmented score must be integrable in the propensity-correct branch.
- T125: the zero-variance WLLN case. T126: both CLT forms, the finite
  standardization identities and moments. T127: pointwise rectangular-KDE
  consistency in the continuous-density context with both bandwidth limits.
- T130: both endpoint formulas, positive-sample unbiasedness and full-sequence
  consistency under iid observable pairs.

The three `refuted` statements concern positive canonical assertions:

- T118 refutes positive-variance plug-in normality from Hadamard differentiability
  and supremum-norm Hadamard differentiability of the mean from finite variance.
- T121 uses a compact three-outcome mixture whose likelihood has a unique
  maximizer on every positive-size sample. One estimator cannot converge to
  both distinct true full vectors with the same law, refuting consistency
  and hence the printed consistency-and-efficiency conjunction.
- T124 gives an iid conditional-independence placebo null at level one half
  with guarded rejection probability tending to one. The guard requires n>3,
  invertible sample Gram matrices and positive full residual risk, eventually
  almost surely; actual F-reference medians supply the critical values.

The route uses shared SAP definitions and structural Bridges. Defs parts 1–8
import only Mathlib or earlier Defs parts. `Defs/WholeW1.lean` and `Defs/WholeW2.lean` import Mathlib
and the base Defs root. Challenge and Solution share those compiled definitions;
Solution never imports Challenge. No project declaration was copied under its
original name. Most correspondences are `rfl`; conjunctions assemble T116,
T118, T126 and T129. The special adapters are:

- T119: `Bridge/SieveMSE.lean` transports the Gaussian second moment through
  the source marginal law, then reuses fit existence, the bad-event lower bound,
  event inclusion and the source subsequence contradiction.
- T124: `Bridge/GuardedF.lean` uses existing frequency limits, continuous
  Gram/risk maps, finite-sample identities, statistic divergence and rejection
  facts. Scalar arithmetic and event transport add the validity guard.
- The retained auxiliary T120 uses `Bridge/KLStatistic.lean`: the source's
  clipped finite outcome mean is a measurable sample rule, with correspondence
  supplied by `Fin.sum_univ_eq_sum_range`. It is not a true-model witness.

The pre-existing whole proofs for T115/T117 remain in `WH/W1/Proofs/`, using
`Leaves.lean`, `Elementary.lean` and the existing `P/` adapters. The historical
T128 proof remains only as an auxiliary fact about endpoint order and coverage;
it is not used by the coverage-only target. Existing mathematical definitions and WH
proof bodies remain unchanged. Round 4 removed only blank lines from `Elementary.lean`.

The total-function checks guard finite probabilities, outcome integrability,
conditional means by positive arm masses, IPW denominators by overlap, and
finite standardization by positive sample size and variance. T119's L2 outcome
and compact covariate support ensure finite polynomial residual MSE; continuous
fits and the analytic CEF also ensure finite prediction risk. Fit-event outer
values are disclosed. Hadamard directions are bounded and the mean functional
uses finite-second-moment CDFs. KDE bandwidths are positive. Expected-log
statements have support and integrability guards. T124's rejection guard excludes
singular fits, zero residual risk and invalid degrees of freedom. No omitted
result is recovered by adding its desired conclusion as an assumption.

The supplied [Comparator result](SAP/P001g/verification/comparator-result.json)
and [log](SAP/P001g/verification/comparator.log) certify a historical 13-theorem
snapshot. They are preserved as history and do not certify this revised package.
The current 13-theorem configuration needs a fresh external Comparator run;
local compilation and identity checks are not three-kernel certification.

## Declaration review round 1

The T128 `label_wrong` / minor finding `a476e39615a06ad1` was accepted;
see [findings.json](fw/round1/T128/r1g3/findings.json). T128 was initially
restricted to coverage, then replaced by an existing endpoint-order refutation.
Round 9 returned to positive coverage; round 11 discloses its omitted interval
property. Historical checks passed; see the [log](scratch/P001gRound1Compile.log).

## Declaration review round 2

The T119 `omission_questionable` / major finding
`f3e781e65d11b9b931659d5c0379749bb429a57b72a617e6a50538dc10b8d663` was
accepted; see [findings.json](fw/round2/P001-T119/r3g4/findings.json).
[SieveRate.lean](AronowAudit/P001/Wave1/SieveRate.lean:35) supplied the restricted
integrated-risk result with its exact interpretation and limits disclosed.
Literal `ContDiff ℝ ⊤` is analytic here; see
[ContDiff/Defs.lean](/home/ubuntu/sal/deps/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1060).
Checks passed; see the [log](scratch/P001gRound2Compile.log).

## Declaration review round 3

The T120 `not_faithful` / major finding
`69e8644c43fc3a79a6690ffdb498946470e0a4594846a2d816805a7c5fc1f7da` was
accepted; see [findings.json](fw/round3/T120/r4g2/findings.json). The negated
assertion now requires a measurable rule of the first n observed pairs. The
existing clipped mean supplies it by finite-sum and measurability transport.
That proof now serves only the auxiliary result. Checks passed; see the
[log](scratch/P001gRound3Compile.log).

## Declaration review round 4

Both T119 `not_faithful` / major issues
`f4b89aef4db7ab9bad68cec5f6b98228ab22c6c6ac997da30f7dd596c9dd70bc` were
accepted; see [findings.json](fw/round4/T119/r6g1/findings.json). The domain
lacked inherited finite population MSE and disclosed only L1. `T119Statement`
adds `MemLp (Y 0) 2 μ`; the existing Gaussian marginal law supplies it by moment
transport, and source nodes supply the same fit, bad event and contradiction.
Only T119's shared definition changed. Checks passed; see the
[log](scratch/P001gRound4Compile.log).

## Declaration review round 5

The T116 `not_faithful` / minor finding
`11744f85603bbed2f266def2d2060a7296135e3178cf00e0853f60ba6ca7fc6f` was
accepted; see [findings.json](fw/round5/T116/r7g1/findings.json). Its docstring
now expressly assumes the usual measure-theoretic conditions already present
in the identification domains, retaining a separate moment-free score domain.
No statement or proof changed. Checks passed; see the [log](scratch/P001gRound5Compile.log).

## Declaration review round 6

All three T120 `not_faithful` / major issues
`8035b5ff6ad669846352727da8e141b70d6425ec43dbcff93f977c235c3696fd` were
accepted; see [findings.json](fw/round6/T120/r8g2/findings.json). The missing
true-model condition was acknowledged and the negation relabeled `restricted`.
Round 8 superseded that decision: disclosure alone did not produce a canonical
result. Checks passed; see the [log](scratch/P001gRound6Compile.log).

## Declaration review round 7

The initial T121 `faithful` / `none` finding
`3acd0615bdaab920b372d5927ae6e25b62f053a71dcfab012e8ff013ab10789b` is in
[findings.json](fw/round7/T121/r9g2/findings.json). The subsequent major recheck
in [the update](revise-fw7.md:8) was accepted then, and T121 relabeled
`restricted` over the unique-argmax reading. The binding round-10 decision
settles the later split by omission. Checks passed; see the [log](scratch/P001gRound7Compile.log).

## Declaration review round 8

The major findings were accepted then: T120 fingerprint
`8fcf7803e574e72c96565c8969b7c34732767fafbccef096f6520b370cea1824` in
[its findings](fw/round8/T120/r10g2/findings.json), and T121 fingerprint
`4e216d0e308a6a39664cd78d897d18d10171b3e45202b4018d72acee2a40d02f` in
[its findings](fw/round8/T121/r10g2/findings.json). Both Challenge declarations
were omitted, their original Solution proofs retained as auxiliary. Round 9
restored T121 temporarily; the binding round-10 decision supersedes that step.
Checks passed; see the [log](scratch/P001gRound8Compile.log).

## Declaration review round 9

The T121 `omission_questionable` / major finding
`d0e5d8224aa85d74975fd553bcf4e963d677f4921cae01b4ae49311980ac9af3` was
accepted then; see [findings.json](fw/round9/P001-T121/r11g4/findings.json).
T121 was restored under the reading without uniqueness, using its unchanged
statement and source proof. The binding round-10 decision supersedes that step.
All three T128 `label_wrong` / major issues
`75d57b76c83886fdfe9ae9eebc4f3f784b38e1ce8edbb0109e142de6b6bc367f` were
accepted; see [findings.json](fw/round9/T128/r11g2/findings.json). T128 was
changed to positive coverage using the existing `T128Statement` and `Bridge.t128`.
The old endpoint-order proof was retained as auxiliary with corrected docstrings.
Round 11 qualifies the coverage theorem's then-`whole` label. Checks passed;
see the [log](scratch/P001gRound9Compile.log).

## Declaration review round 10

Both T121 `not_faithful` / major issues, fingerprint
`a630bd1f9c414b5e6271da95a5388aa2ad21431fec45282e2477c6cc57a08259`, were
accepted; see [findings.json](fw/round10/T121/r12g2/findings.json). The binding
decision for that round settled the split by omission; round 13 supersedes
that outcome using a different witness. [Definition 5.2.2](work.json:468)
carries the glossary convention (p. 285): "Our use of arg max assumes that
there exists a unique maximum." The then-existing witness had tied maximizers
on every true-support sample and supplied no refutation of the printed reading.
At that point T121 had no Challenge or Comparator entry, and both old credited
rows were unused. Its original proof and required docstring were retained as
auxiliary. Other target edits were reverted. Checks passed; see the
[log](scratch/P001gRound10Compile.log).

## Declaration review round 11

Both issues in the T128 `not_faithful` / major finding, fingerprint
`fc122ba722998e84ee67961333468d13f0b0423cd10f0d9be4c03a7ce86501e9`, are
accepted; see [findings.json](fw/round11/T128/r13g2/findings.json) and the
[review report](fw/round11/T128/r13g2/REPORT.md). The existing nonnegative-variance
premise permits zero. Coverage alone does not establish footnote 34's
almost-sure strict ordering at each positive sample size, required for the
canonical random-interval object in [definitions_needed](work.json:800).
The already-proved iid Gaussian
[countermodel](SAP/P001g/WH/W1/Elementary.lean:140) sets the variance estimate
to zero at n=1 and has all coverage premises; the existing
[endpoint argument](SAP/P001g/WH/W1/Elementary.lean:226) confirms the failure.
No new counterexample or statistical proof is needed to assess this finding.

T128 is now `restricted`, retaining exactly the same theorem statement and
proof. Its docstring describes the displayed open sets and, with the manifest,
expressly discloses omission of almost-sure strict endpoint order at every
positive sample size and the possibility of finite-sample empty sets. The
usual measure-theoretic conditions remain presupposed. No positivity hypothesis
or other premise is added. The restriction is about the missing claim clause,
not about the source of the proof. The finite studentization row supplies no
such ordering guarantee under these nonnegative-variance premises.
All 12 Challenge statements, all 14 Solution statements and proof bodies,
shared definitions, Bridges and the binding T121 omission remain unchanged.

Round 11 validation passed. All 24 package modules rebuilt with `sap-lean` in the [recorded dependency order](scratch/P001gRound11Order.json), then all 14 preserved Solution theorems passed the foundation check, using exactly `propext`, `Classical.choice` and `Quot.sound`. All 12 packaged theorem types and universe lists match, as do all 91 shared SAP definitions; both omitted auxiliaries occur only in Solution. See the [log](scratch/P001gRound11Compile.log) and [baseline hashes](scratch/P001gRound11Before.json). Both JSON files parse; their theorem names and credited-row accounting agree. Every SAP source has both implicit-variable options and meets the 300-line limit. Counts are 7 whole, 3 restricted, 2 refuted and 2 omitted; all 12 packaged theorems are proved, with no open glue tasks. No fresh external-kernel certification is claimed.


## Declaration review round 12

The [round 12 update](revise-fw12.md) lists no open findings. No `fw/round12/`
directory was supplied in this worktree. There are therefore no findings to
correct or dispute. All statements, proofs, shared definitions, Bridges and
target decisions are retained, including the binding T121 omission and the
explicit T128 coverage-only restriction. The manifest and Comparator
configuration were parsed, revalidated and retained without content changes.

Round 12 validation passed. All 24 package modules rebuilt with `sap-lean` in the [recorded dependency order](scratch/P001gRound12Order.json). All 14 preserved Solution theorems use exactly `propext`, `Classical.choice` and `Quot.sound`. The 12 packaged theorem types and universe lists match, as do all 91 shared SAP definitions; both omitted auxiliaries remain only in Solution. See the [compile log](scratch/P001gRound12Compile.log), [baseline hashes](scratch/P001gRound12Before.json) and [validation record](scratch/P001gRound12Validation.json). Source hashes confirm that only this report changed. Counts remain 7 whole, 3 restricted, 2 refuted and 2 omitted, with all 12 packaged theorems proved and no open glue tasks.

## Declaration review round 13

The [round 13 update](revise-fw13.md) lists no open findings, and no `fw/round13/` directory was supplied. Its binding restoration instruction is implemented below. Every other target entry, statement, definition and proof is unchanged.

## T121 restored as a refutation (Opus adjudication a4)

The binding [adjudication](/home/ubuntu/sap/wh/adjudicate/a4/ADJUDICATION.md)
changes P001-T121 from `omitted` to `refuted`. These seven files were copied
byte-for-byte from the authorized WHOLE group P001g-W2:

- `SAP/P001g/Defs/WholeW2.lean`.
- `SAP/P001g/WH/W2/Elementary.lean` and `Leaves.lean`.
- `SAP/P001g/WH/W2/P/T121_L1.lean`, `T121_L2.lean` and `T121_L3.lean`.
- `SAP/P001g/WH/W2/Proofs/T121.lean`.

The Challenge uses exactly the group's `targets.json` docstring and `T121WholeStatement`. Solution applies `WH.W2.T121_whole`; no proof was written or modified. The old theorem is renamed `SAP.P001g.T121_tiedAuxiliary`, with its auxiliary docstring and proof unchanged, and remains uncredited. The new model satisfies the unique-arg-max convention on every positive-size sample. The project donors are `PrintedConfidence.lift_stream_iid` and `probability_limit_unique`; both old tied-maximizer rows remain unused with their original reasons. The manifest and Comparator now include restored T121.

Round 13 validation passed: the required clean rebuild compiled all 31 modules.
All 15 Solution theorems use only `propext`, `Classical.choice` and `Quot.sound`.
All 13 packaged types and universe lists and all 105 shared SAP definitions
match; both auxiliary declarations remain only in Solution. The copied files
match the source hashes, and every other target is unchanged. See the
[build log](scratch/P001gRound13Compile.log) and
[validation record](scratch/P001gRound13Validation.json). Both JSON files parse;
all source limits and implicit options pass. No external certification is claimed.
