P017 packages the sixteen unit targets for *Data-Adaptive Causal Effects and Superefficiency*.

| Decision | Count |
| --- | ---: |
| whole | 13 |
| restricted | 0 |
| refuted | 3 |
| omitted | 0 |

All 16 named theorems are proved in `SAP/P017/Solution.lean`; no glue tasks are
open. These are the current counts, including the supplied whole-statement
certificates and the corrected whole T7 statement supplied before round 3.

No target is restricted. The current **T7** separately states the consistency-only
clipping conclusions and the additional root-n boundedness supplied by Definition 1.
It includes the exact zero region, event inclusion and probability bound,
outside-probability limit, every positive deterministic scale, root-n actual-error
limit, and infinite-radius case.

No targets are omitted. **T9** refutes the universal empirical-statistic weighted
representation assertion in a genuine IID sampling experiment induced by G.
Its empirical-law functional is explicitly required to be measurable.
**T14** and **T15** retain the valid proposition
conclusions and refute false assertions quoted in their canonical printed proofs:
the intermediate-error rate and exact tail probability for T14, and the central
zero-error assertion and intermediate mean-square tail bound for T15. Their
counterexamples concern the original Definition 2 target and satisfy the printed
assumptions; neither theorem refutes its proposition's actual conclusion.
T1, T5, T6, and T12 already have counterexamples as their canonical claims, so
their whole labels describe coverage of those counterexamples. T12 identifies
the universal-rate reading of “quickly”; the printed sentence gives no numerical rate.

The manifest records the credited rows and supporting declarations. Definitions
use genuine probability measures, measurable integrable population effects, closed
pushforward supports, and extended support bounds. Admissible weights have
integrable weights and weighted effects and a finite positive denominator.
Positive sample-size hypotheses guard fixed-sample divisions; the initial index
zero does not control any limit. Infinite radius clips identically before any
conversion to a real radius. The normal-remainder condition requires actual
Gaussian laws and square-integrable remainders without independence. The usual
measure-theoretic conditions are presuppositions, not substantive restrictions.

The shared-definition route is used. `Defs/Part1.lean` defines the population,
weighting, clipping, probability, convergence, and Gaussian-tail notions.
`Defs/Part2.lean` gives the explicit validator populations, potential outcomes,
observed records, IID sampling measures, estimators, and events. Parts 3 through 6
hold the initial target propositions. `Defs/WholeW1.lean` and `Defs/WholeW2.lean`
hold the supplied fuller statements and their additional SAP definitions; they
import Mathlib and the earlier Defs modules. Both Challenge and Solution import
the same compiled SAP definitions, including auxiliary proof terms.

All sixteen original `Bridge.Tk_correspondence` lemmas use `Iff.rfl`, with matching
universe parameters. They transport the initial statements to definitionally
equal project notions; no substantive bridge argument is needed. The new
`Bridge.T9Sampling_correspondence` also uses `Iff.rfl` and includes the sampling-law
and estimator-measurability premises. The current Solution directly uses the
supplied whole-statement certificates for T2, T3, T7, T11, T12, T14, and T15,
and uses bridges for the remaining targets. Those
certificates assemble the existing leaves in `SAP/P017/WH/W1/` and `WH/W2/`.
Round 2 changed no mathematical statement or argument. Round 3 strengthens T9's
refutation by connecting its sample law to G, using a new statement definition and
the existing concrete IID counterexample certificate. No new mathematics is proved.

The original Solution glue comprises specialization and conjunction, interval
membership and clipping equality, measure monotonicity for the zero-error event,
a triangle inequality, and scalar algebra. T4's half-radius choice uses positivity
and halving arithmetic. T6 specializes the existing corrected mean-square limits,
with square-root cancellation at positive sample sizes and a separate zero case.
The supplied whole certificates now also state T2's explicit weights, T3's full
support geometry and finite-valued case, T11's alternative identities and infinite
radius, T12's explicit rate witness, and T14/T15's printed-proof refutations.

The corrected whole T7 separates consistency-only deductions from root-n boundedness.
For T8, the detailed infinite-radius clause asserts zero actual error;
the intermediate normal-minus-actual-target difference is explicitly `y - x`.
T10's full-support remark concerns numerical equality, without silently adding a
weighted representation assertion. These distinctions are preserved.

## Declaration review round 1

All five round-1 findings were accepted. The complete pre-round-2 report,
including the earlier removed restrictions and whole-certificate handoff, is
preserved in [scratch/report-before-round2.md](scratch/report-before-round2.md).
The initial round-1 revision had 8 whole, 7 restricted, 1 refuted, and 0 omitted;
the subsequently supplied whole certificates account for the current counts.

- **T3 — not_faithful/minor:** The [finding](fw/round1/T3/r1g1/findings.json)
  distinguishes values strictly between support bounds from the topological
  interior of the support. Equal mass at -1 and 1 has representable mean zero
  outside its support. The precise bound wording is retained in the current
  whole-version theorem and statement-definition docstrings.
- **T11 — restriction_inaccurate/minor:** The [finding](fw/round1/T11/r1g3/findings.json)
  identified the missing infinite-radius empty-tail case. Round 1 disclosed that
  omission. The supplied `T11WholeStatement` now includes the empty-tail integral,
  truncated moment, and limits as well as the finite-radius equivalent identities.
- **T12 — not_faithful/minor:** The [finding](fw/round1/T12/r1g3/findings.json)
  requested the quantitative reading of “quickly.” The current whole-version
  docstring identifies that interpretation and the absence of a printed numerical
  rate. Its statement now includes the supplied explicit eventual square-root witness.
- **T14 — label_wrong/major:** The [finding](fw/round1/T14/r1g3/findings.json)
  correctly treated the quoted printed proof as canonical content. The proposition-only
  theorem was first marked restricted. The supplied whole version now retains the
  valid conclusion and refutes the invalid intermediate assertions, with decision refuted.
- **T15 — label_wrong/major:** The [finding](fw/round1/T15/r1g3/findings.json)
  likewise required accounting for the quoted proof. The proposition-only statement
  was first marked restricted. The supplied whole version now retains the valid
  conclusion and refutes the central-zero and tail-bound assertions, with decision refuted.

The original rounds' build and dependency logs remain under `scratch/`. Their
statement-closure counts refer to those earlier versions. The validation below
covers the current whole-version package.

## Declaration review round 2

All four findings are accepted after inspecting their complete entries, the
canonical claims in [work.json](work.json), and the explicit Lean conditions.
Each affected theorem docstring and corresponding statement-definition docstring
now says: “The usual measure-theoretic conditions are assumed.” The manifest
records that disclosure as a presupposition, while decisions and restrictions
stay unchanged. No substantive hypothesis is added.

- **T11 — not_faithful/minor:** The [finding](fw/round2/T11/r5g3/findings.json)
  points to the measurable Gaussian-law variable under a probability measure in
  [T11WholeStatement](SAP/P017/Defs/WholeW2.lean). Its conclusions also certify the
  needed integrability. Both docstrings now disclose the usual conditions.
  Decision: whole.
- **T13 — not_faithful/minor:** The [finding](fw/round2/T13/r5g3/findings.json)
  points to [T13Statement](SAP/P017/Defs/Part6.lean), which explicitly requires
  measurable integrable effects, genuine population and sampling probabilities,
  measurable estimates, and measurable normal and remainder functions where used.
  The theorem and statement-definition docstrings now disclose those presuppositions.
  Decision: whole.
- **T14 — not_faithful/minor:** The [finding](fw/round2/T14/r5g3/findings.json)
  points to the population conditions in the universal proposition component
  [T14Statement](SAP/P017/Defs/Part6.lean), used by
  [T14WholeStatement](SAP/P017/Defs/WholeW1.lean). The whole-version docstrings
  now disclose the usual conditions. The valid proposition and printed-proof
  counterexample remain exactly as supplied. Decision: refuted.
- **T15 — not_faithful/minor:** The [finding](fw/round2/T15/r5g3/findings.json)
  points to the explicit probability, measurability, and remainder-integrability
  conditions in [T15WholeStatement](SAP/P017/Defs/WholeW1.lean). Both docstrings
  now carry the disclosure; independence is still not assumed. Decision: refuted.

The earlier precise support-bound wording was also restored in both T3
whole-version docstrings, where the whole-certificate handoff had reintroduced
“support interior.” This changes no formal assertion. Shared definition bodies
are unchanged, so no declaration acquires a changed mathematical dependency.

To satisfy the 300-line limit, the supplied unused T7 assembly was moved verbatim
from the 371-line `WH/W1/Leaves.lean` to `WH/W1/T7Assembly.lean`; its wrapper now
imports that module. The original module is at most 300 lines. No Challenge
statement depends on this unused assembly. A duplicate T12 entry was removed
from `rows_not_used` because that declaration was already recorded in `rows_used`.
The comparator configuration was refreshed with the same sixteen theorem names
and required settings. No claim classification changed in this round.

All 34 SAP Lean modules recompiled successfully with `sap-lean` in dependency order,
including the supplied whole certificates and the unused T7 wrapper. The sixteen proofs'
`#print axioms` checks use `scratch/Axioms.lean`. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. Build order, status, output, dependency-audit
output, and the separate-environment identity check are recorded in
`scratch/round2-compile-order.json`, `scratch/round2-compile-status.json`,
`scratch/round2-compile.log`, `scratch/round2-axioms.log`, and
`scratch/round2-identity.log`. Expected Challenge placeholder warnings have their
labels normalized in the saved build log.

JSON parsing, target and credited-row coverage, all theorem names and proof
statuses, required implicit-variable options, allowed imports, file sizes,
unchanged mathematical definitions, the verbatim moved proof, presupposition
disclosures, and dependency results are checked by `scratch/validate_round2.py`.
The round-2 build and identity results are summarized in `scratch/round2-validation.log`.
All sixteen audits passed with exactly the three permitted axioms. The identity
check passed for 16 statements, 2,183 definition bodies, and 4,932 dependencies.
This local check does not claim three-kernel Palomar certification; the Palomar,
`con-ron`, and `nanoda_bin` executables were not found on PATH. The required
external-kernel commands remain in `comparator.json`.

## Whole versions (new proofs)

- **P017-T7 (`SAP.P017.T7`):** switched from restricted to
  whole using `SAP.P017.T7WholeStatement_W3` and
  `SAP.P017.WH.W3.T7_whole`. The Challenge stub and its new docstring are in
  `SAP/P017/Challenge/Part1.lean`; the proof is in `SAP/P017/Solution.lean`,
  importing `SAP/P017/WH/W3/Proofs/T7.lean`. The supplied statement and
  assembly remain in `SAP/P017/Defs/WholeW3.lean` and
  `SAP/P017/WH/W3/Leaves.lean`; credited declarations are recorded in
  `SAP/P017/manifest.json`.

  Old restriction now removed: Retain asymptotic normality for root-n boundedness and for the combined theorem. Omit the final canonical sentence asserting that consistency alone establishes all of (a)-(c), which includes root-n boundedness; do not assert a separate consistency-only formulation. Retain the exact zero region, event inclusion and probability bound, consistency and outside-probability limit, every-positive-sequence conclusion, root-n error conclusion, and infinite-radius case.

  The corrected whole claim gives the separate consistency-only clipping limits;
  Definition 1 additionally gives root-n boundedness and consistency.
  No other Solution proof uses T7, so no dependent proof repairs were needed.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P017` rebuilt all
37 modules from scratch with a clean token scan. The scratch file
`scratch/WholeSwitchAxioms.lean` imports `SAP.P017.Solution`;
`#print axioms SAP.P017.T7` reports only `propext`, `Classical.choice`, and
`Quot.sound`. Lean processes ran sequentially, without invoking Lake.

## Declaration review round 3

**T9 — not_faithful/major:** The [finding](fw/round3/T9/r7g2/findings.json)
is accepted. The canonical standing reading in [work.json](work.json) makes the
sampling distribution arise from G. The old `T9Statement` and the credited
negation at [FidP017Contracts.lean](AronowAudit/P017/Wave1/Checks/FidP017Contracts.lean)
allow an unrelated sampling law and data map. Negating that larger universal
alone does not guarantee a counterexample in the printed sampling setting.
The earlier row review's acceptance does not override this canonical condition.

`SAP.P017.T9` now states `T9SamplingStatement`. Inside its negated universal,
`P.map data = iidSamples G` connects the joint full-data sample law to the
population, and each estimate is required to be measurable. Observations and
the data map remain measurable, and the estimator still factors through the
observed empirical measure. The docstring explicitly identifies IID sampling
from G and the usual measure-theoretic presuppositions. This is a stronger
refutation: an IID experiment is a valid subclass of the printed population
sampling setting, so decision `refuted` and restriction null are retained.

The proof uses the existing
[proposition1_printed_empirical_counterexample](AronowAudit/P017/Wave1/Gap/FidP017.lean)
certificate. It already exports the uniform-effect population's integrability,
positive radius, measurable observed records, root-n asymptotic normality,
empirical IPW factorization, and positive-probability unrepresentable endpoint
events. Instantiate with `P = iidSamples ipwPopulation` and identity data.
`Measure.map_id` supplies the law equality; measurability of the finite polynomial
sample mean is routine glue. At sample size one the all-control outcome -1
realization contradicts the universal representation assertion using the exported
endpoint obstruction. Its enclosing event has the certified positive probability
one quarter. No probability or asymptotic argument is reproved.

The old credited negation is now listed as unused, with the missing sampling-law
reason. The existing concrete certificate and identity-map theorem are recorded
as supporting declarations. `T9Sampling_correspondence` is definitional transport
by `Iff.rfl`. The old statement definition is retained unchanged for historical
bridges. Existing definition bodies are unchanged: the new definition is appended
after them, and only Challenge theorem T9 mentions it. T9 is the only audited
declaration whose statement changes in this round. All fully qualified theorem
names and every other Challenge statement and Solution proof are preserved.

Both metadata files are refreshed and parsed. The T7 handoff had recorded
`root_normal_tight_and_consistent` in both used and unused rows; the duplicate
unused entry is removed without changing its statement or proof. The full
37-module rebuild passed using `sap-lean` in dependency order;
`scratch/round3-compile-order.json`,
`scratch/round3-compile-status.json`, and `scratch/round3-compile.log` record it.
The isolated glue check is `scratch/T9SamplingGlue.lean`. All sixteen
`#print axioms` checks and the separate-environment statement/definition identity
check passed in `scratch/round3-axioms.log` and `scratch/round3-identity.log`.
All sixteen proofs use exactly the three permitted axioms. The identity check
passes for 16 statements, 2,186 definition bodies, and 4,935 dependencies.
`scratch/validate_round3.py` checks the package, metadata, source preservation,
sampling premises, build order, and audit results; its output is
`scratch/round3-validation.log`. No open glue tasks remain.

## Declaration review round 4

All three findings are accepted. Decisions remain 13 whole and 3 refuted, with
no restricted or omitted targets and all sixteen named theorems proved.

- **T8 — not_faithful/minor:** The [finding](fw/round4/T8/r8g2/findings.json)
  correctly identifies the missing presupposition disclosure. `T8Statement`
  already requires measurable estimates and, through `NormalRemainder`, measurable
  square-integrable remainders. The theorem and statement-definition docstrings
  now both say: “The usual measure-theoretic conditions are assumed.” Its
  mathematical statement and whole decision are unchanged.
- **T9 — not_faithful/major:** The [finding](fw/round4/T9/r8g2/findings.json)
  is correct: a measurable composite and pointwise factorization do not ensure
  that its empirical-law factor is measurable. Inside the negated universal,
  `T9SamplingStatement` now also requires
  `∀ n : ℕ, 1 ≤ n → Measurable (H n)`. Its IID-law premise, measurable estimates,
  and empirical factorization are retained. Both docstrings explicitly describe
  the measurable empirical functional. This strengthens the refutation within
  the printed measurable-function reading; the refuted decision remains correct.
  The existing IPW functional is the integral of its polynomial observed-record
  summand. Its measurability follows by instantiating
  [StronglyMeasurable.integral_kernel](/home/ubuntu/sal/deps/mathlib/Mathlib/Probability/Kernel/MeasurableIntegral.lean:55)
  with the identity map on measures as a kernel. The integrand is a measurable
  real polynomial. This applies an existing Mathlib theorem and adds no integration
  or probability argument. Empirical values are finite sums of finite real values,
  so the counterexample uses genuine integrals. The same existing IID certificate
  supplies all remaining witness facts.
- **T10 — not_faithful/minor:** The [finding](fw/round4/T10/r8g2/findings.json)
  likewise correctly asks for the usual-conditions disclosure already present in
  its hypotheses. Both docstrings now contain that sentence. Its mathematical
  statement and whole decision are unchanged.

Only the audited T9 statement gains a changed mathematical dependency. T8 and
T10 have docstring-only changes; all other definition bodies, Challenge statements,
and Solution proofs are preserved. The T9 bridge still uses `Iff.rfl`. The manifest
records the disclosures and Mathlib support; comparator names and settings remain.
All 37 modules rebuilt successfully in dependency order. All sixteen dependency
audits passed with exactly the three permitted axioms. The identity check passed
for 16 statements, 2,186 definition bodies, and 4,935 dependencies. Logs use the
`scratch/round4-` prefix. `scratch/validate_round4.py` confirms these results,
metadata, source preservation, disclosures, and file limits; its output is in
`scratch/round4-validation.log`. No open glue tasks remain.
