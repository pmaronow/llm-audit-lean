# P022 statement audit

Audited all 18 targets. Counts:

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 2 |
| restriction_inaccurate | 1 |
| not_faithful | 5 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 12 none, 5 minor, 1 major. No target is omitted in the supplied record. No false or globally vacuous Lean statement was found. The six findings below concern canonical coverage, polarity, or the declared restriction; the retained mathematical assertions are sound as far as this audit could determine.

The comparison treats separately asserted general statements, stronger limits, and alternative counterexamples in the canonical target text as part of that target. It does not count every intermediate proof lemma as an additional required conclusion. A retained counterexample can correctly refute the printed error while still covering less than all the canonical target text. The minor coverage findings can be resolved by accurate restriction declarations, consistent with the author's rule that saying less is allowed.

## Findings requiring correction

### P022-T18 — not_faithful, major

The canonical target is the affirmative printed Lemma 2. The record labels the target `whole`, but `T18Statement` begins with the **negation** of its universal formulation ([Defs/Part6.lean:127](SAP/P022/Defs/Part6.lean#L127)). The Challenge docstring itself correctly describes a refutation.

The refutation has the right scope: it negates functions chosen from the limiting law before the sequence and allocation parameters, and the reciprocal witness defeats even functions chosen after that sequence. It genuinely refutes the affirmative statement in the [paper's Lemma 2](https://arxiv.org/pdf/1405.6555). It does not prove that statement.

Fix the target decision: omit the false affirmative claim with this counterexample as justification, and retain the negative theorem as an explicitly identified auxiliary refutation; alternatively, change the canonical target to request a refutation before labeling the negative theorem `whole`. Merely removing the negation would leave a false theorem. This finding preserves the step-2 `different` reading.

### P022-T1 — not_faithful, minor

The record says `whole`. The theorem correctly supplies the negative-reciprocal witness A, its hypotheses, exact CDF distances, and infinite scaled tails ([Defs/Part5.lean:12](SAP/P022/Defs/Part5.lean#L12)). The canonical text separately supplies witness B, whose limiting law is nonsingular. That witness is absent. The explicit left-CDF proof-step failure and extra boundedness/UI observations are also not conclusions of this theorem.

The remaining witness really refutes both printed conclusions. Add the omitted assertions or declare the restriction. An accurate declaration is: “Retains counterexample A's conditions 1–3, exact population and sampled CDF distances, infinite scaled tails, and failure of Lemma 2. Omits the explicit boundedness/uniform-square-integrability observations, the left-limit proof-step assertion, and counterexample B with nonsingular limiting law.”

### P022-T5 — not_faithful, minor

The four-unit constant-one counterexample is fully correct ([Defs/Part5.lean:91](SAP/P022/Defs/Part5.lean#L91)). The canonical statement additionally asserts the general characterization: for `m<N`, equality in the printed last member of (11) holds exactly when the population CDF at the threshold equals `1/2`. The theorem does not state this characterization, while the record says `whole` and declares no restriction.

Add that characterization or declare that only the concrete counterexample is retained. Nothing here invalidates the counterexample or suggests a false theorem.

### P022-T7 — not_faithful, minor

Both infinite scaled tail limsups are correctly asserted for the corner population ([Defs/Part5.lean:173](SAP/P022/Defs/Part5.lean#L173)). The canonical second example states more: convergence in probability of `N|hat_V_H−V|` to `1/2`, threshold probabilities tending to one, and convergence of the scaled probability sequence to infinity. The formal statement gives only the last sequence's **limsup** as infinity. That does not assert these stronger limits.

The row choice `q=4r` means `N=4(r+1)`, which is the same cofinal subsequence of multiples of four; there is no indexing error. Add the stronger limits or declare that the theorem retains just the hypotheses and two infinite limsups, omitting the explicit finite-N calculations and stronger convergence assertions.

### P022-T9 — not_faithful, minor

The negative-output example and both endpoint discrepancy identities are correct under the exact canonical cell-width hypothesis ([Defs/Part5.lean:218](SAP/P022/Defs/Part5.lean#L218)). The canonical general identity also asserts that the shifted weights sum to `1−2e` and explicitly compares translation invariance of the correct estimates with its failure for the code expression. Neither assertion appears as a conclusion of the formal theorem.

These are elementary consequences of the definitions and discrepancy formulas, and the core printed-code error is already demonstrated. Nevertheless, `whole` overstates the explicit coverage. Add the two assertions or declare their omission, retaining the counterexample and discrepancy formulas.

### P022-T17 — restriction_inaccurate, minor

The theorem covers the entire canonical CLT/coverage target ([Defs/Part6.lean:105](SAP/P022/Defs/Part6.lean#L105)). The record and Challenge docstring call it restricted because it drops the “narrowest … assured” assertion. But `claims.json`, `P022-T17.canonical_claim.note`, expressly says those words **“are not a target”** and identifies the coverage limit as Remark 4's formal content.

Set `decision=whole`, `restriction=null`, and remove the restriction paragraph. Retain the existing statement. This is a metadata/docstring correction: there is no omitted canonical CLT or coverage conclusion and no added CLT hypothesis. The step-2 `whole` reading is unchanged.

## Accepted restrictions and remaining decisions

T6 is correctly restricted. Its docstring accurately discloses that the functions and constant are selected after the sequence, parameters, and two tolerances, and that their positivity/monotonicity, law-only dependence, and minimization are not asserted. The Lemma 2 conclusions and earlier six rate bounds are already explicit conditional premises of the canonical parts (c)–(d), so these are not newly assumed conclusions.

T10 is correctly restricted. The statement and disclosure agree about retaining the fixed-observation identity and limit and the bounded-variance, eventually fixed-arm approximation, while dropping the exact actual-variance remainder and the special numerical formulas. No unsupported R execution claim is made.

The `whole` decisions for T2, T3, T4, T8, T11, T12, T13, T14, T15, and T16 are correct. All target/theorem mappings in the record exist. No step-2 reading or classification was changed after reading the record.

## Definition and nonvacuity checks

The population/design definitions match deterministic potential outcomes and uniform random disjoint treatment/control groups. Uniform permutation averaging introduces the constant multiplicity `m! k! (N−m−k)!` per unordered group assignment, so it gives exactly the intended distribution. Designs ensure nonempty populations and arms, and positive statistical denominators.

CDF distances are genuine bounded real suprema. All probability limsups are in `ENNReal`, so infinity is represented honestly. The uniform-square-integrability definition explicitly bounds its supremum sets; this prevents the real unbounded-supremum default. The compatible-law extrema are nonempty and bounded under the relevant moment hypotheses. Finite empirical-quantile integrands are bounded measurable step functions. Rank-zero/endpoint conventions affect only null endpoints in the substantive quantile integrals. No junk integral, truncated subtraction, empty index set, or division-by-zero convention was found to drive a claimed result.

T12's numerical implication to `False` is an intentional incompatibility assertion. Its lack of a jointly satisfying numerical instance is the intended conclusion, not an accidentally vacuous statistical claim. The corner population gives a bounded nonsingular instance for T17, with limiting covariance matrix `diag(1/4,1/4)` and `gamma=1/2`. For T6, the all-zero balanced population makes the conditional Lemma 2 and six earlier rate premises genuinely satisfiable.

Validation performed:

* `scratch/Check.lean` compiled with `/home/ubuntu/sap/tools/sap-lean`. It imports only the supplied definitions and checks a real assignment, a nonconstant finite bounded-outcome instance, simultaneous Table 1 rounding-bin/Wald hypotheses, a nonconstant finite Jensen instance, fixed-arm bounded variances, and bounded third moments for the corner sequence.
* `scratch/AsymptoticNonvacuity.lean` compiled with the same wrapper. It constructs the balanced-arm allocation limit and proves conditions 1–3, atom-left convergence, and uniform square integrability for `zeroWitness` and `originLaw`. The compile log is `scratch/asymptotic-nonvacuity.log`; remaining diagnostics are style warnings only.
* `python3 scratch/finite_audit.py` passed **7,434 exact rational assertions** across **558 assignment instances** in five designs, including partial sampling. Checks cover unbiasedness, actual variance, sampled-CDF variances, integrated-CDF moments, the seven-term decomposition, finite endpoint bounds, midpoint/rank/overlap identities, printed-code discrepancies, and fixed-sample formulas. Results are in `scratch/finite-audit-result.json`. These finite checks support the audit; they are not asserted to prove asymptotic theorems.
* Python parsed `claim-stage.json` and `findings.json` and checked one entry per canonical target, exact target order, required fields, verdict/severity enums, and confidence ranges. The report counts were checked against `findings.json`.

The blind reading was saved in `reading.md` before opening `claims.json`; the claim-stage judgments were saved in `claim-stage.json` before opening `record.json`. No Solution or Comparator sources were inspected, no source theorem was edited, and no `lake` command was run.
