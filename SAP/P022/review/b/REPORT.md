# Referee report

The package has **18 targets: 13 correct whole, 2 correct restricted, 2 inaccurate restriction/coverage declarations, and 1 not faithful**. No current Lean statement was found false or accidentally vacuous. There are no omitted targets. Severity: **15 none, 2 minor, 1 major**.

| Verdict | Count |
| --- | ---: |
| correct_whole | 13 |
| correct_restricted | 2 |
| restriction_inaccurate | 2 |
| not_faithful | 1 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

## Findings requiring changes

**P022-T18 — not faithful; major.** The canonical target is the positive printed Lemma 2. The [definition](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Defs/Part6.lean:127) instead starts with its negation. The [docstring](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Challenge/Part1.lean:78) says it is a refutation, while the record marks it `whole`. Those are different mathematical propositions. The negation is true; the positive target is false, as the reciprocal population in T1 demonstrates. Mark the unchanged positive target omitted for that explicit mathematical reason, and retain the present theorem only as a separately identified auxiliary refutation. A target cannot be covered by proving its opposite.

**P022-T1 — inaccurate whole-coverage declaration; minor.** The [statement](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Defs/Part5.lean:12) correctly formalizes negative-reciprocal counterexample A. The canonical text also includes counterexample B: bounded four-corner outcomes perturbed by a vanishing negative shift, with a nonsingular limiting distribution. B is absent. The record says `whole` and the [docstring](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Challenge/Part1.lean:7) does not declare the omission. This does not undermine A's refutation of the printed lemma. Either add B and the other explicit canonical assertions, or mark the target restricted and use the precise disclosure given in `findings.json`.

**P022-T5 — inaccurate whole-coverage declaration; minor.** The [statement](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Defs/Part5.lean:91) gives the correct four-unit counterexample. The final general assertion in the canonical target, that for `m<N` equality in the quarter-factor variance bound holds exactly when the population CDF is `1/2`, is missing. The record says `whole` with no restriction; the [docstring](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Challenge/Part1.lean:23) describes only the example. Add the universally quantified characterization, or explicitly disclose its omission. The issue concerns this additional canonical sentence, not whether the example refutes the printed equation.

## Record assessment for the remaining targets

The `whole` decisions for T2, T3, T4, T7, T8, T9, T11, T12, T13, T14, T15 and T16 agree with their mathematical scope.

T6 is **correct restricted**. Its [restriction text](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Challenge/Part1.lean:27) accurately states the quantifier order: the selected integer functions and constant may depend on the sequence, parameters, `epsilon1` and `xi`. Their positivity and monotonicity are not asserted, law-only dependence and minimization are dropped, and both Lemma 2 conclusions and the earlier six rates remain explicit hypotheses. The finite decomposition, inclusions and tolerance identities are retained.

T10 is **correct restricted**. Its [restriction text](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Challenge/Part1.lean:44) matches the retained fixed-sample identity and limit and eventual-fixed-arm actual-variance limit. It discloses the missing exact actual-variance remainder and the `(0,1)` formulas/examples. Its mention of R execution is conservative; the canonical note already excludes floating-point execution from the mathematical target.

T17 covers the **whole canonical mathematical target**. The record conservatively calls it restricted because it drops interval optimality. The final paragraph of the T17 canonical note explicitly excludes that optimality prose from the target. The CLT, admissible hypotheses, gamma range, actual-variance limit and literal coverage limit/lower bound are all present. The [docstring](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Challenge/Part1.lean:73) accurately says what is absent from the stronger paper prose; this is harmless overdisclosure, not an undisclosed mathematical restriction.

No step-2 verdict was changed after reading the record. All 18 targets are mapped to theorems, so no actual omission decision needed assessment.

## Definition, truth and nonvacuity checks

The [blind reading](/home/ubuntu/sap/tasks/CHFID-P022-b/reading.md) was saved before opening the claims; [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P022-b/claim-stage.json) was saved before opening the record. No Solution, Comparator or external formalization source was read. The [paper](https://arxiv.org/pdf/1405.6555) was consulted for its population setting and printed lemma/corollary; the supplied canonical claims remain the comparison standard.

Finite permutation averages induce exactly the paper's uniform disjoint-subset assignment distribution. Populations and samples are nonempty, and all substantive design denominators are positive. Empirical quantile endpoints differ from extended-real inverse conventions only at measure-zero points. Integrands are bounded step functions. All CDF-distance ranges are nonempty and bounded by one. UI2 requires bounded tail ranges explicitly; this is implied by genuine uniform square integrability. Compatible-law covariance extrema are over nonempty sets with common finite second moments. Scaled tail limsups are in extended nonnegative reals, so infinite values are genuine divergence.

T7's zero-threshold event intentionally evaluates the printed expression at `epsilon1=1`; it actually refutes the printed bound. T12's numerical incompatibility clause intentionally proves that its constraints have no joint solution. Neither is accidental vacuity. T14's full-sampling hypothesis is already part of the canonical formal reading.

[Nonvacuity details](/home/ubuntu/sap/tasks/CHFID-P022-b/scratch/nonvacuity.md) give witnesses for every family of hypotheses, including a nonsingular periodic population for T17 and a zero-outcome sequence satisfying all of T6's conditional hypotheses. The T11 display bins and common multiplier admit a complete exact witness, including both variance bins; they do not secretly contradict each other.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` passed (exit 0; one harmless proof-style warning). It imports only Defs and checks finite design constraints, nonconstant bounded finite outcomes, a fixed-arm sequence, corner bounds and bounded third moments, the full T11 rounding/Wald witness, T12's multiplier hypotheses, and T9's cell-width condition. The sequence-limit and nonsingularity arguments in the accompanying notes are mathematical arguments, not claimed Lean certificates.

`python3 scratch/audit_checks.py` passed **26,423 exact rational checks**, including uniform allocation expectations and variances for every design with `4<=N<=7` on the specified arrays, finite rearrangements, the seven-term decomposition, original partition/rank/overlap formulas and shifted-code discrepancies. [Results](/home/ubuntu/sap/tasks/CHFID-P022-b/scratch/audit_checks.json) are reproducible. These checks support the finite calculations; they do not purport to prove the asymptotic theorems.
