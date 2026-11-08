# P010 review: T11–T15

Process: blind reading (`reading.md`), then a check against the claims (`claim-stage.json`), then a check against
the record. Outputs: `findings.json`; scratch checks in `scratch/`.

| Theorem | Record decision | Verdict | Severity |
|---|---|---|---|
| SAP.P010.T11 | whole | faithful | none |
| SAP.P010.T12 | whole | faithful | none |
| SAP.P010.T13 | refuted | faithful | none |
| SAP.P010.T14 | whole | faithful | none |
| SAP.P010.T15 | whole | faithful | none |

## Notes

- **T11** (Defs/Part4.lean:64). This is the validator's eight-subject counterexample to the formal
  exact-matching reading of footnote 7. It shows that the saturated logistic fit (unique log-likelihood
  maximiser, intercept log(1/3), slope log 9) equals the true propensities, and that the printed odds weights give
  share 27/28 ≠ 1/4. The reciprocal odds recover f_O. The claim refutes a *reading* of printed guidance, so the
  `whole` label is right, and the docstring names the reading and does not say "printed claim is false". Checked
  with exact fractions.
- **T12** (Defs/WholeW1.lean:38). Every clause of corrected footnote 7 is stated:
  - (i) the Bayes odds identities;
  - (ii) the transport by reciprocal odds, the (1−π)/π normaliser, and cancellation of any positive constant;
  - (iii) the printed weights give f_R²/f_O normalised by Z when Z < ∞, with Z > 0, and this equals f_O iff
    f_R = f_O a.e.;
  - when Z = ∞, the mass is infinite and no constant c ≥ 0 gives a probability measure;
  - the original-coding identity odds(1−p) = (1−p)/p.

  The statement avoids the Bochner junk value when Z = ∞ by using `lintegral` and `withDensity`. Counting measure
  covers the discrete case. The scale-cancellation clause is stated only for c > 0. That is the meaningful case:
  weights are nonnegative, and c = 0 is degenerate.
- **T13** (Defs/Part6.lean:162). Printed reading: under Assumptions 1–3, continuity, Pr[all pass] > 0 and r < 1,
  E[Y(1) | U=1, S(1)=1] ≤ E[Y(1) | Y(1) ≤ Q_{Y(1)|S(1)=1}(1−r)].
  - The witness `normalCommonPopulation` is the validator's, and the statement proves every condition.
  - The left side is 0. The printed right side, which lacks S=1 in the tail conditioning exactly as printed, is
    −φ(q)/(3/4) < 0.
  - `q` is hard-coded as Φ⁻¹(3/4). `scratch/T13q.lean` derives from the certified T13 and T15 statements that the
    witness's conditional law of Y(1) given S(1)=1 is N(0,1) and that 1−r = 3/4, so `q` is the printed quantile.
  - The witness contradicts the printed display's own assertion, so `refuted` is right.
- **T14** (Defs/Part6.lean:180). The hypotheses are exactly the corrected statement's: Pr[all pass] > 0, and
  Y(1) given S(1)=1 is continuous with a finite mean. The standing Assumptions 1–3 are omitted. The claim says
  (i)–(iii) involve only the potential variables, so omitting them only makes the statement stronger. The clauses
  stated are:
  - (i) the fixed-mass maximisation over all couplings, with the upper-tail coupling attaining the maximum and the
    maximum monotone in p;
  - (ii) the union bound p_{U⁰} ≤ r;
  - (iii) the bound for r < 1, written with the S(1)=1-conditional quantile and law.
- **T15** (Defs/Part6.lean:200). Under Assumptions 1–3 (corrected 3), Pr[all pass] > 0, continuous Y and
  E[|Y| | Z=1, S=1] < ∞, it states:
  - (i) the law and pass-rate identities;
  - (ii) potentialTrimShare = trimmingRatio, i.e. the focal-arm denominator r₁;
  - (iii) the corrected observable upper bound.

  The tail-mean equality of (ii) is stated only when r₁ < 1. For r₁ ≥ 1 those conditional expectations do not
  exist, so this guard only presupposes that they exist; it is not a narrowing. The docstring discloses it.

No junk value affects any of the five statements; details are in `reading.md`. Nonvacuity: `scratch/Nonvac.lean`
compiles a one-arm Gaussian population satisfying all hypotheses of T14 and T15, and a one-point instance for
T12. T11 and T13 are closed statements.
