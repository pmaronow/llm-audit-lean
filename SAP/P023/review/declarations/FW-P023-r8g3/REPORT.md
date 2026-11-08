# Declaration review

Both current declarations are faithful to their recorded scope. The blind
expansion is in reading.md; it was saved before the claims and prior-review
materials were opened. claim-stage.json was saved before record.json was
opened. The record required no changes to the claim-stage conclusions.

SAP.P023.T11 has narrower coverage than the full canonical claim: it proves
the printed estimator equality under Conditions 1–3 and positive winner/loser
counts, and omits the necessity remark in claims.json:26. The current
`restricted` decision at record.json:4 and restriction at record.json:6
describe exactly this omission. Both docstrings disclose it
(Challenge/Part1.lean:89 and Defs/WholeW2.lean:21). The sole earlier issue is
fixed. The definition's legacy name does not override its explicit restriction.
The bin widths, ceiling, omitted reference bin, half-open central window,
binary tie flexibility, and quantification over every OLS solution all match
the canonical estimator. No full-rank assumption was added.

scratch/Nonvacuity.lean compiled successfully using sap-lean. At k=1/2,
margins (-1/4,1/4), indicators (0,1), and outcomes (3,5), it verifies all
hypotheses, both positive counts, RD=2, and two distinct OLS coefficient
vectors (3,2,0,0) and (2,2,1,17); both have party coefficient 2 despite empty
nuisance bins. It also verifies that replacing the positive margin by 1/2
preserves positive counts and RD=2 while Condition1 fails. Omitting the false
necessity remark preserves correct mathematics and is accurately disclosed.

SAP.P023.T12 negates the complete fixed-law reading explicitly specified in
claims.json:39. Its docstring confines the failure to that adopted reading;
the `whole` decision at record.json:25 therefore follows the task's rule for
interpretation-specific refutations. This neither proves the positive
proposition nor declares the undefined printed guidance unconditionally false.
IID independence, compact margin support, continuity, the finite left limit,
conditional means, bandwidth limits, and usual RD regularity remain present.
Extra moment premises inside the negated universal strengthen the required
counterexample. They do not weaken it by allowing a printed premise to fail.

The T12 witness check is detailed in scratch/T12-witness.md, including the
adopted reading, its conditions and verification of each. It uses uniform
margins, the supplied bounded continuous zero-jump h, deterministic bounded
outcomes, independent coordinate samples, and k_N=1/sqrt(N+1). Every printed
condition and every additional formal guard is compatible with that model.
scratch/T12Witness.lean compiled: using the supplied T6 witness specification,
it verifies failure of T12's population-bias tolerance at epsilon=1 without
using T12 itself. The complete infinite sampling model was checked
mathematically, not rebuilt in Lean.

Every declaration in both closures was read, including the generated proof
constants. The finite normal equations and population coefficient definitions
render genuine least squares. Positive finite quantities exclude the relevant
division, non-integrable-integral, and infinity-to-real defaults; sample empty
windows and singular designs are asymptotically negligible in the T12 model.
The author's usual measure-theoretic conditions are assumed throughout. No
definition placeholder, hidden conclusion hypothesis, or junk-value
refutation was found. Only supplied unit sources and the permitted Mathlib
sources were used for mathematical checks. The supplementary paper lookup
reached the [institutional paper listing](https://isps.yale.edu/resource/a-note-on-close-elections-and-regression-analysis-of-the-party-incumbency-advantage);
its publisher full-text link was inaccessible, so the supplied canonical
transcription controls the paper comparison.
