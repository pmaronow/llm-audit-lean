# Declaration review

All five declarations are faithful at their recorded scope. T8, T5, T6 and T16
cover their whole canonical mathematical claims. T7 accurately discloses its
restriction to population expected-likelihood projections that allow
misspecification. No current defect was found.

The blind reading, including every dependency and relevant totalization, was
saved in `reading.md` before the claims and history were opened. All 70 distinct
generated auxiliary closure declarations were printed and read. The claim-only
comparison was saved in `claim-stage.json` before `record.json` was opened; the
record required no change to those conclusions.

T8 includes the actual score derivatives, normalized canonical means, named
Bernoulli and Poisson laws, probit multiplier and example, both linearizations,
the nonzero-factor guards, cancellation criteria and risk-set illustration.
Its Taylor assertion concerns the exact polynomial, with no unsupported
quadratic nonlinear remainder. The T7 construction remains relevant to this
calculus statement, which imposes no correct-specification condition.

T5 and T6 include all specified counts, rank, residual, genuine score,
derivative and nonmaximum assertions. Their converse-reading caveats are
accurate: a residual root that is not a maximum does not contradict the
necessary implication from an ML fit to an estimating equation. Neither is
mislabelled as a refutation of its canonical example.

For the earlier T7 issue, the stronger printed reading is: within the correctly
specified conditional-probability GLM of Appendix C, a regular expansion about
the inverse link of the outcome mean gives the asserted first-order scaling.
Its relevant conditions include the causal assumptions, an admissible model,
correct conditional-mean specification and a path through that model. The
explicit square-link construction satisfies the causal and admissibility
conditions but fails the last two. The current docstring
(`SAP/P015a/Challenge/Part1.lean:94–100`) and record explicitly acknowledge this.
The earlier issue is fixed as a scope/documentation defect; the witness has
not become a correctly specified counterexample. No such refutation is now
claimed.

T16 has all numerical bounds, the all-real fitted-ratio identity and the actual
four-observation OLS example separating exponentiated fitted contrasts from
arithmetic spending means.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` passes using only definitions,
without Challenge stubs. It checks nonvacuity and data validity across all five
items, independently protects the probit infimum, computes the OLS coefficient,
and proves the T7 baseline cannot be fitted by any admissible square-link
parameter. These checks supplement the supplied proof certification; they do
not independently reprove its nonlinear optimization or Gaussian score bounds.
No relevant junk value, inconsistent hypothesis or definition encoding a
conclusion was found. `findings.json` contains exactly the five requested
declarations with their supplied fingerprints and empty current-issue lists.
