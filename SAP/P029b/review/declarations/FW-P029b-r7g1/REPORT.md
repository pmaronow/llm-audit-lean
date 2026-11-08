All five declarations are **faithful**, with severity **none**. Their `whole`
decisions are correct. No claim-stage conclusion changed after reading the record.
The current docstrings accurately describe the statements and their usual
measure-theoretic conditions.

The blind expansion and junk-value review were saved in `reading.md` before the
canonical claims or review history were opened. Every closure declaration was
read, including the generated auxiliary declarations printed by
`scratch/ClosureChecks.lean`. `claim-stage.json` records the independent comparison
with each canonical statement and its definitions.

- **T14:** Includes the unconditional unique ordered-binomial maximizer, its
  identification with the clipped rate difference, interior nested parameters,
  all bias and probability bounds, the extreme event, individual and simultaneous
  finite-stratum consistency, and one-sided unbiasedness. Its arm law really is
  the product of binomial masses. Numerical checks realize strict bias and both
  fitting branches; a separate two-stratum instance realizes all joint-consistency
  hypotheses with growing arms.
- **T15:** Uses exactly the canonical six-atom law. Both quantile conventions
  exist and have the claimed value, including at the power levels. The fixed
  score is consistent and satisfies overlap; the cutoff stays positive while
  scores and weights remain unchanged. The population ICSW ratio and ATE are both
  one. The sample identity on undefined inputs is merely an identity of identical
  real-valued expressions and does not supply the counterexample.
- **T16:** The reindexing from sample size N to Lean's n+1 preserves the type-7
  rank, floor, fraction and weight bounds. The limit component uses the canonical
  finite-profile iid assumptions, uniform score consistency and overlap. It
  concludes both specified probability limits, their vanishing difference and
  ATE identification under Assumption 1. It adds neither eventual sample-definedness
  nor a supplied conditional-expectation characterization. A compiled infinite
  product model realizes every hypothesis, including measurable power-level
  cutoffs.
- **T17:** States the corrected Bernoulli product, the one-sided treated-arm
  reduction and equality of maximizer predicates. It also states the general
  formulas and lower bound for the misprinted additive expression and all four
  specified values at three quarters. The checked observation type is nonempty
  and contains both assignment arms and both treated receipt outcomes.
- **T18:** Includes the conditional probability definitions and partition,
  both receipt formulas, the nested representation, universal discrepancy clause,
  probability range, actual weighted-ITT integral identity and cancellation, and
  the corrected sample-display equality. The integral uses the covariate law and
  conditional-mean versions, with existing expectations and positive compliance
  almost surely; it imposes no uniform overlap bound. Separate compiled laws
  realize every discrepancy antecedent and every integral-identity hypothesis;
  a sample instance has nonzero arm and first-stage denominators.

For T15, the printed assertion being tested is: under the IV assumptions and
Assumptions 1--3, the empirical n^(-alpha) cutoff tends to zero for fixed alpha>0.
The witness meets each condition:

- Independent random assignment, exclusion/SUTVA, relevance and no defiers:
  the six-atom product law has observed Y=D and receipt-arm means 3/4 and 1/4.
- Assumption 1: every potential treatment effect equals one.
- Assumption 2: the oracle half-score estimates have zero error for every n.
- Assumption 3: the true score is 1/2, strictly above epsilon=1/4.
- Fixed positive alpha and the specified sample quantile: both quantile
  conventions return 1/2 for every nonempty constant vector and power level.
- Independent observations and usual measure conditions: independent copies of
  the finite law exist; all functions are measurable and all relevant moments
  are finite. No dependent-replicate construction is needed.

Thus this witness contradicts the cutoff-to-zero assertion itself. It does not
contradict the assertion that Winsorization has no effect in this example. The
record correctly labels the complete canonical counterexample `whole`.

The sole earlier issue, concerning T18's description of its three probability
conditions, is fixed in both docstrings: they now specify zero always-takers and
the two actual half-probabilities. It is recorded in `resolved`, with no current
issue retained.

All four scratch files compiled successfully using `sap-lean`; the instances use
definitions and Mathlib without invoking the five Challenge theorem stubs.
Finite nonempty vectors and explicit positive denominators prevent the relevant
quantile and population junk values. T16 expressly permits real-valued extensions
on undefined samples. No undefined quantity or nonmeasurable function is used as
a refutation. The JSON outputs were parsed and checked for exactly one entry per
assigned declaration and exact fingerprint agreement with `closure.json`.
