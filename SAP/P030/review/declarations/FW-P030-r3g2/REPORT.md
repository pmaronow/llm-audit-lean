# P030 declaration review

All five declarations are **faithful**, with severity **none**. Each recorded
`whole` decision is justified. No step-2 conclusion changed after reading the
record. The docstrings accurately describe the corresponding statements.

- **T6** covers the no-interference implication, observed-outcome imputation,
  the entire uniform conditional reference distribution, and a genuine
  counterexample to statistic constancy. Its CDF equality, specialized to the
  observed statistic, also gives the canonical Equation (2) p-value identity.
  The observed assignment guarantees nonempty conditional support.
- **T7** uses the corrected same-unit treatment comparison throughout. All
  treatment/outcome invariance implications, the variation contrapositive,
  arbitrary direct effects, and the no-effects implication are included.
- **T8** states the canonical counterexamples themselves, appropriately labelled
  `whole`. It includes the observed ranks and both moment conventions, all six
  printed and corrected formula values, square comparisons, the ordering
  reversal, and the nonconstant weakly monotone example with its detailed
  computations and rounding. The weak example concerns weak monotonicity;
  it says nothing adverse about strictly monotone tie-preserving relationships.
- **T9** includes every corrected rank-correlation clause: means, definedness,
  divisor independence, bounds, the exact proportionality criterion with signs,
  both tie-preserving order cases, the weak example, and the table. The identity
  for every positive divisor strengthens the two conventional cases correctly.
- **T10** uses actual off-diagonal sums and a generic Option-valued partial
  quotient for the undefined self term. It includes all inverse-square values,
  decay, non-exponential character, the explicit divergence bound, and the finite
  exponential limit. Positive off-diagonal matrices include the canonical
  distinct-position Euclidean case. The canonical `definitions_needed` expressly
  excludes mean normalization from formal content; this conclusion does not
  rely on the audit-history note.

The blind reading was saved in `reading.md` before opening the claims;
`claim-stage.json` was saved before opening the record. All 101 distinct closure
declarations were inspected, including 49 printed generated auxiliaries.

Both `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` and
`/home/ubuntu/sap/tools/sap-lean scratch/Witnesses.lean` completed successfully.
They import only `SAP.P030.Defs`, use no audited stubs or `sorry`, and establish
concrete hypotheses and genuine witnesses, including the ten-unit statistics
with distinct squares 1/90 and 25/36. `scratch/numerics.py` separately passed
exact rational checks of the conditional support, six-row ranks and moments,
both printed-formula arrays, ordering reversal, and rounding tolerances.

Empty supports, empty minima, zero rank variance, and zero inverse-square
arguments have totalized values in some definitions. The asserted statistical
and scalar uses exclude those cases. T10 explicitly models the partial self
quotient rather than treating Mathlib's zero-valued division by zero as ordinary
defined arithmetic. No additional measure-theoretic restriction is imposed;
the randomization spaces and all sums are finite.
