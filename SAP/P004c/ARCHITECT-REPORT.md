P004c packages the 13 targets assigned in `work.json`: **7 whole, 2 restricted,
0 refuted, 4 omitted**. All **9** retained theorems are proved. There are **0**
open glue tasks. Other units' targets are excluded.

The whole targets are T31, T32, T33, T39, T40, T41 and T42. T31 includes the
corrected sharp-null definition, unconditional arm-count identities, the unique OLS fit,
the sandwich identity, the negative-eigenvalue expansion, all six semidefinite
assertions and the actual treatment-entry ordering. T32 includes the exact
expansion, the upper bound obtained by dropping the negative diagonal term,
both component bounds and their orders, and the actual variance order. Its
diagonal rate requires bounded outcomes alone. T33 retains the variance
expansion, homophily identity and equivalence, and every standardized-summand
assertion. T40 uses genuine spatial integrals and arbitrary marginal design
laws. T41 includes both the variance order and the Gaussian limit.

The restricted targets are:

- **P004-T34**, Supplement A pp. 35-36, eqs. (124), (127)-(129): retains the
  corrected absolute-value identities, finite kernel cross-sum bound,
  Bernoulli denominator order and scalar witness arithmetic. It drops the
  composed bandwidth conclusion `O_p(N^(-1/2)*b_N^2)=o_p(1)` and the certified
  realization of the eight-node assignment, arm-centred residuals, all-pairs
  kernel and `S=-1/4`. Positive sample size and bandwidth make the finite
  kernel formula meaningful. The denominator error is defined on nonempty
  treated arms and extended by zero on empty arms; its rate follows by event
  inclusion from the exported rate. The scalar arithmetic is not presented
  as a certified spatial or regression counterexample.
- **P004-T44**, Supplement A pp. 28-29, Lemma C.4 and Proposition 5: retains
  unbiasedness, the HT variance order, the root-N linearization remainder
  and the nondegenerate Hajek Gaussian limit under the credited theorem's
  actual spacing premise. That premise uses `C_b*(1+s^2)` and one eventual
  sample-size threshold for all radii simultaneously, replacing the printed
  radiuswise-eventual `C_b*s^2` premise. Finite unbiasedness is asserted for
  positive sample sizes with genuine averages. Eventual spatial regularity
  and the Appendix C metric node-distance assumption are explicit.

The omitted targets are:

- **P004-T35**: both narrower rows negate a universal over arbitrary metric
  measurable spaces. Their exported statements do not place a counterexample
  in the canonical two-dimensional spatial domain. They establish no positive
  component of the printed proposition either.
- **P004-T36**: the sole row has final status `wrong_credit`. Its fitted-IPW
  numerator differs from the canonical printed Hajek numerator. It establishes
  neither the printed coverage assertion nor its refutation.
- **P004-T37**: the narrower row concerns arbitrary real circle tables and
  positive weights. Its statement does not certify a common binary spatial
  outcome field and ordered distance bands partitioning each regional average.
  The empirical estimate and p-value are outside the mathematical target.
- **P004-T43**: the negative row has the same larger-domain problem as T35.
  The two usable finite rows are oracle variance auxiliaries; they do not
  establish the printed ordinary-limit coverage conclusions. Packaging those
  bounds alone would substitute helper facts for the coverage claim.

The shared-definitions route is used throughout. `Defs/Part1.lean` through
`Defs/Part5.lean` import only Mathlib and earlier Defs parts. Challenge and
Solution import these same compiled modules, and each theorem's type is its
shared `T<k>Statement` constant. The Challenge imports no project module.

The bridges are:

- `Bridge/Part1.lean`: a field-preserving adapter from the SAP spatial
  structure to the project structure, applied pointwise to sequences. All
  displayed data and statistical correspondences are definitional, proved
  by reflexivity. Positive semidefiniteness is translated to Mathlib's
  `Matrix.PosSemidef` using the existing project equivalence.
- `Bridge/Part2.lean`: distributes finite sums and the two Boolean arm signs
  to expand the exported variance formula; uses the existing `barMu_difference`
  identity to centre homophily at the AME; and distributes spectral sums using
  `max(v,0)-v=max(-v,0)`. The unbounded-outcome exact HT formula instantiates
  the existing `augmented_variance` declaration at zero fits. These are
  algebraic correspondences, with no new variance argument.
- `Bridge/Part3.lean`: converts the exported component inequalities to their
  orders by the definition of `IsBigO`, and uses the existing probability
  monotonicity lemma for the nonempty-arm denominator error.

The main concerns were the domain of negated universals, the printed estimator
name in T36, the difference between ordinary coverage limits and lower limits,
and the quantifier strengthening in T44. The literal printed quadratic bound
at radius zero cannot hold for a nonempty population; the nonvacuous spacing
premise is therefore identified as a change, not silently read into the claim.
Spatial averages require measurable regions of positive finite measure and
integrable outcomes. Node sets are nonempty, so their separation infima have
nonempty, bounded-below defining sets. Finite standardized sums require
strictly positive variance. For asymptotic standardization, `Nondegenerate`
ensures a positive variance denominator eventually. Empty-arm means use the
supplement's zero convention.

All five Defs parts and their root, all three Bridge parts and their root,
the Challenge part and root, and Solution compiled with the supplied
`sap-lean` command in dependency order. `scratch/P004cAxioms.lean` also compiled:
each of the nine theorem dependency lists is exactly
`[propext, Classical.choice, Quot.sound]`. Both JSON files parse, their target
and theorem inventories agree, and every SAP file is at most 300 lines.
Existing project sources were unchanged.

`SAP/P004c/comparator.json` supplies the requested Comparator configuration.
The orchestrator-supplied [Comparator result](SAP/P004c/verification/comparator-result.json)
records acceptance by all three kernels for the original snapshot stamped
`20261103T204229Z`. That result predates the T31 statement correction below
and does not certify this revised snapshot. The revision's completed checks
are Lean compilation and the dependency checks described below; renewed
external Comparator certification remains pending.

## Declaration review round 1

- **SAP.P004c.T31 / P004-T31 — `label_wrong`, minor.** Accepted both issues
  in the review's [T31 finding](fw/round1/T31/r1g1/findings.json): the
  positive-arm premises wrongly qualified all three count identities, and
  the `whole` label and docstring therefore overstated the old statement's
  scope. The [canonical corrected clause (a)](work.json:42) states the counts
  unconditionally and qualifies only the OLS minimizer by nonempty arms.
  Moved those premises after the count identities in
  [T31Statement](SAP/P004c/Defs/Part4.lean:13). The counts now hold for every
  assignment, including all-control and all-treated assignments; regression
  and matrix conclusions retain their positive-arm premises.
- The [Solution](SAP/P004c/Solution.lean:16) uses the existing unconditional
  `AronowAudit.P004.MatrixCompletion.counts_total` and `sum_bit` declarations,
  plus finite Boolean simplification and one-line arithmetic. There is no
  new mathematical argument. The Challenge docstring now spells out the
  unconditional scope. T31 remains `whole`, with no restriction, and the
  manifest records the additional supporting declaration.
- Recompiled every SAP module in dependency order and reran all nine
  `#print axioms` commands in `scratch/P004cAxioms.lean`. Each dependency list
  remains exactly `[propext, Classical.choice, Quot.sound]`.
  [Count-scope checks](scratch/P004cCountScopeRound1.lean) extract the three
  identities for an arbitrary assignment without positivity assumptions and
  instantiate the complement identity at both empty-arm boundary cases.
  Both JSON files were regenerated and parsed; the Comparator still lists
  the same nine fully qualified theorem names. Counts remain 7 whole,
  2 restricted, 0 refuted, 4 omitted; 9 proved and 0 open glue tasks.
- The shared `T31Statement` definition changed, so T31 requires renewed
  declaration review. No other statement definition or statistical
  definition was edited. No reviewer finding was rejected.
