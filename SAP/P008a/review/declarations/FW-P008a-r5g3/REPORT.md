# Review of P008-T11–T14

All four declarations are **faithful**, with severity **none**. T11 is faithful
to its accurately disclosed restriction; T12–T14 cover their canonical claims.

The required order was observed: `reading.md` was saved after reading and
printing every declaration in the closures, before opening `claims.json`;
`claim-stage.json` was saved before opening `record.json`. The record caused
no revision of the step-2 conclusions. No other review or formalization files
were consulted.

| Declaration | Claim coverage and record assessment |
| --- | --- |
| T11 | Narrower than the full canonical statement. `Defs/Part8.lean:40–54` includes both exact displayed sums, every rounding bound, exclusion of 12.38, and the strict comparison against values displayed as 7.97. The actual unrounded total, its display 8.00, and certification of empirical percentile outputs are absent. `Challenge/Part1.lean:136–141` and the record accurately disclose those omissions. The lower-envelope example confirms that the retained hypotheses cannot force the 8.00 display. |
| T12 | Whole. `Defs/Part8.lean:57–66` proves the precise canonical incompatibility: the printed grid misses the closed window, all selected sums and finite type-7 percentiles are zero, and the three reported values are nonzero. This establishes the canonical counterexample; it does not refute the canonical counterexample. The docstring and record describe this correctly. |
| T13 | Whole. `Defs/Part8.lean:69–77` and the explicit formula `correctedGrid(k)=k/222` give 41 distinct points starting at zero, the endpoint, spacing, exact four selected indices, kilometre conversion, and their sum for every real array. The docstring and record accurately describe this exact-arithmetic statement. Empirical reconstruction mentioned only in the canonical note is not a missing clause. |
| T14 | Whole. `Defs/Part8.lean:80–86` expresses the corrected identity for every positive finite node count, the exact condition for a real number to equal its square, and the specified two-node calculation. Arbitrary real mean arrays suffice for this algebraic identity and include the intended well-defined circle means. The docstring correctly diagnoses the literal product reading, and the record's whole decision is warranted. |

For T12, the printed reading is: **the specified five-point grid and closed
test window, using sums of the AMR estimates in that window, produce the three
reported nonzero observed/percentile outputs**. Its relevant conditions are the
exact grid `5k/111` for `k=0,…,4`, the endpoint `20/111`, the closed window
`[1/111,5/222]`, ordinary finite summation, and a nonempty finite permutation
sample with the type-7 convention and percentile positions in `[0,1]`.
The theorem checks the grid and its next value, proves selection empty for
every estimate array, quantifies over every nonempty finite sample, and checks
the reported constants are nonzero. Thus it applies to the actual design and
to independently drawn replicates as well: no change to the design or replicate
dependence supplies the incompatibility. It is correctly classified **whole**
relative to the canonical assertion of this incompatibility.

For T14, the literal reading is: **with node effects defined as the given
differences and the stray bars read as the same means, juxtaposition multiplies
the two equal averages**. Its conditions are positive finite `N`, finite real
means, and the pointwise difference definition. The compiled `N=2` example
meets every condition. If a spatial realization is wanted, take two nodes with
disjoint radius-one circles and define the outcome on the first circle to be
`3z₁`, and on the second to be `2+5z₂`, under independent Bernoulli(1/2)
treatment and normalized circle measures. These give precisely the four
specified marginalized means. The theorem affirms the canonical corrected
identity and its diagnosis of the literal product; it does not label the
corrected identity false.

All SAP definitions in the four closures were inspected, including generated
numeral/index proofs and decidability. There are no hidden substantive
hypotheses. All fixed denominators are positive; T14 assumes `N>0` before
inverting it. T12's empty sum is intentional mathematical content, not an empty
mean. `quantile7` is interpolation of supplied entries rather than a sorting
operation, but the only sample passed to it here is identically zero and hence
already sorted. Its index conversions and clamps cannot change that result;
the one-element case is included. No other junk-value conventions affect these
statements.

`/home/ubuntu/sap/tools/sap-lean scratch/Blind.lean` successfully printed all
50 distinct closure declarations. The independent constructions and computations
in `scratch/Check.lean` compiled successfully with the same launcher (exit 0),
without importing the Challenge theorem stubs. These check simultaneous T11
hypotheses and a lower-envelope witness, the actual T12 empty filter with a
strictly positive three-sample array, the T13 selected set/cardinality and a
nonzero sum, and every T14 two-node premise and numerical conclusion. No `lake`
command was run, and at most one Lean process ran at a time.
