# P041 declaration review

All five declarations are faithful. T2 is a correctly disclosed restriction;
the other four cover their canonical mathematical claims. No definitions
trivialize a statement, and no asserted calculation uses an inappropriate
junk value. The record required no change to the claim-stage conclusions.

| Declaration | Record decision | Assessment |
|---|---|---|
| SAP.P041.T1 | whole | All exponential laws, common non-null ratios, exact contrasts and four positive binomial masses are present. |
| SAP.P041.T2 | restricted | The numerical bounds, interval membership, pooled contrasts and existential model are present. Challenge/Part1.lean:17 and record.json:22 accurately disclose the omitted comparisons, interpretations, finer approximations and exact model contrasts. |
| SAP.P041.T3 | whole | All three directional failures, corrected roundings, symmetric alternatives and general positive-gap identity are present. |
| SAP.P041.T4 | whole | Every corrected percentage, decimal enclosure, whole-number rounding, hypothetical 76-count calculation and symmetric alternative is present. |
| SAP.P041.T5 | whole | The full scrutiny model, six orders, general formulas, size-50 instance and both boundary checks are present. |

The counterexample readings and their conditions were checked separately:

- **T1:** a smaller absolute contrast does not entail absence of relative
  bias. Required conditions are genuine positive removal hazards, common
  proportional non-null ratios, the stipulated populations and horizons,
  and independent facts for the binomial interpretation. Both supplied
  parameters lie in (0,1); the rates are positive and the ratios equal 2/3.
  Independent exponential times can be constructed by a finite product of
  their laws. Every observed count is within its arm size and has positive
  mass. This establishes the canonical countermodel without asserting an
  empirical bias estimate.
- **T3:** “more likely than” means a directional increase over the reference
  removal risk, rounded to a whole percentage. The conditions are the supplied
  counts, equal arm sizes, positive reference risks and the specified rounding
  cells. All hold. Each directional value misses its printed cell; the symmetric
  values match. The docstring explicitly distinguishes the two readings.
- **T5:** uniformly random insertion order alone does not ensure that an
  accelerated protocol preserves the contrast. Conditions include an order
  independent of balanced assignment, the specified past-only scrutiny rule,
  zero slow outcomes, and the stated contrast. A uniform permutation gives
  each m-subset of cited ranks the same multiplicity m!², exactly the law in
  balancedExpectation. The response rule and both schedules are those of the
  canonical construction. The independent-assignment boundary uses all sixteen
  equally likely assignments and the correct Horvitz–Thompson weights.

T1, T3 and T5 establish canonical counterexamples; their `whole` labels are
appropriate. None purports to refute its own canonical assertion. T4's
76-removal expression is evaluation at a hypothetical input, not an assertion
that the deposited stored-duration count is 76.

The blind reading was saved in reading.md before claims.json was opened;
claim-stage.json was saved before record.json was opened. Every closure entry,
including the generated numeral proofs, was inspected through Lean printing.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit status
zero, importing only Defs. It checks the concrete hypotheses and witnesses,
the complete T4 conjunction, nonempty balanced support for every m, and the
balanced and independent four-rank expectations. Separate exact enumeration
checks m=1 through 7 and the combinatorial size-50 moments. The scratch checks
supplement the supplied proof certification; they do not replace it.
