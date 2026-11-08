# Review of P016-T8 through P016-T11

All four declarations are faithful, with severity `none`. All four `whole`
decisions in `record.json` are correct; their docstrings accurately describe
their statements. No step-2 conclusion changed after reading the record.

The blind reading and junk-value audit were saved in `reading.md` before the
claims were opened. `claim-stage.json` was saved before the record was opened.
Every declaration listed in the four closures was read, including the generated
auxiliaries inspected by `scratch/ClosureCheck.lean`.

| Declaration | Clause-by-clause assessment |
| --- | --- |
| T8 | `Defs/Part5.lean:69` gives additive adjustment and recovery; `:72` gives equality of laws and inclusive-upper-tail calibration; `:80` gives the raw mean shift and its exact equality condition. The design can be represented by arbitrary finite indices; taking the canonical assignment set as indices recovers the claim directly. |
| T9 | `Defs/Part6.lean:12` gives both signed-KS labelings; `:16`, `:29` and `:30` give the pooled total, complete residual table, contrasting tails and general point-mass law; `:20` gives the six-unit intercept discrepancy and actual minima. The docstring correctly identifies the pooled-mean and missing-intercept **readings**. These are the canonical claim's own counterexamples, so `whole` is appropriate. |
| T10 | `Defs/Part6.lean:37` gives the simple regression minimum and exact minimizing coefficients; `:44` gives general attainment and unique fitted vectors without a rank assumption; `:49` gives the KS supremum, label invariance and bounds, including ties; `:53` gives the two network-column identities. The extra explicit `2 <= n` follows from the two nonempty groups. Binary adjacency is part of the canonical definitions. |
| T11 | `Defs/Part2.lean:83` matches the directional effect-increasing definition. `Defs/Part6.lean:65`, `:72`, `:77` and `:79` give every weak/strict KS witness, CDF entry, opposing SSR change and monotonicity failure. The claim concerns these failures; it does not assert invalidity of randomization tests. |

Means and CDFs in the numerical witnesses have denominators two. The explicit
positive-size assumptions protect the general mean and KS identities. Although
`EffectIncreasing` also quantifies over assignments with an empty group, all its
reported failures already have two units in each group. A `FiniteLaw` cannot
exist on an empty type. Least-squares infimum sets contain the zero-coefficient
objective and are bounded below by zero; the CDF-difference supremum range is
nonempty and bounded above by one. None of the conclusions depends on a junk
value or a hypothesis encoding the conclusion. The pooled statistic's constant
law is intentional canonical content, not an artificial trivialization.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/ClosureCheck.lean` and
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` both completed with exit
code 0. Both import only `SAP.P016a.Defs`, and the checks use no Challenge stubs
or admitted proofs. The latter constructs simultaneous hypothesis instances,
checks the exact counterexample values and directional inequalities, establishes
the two six-unit regression minima by universal lower bounds and attaining
coefficients, and checks a rank-deficient minimum with distinct coefficients but
identical fitted values. Its output contains only unused-variable linter
warnings. `findings.json` and `claim-stage.json` were parsed and their target
coverage checked with Python 3.
