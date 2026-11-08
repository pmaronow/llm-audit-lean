P035 packages exactly the three unit targets in `work.json`: **1 whole,
1 restricted, 0 refuted, 1 omitted**. Both listed theorems are proved;
there are **0 open glue tasks**.

- **P035-T1 — whole; `SAP.P035.T1`.** The statement gives the complete
  validator witness, including the three LCM population sizes, integer
  thresholds, valid independent finite design, pointwise observed equality,
  all six calibrated counts and frequencies, zero individual direct-world
  campaign effects, zero comparison-arm campaign effects, the three exact
  positive campaign-enabled effects, the raw-share overall effect
  `83755728/5240292055` against zero, observational equivalence for every
  assignment mechanism, and failure of campaign identification. Its source is
  `AronowAudit.P035.campaign_nonidentification_counterexample`.
- **P035-T2 — restricted; `SAP.P035.T2`.** The statement retains both specified
  mathematical campaign clauses (a)–(b): two calibrated models have the same
  observed law but zero versus positive campaign effects, and campaign
  enablement of the entire porch contrast is compatible with every year's
  frequencies. It includes the three exact yearly effects. It does not assert
  the correction's retained empirical estimate that porch assignment increased
  raisin choice or formalize the instruction to replace wording on page 5/6.
  The policy counterfactual concerns initiative presence; there is no separate
  health-message mediator. The credited source proves both mathematical
  clauses, but the conservative decision records the surrounding canonical
  text that is not stated as a theorem. The source is
  `AronowAudit.P035.corrected_campaign_interpretation`; its existing
  `frequency_contrast` helper supplies the exact rational effects by equality
  transitivity.
- **P035-T3 — omitted.** `work.json` records no Lean and no credited rows.
  Nonidentification does not establish either the truth or the falsity of the
  printed empirical attribution. No theorem is assigned to this target.

The route uses shared Mathlib-only definitions in `SAP/P035/Defs/Part1.lean`
through `Part3.lean`, imported by both Challenge and Solution. Part1 defines
the supplied counts, finite latent populations and binary potential outcomes;
Part2 defines finite means, the common design and observed laws; Part3 states
the two claims. No project module is imported by these definitions or the
Challenge. The Challenge and Solution signatures use the identical shared
`T1Statement` and `T2Statement` constants.

`SAP/P035/Bridge/Part1.lean` is needed because SAP and the project have distinct
three-constructor year types. `toYear` and `fromYear` are inverse constructor
maps. Outcome functions and observed-law functions are transported by
composition. Their inverse identities and the pointwise data, outcome, count,
mean, mass and law correspondences follow by constructor cases and reflexivity.
`sum_years` expands the two three-element sums with simplification. Calibration,
equality of observed laws and identification are transported by the inverse
maps and elementary logic. The overall-effect correspondence rewrites the
finite year sum and its summands. These are structural correspondences;
no statistical or counting argument is added.

The Solution decomposes the existing complete witness and transports its
components. Equality of observed laws with arbitrary real weights is direct
substitution of the exported pointwise observed-choice equality into the
finite sums. Thus the any-mechanism clause includes real probability weights,
as well as the arbitrary rational weights exported by the source. The
no-function-of-law conclusion is transported by composing the hypothetical
function with the observed-law adapter. T2 transports the existing existential
witnesses rather than constructing a new mathematical counterexample.

All Defs parts and root, Bridge part and root, Challenge part and root, and
Solution compiled successfully with the specified `sap-lean` command in
dependency order. `scratch/P035Axioms.lean` compiled and printed exactly
`[propext, Classical.choice, Quot.sound]` for each of `SAP.P035.T1` and
`SAP.P035.T2`. No other proof dependencies were reported. Both JSON files
parse; target coverage, credited-row references, theorem lists, proof statuses
and permitted dependencies agree. Every package file is below 300 lines.

The Comparator configuration lists exactly the two proved theorems and the
requested kernels. Independent Comparator and external-kernel execution was
not performed: the Comparator command variants, `con-ron` and `nanoda_bin`
were absent from PATH, and no matching executable was found in the permitted
dependency tree. Compilation and dependency checks are complete; a three-kernel
certificate is not claimed.

Scope concerns: the data are supplied constants, not a verified extraction of
the released data. The overall mixture uses raw enrollment shares, not the
paper's pooled weighting. All latent sizes and complete-case denominators are
fixed positive integers, all averages are finite, and the threshold ordering
is included in T1; no division-by-zero or truncated-subtraction branch supplies
the conclusions. The models grant randomization, consistency and no
interference for the witness, without establishing these for the actual trial.
Neither theorem decides the actual initiative effect or refutes campaign
reinforcement as a possible explanation.
