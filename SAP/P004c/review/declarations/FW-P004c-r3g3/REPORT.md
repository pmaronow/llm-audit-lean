All four omissions are justified. Each target has proved credited rows and
`no_lean: false`; the reasons accurately identify limitations of those rows.
No faithful restricted statement of the respective whole claim follows by the
allowed glue. No corrected reason or replacement statement is proposed.

The review uses each canonical `statement`, `definitions_needed`, and the
standing assumptions. Audit-history `note` and `finite_lemmas` fields do not add
claim clauses. A negation of a universal over a larger domain does not imply
the negation of its restriction to the paper's domain. Translating the exported
types into Mathlib-only definitions would preserve this logical gap.

- **P004-T35 — omission_ok, none.** Both rows have final status `narrower`.
  `Wave1/IpwBoundCoverage.lean:30` negates the conjunction of the printed bound
  and literal Hájek coverage assertions; `Wave1/IpwProposition.lean:30` negates
  the linearization, variance-equality, and normal-limit conjunction. Both
  place arbitrary metric measurable population spaces inside the negation.
  Neither exports a counterexample certified to be in S1's two-dimensional
  spatial domain. Failure of a single conjunct on that domain would suffice;
  separate refutations of all conjuncts are unnecessary. The exported types
  supply neither that domain-specific failure nor a positive component.
  Constructions used inside the proofs are not additional credited conclusions.

- **P004-T36 — omission_ok, none.** The sole row,
  `Wave1/ObservationalCoverage.lean:29`, has final status `wrong_credit`.
  Considering its actual statement remains permissible: it refutes coverage
  with `fittedIPW` in the numerator. The canonical claim explicitly retains
  `hajek`. These are distinct estimators for the allowed heterogeneous
  propensities, and the row supplies no equality or implication transferring
  its coverage failure to Hájek. Its statement also supplies no positive
  coverage conclusion. The omission is justified by this mismatch, rather
  than by treating `wrong_credit` as an unusable theorem.

- **P004-T37 — omission_ok, none.** The `narrower` row
  `P004_ConfidenceCompletion.lean:15` negates the unweighted-sum/weighted-mean
  equality for arbitrary real circle tables and positive bin weights. Its type
  imposes no common binary spatial outcome field, ordered distance bins, or
  partition realizing the regional averages required by the canonical claim.
  Extracting a counterexample from that negation does not add these properties.
  The binary construction mentioned in the proof is not exported by the
  credited type. The reason also correctly excludes the empirical estimate
  and p-value from the mathematical proof obligations.

- **P004-T43 — omission_ok, none.** The `narrower` row
  `Wave1/Gap/DecideD.lean:718` again negates a universal over arbitrary metric
  measurable spaces, without exporting a counterexample in the canonical
  spatial domain. `PrintedCoverage` genuinely requires an ordinary limit
  (`P004_Spatial.lean:224`); failure of its existence would suffice on the
  correct domain. The two `ok` rows at `P004_VarianceCompletion.lean:105,133`
  establish the finite homophily identity/iff and oracle SAH variance bound.
  They establish no consistency of the fitted variance estimators or coverage
  limit. Their combination retains neither canonical coverage clause. The
  homophily identity is already part of T33 in the supplied Challenge, and the
  audit-history finite lemmas do not turn these helpers into additional clauses
  of T43.

Validation: `sap-lean scratch/Check.lean` succeeded with checks of all seven
credited declarations and a print of `PrintedCoverage`. The scratch file adds
no declarations or proofs. `findings.json` was parsed and its required fields,
target IDs, verdict/severity pairs, and closure fingerprints checked with
Python 3. No Challenge or Defs file was changed.
