All 13 architect decisions are accepted: **2 correct whole statements, 5 correct
restricted statements, and 6 justified omissions**. There are no major or minor
issues and no requested fixes.

| Verdict | Count |
|---|---:|
| `correct_whole` | 2 |
| `correct_restricted` | 5 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 6 |
| `omission_questionable` | 0 |
| Total | 13 |

There are no targets outside `correct_*` and `omission_ok` requiring an adverse
finding. Every target, including every omission, has an entry in
[findings.json](/home/ubuntu/sap/tasks/CHFID-P037c-a/findings.json).

The blind translation was saved in
[reading.md](/home/ubuntu/sap/tasks/CHFID-P037c-a/reading.md) before opening
`claims.json`. The seven comparisons in
[claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P037c-a/claim-stage.json) were
saved before opening `record.json`. **No step-2 verdict was changed after reading
the record.** The canonical statement, definitions needed and standing
assumptions determined scope; notes and finite-lemma history were not used to
remove clauses.

The [Challenge docstrings](/home/ubuntu/sap/tasks/CHFID-P037c-a/SAP/P037c/Challenge/Part1.lean)
accurately disclose these five restrictions:

| Target | Retained content | Exactly what is omitted |
|---|---|---|
| T35 | Clauses (i)–(v), including every one-block distribution and p-value assertion | Entire four-block clause (vi): its support size, observed statistic, extreme count and p-value |
| T27 | Both deterministic WLS comparisons and all of the synthetic six-school E2 construction | E1's independent assignment law, its marginal exposure probabilities, and realization probability `(1/4)^12` |
| T33 | Point fit, residual vector, contrast shift, both exact contrast variances and strict discrepancy | Clause (iii)'s individual-exposure refitted-mean shift for every exposure and assignment |
| T34 | All of (a)–(c), including individual mean shifts and all mean/contrast variance equalities with fixed controls | Clause (d)'s fewer-controls column-space comparison and referenced variance-discrepancy instance |
| T43 | Expected-normal-equation moderation-bias identity and common-intercept corollary | The four separate residual-moment conclusions and the nondegenerate four-state certificate, including its two second moments |

T36 covers the nomination statistic, exact sharp-null validity, direct-effect
decomposition and no-social-influence witness. Its positive recipient
denominators express the domain of the two means. T28 covers the joint and
separate WLS identities, standardized means, one-covariate coefficient formulas
and equality characterization. Its generic prediction-averaging identity also
applies separately to each exposure's slope vector. The minimizer hypotheses
describe the estimators; positive weights and full rank independently ensure
those minimizers exist.

The exact finite checks in
[scratch/audit_exact.py](/home/ubuntu/sap/tasks/CHFID-P037c-a/scratch/audit_exact.py)
passed. They import no Solution or Challenge proof. All arithmetic uses rational
numbers, and Gaussian elimination fails on a singular Gram matrix rather than
assigning it a default inverse. The results are saved in
[scratch/exact-check-results.json](/home/ubuntu/sap/tasks/CHFID-P037c-a/scratch/exact-check-results.json).

- T35: all 252 assignments and their full permutation p-values were enumerated;
  the six counts are `1,25,100,100,25,1`, and exactly 32 assignments reject,
  giving probability `8/63`. Recipient denominators are five.
- T27: the 48-student school graph has exactly the 12 required focal students.
  Enumeration of 1280 effective states integrates out the `4^3` unused
  control-school choices in each fiber of the full `20*4^6` design. The exposure
  probabilities, `1/640` observed-event probability, both WLS fits and augmented
  contrasts agree exactly.
- T33: all 96 masses are positive and normalized; all full and collapsed designs
  have full column rank. Both large variance fractions, the residual vector and
  the imputed full-control contrast variance agree exactly with the definitions.
- T28 and T34 have explicit eight-unit, one-control examples with rank-five
  pooled/refit designs, positive weights, and nonempty exposure groups. Each
  separate T28 design has rank two and positive `Sxx`.

[scratch/Nonvacuity.lean](/home/ubuntu/sap/tasks/CHFID-P037c-a/scratch/Nonvacuity.lean)
was compiled using `/home/ubuntu/sap/tools/sap-lean`, importing only the Defs.
It checks feasible positive-denominator sharp-null premises for T36 and actual
T43 premises with binary complementary two-of-four treatments, compositions
`1/4` and `3/4`, nonconstant untreated levels, `E[t't]=1` and `E[r'r]=1/16`.
The supplied normal-equation coefficients have zero residual coordinatewise.
Thus the bias theorem's premises are jointly satisfiable and do not assume its
conclusion. No `lake` command was used, and at most one Lean process ran at a time.

The general identities are also mathematically consistent with their stated
hypotheses: T36 is the inclusive upper-tail rank bound under the finite design
law; T28 follows from the WLS intercept normal equations and weighted centered
covariance formulas; T34 follows from `L_z H_z = I` and invariance of variance
under a fixed shift. For T43, the first moments give `E[r]=0`, orthogonality to
the fixed controls and treatment, and `E[r'z]=E[r'r]`. Pairing the expected normal
equations with this residual yields the stated moderation term. Actual block
demeaning preserves that pairing. None of these statements relies on an empty
index type, a zero denominator, a singular default inverse, an undefined
integral or an unbounded limit.

The six omissions are reasonable on the canonical content itself:

| Target | Reason omission is acceptable |
|---|---|
| T37 | Reported empirical tests and rounded estimates/standard errors; the data, exact robust covariance choice and sidedness needed to settle those reports are absent. |
| T38 | Actual school availability, treatment counts, reporting practices and missing-data handling; no precise availability rule or empirical evidence is supplied for a mathematical refutation. |
| T39 | A coherent positivity-based population definition, a necessary connection condition and an empirical population count/use assertion; a different selection rule does not refute those printed assertions. |
| T40 | Descriptions of particular published figure bands and empirical significance; generic covariance algebra alone cannot establish which bands were drawn. |
| T41 | Definitional dot-product count identities with an unspecified adjacency convention; differing conventions establish ambiguity rather than falsity of the printed definition. |
| T42 | Definition of the exposure-specific estimator and description of its use; it does not assert equality with pooled regression. T27–T28 state the specified mathematical comparison. |

The omission verdicts do not certify the empirical reports as true. They accept
the decision to supply no theorem about those reports on this evidence. In
particular, the package does not mislabel an ambiguity or an interpretation of
guidance as a refutation of the printed assertion.

Both requested JSON outputs were parsed and their target/theorem coverage was
checked with Python 3.
