# Review of SAP.P005b.T20–T24 (Chang, Middleton, Aronow, Econometrica 92(5), 2024)

Files: `reading.md` (blind reading, written before the claims), `claim-stage.json` (step 2), `findings.json` (final).
Scratch checks: `scratch/Check.lean`, `scratch/NonVac.lean`, `scratch/WitA.lean` (all compile, no `sorry`).

| Theorem | Record | Verdict | Severity |
|---|---|---|---|
| SAP.P005b.T20 | refuted | faithful | none |
| SAP.P005b.T21 | whole | faithful | none |
| SAP.P005b.T22 | whole | faithful | none |
| SAP.P005b.T23 | whole | faithful | none |
| SAP.P005b.T24 | whole | faithful | none |

## What I checked

- **Definitions.** Every closure member matches the paper's printed notation. Means and covariances follow the paper's conventions: `sampleCov` is Ĉov with divisor |S|, and `leverageCov` is the population covariance with divisor n. The leverage is h_i = ‖x_i‖² ("rescaled", as printed) and κ = max h_i/n. L̂, N̂, L̂_T and N̂_T are the printed formulas. ν₁, ν₂ and ν₃ (pooled and armwise) match the printed definitions. NTTT, NCCC and NTTC are the Appendix A.1 constants; NCCC is defined through ℕ subtraction, which is harmless because m < n. The estimators (3), Lin's interacted estimator, (7)+(8), Bias_I, and (11)/(12) (`biasPart11/12`) all match. The two `_proof_1` closure members are only `OfNat 2` instances.
- **Junk values.** Three junk values could matter: the matrix inverse, which is 0 when the matrix is singular; division by zero at (n−2), (m−1) and (n−m−1); and the mean over an empty arm. Hypotheses exclude all three wherever the values are used: regularity for every S in the design, 3 ≤ n, 2 ≤ n_T and n_C where (11)/(12) appear, and 0 < m < n. In `Real.log (d n)` we have d_n ≥ 1, so the logarithm is never outside its domain. log 1 = 0 is a genuine value; it is exactly what the printed condition allows.
- **Algebra.** I re-derived by hand every coefficient identity: the ν₁ moments, the third-moment identity, (5), (6), the display before (12), the coefficient of (11)+(12), and the armwise debiasing weights. All agree with the stated forms.
- **Nonvacuity.** I built P4 with n = 4, d = 1, m = 2 and x = (7/5, 1/5, −1/5, −7/5). It is standardized, interactedRegular and noninteractedRegular, and it satisfies every hypothesis of T21–T24, including the conditional (11)/(12) clause and T22's weaker conjuncts.
- **T20 refutation.**
  - *Printed reading:* under Assumptions 1–3 and invertibility under every assignment, the ν₃ difference equals NCCC·S₀ − NTTT·S₁. Separately, if κ log d = o(1), then ATE_I − ATE − (linear term) = O_p(√(κd/n)).
  - *Conditions on a witness:* n ≥ 3 and 1 ≤ n_T ≤ n−1; x̄ = 0 and the mean of xx′ equals I at that n; L̂_T and L̂_C invertible. For the sequence part, Assumption 1 with a uniform K and d ≤ n; Assumptions 2 and 3; eventual invertibility (footnote 4 cannot hold at small n once d ≥ 1); and κ log d → 0.
  - *ν₃ part:* the formal universal has exactly these hypotheses. My own witness P5 satisfies all of them (n = 5, d = 1, m = 2, x = (3/2, 1/2, −1/2, −3/2, 0), yT = e₀, yC = 0). At P5 the left side is 1/64 and the printed right side is −1/64; the signs are reversed, as the canonical status (2) says.
  - *Expansion part:* `standingAssumptions` encodes Assumptions 1–3, plus d ≥ 1, which only strengthens the witness. The leading term and the rate are the printed ones. Its negation contradicts the printed assertion at d = 1, which matches canonical status (3).
  - So `refuted` is the right label, and "The printed claim is false" is accurate.

## Remarks (no defect)

- T20's docstring phrase "universal third-component sign identity" is terse. It means the universally quantified ν₃ identity with its printed signs.
- T21 adds the unique-OLS-minimiser clause (`wholeW1OLS`). That clause is true extra content and is consistent with the claim's remark that the formula is the OLS τ̂ of regression (1).
- T24, T23 and T22Main assume the full Assumption 2 and regularity even for clauses that do not need them. This matches the claims' explicit hypotheses.
