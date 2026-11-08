# Review of SAP.P002a.T6–T10

All five mathematical declarations state their canonical claims wholly. Their dependent definitions render the finite-population, regression, probability and spectral notions correctly. I found one minor scope-description error in the record for T7; no mathematical statement or Challenge docstring needs correction.

| Declaration | Verdict | Severity |
|---|---|---|
| SAP.P002a.T6 | faithful | none |
| SAP.P002a.T7 | restriction_inaccurate | minor |
| SAP.P002a.T8 | faithful | none |
| SAP.P002a.T9 | faithful | none |
| SAP.P002a.T10 | faithful | none |

T7's `row_use_note` at `record.json:47` says the theorem is restricted and drops models. The corrected canonical claim dated 2026-11-04 explicitly requires positive population OLS residual variances in both arms at each size. The theorem states that same premise, with no uniform lower bound, and gives all four limits with the correct oracle variance and simultaneous threshold quantifiers. Its docstring and the record's `whole` decision are correct. Replace the stale restriction description as specified in `findings.json`; retain the theorem, definitions, docstring and decision. This finding does not change the step-2 assessment of `whole`.

T6 refutes the printed feasible-variance denominator assertion itself. Its even family satisfies the entire Xi class, has positive residual and feasible variances, and has full-rank arm fits for every design reassignment. Its conditional failure probability is one for every observed assignment. The odd extension supplies the same fixed class at the intervening sizes. Holding observed responses fixed and averaging uniformly over fresh reassignments implements the required conditional law; no dependent-replicate substitution occurs.

T8 supplies exactly the canonical counterexample to passing the covariate spectral bound unchanged to the augmented Gram. Its docstring correctly limits the refutation to that implication. It does not claim that the example disproves the asymptotic display for the particular coefficient-error vector. T9 states both the entire corrected finite spectral assertion and its asymptotic coefficient-error consequence, with one vanishing error for both arms along each fixed subsequence.

T10 gives the complete specified four-unit counterexample and corrected finite evaluations. The positive value `S1²=1/12` ensures that its unnormalized unequal expectations also contradict the normalized first equality of (C.17).

The blind expansion and junk-value audit were saved in `reading.md` before opening the claims. Every closure entry was read, including all 33 generated declarations. `claim-stage.json` was saved before opening the record; none of its classifications changed afterward. Printed readings and condition-by-condition witness checks are in `scratch/RefutationAudit.md`.

Both independent mathematical check files compile successfully with the supplied `sap-lean` command. `scratch/Checks.lean` constructs an entire increasing four-cell Xi sequence, positive residual variances, and an explicit infinite-product probability space with exact randomization marginals, satisfying all T7 and T9 sequence hypotheses jointly. It also checks a finite T9 spectral instance. `scratch/FiniteChecks.lean` calculates a T6 design instance, a T8 matrix counterexample, and independently proves the full numerical T10 statement. These checks do not invoke the reviewed Challenge theorems. Exact-rational Python enumeration additionally checks all 70 reassignments of the n=8 T6 model, its n=9 extension, and the other finite witnesses. Commands and successful statuses are recorded in `scratch/validation.json`.

No failure relies on zero division, an empty or unbounded Rayleigh set, an undefined expectation, or a singular regression default. No audited source file was edited.
