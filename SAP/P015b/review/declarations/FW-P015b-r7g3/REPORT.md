# Declaration review

Both declarations are **faithful**, with severity **none**. Their `refuted` decisions concern the canonical assertions themselves, and their docstrings accurately disclose the retained results, domain restrictions, and omissions. No definition trivializes either statement or relies on a junk value in the asserted domain.

The blind expansion of both complete dependency closures was saved in `reading.md` before opening the claims. The claim comparison was saved in `claim-stage.json` before opening the record. Its `different` classifications reflect that the declarations refute affirmative claims. Reviewing the record required no change to either conclusion. Printed readings, condition lists, and separate witness checks are in `scratch/claim-witness-checks.md`.

## SAP.P015b.T18

Logistic stationarity states canonical (A). The square inverse link supplies a counterexample to the universal assertion in (C): the two families have the same outcome mean 1/4 and OLS treatment derivative 1, but their actual maximizing treatment coefficients have derivatives 120/119 and 1. The definition requires genuine unique likelihood maxima and actual derivatives. The causal distribution supplies binary potential outcomes, conditional unconfoundedness, an affine treatment mean, and full rank. Changing from treatment D to its centered residual preserves the treatment coefficient. The admissible domain keeps every logged probability strictly between zero and one.

The population likelihoods also have exact finite binary realizations along epsilon=1/(16m): integer cell counts with total sample size 768m reproduce their objectives up to a positive scale. Thus the counterexample connects to actual ML fits. Canonical (C) quantifies over any GLM; the target does not claim to refute each named family in (B), and its omission of that assessment is accurately disclosed.

## SAP.P015b.T17

The positive conditional-variance implication has the disclosed countable-covariate and global-second-moment scope. The approximate-zero population example retains overlap and admits a consistent IPW estimator. The exactly-zero fitted-weight example is a full-rank iid sample event of probability 1/256; repeated observations are compatible with independent draws. Neither example claims to refute the exactly-zero population-weight implication.

For the fixed pair 0,1, the multivalued-treatment example has effective atom probabilities (1/10,1/10,2/5,2/5). Profile 1 has effective probability 4/5 but no treatment-1 observations. This contradicts canonical pair-specific positivity by construction. Both treatments remain possible globally. The witness has finite moments and a positive finite normalization, and deterministic potential outcomes extend it to the stated causal setting.

## Validation

`scratch/Blind.lean` successfully prints all 25 generated auxiliary declarations in the closures. `scratch/Nonvacuity.lean` compiles independently from `SAP.P015b.Defs`, including a full-rank logistic global-maximizer instance, valid square-link data and finite realizations, every hypothesis of a nonvacuous discrete positivity instance, and the actual OLS zero-weight calculation. The remaining analytic and consistency arguments are checked in the witness notes. Both JSON outputs were parsed and checked against the requested declaration names, target IDs, and fingerprints.
