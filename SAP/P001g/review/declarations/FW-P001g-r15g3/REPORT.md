# Review of T128–T130

All three declarations are faithful to their recorded scope: T128 and T129
are accurately disclosed restrictions; T130 states its whole canonical claim.
There are no adverse findings.

- **T128:** `Defs/Part6.lean:53` states the canonical asymptotic coverage lower
  bound with the corrected n-scale variance consistency. It omits the
  finite-sample strictly ordered endpoint requirement in the definition of a
  random interval, exactly as disclosed in `Challenge/Part1.lean:80` and the
  record. The compiled Gaussian instance satisfies every hypothesis yet has
  coincident endpoints at sample size one. This confirms the omission and the
  appropriateness of the restricted label; it is not a refutation of the
  canonical claim under its full reading.
- **T129:** `Defs/Part6.lean:63` uses actual product likelihoods and assumes
  an explicit uniform empirical-log error envelope. Its independent second
  conjunct (`Defs/Part6.lean:87`) gives both expected-log maximality and the
  almost-sure density-equality characterization. The additional hypotheses
  and omitted proof-sketch conclusions are accurately disclosed in
  `Challenge/Part1.lean:85` and the record. Positivity and integrability keep
  population logs out of their junk-value domains; true positive likelihood
  and actual-product maximization also prevent a zero-likelihood selected
  estimator almost surely at positive sample sizes.
- **T130:** `Defs/Part6.lean:106` states both displayed estimators, exact
  unbiasedness for every positive size, and consistency for both specified
  endpoints. The two positive response probabilities render the printed
  support condition correctly. Conditioning is on a positive-probability
  atom, and the bounded outcomes make every integral legitimate. Iid is
  required for the observed pairs, as printed; no missing-at-random premise
  is introduced.

The blind reading and full closure audit were saved in `reading.md` before
opening the claims. The independent claim-stage conclusions were saved in
`claim-stage.json` before opening the record; none changed at the record
stage. Notes and finite lemmas were not treated as additional claim clauses.

`scratch/BlindCheck.lean` and each of `scratch/Nonvacuity128.lean`,
`scratch/Nonvacuity129.lean`, and `scratch/Nonvacuity130.lean` compiled
successfully with the permitted `sap-lean` wrapper. The three nonvacuity
files construct every hypothesis without importing Challenge theorem stubs.
No package sources were modified, no `lake` command was run, and no external
paper lookup was needed. `findings.json` has been checked with Python's JSON
parser against the three theorem names and fingerprints in `closure.json`.
