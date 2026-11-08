All five declarations are faithful to their canonical claims. All five `whole`
decisions in `record.json` are correct; no restrictions or fixes are needed.

| Declaration | Verdict | Severity | Main check |
|---|---|---|---|
| `SAP.P029a.T1` | faithful | none | Complete six-atom witness, receipt ignorability, pair independence, failed latent equality, and both Wald values. |
| `SAP.P029a.T2` | faithful | none | Both incomparability witnesses and the general one-sided implication with exactly its stated substantive premises. |
| `SAP.P029a.T3` | faithful | none | Both full-type independence readings, complete finite laws, nested probabilities, and separating population ratios. |
| `SAP.P029a.T4` | faithful | none | All population formulas, separate sufficiency implications, separation laws, joint-independence alternatives, and sampling consistency. |
| `SAP.P029a.T5` | faithful | none | Both admissible 500-record inputs, matrix calculations, opposite scoring discrepancies, and recovery for arbitrary positive weights. |

The review followed the required order: `reading.md` was saved before opening
`claims.json`; `claim-stage.json` was saved before opening `record.json`. No
claim-stage conclusion changed after reading the record. Every dependency listed
in `closure.json` was read, including the 44 generated proof declarations printed
by `scratch/ClosureChecks.lean`. They supply only numeral and finite-index facts.

For T1, the ordering reading being tested is that the two received-treatment mean
equalities imply latent complier mean equality under the five IV assumptions.
Its conditions are binary receipt and assignment, exclusion/SUTVA, nondegenerate
random assignment independent of the full potential tuple, relevance, no defiers,
the same covariates, and defined conditional means. The six-atom witness satisfies
each condition and even potential-pair independence from receipt. Its ATE is 1/2
and its complier mean is 1. The `whole` label correctly describes coverage of the
canonical counterexample, without claiming that latent ignorability itself or
consistency under that assumption fails.

For T3, the marginal reading says type independence suffices for latent equality
and both ATE ratios; the conditional reading says type independence given X
suffices for both ATE ratios. Both require the IV setting and positive compliance
at supported profiles. Each witness satisfies those conditions, including
independence of the entire type, in its respective reading. The first gives ICSW
7/16 against ATE 1/2; the second gives ordinary IV 5/8 against ATE 1/2. The
docstring explicitly identifies the two readings, and `whole` is the correct label.

T2's one-sided implication adds no independent relevance or no-defiers premise.
T4's positive-mass profile type represents precisely the canonical finite support.
Positive scores on that finite support imply the uniform positive lower bound
in Assumption 3. Its estimator is the normalized weighted Wald estimator from
the claim; the n+1 indexing merely ensures a nonempty total sample. Measurability
and integrability are usual conditions, and no rate, sample splitting, or
all-sample positive-score assumption has been introduced.

For T5, the reading tested is that the coded statistic equals RMSE about the
homogeneous effect five on admissible design inputs. Conditions checked are
500 units, balanced assignment, permitted coefficient/covariate/normal support,
the corrected compliance indicators, constant individual effect five, full-rank
regressor/instrument matrix, and positive weights for weighted recovery. The
witnesses satisfy them. The benchmark's latent covariates and the regression's
observed noise covariates are correctly distinct. These are concrete support
inputs, not proposed population laws with outcome errors dependent on assignment.
The constant-run RMSE identities assert arithmetic on arrays and do not replace
independent draws with one repeated draw. No historical table values are claimed
to have been recomputed.

All conditioning and population-ratio denominators used in the examples are
positive. Probability measures prevent `toReal` of infinity; integrability
prevents undefined Bochner integrals. T4's zero-denominator finite-sample values
are harmless for convergence in probability because its limiting denominators
are nonzero. T5's run counts are positive, square-root arguments nonnegative, and
the matrix inverses nonsingular. No definition relies on an inappropriate junk
value or encodes a conclusion as a hypothesis.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully
with an empty diagnostic log. It independently checks all three finite laws,
constructs every premise of T2's one-sided implication, and constructs T4's
population and sampling hypotheses, including a genuine infinite product of
independent fair assignments and consistent measurable score estimates. Its
proofs do not invoke the Challenge theorem stubs. `scratch/ExactChecks.py` also
passed independent exact-rational checks of the finite witnesses and matrix
calculations; results are in `scratch/ExactChecks.json`.

`findings.json` contains exactly one entry per reviewed declaration, with
fingerprints copied from `closure.json`. Both output JSON files were parsed and
their declaration coverage validated with Python.
