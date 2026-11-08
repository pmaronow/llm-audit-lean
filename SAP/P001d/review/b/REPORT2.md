# P001d delta review

All 19 targets were rechecked against the revised Defs, Challenge, `record2.json`, `architect-report.md`, the saved blind reading, and the canonical claims. There are no outstanding statement or disclosure findings.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 12 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 19 none, 0 minor, 0 major. No target is omitted or labelled `refuted`.

## Earlier findings and their disposition

### T65: no requested edit; earlier objection withdrawn

My only earlier adverse finding was T65's `restriction_inaccurate` verdict. The architect did **not fix it by the requested edit**: the theorem, restricted decision and disclosure are unchanged. After checking the stated reason against the primary claim, I withdraw that objection. The revised verdict is `correct_restricted`.

The specific error in my earlier interpretation was treating the sentence “Theorem 4.1.5 inherits the invertibility” in `claims.json`, target T65, `canonical_claim.note`, as an added hypothesis of the separately quoted theorem. In `canonical_claim.statement`, Theorem 4.1.4 explicitly assumes an invertible Gram matrix, whereas Theorem 4.1.5 separately quantifies over an OLS coefficient estimator and states the residual properties without that assumption. The supplied Definition 4.1.2 in `definitions_needed` defines OLS through least-squares minimization. That definition permits singular designs. The explanatory note conflicts with this separately stated theorem and should not supply its missing premise.

This correction is supported by the actual scope difference. Take three identical design rows (1,1) and responses (-1,0,1). For b=(0,0), RSS=2; for arbitrary b, RSS=2+3(b0+b1)^2, so b is a least-squares minimizer. The residuals have mean zero, zero empirical products with each regressor and zero empirical covariances. The Gram matrix is singular. `scratch/DeltaCheck.lean` proves the minimization, singularity and all three residual identities directly from the supplied definitions. T65 excludes this legitimate printed-theorem instance, and its docstring says so accurately.

I therefore accept the architect's mathematical scope argument, independently of the upstream brief it cites. No change to the theorem or its current restriction is needed. The earlier `reading.md`, `claim-stage.json` and findings remain unchanged as the historical review record; this report records the corrected interpretation explicitly.

### T62: scope defect fixed by disclosure

My earlier `correct_whole` assessment missed a restriction that the other referee identified. The saved blind reading already recorded `T measurable for every natural sample size`; my comparison failed to count its stronger global scope. Revision 2 changes the decision to `restricted` and adds the matching restriction sentence in `Challenge/Part1.lean`. This disclosure fix is complete. The mathematical statement is unchanged and is correctly restricted.

The premise at `Defs/Part2.lean:16` is global Borel measurability of every T_n on all of R^n. The canonical criterion only needs the observed and resampled quantities to be random variables. For IID Bernoulli data, changing T_n arbitrarily on nonbinary data vectors leaves all observed and resampled values unchanged; such an extension can fail global Borel measurability. Consequently the extra premise is a real restriction. Dropping other unnecessary premises, such as IID sampling or a marginal normal limit in the abstract moment criterion, does not eliminate it.

The revised text identifies exactly this additional premise and retains the moment equivalence, standard-error consequence, exact sample-mean variance formula, finite-variance mean consistency, and all-positive-size local-density median result with a positive fractional moment. These clauses are all still present.

The other 17 earlier accepted target assessments remain accepted with the same scopes.

## Changes and label checks

I reread all four Defs parts, both Challenge parts and their root imports. Every mathematical theorem and shared definition matches the saved mathematical reading: no changed quantifier, hypothesis, definition, conclusion or theorem name was identified. This is a semantic comparison with `reading.md`, not a claimed byte comparison with an archived source tree. Comparing `record.json` and `record2.json` identifies only T62's decision and restriction text as changed. Its new Challenge restriction matches the new record exactly. All other restriction docstrings also match `record2.json` exactly.

The seven remaining `whole` labels were checked clause by clause:

| Target | Canonical content present |
| --- | --- |
| T59 | Nonnegative normalized estimated density; monotone continuous integrated CDF with both endpoint limits. These give the domain condition for every functional on CDFs. |
| T60 | General integrated-kernel formula and rectangular-kernel empirical-CDF formula, with the correct lower-endpoint exclusion. |
| T63 | IID cluster averages; equality of cluster and average-of-averages means; expectation and coordinate-mean identities; both variance formulas; weak law under the finite-moment regime. |
| T67 | Conditional second moment, population-moment factorization and exact sandwich simplification. The canonical formal content does not require proving the explanatory asymptotic approximation. |
| T71 | Correct coefficient dimension; slope-penalty seminorm and non-norm witness; zero-penalty OLS minimizer equivalence; convexity for nonnegative penalty. |
| T72 | Positive-scale nonnegative integrable normalized normal density and integrable first moment equal to x dot beta; explicit rejection of the totalized zero-scale formula as a density. The conditional-density mean computation is at every fixed covariate. |
| T75 | Complete two-point conditional-PMF mean at fixed x, equal to h(x dot beta) and within [0,1]. |

The twelve restricted labels are T58, T61, T62, T64, T65, T66, T68, T69, T70, T73, T74 and T76. Beyond the focused T62/T65 checks, the previously disclosed omissions remain unchanged: the additional signed-kernel counterexample; the omitted heavy-law/regular-functional components; correlation derivation and covariance-count expansion; covariance-estimator matrix-form equivalences; weaker composite measurability; the general APD estimator; the distinct-covariate necessary condition; further finite-model residual properties; weaker residual moment/measurability regimes and pointwise Gaussian conditional laws; and full-rank likelihood uniqueness/formula. No new undisclosed restriction was identified.

T58, T61 and T73 have canonical counterexample claims and are still restricted packages of those counterexamples. Their retained negative integrated estimate, bootstrap-variance obstruction, and failed independence product equation respectively contradict the relevant printed readings. None is a newly labelled refutation of a positive canonical target, and none is incorrectly promoted to `whole`.

## Junk values, nonvacuity and validation

For the metadata-changed T62, the statistic family of sample means is globally Borel measurable at every size; `scratch/DeltaCheck.lean` verifies this directly. It also verifies strict positivity of every (n+1)-size bootstrap denominator and nonnegativity of the finite bootstrap variance. Standard normal IID observations provide the positive-variance mean/conditional weak-bootstrap instance. IID uniform[-1,1] observations supply the median instance, with m=0, local density 1/2, positive neighborhood radius and finite positive moments. The abstract conditional CLT and median asymptotics are assessed mathematically rather than independently reproved in scratch.

All other guard and nonvacuity checks from the earlier reading still apply. In particular, T59's kernel integral equal to one excludes nonintegrability; the real limsup in T62 has inputs in [0,1]; sample sizes and bandwidths are positive where needed; the heavy-tail endpoint is null and its maps are measurable; the local functional identity stays in the linear branch; matrix inverses have invertible Gram premises; and the finite conditioning masses are 1/2. T72's zero-scale claim explicitly concerns a totalized algebraic extension, not a probability law or a density for a Dirac measure.

Both `scratch/Check.lean` and the new `scratch/DeltaCheck.lean` were compiled successfully against the refreshed Defs using `/home/ubuntu/sap/tools/sap-lean`. They use no Challenge theorem or admissions. No `lake` command was run, and the two-process limit was respected. The old check includes the heavy-law IID realization and exact finite counterexample; the new check additionally establishes the T62 guards and the singular-design witness for T65.

`findings2.json` contains one object per canonical target, using the requested schema and theorem names. Python 3 parsed the JSON and checked target coverage, field names, allowed verdicts/severities, counts and agreement with the revised decisions. Original review outputs and input files were preserved.
