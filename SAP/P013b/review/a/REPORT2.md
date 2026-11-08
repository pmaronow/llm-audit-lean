# P013b delta review

Thirteen targets, twelve included theorem stubs. Counts:

| Verdict | Count |
| --- | ---: |
| correct_whole | 11 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

All severities are `none`. No new statement problem was found. `correct_whole` includes acceptance of T18's whole-assertion refutation, whose decision remains `refuted`.

## Earlier findings

| Target | Earlier verdict | Status | Revised verdict |
| --- | --- | --- | --- |
| P013-T24 | restriction_inaccurate, minor | Fixed: the docstring and record now explicitly omit the inter-set nesting. | correct_restricted |
| P013-T20 | omission_questionable, major | Fixed as a justification issue by additional information about precedence and permitted proof rows; the omission itself is retained. The earlier recommendation is withdrawn on that account. | omission_ok |

**T24.** The [revised docstring](/home/ubuntu/sap/tasks/CHFID-P013b-a/SAP/P013b/Challenge/Part1.lean:46) accurately distinguishes the two assumed relations `item ⊆ S` and `survey ⊆ S` from the omitted relation `item ⊆ survey`. The latter represents containment of the 151 survey nonrespondents among the 342 item nonrespondents. It also lists the three assumed cardinalities, positive weights and retention of every nonzero score in both sets. The actual data facts, zero coding and indicator provenance remain unverified; rounded-estimate reproduction and a separate strictness assertion remain excluded. `record2.json` gives the same restriction.

The formulas in [T24Statement](/home/ubuntu/sap/tasks/CHFID-P013b-a/SAP/P013b/Defs/Part8.lean:74) still match the saved blind reading. No mathematical repair was needed. The earlier nonnested example remains an admissible, nonzero-score instance, and the new wording now says exactly that nesting is not part of the statement.

**T20.** The [architect's response](/home/ubuntu/sap/tasks/CHFID-P013b-a/architect-report.md:145) adds relevant information absent from my earlier assessment: it quotes a rule that diagnostic notes are “diagnostic history, never instructions”, and reports that the two almost-sure convergence rows have final `wrong_credit` status and are excluded even from an IID restriction. It identifies their extra premise as `iIndepFun Z μ` and says no other mismatch is alleged. On this supplied account, the remaining allowed rows are only finite identities or transform a limit already assumed; they do not supply either required almost-sure limit.

My earlier report correctly observed that `claims.json`'s T20 note explicitly requests independent replicates. Its recommendation treated that note as controlling and did not account for the newly documented precedence and row-use restrictions. I withdraw the recommendation to reuse those rows under the stated constraints. This accepts omission; it neither adds independence to the bare canonical statement nor endorses a positive convergence theorem without independence.

The distinction is mathematical as well as procedural. If only the one-draw design law is required, let every replicate equal the same fair binary assignment B. Every replicate has the correct marginal law. For a one-unit exposure indicator at label 1, on B=1 the smoothed diagonal empirical entry is `(R+1)/(R+1)=1` for every R, whereas its design-law target is 1/2. This positive-probability event prevents almost-sure convergence to the target. [DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P013b-a/scratch/DeltaCheck.lean:12) verifies the marginal law and this nonconvergence directly. Thus an independent-sequence limit row does not establish the weaker marginal-only formulation.

The external brief, source declarations and credit ledger linked by the architect lie outside this review workspace and were not read. Acceptance of the omission is based on the explicit constraints and signature account supplied in `architect-report.md` and `record2.json`; it is not an independent certification of those external files. There is no new theorem or refutation certificate for T20 in the package.

## Comparison with the saved reading and decision labels

I reread every revised Defs part, both Challenge files and `reading.md`. All twelve expanded theorem statements and their supporting definitions match the saved mathematical reading: no changed hypothesis, quantifier order, estimator, correction term, conclusion, critical-value convention or limit predicate was found. The identified Challenge change is T24's disclosure. A direct comparison of `record.json` with `record2.json` changes only the T20 omission explanation and T24 restriction text.

| Target(s) | Revised decision | Clause and scope check |
| --- | --- | --- |
| T15 | whole | Both conservative covariance assertions, the no-effect equality and conservative effect variance, with positive cross joints only where required. |
| T16 | whole | Every selected finite clause: fixed-prediction unbiasedness, residual identity, unbiased count and the prescribed zero-convention Hajek bound. No contextual asymptotic claim is added. |
| T17 | whole | Total and contrast expectations under the exact existential misspecification condition, using the induced exposure in each weight denominator. |
| T18 | refuted | Negates the complete printed natural coverage assertion under nestedness, standing positivity and Conditions 3, printed 5 and 6. It preserves the printed complements in the dependency predicate. |
| T19 | whole | Consistency in probability under the uniform boundedness and pair-dependency conditions, with nested potentials and the stated positivity. |
| T21 | whole | The entire specified three-unit counterexample, including baseline/shifted values, errors, residuals, moments and the joint-translation repair. Its canonical claim is itself the counterexample. |
| T22 | whole | Every corrected part (a)–(f): exact changes, equivariance/invariance, both characterizations, fixed-prediction cases, expectation identities and count calibration. The two-unit example supplies a case where unchanged predictions suffice. |
| T23 | whole | All three worlds, identical full records, estimator/effect/loss/bias values, nonidentification and respondent comparison. The additional zero-scoring rule remains explicit. |
| T24 | restricted | All retained loss/identification/exclusion formulas and numeric scaling remain; the revised disclosure accurately identifies empirical and nesting omissions and the unasserted strictness comparison. |
| T25 | whole | The specified support counterexample, binary potential population, moment formulas, both wrong-joint bias signs and correct-joint equality. It does not refute the article's correct block-randomization sentence. |
| T26 | whole | Counts, strict support inclusion, marginals, full pair laws and differences, student-law preservation and nonhosting exposure formulas. |
| T27 | whole | The full supplied formal wearing-outcome reading for the five-exposure map, with binary potentials, consistent observation and positive marginals. Empirical estimates and Hajek/WLS descriptions are contextual rather than its formal conclusions. |

T21, T23 and T25 correctly retain `whole`: proving their canonical counterexample claims is different from negating those claims. T18 correctly retains `refuted`: its canonical target is the positive printed assertion. No label hides a polarity change or a dropped mathematical clause.

## Junk values, nonvacuity and checks

There is no changed theorem type requiring a new nonvacuity construction, but I recompiled the earlier [Check.lean](/home/ubuntu/sap/tasks/CHFID-P013b-a/scratch/Check.lean) against the refreshed Defs. Its positive-marginal and cross-joint instances, misspecification witness, calibration instance, five-exposure graph instance and printed-dependency checks still pass. The T18 family still gives zero estimate and estimated variance on a positive-probability all-control assignment, with a positive target. Its bounded coverage sequence makes the real liminf meaningful.

For the revised T24 disclosure, the nonnested example has S={0,…,2049}, item={0,…,1707}, survey={1,…,1898}∪{2049}, weights 1 and a score nonzero only at unit 1. The exact Python check verifies cardinalities 2050,1708,1899. `DeltaCheck.lean` verifies the subset, score-retention and nonnesting facts. All sample normalizers are positive, the retained Hajek denominator hypothesis excludes a zero retained denominator, and subset inclusion with positive weights also makes the full denominator positive. The fixed Hajek example has positive denominators and contrasts −1/2 and 0, so its no-common-factor assertion is substantive. The arithmetic natural subtractions have larger minuends and do not truncate.

The finite design normalization excludes an empty probability space. Marginal divisions have positive denominators under the relevant hypotheses. Zero joint probabilities correspond to impossible joint events and use the paper's specified convention; T16's zero-count ratio convention remains explicit. The generic school moment hypotheses force nonempty support through their 1/2 marginals, and the named school supports have positive exact counts. No new use of junk values or inconsistent premises was found.

Both scratch Lean files import only `SAP.P013b.Defs`; they do not use the Challenge stubs. They were compiled with `/home/ubuntu/sap/tools/sap-lean`, with no `lake` invocation. Logs are `scratch/revision2-lean-check.log` and `scratch/delta-lean-check.log`. The exact check script again passes all 243 signed-outcome/design cases and the numerical school and finite-example checks; its output is `scratch/revision2-exact-check.json`. These checks supplement, rather than replace, the mathematical statement audit. Python validates `findings2.json`, all thirteen target IDs, the twelve theorem names and the report counts.
