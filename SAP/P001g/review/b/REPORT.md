# Palomar statement referee report

Audited 14 targets: 13 theorem statements and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity counts: none 14, minor 0, major 0. There are no adverse findings requiring a fix.

The ten `correct_whole` findings comprise six faithful positive results (T116, T125–T128, T130) and four valid refutations (T118, T120, T121, T124). For a record decision of `refuted`, this verdict means that the theorem correctly refutes the printed claim; it does not affirm that printed claim. The claim-stage classification remains `different` for these four because their theorem types assert refutations rather than the original positive assertions.

The restrictions in both the record and the Challenge docstrings are accurate and complete:

* T115 retains population random-assignment identification and the final ATT/selection-bias identity, omitting the sample difference-in-means formula and two intermediate equalities.
* T117 retains both double-robustness alternatives while requiring measurable nuisances and separate integrability of the two regressions. Opposite nonintegrable regressions can cancel in the combined score, so the declared exclusion is real.
* T129 states actual-product consistency under the explicit finite uniform error envelope and population separation assumptions. Its maximum/equality lemma has an independent domain. The omitted auxiliary conclusions and absence of a derivation of the envelope are disclosed. A nontrivial Bernoulli-family instance supplies this envelope without assuming estimator consistency.

T119's omission is defensible on the supplied evidence. The book leaves “consistent across regions” undefined, and the record declines to credit an integrated squared-risk refutation as a refutation of that prose. An expectation-of-squared-error assertion and convergence in probability require an explicit connection; one cannot substitute one for the other without argument. The canonical notes identify an audit interpretation, but they do not establish that connection to the printed meaning. No such connection is supplied here. The unavailable row's reported credit status cannot independently be checked from these files, so this finding has lower confidence than the statement findings.

The blind [reading](reading.md) was saved before opening `claims.json`; [claim-stage.json](claim-stage.json) was saved and parsed before opening `record.json`. No claim-stage verdict was changed after reading the record. Every SAP definition used in a theorem was expanded, with the relevant Mathlib totalization conventions checked explicitly. No proof row named in the record was inspected or relied upon.

Concrete instances and counterexamples are in [nonvacuity.md](nonvacuity.md). [scratch/Check.lean](scratch/Check.lean) compiled successfully with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, importing only Defs. It checks generic IID product coordinates, the standard Gaussian's finite second moment, Hadamard differentiability of a constant functional, nuisance cancellation, and exact placebo-cell normalization, Gram determinants, coefficients and positive residual risk. The successful run emitted only an unnecessary-`simpa` linter warning. These are supplementary statement checks, not a recheck of the unavailable Solution/Comparator proofs. No `lake` command was run.

Both JSON deliverables were parsed with Python 3 and checked for unique identifiers, permitted verdict values and exact target/theorem coverage.
