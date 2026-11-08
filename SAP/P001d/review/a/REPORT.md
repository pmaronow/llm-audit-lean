Audited all 19 targets, P001-T58 through P001-T76. All have Challenge theorem stubs; none is omitted.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 10 |
| restriction_inaccurate | 1 |
| not_faithful | 1 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| Total | 19 |

Severity: 17 none, 2 minor, 0 major. No mathematical falsity or jointly unsatisfiable premise was detected. The two adverse verdicts concern disclosure of scope.

1. **P001-T62 / SAP.P001d.T62 — not_faithful, minor.** `SAP/P001d/Defs/Part2.lean:16` requires every `T_n` to be globally Borel measurable on all data vectors. The canonical moment criterion does not impose this condition, and standing assumption S2, Definition 1.2.2, requires measurability of the composite random variable. For IID Bernoulli data, a statistic can equal the sample mean on every binary vector and be non-Borel outside that finite support. Every observed and resampled statistic, the sampling and bootstrap weak limits, and all conditional moments then agree with the sample mean, while the Lean global-measurability premise fails. The record says `whole`, and the Challenge docstring has no restriction. The theorem is mathematically sound in its stated regime. **Fix:** mark it `restricted` and disclose global Borel measurability of each statistic, using the replacement text in `findings.json`, or weaken the premise to measurability of the observed and resampled compositions.

2. **P001-T65 / SAP.P001d.T65 — restriction_inaccurate, minor.** The record and `SAP/P001d/Challenge/Part1.lean:41` say Gram invertibility is added to the residual properties. The supplied canonical note explicitly states that Theorem 4.1.5 inherits Gram invertibility. Consequently, the theorem covers the full canonical setting; the declaration that it adds this hypothesis and drops singular designs misstates the comparison with this target. **Fix:** mark it `whole` and replace the restriction paragraph with the accurate scope statement in `findings.json`. The Lean statement needs no change.

The other record decisions agree with the claim comparison. The ten restricted targets are T58, T61, T64, T66, T68, T69, T70, T73, T74 and T76; their docstrings accurately describe their retained content and restrictions. The seven correctly whole targets are T59, T60, T63, T67, T71, T72 and T75. No step-2 reading or classification was changed after reading the record.

The blind readings, including every hypothesis and quantifier, were saved in `reading.md` before opening `claims.json`. The comparison was saved in `claim-stage.json` before opening `record.json`. SAP definitions were followed into Mathlib, including conditional-mean certificates, Gaussian variance parameters, bootstrap weights, nonsingular matrix inverses and totalized integrals. In particular, normalization excludes nonintegrable kernels in T59; T62's real limsup is of bounded probabilities; the conditional-square certificates in T67 and T74 correctly use the supplied conditional means; positive sizes and scales protect the statistical denominators; and T61's local identity forces the branch that avoids the arbitrary-function infimum. The retained T58 and T73 examples refute the specified printed readings.

`scratch/Check.lean` imports only `SAP.P001d.Defs` and was checked with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It verifies a full-rank two-column intercept design, the even-sample median convention, the entire four-atom counterexample, normalization/integrability guards, the zero-scale density computation, and an admissible normalized kernel. It also constructs independent copies of any probability law and a simultaneous witness for **all** T61 sampling premises using the actual heavy-tailed law, after proving that law is a probability measure and its tail map is measurable. Other nonvacuity instances, including nondegenerate cluster, homoskedastic, Gaussian and median models, are specified per target in `findings.json`. These checks use no Challenge theorem and do not re-prove the asymptotic results.

Both JSON output files were parsed and checked with Python for target coverage and required fields.
