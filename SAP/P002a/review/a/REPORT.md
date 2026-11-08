# Palomar statement audit: P002a

All 15 targets were reviewed. The 14 exported theorem statements are faithful at their disclosed scope. The remaining target is reasonably omitted on the supplied record.

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 9 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |

Severity: 15 none, 0 minor, 0 major. No item requires a statement or docstring correction.

The blind expansion was saved in [reading.md](reading.md) before opening [claims.json](claims.json). The 14 comparisons in [claim-stage.json](claim-stage.json) were saved before opening [record.json](record.json). No claim-stage verdict was changed after reading the record. [findings.json](findings.json) contains one entry for every target, including the omission, with individual nonvacuity evidence and confidence.

| Target | Record decision | Audit verdict |
| --- | --- | --- |
| P002-T1 | restricted | correct_restricted |
| P002-T2 | restricted | correct_restricted |
| P002-T3 | refuted | correct_whole |
| P002-T4 | restricted | correct_restricted |
| P002-T5 | restricted | correct_restricted |
| P002-T6 | restricted | correct_restricted |
| P002-T7 | omitted | omission_ok |
| P002-T8 | restricted | correct_restricted |
| P002-T9 | whole | correct_whole |
| P002-T10 | whole | correct_whole |
| P002-T11 | restricted | correct_restricted |
| P002-T12 | whole | correct_whole |
| P002-T13 | whole | correct_whole |
| P002-T14 | restricted | correct_restricted |
| P002-T15 | restricted | correct_restricted |

All nine restriction descriptions occur verbatim in their corresponding Challenge docstrings and accurately describe the retained conclusions, omitted evaluations, and added hypotheses. In particular, T5 supplies sufficient unadjusted sharpness rather than a necessity or adjusted sharpness characterization. T15 explicitly excludes zero conditional denominators at every index and every outcome of the probability space, and explicitly permits arbitrary couplings with the required randomization marginals.

T3 refutes each printed universal variance bound with its actual hypotheses and multiplier. Its verdict concerns the correctness of that refutation. T8 refutes only the covariate-to-augmented-Gram implication identified in the canonical claim; it does not claim to refute Lemma 19. T9 retains the exact finite spectral statement and the almost-sure inequality for the actual coefficient-error vectors. Its independence hypothesis matches the Supplement's sequence setup described in the supplied canonical definitions for T14 and T15. T13's shared balance parameter does not remove any valid design from its first inequality: every valid design admits a positive r=min(n1/n,n0/n).

The potential totalization traps are guarded. Valid designs have nonempty assignment sets and positive arm sizes. The singleton-complier covariance convention and studentized 0/0=0 convention agree with the supplied paper definitions. Reassignment freezes the observed outcome vector. T6 uses the feasible refitted statistic in its variance denominator; T2 uses the oracle statistic. T9's real Rayleigh infima have nonempty unit spheres and nonnegative values. T5 takes its coverage liminf on a nontrivial filter of nonempty classes, so empty-class extended-real infima cannot supply its result. The explicit families give jointly satisfiable hypotheses, including positive-variance sequences for T5, T11 and T15.

T7's omission is justified on the evidence available here: the record excludes its only named four-limit declaration by final `wrong_credit` status, while its remaining listed rows are finite OLS and oracle-variance helpers. No corrected Lemma 20 limit is exported elsewhere in this package. This judgment accepts the availability information in the record; the underlying external declarations and status history were outside the permitted files.

Verification used only Defs, Challenge, the supplied canonical claims and record, and relevant Mathlib definitions. No Solution or Comparator was read. [scratch/Check.lean](scratch/Check.lean) compiled through the supplied `sap-lean` command and proves representative Theta and Xi membership directly from Defs, without assuming any Challenge theorem. [scratch/audit_checks.py](scratch/audit_checks.py) independently checks exact rational values: all 66 negative-delta assignments, all six centering assignments, all 70 eight-unit sign assignments, and all 70 and 252 near-singular assignments at n=8 and n=10. It also checks degenerate witnesses for n=2 through 64, odd-family admissibility at n=9,11,13, and the sign-family ratio calculations through n=128 plus n=256,512,1024. Its output is [scratch/check-results.json](scratch/check-results.json).

The asymptotic statements were assessed mathematically and for faithful definitions and quantifiers; these finite checks do not reproduce their general limit proofs. Both requested JSON outputs parse, contain the expected distinct entries, and agree with the target-to-theorem mapping.
