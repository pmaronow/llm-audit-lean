P008-T24: `omission_ok`, severity `none`.

The recorded reason is accurate. `claims.json` has `no_lean: false` and exactly one credited row, `AronowAudit.P008.printed_sum_probability_gloss_refuted`, with final status `wrong_credit`. The omission does not depend merely on that status: the row's actual statement is insufficient for this target.

At `AronowAudit/P008/P008_PrintedRefutations.lean:26–35`, the theorem negates the assertion that every finite sum of differences of numbers in [0,1] is itself a difference of two numbers in [0,1]. Its proof uses four entries with q₀ = 1 and q₁ = 0, giving sum −4. It contains no spatial outcome schedule, Hajek statistic, assignment law, permutation percentile, or forest-loss event linked to T24's reported experiment.

T24 concerns the probability interpretation of the reported cumulative statistic and its percentiles, with the canonical definitions of those objects. The printed values −0.0304, 0.0336, and −0.0321 all lie in [−1,1], so the row's range obstruction does not contradict their interpretation. Negating a universal array proposition also does not permit specialization to these particular empirical objects. Conversely, the row establishes none of the positive empirical assertions.

The row remains usable for its exact general warning about unweighted sums. Retaining only that warning would substitute the separate T7/T8 subject rather than give a faithful restricted T24 statement. The printed estimate-versus-cutoff comparison is already T21. No faithful whole or restricted T24 statement is obtainable from its credited row by the permitted glue, and no correction to the omission reason is needed.

Validation: `scratch/Check.lean` imported the credited declaration and checked its type and axioms successfully using `sap-lean`. No new theorem or proof was added. `findings.json` was parsed and checked with Python.
