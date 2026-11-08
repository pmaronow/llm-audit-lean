# P045a statement audit

16 targets reviewed: **1 correct whole, 15 correct restricted**. No false, vacuous, unfaithful, inaccurately restricted, or omitted target was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 15 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

P045-T8 states the whole canonical counterexample. P045-T1–T7 and P045-T9–T16 retain correct portions of their canonical claims and disclose their restrictions accurately. Every recorded decision agrees with the independent claim-stage comparison; all 15 recorded restriction texts match their Challenge docstrings. No step-2 verdict was changed after reading the record. There are no adverse items to list and no proposed fixes.

The audit used `statement`, `definitions_needed`, and the standing assumptions as the claim. Notes, finite-lemma history, and the record's proof-row names were not treated as extra clauses or as evidence of faithfulness. Descriptions of omitted clauses concern what is separately asserted; some omitted numerical or algebraic consequences also follow from the retained formulas and definitions. Their availability does not make the retained statements incorrect or the disclosed theorem scope misleading.

The counterexamples support the canonical counterexamples, rather than refuting those canonical assertions. In particular, T8's docstring correctly identifies the universal monotonic-bias reading that its example refutes. No target is incorrectly classified as refuting its own canonical statement.

## Verification

The blind expansion of every theorem, including quantifier order, all hypotheses, shared definitions, and relevant Mathlib conventions, is saved in [reading.md](reading.md). It was saved before `claims.json` was opened. The claim comparison is in [claim-stage.json](claim-stage.json), saved before `record.json` was opened. Per-target verdicts and nonvacuity evidence are in [findings.json](findings.json).

The real zero-division convention does not supply any retained estimator assertion: the stated conditioning events have positive probability, meaningful ratio denominators are positive on design support, and `Option.none` represents the undefined required sample variances and empty-subclass printed ratios. The singleton-dropping variance term explicitly drops singleton arms, as required by its canonical claim. Natural subtraction is protected by the domain hypotheses or the explicit graph's degree bounds. Disconnected graph distances use extended-natural `SimpleGraph.edist`, preserving infinite distances. Auxiliary unselected-group draws integrate out; T2 additionally discloses its independent product-law restriction.

The only infinite sum is the sampler's sum over finite terminating traces. On the four-path, the only repeated-center tail has ratio 1/4, so its geometric series converges. The sum therefore represents the actual terminal law and does not use Mathlib's default value for an unsummable real series.

Independent rational calculations in [scratch/audit.py](scratch/audit.py) passed. They cover all 512 Bernoulli witness outcomes; all retained singleton variance moments; both two-unit extreme-event schedules; all 64 upper triangles; all 2,110 deletion-mask/treated-unit cases, including every Hajek denominator; both four-path absorbing-chain laws; all 45 cycle pairs; all 20 tract first stages; and all 45 printed-network pairs and restricted-support averages. Results are in [scratch/numerical-checks.json](scratch/numerical-checks.json).

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` passed. Its instances construct a genuine finite probability design and network, verify positive own-treatment and exposure/extreme-event probabilities, satisfy the full conservative-variance domain with G=3,C=2,n_g=4,m_g=2, supply a nonconstant baseline for strict singleton biases, and check extreme-event stability with a nonconstant outcome schedule. General retained variance and mixture formulas were also checked by ordinary finite-population variance and conditioning arguments; the scratch checks are nonvacuity checks, not replacement proofs of the theorem stubs.

The executable R modifications, recomputations and other software clauses explicitly dropped by the docstrings are not certified. The supplied canonical descriptions of the staged R operations were used as premises; no unstaged source, Solution or Comparator was inspected. No `lake` command was run, and Lean processes were run sequentially.
