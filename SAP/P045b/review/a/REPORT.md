# Palomar statement audit — P045b

16 targets; 16 theorem stubs. All 16 receive `correct_whole`: 12 assert their canonical mathematical content and 4 are valid refutations of the canonical universal assertions. A valid full refutation is counted as `correct_whole` because the requested verdict vocabulary has no separate refutation verdict.

| Verdict | Count |
|---|---:|
| correct_whole | 16 |
| correct_restricted | 0 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: none 16, minor 0, major 0. There are no outstanding non-correct items, declared restrictions, or omitted targets. Unused proof rows in the record are not omitted target claims.

The blind reading was saved in [reading.md](reading.md) before opening `claims.json`; the claim comparison was saved in [claim-stage.json](claim-stage.json) before opening `record.json`. The `different` entries for T25, T26, T27 and T29 record the literal difference between an assertion and its negation. They do not by themselves reject a genuine refutation.

| Target | Record decision | Assessment |
|---|---|---|
| P045-T17 | whole | Correct: every empty-cell and expectation clause is included. |
| P045-T18 | whole | Correct: ordered deletion, bijection, uniqueness and example are included. |
| P045-T19 | whole | Correct: real fixed-count identities and the three-member instance match. |
| P045-T20 | whole | Correct: the canonical counterexample targets the specified within-three reading. |
| P045-T21 | whole | Correct: maximality, greedy construction, existence and enumeration match. |
| P045-T22 | whole | Correct: the specified witness has both relative failure and absolute consistency. |
| P045-T23 | whole | Correct: table arithmetic and all four implication/counterexample clauses match. |
| P045-T24 | whole | Correct: five effects, direct-effect ordering and general decomposition match. |
| P045-T25 | refuted | Correct refutation: a positive-probability two-unit Bernoulli example falsifies the group-mean assertion. |
| P045-T26 | refuted | Correct refutation: the computed formula drops singleton terms and underestimates variance even at additive effect zero. |
| P045-T27 | refuted | Correct refutation of the canonical package-documentation equivalence, not the chapter estimand. |
| P045-T29 | refuted | Correct refutation of the canonical package-documentation 3-net contract, including actual retry traces. |
| P045-T30 | whole | Correct: both exact-positive-marginal unbiasedness statements match. |
| P045-T31 | whole | Correct: both mediation decompositions and the unchanged-mediator clause match. |
| P045-T32 | whole | Correct: this canonical target is the specified counterexample; it is not a refutation of the exact-probability theorem. |
| P045-T33 | whole | Correct: the exact ordered-pair surplus and both consequences match. |


## Cited correction to the stage-2 scope discussion

The mathematical readings and the stage-2 comparison categories are unchanged. The stage-2 reasons for T27 and T29 provisionally objected to the opening phrase “The printed claim is false” by treating “printed” as referring only to the chapter. That objection misread the canonical claim's scope and is withdrawn for the following specific reasons:

* In `claims.json`, T27 **statement**, the staged documentation explicitly calls the second condition “All Control; a unit and 100% of its first-degree neighbors are in the control condition.” Its own final assertion, introduced as “[Formal reading of the function's documented claim]”, equates the second returned indicator to the whole closed neighborhood being untreated. T27 negates precisely that assertion. This is a direct contradiction of the included documentation contract, not a counterexample to an optional interpretation supplied by the audit-history note.
* In `claims.json`, T29 **statement**, the staged documentation says “Assign treatment via 3-net clustering randomization.” Its own final assertion, introduced as “[Formal reading of the sampler's documented claim]”, requires the returned centres to be a 3-net with probability one. The defined sampler violates this assertion on the four-vertex path. The Challenge docstring explicitly identifies the “documented sampler” and its contract as the target. The theorem does not purport to falsify the printed table's numerical entries.

Thus the record's `refuted` labels satisfy the rule that a refutation must contradict an assertion actually in the canonical statement. No clause was added or removed on the authority of `note`, `finite_lemmas`, or a proof-row name. For T20 and T32, by contrast, the canonical assertions are themselves specified counterexamples; their `whole` labels and reading-specific docstrings are appropriate.

## Verification and mathematical limits

[Check.lean](scratch/Check.lean) imports only `SAP.P045b.Defs` and compiled successfully using `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It checks normalized nonempty designs, positive marginal probabilities with positive-probability empty cells, the exact T25 conditional counterexample, the fixed-count hypotheses, the T27 graph counterexample, structural-zero exposure probabilities and a positive baseline. It also checks pointwise positivity/nonnegativity for the T23 sequence described in `findings.json`; its limit hypotheses follow from Var=Vhat=1/(n+1)^2 and identically zero mean-SE discrepancy. No Challenge stub or solution theorem was used as evidence.

[referee_checks.py](scratch/referee_checks.py) independently uses exact rational arithmetic. [check-results.json](scratch/check-results.json) records the exhaustive nine-path enumeration; the fair-sign moments at N=1 through 8 and table ratios; the six-group singleton-arm counterexample; the four-path absorption law; every T32 retained table, moment and graph-preserving relabeling; and a T33 example exercising both within-label and cross-label structural zeros with signed outcomes. Finite sign enumeration supplements the all-N mathematical reading; the asymptotic conclusions use the displayed deterministic bound and fixed positive tail probability, not finite numerical extrapolation.

No hypothesis assumes its conclusion. Positive population/group sizes, explicit probability positivity, and the positive epsilon bound protect the used divisions and subtraction. The singleton terms in T26 are the explicitly audited dropped implementation terms. In T29, centre sets increase except on self retries, and each nonterminal state has a positive-probability transition adding an unmarked vertex. There are finitely many centre sets, so the self-retry geometric sums converge and terminal mass is one; the counterexample uses genuine nonnet terminal mass rather than Mathlib's zero value for a nonsummable real `tsum`. All other expectations are finite sums, so there is no non-integrability or unbounded-limsup issue.

The general exposure formulas were checked term by term: positive-joint terms reproduce the variance/covariance contribution; each same-label structural zero contributes (y_i+y_j)^2/2 surplus, and each cross-label structural zero contributes (y_i-y_j)^2 after the covariance factor -2. This accounts for the ordered-pair factors and cross diagonal in T33. Outcomes factoring through exposure in T17/T30/T33 encode the standing correct-specification assumption rather than adding a conclusion as a hypothesis.

The supplied canonical chapter text controls the audit. The [paper's arXiv preprint](https://arxiv.org/pdf/2001.05444) was consulted as background; no additional theorem or unstated assumption was imported from it. The proof formalization and Comparator were not inspected. These are statement-fidelity judgments, supported by the independent checks above, not replacement proofs of all universal theorems.
