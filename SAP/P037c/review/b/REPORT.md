All thirteen targets were assessed. The seven supplied theorem statements are faithful at their declared scope, and the six omissions are justified on the available evidence.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 5 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 6 |
| omission_questionable | 0 |

Severity counts: none 13, minor 0, major 0. There are no items requiring correction.

The blind mathematical reading was saved in `reading.md` before opening `claims.json`. The seven comparisons in `claim-stage.json` were saved before opening `record.json`. No step-2 comparison was changed after reading the record. Each canonical assertion was assessed with its definitions and standing assumptions; neither the audit notes, the finite-lemma lists, nor the `no_lean` flags were treated as permission to remove clauses.

| Target | Assessment of the architect's decision |
| --- | --- |
| P037-T35 | Correctly restricted to clauses (i)–(v). The entire four-block extension (vi), including all its arithmetic assertions, is absent and explicitly disclosed in the Challenge docstring at lines 6–10. |
| P037-T36 | Whole mathematical claim: nomination-weighted statistic, sharp-null validity, direct-effect decomposition and rejecting direct-only witness. Denominators are positive; permutation outcomes are held fixed; inclusive tail ties and the general rejection inequality are correct. |
| P037-T27 | Correctly retains both deterministic WLS comparisons and the complete synthetic E2 construction. E1's independent probability law, marginals and realization probability are absent and explicitly disclosed at lines 20–25. |
| P037-T28 | Whole mathematical claim: common analysis set, both WLS fits, zero category residual sums, standardized prediction means, scalar coefficient formulas and exact equality characterization. |
| P037-T33 | Correctly retains all concrete design and contrast-variance assertions. Clause (iii)'s individual-exposure refitted-mean identities are reduced to the I-minus-NI contrast shift, explicitly disclosed at lines 33–38. The abstract design has control probability 1/4, as the canonical claim requires. |
| P037-T34 | Correctly retains all of (a)–(c), including individual-mean and contrast variances. The fewer-control comparison (d) is absent and explicitly disclosed at lines 41–45. The hypotheses use a full-rank parametrization, as the canonical setting requires. |
| P037-T43 | Correctly retains both expected-normal-equation conclusions. The separate residual orthogonality assertions and the specified four-state certificate are absent and explicitly disclosed at lines 48–54. Complete four-school blocks and the design moments are genuine premises; normal-equation existence is not a claimed result. |

The six omission decisions were checked individually:

* **P037-T37:** the significance statements and rounded tables concern actual data and the actual variance procedure. No supplied inputs determine those empirical assertions. A general Wald calculation would not certify them.
* **P037-T38:** the availability and loss of administrative records, and whether that missingness was unrelated to treatment, are empirical. A mathematical counterexample for a different inclusion rule would not refute the printed assertion.
* **P037-T39:** the positive-probability population is coherently defined. Its necessary neighbor condition is not a claimed sufficiency characterization. The population's actual size and its actual use require evidence absent from this package.
* **P037-T40:** generic prediction-variance formulas cannot establish which confidence bands were drawn in the published figures. The empirical identification of the displayed bands is not supplied as formal input.
* **P037-T41:** the count identities hold for either specified binary adjacency convention. A discrepancy between directed and either-direction conventions does not make those identities false or settle the printed ambiguity.
* **P037-T42:** the displayed separate estimator is a definition, not an assertion that it equals the pooled estimator. T27 and T28 establish the relevant mathematical distinction. They do not certify which estimator generated the publication or make its definition false.

These omissions leave the empirical assertions uncertified; they do not approve the underlying empirical results. None should be relabeled as a refutation of a printed mathematical assertion. The supplied witness theorems also do not assert that the published sharp-null test is invalid: they demonstrate rejection under a direct-only schedule that violates that global sharp null.

Independent exact-arithmetic checks in `scratch/audit_checks.py` passed. They enumerate all 252 pair assignments and their observed-schedule tails, verify the six-school E2 marginals and probability 1/640, solve both twelve-unit WLS problems, and recompute all 96 full and collapsed fits and both exact variance fractions. Results are saved in `scratch/exact-check-results.json`. The matrix calculation explicitly inverts each rational Gram matrix; it uses no singular-inverse fallback.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully with no diagnostics. That file imports only the allowed Defs and contains no `sorry`, extra axiom or Challenge theorem. It verifies nonempty recipient groups, an eight-unit example with one nonconstant covariate and full pooled/separate ranks, positive within-group Sxx, and a nondegenerate complete-block T43 instance. In the latter, E[t't]=1, K=1/32 and the normal-equation solution has b=3 at beta=2; the model therefore permits nonzero moderation bias rather than assuming the desired conclusion. The eta=0 normal equations are also witnessed. Both coordinate and covariate index sets in these examples are nonempty.

At the general level, finite upper-tail probabilities are super-uniform even with ties; the WLS assertions follow from positive-weight least-squares normal equations. The T34 shifts follow from y*(z)=r+H_z b0 and L_z H_z=I. For T43, the first moments give E[r]=0 and expected orthogonality to the treatment and fixed controls; hence E[r'z]=E[r'r]>0. Applying the given normal equations and self-adjoint block demeaning gives the stated bias formula. None of these statements needs division by zero, out-of-range percentile lookup, empty-population averaging, an undefined variance or an assumed conclusion.

The canonical transcriptions are the source for the SI passages and the validator's synthetic examples. The main article's descriptions of weighting, exposure conditions and the positive-probability population were also checked against the [primary article](https://pmc.ncbi.nlm.nih.gov/articles/PMC4725542/). Direct supplement links did not return a usable PDF through the browser, so no independent verification of every SI transcription is claimed. No author scripts, respondent data, Solution files or Comparator files were inspected; this is an audit of the supplied statements, with independent arithmetic and nonvacuity checks.
