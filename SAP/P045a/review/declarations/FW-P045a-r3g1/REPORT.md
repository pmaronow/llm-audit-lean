# P045a declaration review

All five declarations are faithful to their recorded scope. T1, T2, T3 and T5 cover their whole canonical claims. T4 faithfully states the disclosed restriction: it retains all mathematical parts (a)–(d) and the undefined corrected toy variance, while omitting execution of the R repair, warnings and replacement of the reported entries by NA. It does not claim to have carried out those software changes.

The blind reading and junk-value audit are in `reading.md`, saved before reading either canonical claims or the record. The stage-2 comparison is preserved in `claim-stage.json`. Reading `record.json` required no change to those conclusions. Every source declaration in the five elaborated dependency closures was read, including all 67 distinct generated auxiliary declarations, printed in `scratch/ClosurePrint.out`. They only support concrete numeral and finite-index elaboration.

The counterexamples were checked against these printed readings and conditions:

- **T1:** A fair assignment of two four-unit groups to saturations 1/2 and 1/4, followed by independent Bernoulli assignments conditional on that allocation, gives the stated co-member counterexample on the estimator-specific positive-denominator events. The definitions satisfy both stages, partial and stratified interference, and no own-treatment effect. Every conditioning event used has positive probability; stronger all-arm conditioning is stated separately. Every numerical estimand and conditional expectation is retained.
- **T3:** The uniform three-of-six first stage and independent within-group complete randomizations with counts two and one give the stated counterexamples for the explicit singleton-drop estimator. The product mass has exactly the printed mixed-regime support, rather than sharing one assignment across groups. Additive, dilated and zero-control schedules meet their printed conditions. Dropping an uncomputable singleton term is stipulated by this canonical claim; it is explicit in `droppedWithin`.
- **T5:** The coded closed-neighborhood complement differs from documented all-control on a genuine symmetric loopless two-vertex graph, and the exact HT tables have the asserted expectations under independent fair assignment. The graph, assignment law, outcome schedules and positive event probabilities meet every printed witness condition. This establishes the documented-event error and the given expectation calculations; it does not assert that the chapter's table must be wrong.

For **T2**, conditional coordinate laws specify actual finite marginal distributions, without assuming any unbiasedness conclusion. They allow the printed independent randomizations and additional dependence across groups. Local outcomes enforce partial interference. Both single-regime averaging and actual two-regime contrasts are included, as are the changed fixed-count targets, all empty-arm HT cases, arbitrary-law overall results and numerical instances.

For **T4**, the proper-domain hypotheses guarantee positive denominators and at least two observations in every sample variance. Its equality condition allows a different constant treatment effect in each group, exactly as claimed. Both singleton bias identities and both dilated identities are retained. `requiredDirectVariance` represents the excluded singleton case by `none`.

No definition encodes a conclusion or introduces a contradictory hypothesis. Real division totalizes empty-arm ratios and off-support statistics, but no counterexample depends on those values: T1 conditions on positive arms, T2 uses positive fixed HT denominators or positive fixed-count arms, T3 explicitly defines dropping, and T4 excludes the improper domain. T5 has strictly positive exposure probabilities.

Validation completed:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited successfully. The file independently constructs normalized Bernoulli and fixed-count joint designs with the required coordinate laws, supported positive-mass counterexample outcomes, a nondegenerate proper-domain variance model and a genuine witness network. No target theorem is invoked in these checks.
- `python3 scratch/finite_audit.py` passed exact rational enumeration of all 512 T1 outcomes, all 14,580 actual T3 outcomes, two 648-outcome T4 models and every T5 assignment. Results are in `scratch/finite_audit.out`.
- `findings.json` and `claim-stage.json` were parsed and their five target entries checked against `closure.json`; all fingerprints in the findings are copied exactly.

The final per-declaration findings are in `findings.json`. There are no adverse findings or proposed fixes.
