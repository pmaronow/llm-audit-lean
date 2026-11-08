Audited all 10 targets, in the requested order. `reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. No step-2 verdict changed after reading the record.

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 3 |
| restriction_inaccurate | 2 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The two issues are minor scope-description errors. All ten Lean statements appear true; I found no hidden circular premise or vacuous probabilistic setup. The remaining record decisions are supported: T12, T13 and T16 accurately disclose their restrictions, and T15, T17, T18, T20 and T21 cover their whole mathematical targets. There are no omitted targets.

1. **P016-T14 — restriction_inaccurate, minor.** The record calls the theorem restricted, and the Challenge docstring at `SAP/P016b/Challenge/Part1.lean:28` says exact-tail clause (e) “additionally requires” positive weights. Canonical T14(e) expressly invokes “P016-T12 (iii)”; canonical T12(iii) already requires strictly positive weights at every represented point. `ExactValidity` uses the same domain. Thus the mathematics matches the incorporated claim, while the description incorrectly presents an inherited premise as a new restriction. Mark the record `whole` and describe the positivity as inherited from T12(iii). The iid exchangeability clause correctly allows zero-weight points.

2. **P016-T19 — restriction_inaccurate, minor.** The record and Challenge restriction paragraph at `SAP/P016b/Challenge/Part1.lean:63` describe empirical power statements and a data-specific decimal approximation as omitted target content. The canonical note explicitly says those simulation claims “are not a target”; its mathematical target consists of (a)–(f), all of which are present. The matched-parameter premise `a != 0` is also inherited from the multiplicative adjustments in canonical (d), whose reductions (e) compares. Mark the record `whole` and explain the mathematical domain and the canonical exclusion of empirical material. No Lean theorem change is needed.

Nonvacuity instances for every target are recorded in `findings.json`. `scratch/RefereeChecks.lean` compiles successfully using `/home/ubuntu/sap/tools/sap-lean`, importing only the package definitions. It checks positive group sizes, nonempty balanced designs (including 256 units), positive uniform weights, explicit KS failures, an exchangeable probability example, admissible model multipliers, and a nonempty bounded treated-discrepancy set. The tie-free premises have the explicit probability model of a uniformly random permutation of 0,...,B.

Independent computation in `scratch/referee_compute.py` exactly enumerates the 12,870 balanced 16-unit assignments and their 6,435 RSS fibers, each a complement pair; it also verifies the four-unit KS tables and every calibration-witness number with rational arithmetic. Its outward-rounded decimal interval calculations certify the two weak-cutoff violations, two strict-cutoff comparisons, and positive zero-p probabilities. Results are in `scratch/computation-results.json`. These checks supply evidence for statement truth and nonvacuity; they do not inspect or certify the Solution or Comparator.

Both requested JSON outputs parse, have exactly one entry for each canonical target, and use the required verdict fields. The Defs, Challenge and supplied metadata files were left unchanged.
