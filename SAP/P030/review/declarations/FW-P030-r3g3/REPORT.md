All five declarations are faithful to their complete canonical claims. Each architect decision of `whole` is correct, each restriction is null, and each docstring accurately describes the statement. The record required no change to the independently saved claim-stage conclusions.

| Declaration | Verdict | Severity | Coverage checked |
| --- | --- | --- | --- |
| `SAP.P030.T11` | faithful | none | Disjoint-partition count, printed inconsistency, exactly four single-entry repairs, and subtraction. |
| `SAP.P030.T12` | faithful | none | Both null assumptions, uniform conditional counting, imputation, super-uniformity, attainable exactness, and the greatest-attainable-level formula. |
| `SAP.P030.T13` | faithful | none | All three means, both strict comparisons, total expectation, and every boundary/support condition. |
| `SAP.P030.T14` | faithful | none | Actual adjacency outcomes, conditional masses, six distances and correlations, midranks, positivity and uniqueness, roundings, exact lower-tail assignments, and p=1/3. |
| `SAP.P030.T15` | faithful | none | Completion of the square and complete even/odd integer maximizer characterizations, including C=1. |

The blind reading was saved in [reading.md](reading.md) before opening the canonical claims. [claim-stage.json](claim-stage.json) was saved before opening the architect record. All 100 closure entries across the five declarations were covered, including the generated numeral, index, and finite-law helpers. T14 was reviewed at its actual type, `T14WholeStatement` (`SAP/P030/Defs/WholeW1.lean:162`).

The definitions correctly implement the paper's finite probability and rank notions. T12 explicitly excludes empty conditional supports. T13 guards each conditional-mean assertion by support nonemptiness; empty-set default means affect no asserted formula. T14 proves nonempty treated sets and positive rank-square sums, excluding default minima and zero-denominator correlations. T11's natural subtraction does not truncate, and T15 uses integer subtraction.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully. Its compiled instances cover every hypothesis, direct effects, tied p-values, the weaker fixed-outcome null, both exposure conditioning events, the actual spatial model, and both optimization parities. All twelve printed witness-dependency checks exclude `sorryAx` and the Challenge stubs; the file imports only `SAP.P030.Defs`. [scratch/Nonvacuity.log](scratch/Nonvacuity.log) records these checks.

Independent enumeration in [scratch/enumerate.py](scratch/enumerate.py) checked 894 exposure cases, all six spatial rows, and 125 optimization cases. It uses exact rational arithmetic for counts, ranks, products, square sums, ordering, and probabilities; displayed square-root rounding errors also pass numerical checks. Results are in [scratch/enumeration-results.json](scratch/enumeration-results.json).

[findings.json](findings.json) contains exactly the five requested declarations with the fingerprints copied from `closure.json`, no issues, and no proposed fixes. Both required JSON outputs were parsed and validated with Python.
