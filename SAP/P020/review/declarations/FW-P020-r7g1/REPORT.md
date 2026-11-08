# P020 declaration review

All five declarations are **faithful**, with severity **none**. Their recorded
`whole` decisions are correct. No statement, definition or docstring repair
is needed. No step-2 conclusion changed after reading `record.json`.

| Declaration | Assessment |
| --- | --- |
| `SAP.P020.T1` | Every exact counterexample clause is present, including individual outcomes, all three assignments, the fixed-coefficient MSE minimum, positive replication and persistent probability-one error. |
| `SAP.P020.T2` | All corrected MSE and probability assertions are covered. The theorem proves them for arbitrary finite-support laws, a sound generalization of the growing cluster-population setting. |
| `SAP.P020.T3` | All universal raw-count impossibility assertions and the scalar calculation are present. The docstring correctly distinguishes a scalar calculation from an admissible randomized experiment. |
| `SAP.P020.T4` | The conditional unit conversion, real and integer thresholds, individual probability signs and both average-sign regimes match the claim. |
| `SAP.P020.T5` | Both full arm expectation chains and the corrected ATE expectation and bias identities are present for every assignment-dependent coefficient. |

The review followed the required order: full closure and docstring reading,
saved `reading.md`, canonical claims and saved `claim-stage.json`, then the
record. All 41 distinct generated proof declarations in the closures were
also printed and read. `claim-stage.json` calls T2's domain broader because
it drops unnecessary population structure; this is compatible with `whole`,
since every canonical instance and conclusion is included.

The counterexample targets were checked against their actual conditions.
For T1 the printed reading at issue is that persistent bias or inconsistency
guarantees eventual relative MSE inefficiency. The canonical witness has
complete uniform randomization, fixed positive counts in both arms, positive
integer cluster sizes, genuine individual potential outcomes, and within-cluster
replication with growing total and realized arm counts. Its comparators use
fixed coefficients for each experiment, including arbitrary deterministic
dependence on the replication index. It does not substitute dependent copies
for independently randomized new clusters: that is not this growth scheme.

For T3 the printed reading at issue combines the raw-count definition of size,
the displayed logistic model, treatment coding 0/1, coefficients 2/5 and -9/10,
and reported average 7/1000. Positive counts give shifts at most -1/2; the exact
printed logistic link is strictly increasing; and every nonempty population
average is negative for every finite control predictor vector. This universal
argument applies to every admissible design, including the stated blocked
setting. It does not rely on a one-person cluster experiment. Both T1 and T3
establish their canonical counterexample assertions, so `whole` is the correct
label relative to those canonical claims.

`scratch/Check.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, using definitions only.
It checks the T1 individual realization, joint T2 limit hypotheses on a growing
population, both T4 sign regimes in valid two-cluster designs, logistic values
strictly between zero and one, and a nonconstant T5 coefficient whose covariance
correction and actual bias both equal -1. Exact-rational enumeration independently
checked T1's numerical values and MSE comparisons. All relevant denominators are
positive; unsupported assignment values do not enter any asserted expectation.

`findings.json` contains exactly the five requested declarations with their
fingerprints copied from `closure.json`. JSON parsing and schema-content checks
passed. No source declaration was changed, and no `lake` command was run.
