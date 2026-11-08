All five declarations are faithful; no defects were found. Each was reviewed
with its complete elaborated statement closure. `reading.md` was saved before
opening `claims.json`, and `claim-stage.json` was saved before opening
`record.json`. The record required no change to the claim-stage conclusions.

| Declaration | Record decision | Assessment |
| --- | --- | --- |
| `SAP.P030.T1` | whole | The exact five-unit design, invariant outcomes, nonexperimental fixed units, distance and rank calculations, defined correlations, both inclusive tails, rejection probabilities for every stated level, and numerical thresholds are present. |
| `SAP.P030.T2` | whole | The genuine no-effects population realizes the full six-assignment conditional law. All rank computations, exact values, ordering, roundings, tails, rejection sets, sizes, and the stated range of size violations are present. |
| `SAP.P030.T3` | whole | The arbitrary finite-law formulation includes every requested identity, super-uniformity bound, union bound, size bound, inclusion, strictness example, and conventional two-tailed alternative, with the correct strict versus inclusive endpoints. |
| `SAP.P030.T4` | refuted | The negated proposition is the canonical printed-rule universal size guarantee itself. The genuine five-unit Spearman experiment independently refutes it at level `1/20`; the result does not depend on disputing an interpretation of Equation (1). |
| `SAP.P030.T5` | whole | The entire counterexample, including actual statistic nonconstancy, three distinct values, observed-data `p=1/3`, rank details and roundings, and both generic constant-statistic consequences, is stated. Its docstring accurately identifies the implication being disproved. |

Every SAP notion agrees with the canonical definitions. Probability counts
assignments, retaining tied statistics' multiplicities. The potential outcome
schedules are complete constant schedules specified by the canonical
counterexamples. No hypothesis encodes an unproved conclusion or makes an
intended application vacuous. All four `whole` labels and the `refuted` label
are correct, and the docstrings describe their declarations accurately.

Empty-set distance fallback and zero-denominator correlation are possible in
the total definitions outside the experimental supports. Every correlation
and probability used in a claimed experiment has nonempty treated/reference
sets and positive rank square sums. The equality of actual and imputed
statistics even outside the support follows from identical outcome arguments,
independently of the chosen total extension. These conventions do not supply
any claimed counterexample or probability. All quantities are finite; the
usual measure-theoretic conditions add no restrictions here.

The following checks passed using `/home/ubuntu/sap/tools/sap-lean`:

* `scratch/ClosurePrint.lean`: inspected every generated auxiliary declaration
  in the closures, as well as the finite-law structure and projections.
* `scratch/Check.lean`: directly constructed the nulls, nonempty supports,
  treated-set witnesses, positive outcome variances, an unequal-mass finite
  law, and a two-point constant-statistic instance.
* `scratch/FiveWitness.lean`: independently proved the five-unit actual
  distance/correlation calculations and refuted the exact T4 proposition.
* `scratch/TenWitness.lean`: independently proved all six distance vectors,
  positive distance variances and rational squared correlations, and supplied
  two supported assignments with unequal actual statistics.

The last two witness proofs use no Challenge theorem and have no `sorryAx`
dependency. `python3 scratch/recompute.py` also passed, checking the finite
arithmetic, tails and decimal error bounds using exact rational calculations.
`findings.json` contains exactly five entries with fingerprints copied from
`closure.json`; its JSON syntax and schema were checked with Python.
