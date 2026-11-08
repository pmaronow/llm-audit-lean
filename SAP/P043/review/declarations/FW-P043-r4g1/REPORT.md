# P043 declaration review

All five declarations are faithful to their recorded scope. T1, T2, T4 and T6
cover their canonical claims; T5 is an accurately disclosed restriction.
There are no adverse findings.

The blind reading was saved in `reading.md` before opening `claims.json`.
The comparison with the canonical statements and their definitions was saved
in `claim-stage.json` before opening `record.json`. The record required no
change to those judgments. Every declaration in the five dependency closures
was read, including the generated auxiliaries printed by
`scratch/Closure.lean`.

| Declaration | Claim-stage scope | Record decision | Verdict | Severity |
|---|---|---|---|---|
| SAP.P043.T1 | whole | whole | faithful | none |
| SAP.P043.T2 | whole | whole | faithful | none |
| SAP.P043.T4 | whole | whole | faithful | none |
| SAP.P043.T5 | narrower | restricted | faithful | none |
| SAP.P043.T6 | whole | whole | faithful | none |

T1's printed reading is the existence of the two specified counterexamples to
an unconditional extension of the mediation comparison. Its conditions are
fair assignment independent of all exogenous variables, consistency, the
specified disturbances and response functions, positive knowledge changes,
the stated knowledge-to-support effects, and the integer witness's index
ranges. Both product-law witnesses satisfy those conditions. Both have
M=3/50, D=-3/50 and tau=0. They violate D>=0 and therefore do not refute the
paper's contextual conditional; the docstring expressly says so
(`SAP/P043/Challenge/Part1.lean:20`). The whole-statement definition includes
pointwise cancellation, structural coefficients, integer score cases and
bounds, and the failed unconditional inferences
(`SAP/P043/Defs/WholeW1.lean:85`).

T2 contains all five finite-expectation hypotheses and all decomposition,
comparison, null-inference, linear, ratio and channel-sign conclusions.
The product probability law encodes assignment independence, and the observed
response encodes consistency (`SAP/P043/Defs/Part3.lean:16`). Its law
quantifiers permit arbitrary probability populations, with no finite-type
restriction (`SAP/P043/Defs/Part3.lean:99`). The conditional-mean denominators
are positive, and integrability covers the actual nested expressions used.

T4's printed reading requires independent fair assignment, exclusion,
consistency and a positive first stage. The two-type and both five-type
witnesses meet each condition. They also meet the stated bounds and
nondecreasing response conditions. The two-type witness covers every
normalized average of crossed increaser increments, including probability
averages with integrability concluded (`SAP/P043/Defs/WholeW1.lean:45`).
The five-type witnesses have equal complete observable laws and unequal
effects on positive-probability increaser groups. Consequently the
impossibility of a functional fitting even this pair proves the canonical
nonidentification assertion for the whole class
(`SAP/P043/Defs/Part4.lean:120`). No counterexample relies on dependent
assignment or an undefined conditional effect.

T5 correctly proves the finite weighted-population crossed-margin formula.
The strict positive-margin filter excludes undefined conditional means
(`SAP/P043/Defs/Part5.lean:62`). Its finite-population scope, the retention of
monotonicity and positive-stage premises for identification and covariance,
and the omitted nonmonotone clauses are accurately described in both the
docstring (`SAP/P043/Challenge/Part1.lean:57`) and the record. The note that a
finite population suffices was not used to narrow the canonical claim.

T6 supplies the corrected observation/stratum indicators, the omitted
reference coefficient, both indicator identities, and the equivalent
stratum-intercept regression equation (`SAP/P043/Defs/Part6.lean:16`).
Zero-based `Fin` indexing is an exact relabelling. The single-stratum case
q=0 is valid. The statement and docstring concern notation and algebra and
make no additional estimation or causal-identification assertion.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` compiled independent
nonvacuity and witness checks for every declaration, without using the five
target theorem stubs. These include all T2 and T5 hypotheses, both T4
observable laws, a qualifying finite average and Dirac probability average,
and nonempty T6 models. `python3 scratch/check_witnesses.py` passed independent
exact-rational checks of the T1 and T4 finite witnesses. Details are recorded
per declaration in `findings.json`.

No conclusion depends on division by zero, a nonintegrable Bochner integral,
`toReal` at infinity, or truncated knowledge subtraction. The unused value of
a conditional margin mean at probability zero is filtered out of T5's
formula. Natural predecessor subtraction occurs only at positive margins in
the telescoping and crossed-margin assertions. Empty-index cases do not make
any full theorem vacuous. The JSON artifacts were parsed and checked for
exactly the five requested declarations and matching fingerprints.
