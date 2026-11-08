All five declarations are faithful, with severity `none`. The record's five
`whole` decisions are correct, and the docstrings accurately describe the
statements. No step-2 conclusion changed after reading the record.

| Declaration | Claim and definition checks |
| --- | --- |
| `SAP.P009c.T35` | Both no-interference conclusions, both displayed formulas, and Bernoulli coincidence are present. Every asserted conditional mean has positive conditioning probability. |
| `SAP.P009c.T36` | The complete inequality chain is present. Structural interference, the mandatory diagonal, shared-influencer dependence, and outgoing counts match the canonical notions. |
| `SAP.P009c.T37` | Arbitrary designs share the same outcomes. The full-cube effect bound and the factor twice total variation match Proposition 12. |
| `SAP.P009c.T38` | The normalization, outgoing power mean, unnormalized ground distance, and endpoint convention at r=1 match Lemma 2. |
| `SAP.P009c.T39` | Both coupling marginals and the infimum of expected ground distance match Proposition 13, including its first-order transport convention. |

The blind reading covers all 102 closure entries (45 distinct declarations),
including both generated numeral proofs, and was saved before opening the
claims. `claim-stage.json` was saved before opening the record. Finite mass
laws represent arbitrary distributions on the binary cube; they introduce no
support, independence, or moment restriction. No conclusion depends on a junk
value, a circular definition, or an inconsistent hypothesis.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0
and no diagnostics. The checks construct a fair Bernoulli instance satisfying
all T35 antecedents, a nonconstant two-unit outcome table for T36, and bounded
interaction effects with distinct designs and EATE difference 1/2 for T37–T39.
Generic checks verify that count suprema have nonempty bounded ranges and
transport infima have nonempty cost sets bounded below. These checks import
only `SAP.P009c.Defs` and use no Challenge theorem. Both output JSON files were
parsed with Python, and all five fingerprints were checked against
`closure.json`.
