# Review of P037b T18, T23, T24, T19 and T20

All five declarations are **faithful, severity none, as restricted claims**.
None states the whole canonical claim. Each record entry correctly labels its
declaration `restricted`; its restriction matches the theorem docstring
verbatim and accurately identifies the retained mathematics and omissions.
No step-2 conclusion changed after reading the record.

The blind reading is in [reading.md](reading.md), saved before reading the
canonical claims or record. It unfolds every statement dependency and records
the totalization and empty-index conventions. Every closure entry was read,
including the generated arithmetic/index certificates printed by
[ClosurePrint.lean](scratch/ClosurePrint.lean). The claim comparison was saved
in [claim-stage.json](claim-stage.json) before opening `record.json`.

| Declaration | Retained content and scope assessment |
| --- | --- |
| T18 | Correct full-rank OLS/HC0 definitions, fixed-sample multiplier covariance, leverage facts, homoskedastic covariance shortfall and positive-norm row algebra. The missing expanded sandwich, SE/Wald expressions, code identification and variance-ratio identification are disclosed. Holding X,y fixed correctly represents the conditional bootstrap calculation; integrability assumptions are usual conditions. |
| T23 | The exact six repeated-row groups and candidate matrices match the canonical 56-school example. Inverse, normal-equation and sandwich certificates validate those candidates. The missing explicit rank, contrast/decomposition, control residual mean/sample variance and interval-width statements are disclosed. The numeric 1/5400 expression is not presented as a separately formalized sample-variance certificate. |
| T24 | The prediction algebra, symmetric-matrix decomposition/equality criterion, and same-sample full-rank recentering formulas match the retained clauses. Arbitrary coefficients and symmetric matrices give valid algebraic generalizations. Intervals, realized orderings, residual-control failures, the concrete certificate, the explicit contrast quadratic-form identification and code verification are disclosed omissions. |
| T19 | The potential outcomes, threshold, six equally likely two-of-four assignments, table and expectations are correct. The probability limit uses independent block assignments through the full product law, as the canonical assertion requires. Only the general OLS identification is omitted. This is the canonical constructed selection example; it is not labelled a refutation of a printed empirical assertion. |
| T20 | Strictly positive normalized finite support matches the canonical assignment support. Fixed-inclusion IPW, the varying-inclusion conditional factor and threshold sufficiency are correct. The conditional factor is a joint/marginal ratio with positive denominator. Sharp-null specialization, the T19 probabilities/example and empirical/code assertions are disclosed omissions. |

No definition assumes a conclusion or makes the retained claim trivial. The
literal fit and covariance candidates in T23 are checked against their
defining equations. No incompatible hypothesis set or operative junk-value
dependency was found. Singular Gram matrices are excluded by full rank;
T18's derived integrals are integrable. T19's empty block ratio at B=0 does
not affect its limit. In T20, a zero-probability *excluded* unit contributes
zero to a sum; all retained denominators are positive, and the expression
equals the conventional sum over retained units.

[Nonvacuity.lean](scratch/Nonvacuity.lean) compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`, importing only the
definitions and using no audited theorem. It constructs a nondegenerate T18
instance, checks T23's Gram and HC0 certificates, constructs T24's exact
full-rank design, checks T19's complete finite witness and a product-law
normalization, and supplies T20's positive-probability design and threshold
instances. The log contains only an unused-binder warning.

[findings.json](findings.json) contains exactly the five requested entries,
with fingerprints copied from `closure.json`. Its JSON syntax and entry
coverage were validated with Python. No source declaration was modified.
