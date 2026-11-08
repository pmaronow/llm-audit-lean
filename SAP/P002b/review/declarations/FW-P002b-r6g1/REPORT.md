# Declaration review

All five declarations are **faithful**, severity **none**. Their `whole`
decisions are correct, and their current dependency docstrings describe the
statements accurately. No source change is required.

| Declaration | Assessment |
| --- | --- |
| `SAP.P002b.T16` | Exactly the canonical array and all five witness properties. The unequal values 2 and 3 contradict the printed middle equality. |
| `SAP.P002b.T17` | All corrected finite inequalities, with the stated constants, and the fixed-dimension order consequence. Allowing zero dimension or A=0 is a valid extension. |
| `SAP.P002b.T18` | Both exact differences have the negative treated and positive control signs, with the correct arm means, residuals and inverse Grams. |
| `SAP.P002b.T19` | Both the coefficient error and the actual residual cross term are stated, including the intercept error and coefficient -2. |
| `SAP.P002b.T20` | Both the entire finite oracle expansion and the corrected control remainder limit are present. The asymptotic clause adds neither positive oracle variance nor invertibility of every control Gram. |

For T16, the printed reading is: under the coordinate fourth-moment bound,
the maximum augmented squared norm equals one plus the sum of coordinatewise
squared maxima. The witness has positive size n=4, fixed positive dimension k=2,
centered covariates, fourth moments 1/2, and covariate second-moment matrix
`(1/2)I`; its two sides are 2 and 3. It also admits the full statistical setting:
take complete randomization with two treated units, all units complying, and both potential outcome vectors
equal to `(1,1,-1,-1)`. Population coefficients are zero, residual variances are
4/3, and Xi holds with delta=0, e=A=1/2, B=1 and r=1/2. Thus the counterexample
does not depend on a violation of the setting or an undefined quantity. Its
`whole` label correctly refers to the canonical counterexample target.

T20's Rayleigh inequality is the printed smallest-eigenvalue lower bound, and
its covariance and moment conditions are those of Xi. Its explicit finite-sum
probabilities are complete-randomization probabilities. Singular control Grams
are asymptotically negligible under the fixed-dimension fourth-moment and
eigenvalue bounds. At zero oracle variance, the residual covariance condition
with delta<1 forces both residual variances to vanish; their population means
are zero, so the remainder numerator is also zero. The disclosed totalizations
therefore preserve the ordinary expression and the standing zero-over-zero
convention without discarding the substantive limit assertion.

The sole supplied earlier issue, concerning T20, is **fixed**.
`SAP/P002b/Defs/Part3.lean:34-37` now describes the totalized inverse and real
division, states ordinary-domain agreement, and explicitly says the whole
statement imposes neither of the old additional premises. The older guarded
`T20Statement` is a separate definition, not the reviewed Challenge statement.
This agrees with the architect's response. No step-2 conclusion changed after
reading the record.

`reading.md` was saved before opening the claims, record, or re-review material.
One clerical description of the numeral auxiliaries was subsequently corrected
from “denominators” to “real numerals”; it changes no mathematical reading.
Every closure entry was inspected, including generated auxiliaries via Lean.
`claim-stage.json` records the comparison before the record was opened.

`scratch/Nonvacuity.lean` imports only `SAP.P002b.Defs` and uses no Challenge
theorem. It directly verifies T16, finite and infinite T17 hypotheses,
simultaneously full-rank T18/T19 instances, all finite T20 hypotheses, and every
asymptotic T20 hypothesis for a strictly growing balanced one-covariate sequence.
It also checks a nonzero-residual Xi instance. The genuine fitted-data contrast
is 1/2 and its treated residual cross term is -5/8. Both this file and
`scratch/BlindCheck.lean` were compiled with `sap-lean`; JSON structure,
declaration coverage and fingerprints were checked with Python. No `lake`
command was run, and Lean processes were run sequentially.
