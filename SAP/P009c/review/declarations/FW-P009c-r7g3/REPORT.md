# Review of SAP.P009c.T45--T49

All five declarations are **faithful**, with severity **none**. The record's
five `whole` decisions and the target docstrings accurately describe the
statements. No corrections are needed.

The blind expansion is saved in `reading.md`; it was written before opening
the canonical claims or record. Every closure entry was read, including the
constructors, projections and generated numeral proofs printed in
`scratch/PrintClosure.lean`. `claim-stage.json` was saved before opening
`record.json`. Reading the record did not change any claim-stage conclusion.

| Declaration | Assessment |
| --- | --- |
| T45 | Both estimators' EATE consistency and the exact three-term rate are present. Full-cube interference, uniform moments, both mixing conditions, and the paper's explicit zero-to-zero-power convention are rendered correctly. |
| T46 | Both estimators' ADSE consistency and the exact two-term rate are present. Internal separation and nonempty supported arms are not added as hypotheses. Conditional treatment means have positive conditioning probability. |
| T47 | The difference from the moving bias sequence tends to zero in probability. B1 and B2, their normalizations, spillover orientation, conditional covariance signs, the no-interference specialization, and nonnegative MSQ agree with the canonical claim. No restricted-interference assumption is added. |
| T48 | AVG inflation, the variance-heterogeneity condition and the complete iterated-limit definition of conservativeness agree with Proposition 8. |
| T49 | MAX inflation and both alternatives agree with Proposition 9. The eventual positive MSQ bound correctly expresses the second branch's Omega(1) requirement. |

The `broader` entries for T45 and T46 in `claim-stage.json` record valid
strengthenings: the theorems permit every admissible moment index, including
infinity, and thus include the canonical maximal-index choices. They retain
every canonical conclusion. A common moment constant can be enlarged to
accommodate separately admissible bounds. Quantifying over all real Hajek
extensions also retains the printed contrast wherever both ratios exist.
Neither strengthening calls for a restriction label.

All potentially totalized operations were checked. Positive population sizes
and mandatory interference diagonals keep the scaling denominators positive.
Regularity guards marginal denominators; Bernoulli independence guards all
off-diagonal joint conditioning events. The diagonal B2 summands are zero.
Degree suprema are finite and nonempty, mixing suprema are nonempty and bounded,
and square-root arguments are nonnegative. The infinity branches bypass
`untopD` defaults. No undefined expectation or junk value supports a conclusion.
The finite assignment setting supplies the usual measure-theoretic conditions.

`scratch/Nonvacuity.lean` compiles successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`. It imports only the
definitions and uses no target theorem, `sorry`, or additional axiom. Its
explicit growing study with independent fair assignments and zero outcomes
satisfies every antecedent of all five declarations, including the infinite
moment indices for T45--T46 and T47's no-interference specialization. A separate
positive-effect study has y_i(z)=z_i and MSQ=1, verifying T49's second branch
independently. Compilation emits only style warnings.

`findings.json` and `claim-stage.json` were parsed with Python. The findings
contain exactly one entry per reviewed declaration, with fingerprints checked
against `closure.json`. No refutation or counterexample is asserted.
