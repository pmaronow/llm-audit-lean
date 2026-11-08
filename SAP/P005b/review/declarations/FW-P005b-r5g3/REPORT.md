# Review of T25, T26, and T27

All three declarations are **faithful**, with severity **none**. Every listed
dependency was read, including the generated numeral proofs and population
constructor/projections. `reading.md` was saved before opening `claims.json`;
`claim-stage.json` was saved before opening `record.json`. The record supplied
no reason to revise the independent claim-stage conclusions. No target is a
refutation.

| Declaration | Canonical clauses checked | Record and docstring |
| --- | --- | --- |
| `SAP.P005b.T25` | Common-slope leading terms, `d_n/n → 0`, and `O_p(sqrt(κ_n d_n/n))`. All are in `Defs/Part7.lean:13`. | `whole` is correct; `Challenge/Part1.lean:64` accurately summarizes the result, including positive dimension. |
| `SAP.P005b.T26` | The little-o expansion is in `Defs/Part7.lean:21`; the big-O bound without leverage decay and exact p. 1516 remainder identity are both in `Defs/WholeW1.lean:120`. These last two clauses occur in the canonical **statement**, so checking only the little-o assertion would be insufficient. | `whole` is correct; `Challenge/Part1.lean:70` accurately describes all three clauses. |
| `SAP.P005b.T27` | The separate treatment/control population slopes and little-o expansion are in `Defs/Part7.lean:30`; the big-O assertion without leverage decay is in `Defs/WholeW1.lean:135`. | `whole` is correct; `Challenge/Part1.lean:76` accurately describes both clauses. |

The uniform randomization design, finite averages, covariance divisor, outcome
centering, Gram normalization, leverage, slope formulas, debiasing signs and
weights all match the canonical notions. In T26 the inverse component cancels
to give exactly the negative covariate-mean dot product plus the treated
leverage covariance minus the control covariance, each divided by `n-2`. In
T27 cancellation leaves the within-arm covariance corrections with weights
`n_C/((n-2)n_T)` and `n_T/((n-2)n_C)` and the appropriate treatment/control signs.
These are explicit statistical formulas, not placeholders or definitions of a
remainder as zero.

Positive dimension is explicit in each canonical `definitions_needed`.
Invertibility under **every** assignment is the canonical standing reading of
footnote 4, including both arm matrices for T27. Neither is an undisclosed extra
assumption. Requiring invertibility only eventually and ignoring sizes below
three does not alter any asymptotic assertion. A positive big-O constant is
equivalent to the canonical finite constant because the rates are positive
eventually.

The size assumptions protect all means and correction denominators at the
relevant sizes. The regularity hypotheses protect the regression interpretation
of matrix inverses. The leverage supremum is a finite nonempty maximum for
positive sizes, and `κ_n ≥ d_n/n > 0` under eventual standardization. Empty-set,
singular-inverse, division-by-zero and square-root conventions therefore cannot
produce any of these conclusions. There are no integrability or measurability
loopholes in these finite randomization spaces.

For nonvacuity of **each complete sequence hypothesis**, take `d_n=1`,
`m_n=floor(n/2)` and, for `n≥3`, indices `i=0,…,n-1`,

\[
x_{n,i}=(2i-n+1)\sqrt{\frac{3}{n^2-1}},\qquad
y_{n,i}(1)=x_{n,i}^2,\qquad y_{n,i}(0)=x_{n,i}.
\]

Set the arrays to zero at smaller sizes. Summing an arithmetic progression and
its squares gives population mean zero and second moment one. All covariates
are distinct, `x_{n,i}²<3`, and `K=9` bounds every second moment required by
`standingAssumptions`. The treatment fraction lies in `[1/3,1/2]`, so fixed
strict bounds `lo=1/4`, `hi=3/4` work. For every `n≥4`, both arms of every
assignment contain at least two distinct covariate values. Each scalar arm
covariance is therefore positive, establishing T27's regularity. The common
matrix is the positive weighted sum of those two scalar covariances, which
establishes T25's and T26's regularity. Finally,

\[
\frac{d_n}{n}=\frac1n\to0,\qquad
\kappa_n=\frac{3(n-1)}{n(n+1)}\to0.
\]

Thus T25, T26, and T27 each have jointly satisfiable assumptions, including all
their limit hypotheses. This full sequence argument is mathematical, not a
claim to have compiled a general normalized-sequence construction in Lean.

As a concrete Lean check, `scratch/Nonvacuity.lean` constructs `n=4`, `d=1`,
`m=2`, covariates `(-7/5,-1/5,1/5,7/5)`, and nonconstant outcomes `yT_i=i²`,
`yC_i=i`. It proves standardization, noninteracted regularity under all six
assignments, interacted regularity of both arms under all six assignments,
nonempty-arm/positive-dimension conditions, fraction bounds, and second-moment
bounds with `K=100`. This also supplies genuine hypotheses for T26's finite
identity. It checks the finite definitions independently of the target proofs;
it does not alone establish the sequence hypotheses. Both this file and
`scratch/BlindPrint.lean` compile with `/home/ubuntu/sap/tools/sap-lean`.

No source changes or fixes are needed. `findings.json` and `claim-stage.json`
were parsed and checked with Python, including one-to-one target coverage and
the fingerprints copied from `closure.json`.
