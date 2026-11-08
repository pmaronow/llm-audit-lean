# Blind reading

This file was written before opening `claims.json` or `record.json`. The source
for the three theorem stubs is `SAP/P005b/Challenge/Part1.lean:64–80`.
I read every entry of each closure in `closure.json`, including the population
constructor and projections. The two generated `_proof_1` entries were printed
in `scratch/BlindPrint.lean`: both prove `(1 + 1).AtLeastTwo`, supplying the
numeral used in subtraction; neither adds a mathematical assumption.

## SAP.P005b.T25

### Objects, definitions, and quantifiers

Universally quantify two functions `d,m : ℕ → ℕ`, then a dependent family of
populations `P : (n : ℕ) → Population n (d n)`. A population is exactly three
real arrays, with no built-in conditions: `x : Fin n → Fin (d n) → ℝ` and
`yT,yC : Fin n → ℝ`. `Fin n` indexes integers from zero to `n-1`.

Here is all the finite-population notation used below, with the SAP definitions
expanded. At a fixed size, write `U = {0,…,n-1}`, and let `S ⊆ U` have cardinality
`m`; write `C = U \ S`. The design is the finite set of **all** such `S`, and
probability of an event is its number of assignments divided by the number of
assignments in this design, as a real quotient. Thus each size uses uniform
complete randomization; no relation between randomizations at different sizes
is required. For any real array `a`,

- `ā_A = (Σ_{i∈A} a_i)/|A|`, and `ā = (Σ_{i∈U} a_i)/n`;
- `a_i^c = a_i-ā`;
- `u·v = Σ_{k∈Fin d} u_k v_k`, and `x̄_A` applies the same mean to each coordinate;
- `G_kl = (1/n)Σ_i x_ik x_il`; standardized means `x̄_U=0` and `G=I_d`;
- `ℓ_i = Σ_k x_ik²`, and `κ = sup {ℓ_i/n : i∈Fin n}` in the real order;
- `τ = ȳT-ȳC`, `p=m/n`, and `q=(n-m)/n` (real subtraction);
- `b(y)_k = (1/n)Σ_i y_i x_ik`, and `N=p b(yT)+q b(yC)`;
- `c_A(y)_k = (1/|A|)Σ_{i∈A} y_i x_ik-ȳ_A x̄_A,k`;
- `L̂=I_d-p x̄_S x̄_Sᵀ-q x̄_C x̄_Cᵀ`, and
  `N̂=p c_S(yT)+q c_C(yC)`;
- `β̂=L̂⁻¹N̂`, where the inverse is Mathlib's total matrix inverse and the
  multiplication is ordinary finite matrix-vector multiplication;
- `τ̂=ȳT_S-ȳC_C-(x̄_S-x̄_C)·β̂`;
- `e_i(y)=y_i-ȳ-x_i·N`, using this same `N` for both potential-outcome arrays;
- `L=ē_S(yT)-ē_C(yC)`.

After quantifying the data, the theorem universally quantifies proofs of the
following hypotheses, in this order:

1. For **every** `n≥3`, `1≤d(n)≤n` and `0<m(n)<n`.
2. There exists **one** real `K≥0` such that for every `n≥3`, both outcome
   population second moments are at most `K`, and for every coordinate `k`
   its covariate population second moment is at most `K`.
3. For all sufficiently large `n`, `x̄_U=0` and `G=I_d`.
4. There exist real `lo,hi`, with `0<lo<hi<1`, such that for every `n≥3`,
   `lo<m(n)/n<hi`.
5. For all sufficiently large `n`, for **every** subset `S` in the design,
   `det L̂≠0`. This is invertibility for every assignment at each such size.
6. The real sequence `d(n)/n` tends to zero as `n→∞`.

The first four items form the single `standingAssumptions` argument; their
order within that conjunction does not change their quantifiers.

The conclusion is `τ̂-τ-L = O_p(√(κ d/n))`, with precisely this definition:
for every real `ε>0`, there exist real `M>0` and natural `n₀` such that for
every `n≥n₀`, the fraction of design assignments satisfying
`|τ̂-τ-L| > M sqrt(κ d(n)/n)` is less than `ε`. There is no conclusion about
expectations, asymptotic normality, a common probability space, or a coupling.

### Junk-value audit

All means and proportions are real divisions. An empty mean, an empty-design
probability, and division by zero are zero in Lean. The dimension and arm-size
conditions imply `n≥3` and two nonempty arms at the sizes relevant to the
asymptotic conclusion; the design then is nonempty. Values at `n=0,1,2`, and
values of the displayed estimator outside the design, cannot affect the
conclusion because the order assertion allows a finite initial segment to be
discarded and probabilities count only assignments in the design.

The matrix inverse is zero on singular real matrices, rather than undefined.
The eventual regularity hypothesis prevents this convention on **every**
assignment at all sufficiently large sizes. For earlier sizes its values again
do not affect the order assertion. If `d=0`, coordinate sums/vectors/matrices
are empty, the empty matrix determinant is one, and dot products are zero;
however, the hypotheses explicitly exclude dimension zero at all `n≥3`.

The real supremum in `κ` is zero for an empty index type (`n=0`). For positive
`n` the range is finite, nonempty, and bounded, so this is an ordinary maximum,
not an unbounded-supremum default. Its terms are nonnegative. Under eventual
standardization and positive dimension their sum is `d`, so `κ≥d/n>0`.
`Real.sqrt` returns zero for nonpositive input; the rate has positive input
eventually, so this convention cannot change the asymptotic statement.

The casts of naturals into reals are exact, and the relevant `n-m` in `pC` is
real subtraction, not truncated natural subtraction. Finite-set difference
means complement inside `U`. There is no logarithm, real power, integral,
`toReal` of infinity, `sInf`, limsup/liminf, or partial-function default in this
closure. Ordinary `Tendsto` and `∀ᶠ … in atTop` have their usual filter meanings.

## SAP.P005b.T26

### Objects, definitions, and quantifiers

This theorem is a conjunction of three assertions, so the data and hypotheses
of its three assertions are independently quantified.

For the first assertion quantify `d,m : ℕ→ℕ` and arrays
`x_n : Fin n→Fin (d n)→ℝ`, `yT_n,yC_n : Fin n→ℝ`. All finite sums below are
real sums, all averages divide by the cardinality of their index set, and
randomization is uniform on all `m(n)`-element subsets of `Fin n`.

At each size write `C=U\S`, `ā_A=Σ_{i∈A}a_i/|A|`, `ā=Σ_i a_i/n`,
`x̄_A,k=Σ_{i∈A}x_ik/|A|`, and `u·v=Σ_k u_kv_k`. Define

- `G_kl=Σ_i x_ik x_il/n`, `ℓ_i=Σ_k x_ik²`, `κ=sup_i ℓ_i/n`, `τ=ȳT-ȳC`;
- `p=m/n`, `q=(n-m)/n`, `b(y)_k=Σ_i y_i x_ik/n`, `N=p b(yT)+q b(yC)`;
- `c_A(y)_k=Σ_{i∈A}y_i x_ik/|A|-ȳ_A x̄_A,k`;
- `L̂=I-p x̄_S x̄_Sᵀ-q x̄_C x̄_Cᵀ`, `N̂=p c_S(yT)+q c_C(yC)`;
- `β̂=L̂⁻¹N̂`, `v₂=(L̂⁻¹-I)N̂`;
- `τ̂=ȳT_S-ȳC_C-(x̄_S-x̄_C)·β̂`;
- `cov_A(a,b)=Σ_{i∈A}a_i b_i/|A|-ā_A b̄_A` (denominator `|A|`, not `|A|-1`);
- `B̂=[cov_C(ℓ,yC)-cov_S(ℓ,yT)]/(n-2)+(x̄_C-x̄_S)·v₂`;
- `τ̂_db=τ̂-B̂`;
- `e_i(y)=y_i-ȳ-x_i·N`, `L=ē_S(yT)-ē_C(yC)`.

The first assertion assumes, after the data:

1. For every `n≥3`, `1≤d(n)≤n` and `0<m(n)<n`.
2. A single constant `K≥0` bounds both outcome second moments and every
   covariate coordinate's second moment for every `n≥3`.
3. For all sufficiently large `n`, `x̄_U=0` and `G=I`.
4. Constants `0<lo<hi<1` bound `m(n)/n` strictly between `lo` and `hi` at every
   `n≥3`.
5. For all sufficiently large `n`, `det L̂≠0` for every assignment in the design.
6. `κ_n→0`.

Its conclusion is `τ̂_db-τ-L=o_p(sqrt(1/n))`. Fully expanded: for every real
`δ>0`, the real sequence
`#{S: |S|=m(n), |τ̂_db-τ-L|>δ sqrt(1/n)}/#{S: |S|=m(n)}` tends to zero.

The **second** assertion quantifies fresh data `d,m,P` with hypotheses 1–5
above, **without** hypothesis 6. Its conclusion is
`τ̂_db-τ-L=O_p(sqrt(κ/n))`: for each real `ε>0` there are real `M>0` and natural
`n₀` such that for every `n≥n₀` the fraction of design assignments for which
`|τ̂_db-τ-L|>M sqrt(κ/n)` is less than `ε`.

The **third** assertion independently quantifies naturals `n,d,m` and a single
population of those sizes. It assumes `n≥3`, `0<m<n`, `x̄_U=0`, and `G=I`, then
quantifies each `S` in the `m`-subset design and assumes `det L̂≠0` for that
particular `S`. Its conclusion is the exact identity

`τ̂_db-τ-L = -(x̄_S-x̄_C)·(N̂-N)
             +cov_S(ℓ,yT)/(n-2)-cov_C(ℓ,yC)/(n-2)`.

In this last assertion there is no positive-dimension condition, uniform
second-moment bound, bound away from treatment fractions zero and one,
asymptotic condition, or full-design invertibility hypothesis.

### Junk-value audit

The same real divisions, total matrix inverse, finite-set complements, and
empty-coordinate sums described mathematically above apply here. At all
relevant sufficiently large sizes, `n≥3`, both arms are nonempty, the design is
nonempty, and `n-2>0`. In the finite identity the same nonzero denominators are
protected immediately by its size hypotheses. Invertibility is protected
eventually for the two asymptotic assertions and per assignment for the finite
identity. Thus singular-inverse zero is never used where the statements claim
the corresponding regression meaning. Empty dimensions are excluded in both
sequence assertions but allowed in the finite identity, where they describe
ordinary unadjusted differences and zero-dimensional matrices.

`κ` is a maximum of finitely many nonnegative reals when `n>0` and is zero for
`n=0`; it is eventually positive under these standing hypotheses. The square
root inputs `κ/n` and `1/n` are eventually positive. Their zero or nonpositive
input conventions affect only discarded early indices. Subtractions in the
displayed debiasing denominators are in `ℝ`; in particular they are not natural
truncations. The auxiliary `_proof_1` declarations only instantiate the numeral
two. All casts are exact. No integrals, extended-real conversions, logs, real
powers, unbounded suprema, infima, limsup/liminf, or other partial defaults
occur. `O_p` and `o_p` count finite events and cannot exploit nonmeasurable data.

## SAP.P005b.T27

### Objects, definitions, and quantifiers

This theorem is the conjunction of two independently universally quantified
sequence assertions. In each, quantify `d,m : ℕ→ℕ`, then real arrays
`x_n : Fin n→Fin (d n)→ℝ` and `yT_n,yC_n : Fin n→ℝ`. For a fixed size let
`U=Fin n`, `S` range uniformly over **all** `m(n)`-element subsets, and `C=U\S`.
Let `ā_A=Σ_{i∈A}a_i/|A|`, `ā=Σ_i a_i/n`, `x̄_A` be coordinatewise averaging,
and `u·v=Σ_k u_kv_k`. All probabilities are fractions of assignments in this
finite design. The complete definitions used by the estimator and expansion
are:

- `G_kl=Σ_i x_ik x_il/n`; standardized means `x̄_U=0` and `G=I`;
- `ℓ_i=Σ_k x_ik²`, `κ=sup_i ℓ_i/n`, `τ=ȳT-ȳC`, and `p=m/n`;
- `b(y)_k=Σ_i y_i x_ik/n`;
- `A_A,kl=Σ_{i∈A}x_ik x_il/|A|-x̄_A,k x̄_A,l`;
- `c_A(y)_k=Σ_{i∈A}y_i x_ik/|A|-ȳ_A x̄_A,k`;
- `β̂_A(y)=A_A⁻¹c_A(y)`, `v₂,A(y)=(A_A⁻¹-I)c_A(y)`;
- `τ̂_int=ȳT_S-ȳC_C-[x̄_S·β̂_S(yT)-x̄_C·β̂_C(yC)]`;
- `cov_A(a,b)=Σ_{i∈A}a_i b_i/|A|-ā_A b̄_A`;
- `B̂_int=m/[(n-2)(n-m)] cov_C(ℓ,yC)+x̄_C·v₂,C(yC)
              -(n-m)/[(n-2)m] cov_S(ℓ,yT)-x̄_S·v₂,S(yT)`;
- `τ̂_int,db=τ̂_int-B̂_int`;
- `e_i(y)=y_i-ȳ-x_i·b(y)`, with the separate population slope for each arm;
- `L_int=ē_S(yT)-ē_C(yC)`.

The first assertion assumes, in order:

1. For every `n≥3`, `1≤d(n)≤n` and `0<m(n)<n`.
2. One real `K≥0` bounds both outcome second moments and each covariate
   coordinate's second moment at every `n≥3`.
3. Eventually `x̄_U=0` and `G=I`.
4. There exist `0<lo<hi<1` such that `lo<m(n)/n<hi` for every `n≥3`.
5. Eventually, for every `S` in the design, **both** `det A_S≠0` and
   `det A_C≠0`. This is full rank for both regressions for every assignment.
6. `κ_n→0`.

It concludes `τ̂_int,db-τ-L_int=o_p(sqrt(1/n))`. This means: for each real `δ>0`,
the fraction of assignments satisfying
`|τ̂_int,db-τ-L_int|>δ sqrt(1/n)` tends to zero as a real sequence.

The second assertion quantifies fresh `d,m,P` satisfying 1–5 above; it does
**not** assume `κ_n→0`. It concludes
`τ̂_int,db-τ-L_int=O_p(sqrt(κ/n))`: for each real `ε>0`, there exist real `M>0`
and natural `n₀` such that at every `n≥n₀` the fraction of assignments with
`|τ̂_int,db-τ-L_int|>M sqrt(κ/n)` is less than `ε`.

### Junk-value audit

The averages, covariance normalizations, treatment fraction and correction
coefficients use total real division. Empty means or empty-design probabilities
would be zero; at every sufficiently large relevant size `n≥3` and `0<m<n`,
so neither is an intended empty quantity. These inequalities also protect
`m`, `n-m` and `n-2` in every correction denominator. The printed elaboration
of `interactedBiasEstimate` confirms that both `n-m` and `n-2` in these
coefficients are real subtractions, with exact natural casts.

The two matrix inverses would be zero at singular real covariance matrices.
The eventual all-assignments, both-arms regularity hypothesis explicitly
excludes this case at all sufficiently large sizes. Empty covariate index types
have the usual zero-sum/empty-matrix conventions, but `d≥1` for every `n≥3`.
The real supremum defining `κ` is an actual finite maximum at positive sizes,
and takes its empty-set value zero at `n=0`. Its input to the square root is
nonnegative and eventually positive, as is `1/n`. Arbitrary behavior at the
finitely many earlier sizes has no effect on either stochastic order assertion.

There are no Bochner integrals, infinite means, extended-real conversions,
logarithms, real powers, unbounded suprema, infima, limsup/liminf, natural
subtraction denominators, or partial-function defaults in this closure. The
generated proof dependency only supplies the numeral two. No independence
between sizes is imposed or needed by these finite-probability limit statements.
