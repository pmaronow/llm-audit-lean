# Blind reading

This file was written from `closure.json`, the five Challenge docstrings, their
source definitions, and Mathlib, before opening `claims.json`, `record.json`,
`earlier.json`, or `architect-report.md`. No Solution was consulted.

Indices `i` range over `Fin n = {0,...,n-1}` and covariate indices `s,t` over
`Fin k`. All scalar quantities below are real numbers. All sums and dot products
are finite. A complement of a set of units is taken inside `Fin n`.

## SAP.P002b.T16

Sources: Challenge/Part1.lean:8-10; Defs/Part5.lean:11-18;
Defs/Part3.lean:12-21; Defs/Part2.lean:12-20; Defs/Part1.lean:31.

There are no hypotheses or external quantifiers. The array `x : Fin 4 → Fin 2 → ℝ`
has, in order, the rows `(1,0), (-1,0), (0,1), (0,-1)`.
For a function of the four units, its mean is its sum divided by 4.
The augmented row is the three-coordinate vector `(1,x_i0,x_i1)`, formally
indexed by `Option (Fin 2)`, with `none` the intercept and `some s` coordinate s.
Its squared norm is the sum of its three squared coordinates.
For any real unit array q, the definition called maximum is
`max ({0} ∪ {q_i : i ∈ Fin n})`.

The conclusion is the conjunction of all five statements:

1. For every coordinate s, `Σ_i x_is = 0`.
2. For every coordinate s, `(Σ_i x_is^4)/4 = 1/2`.
3. For every pair s,t, `(Σ_i x_is x_it)/4` is `1/2` when s=t and 0 otherwise.
4. `max_i (1+x_i0²+x_i1²) = 2`.
5. `1 + Σ_s max_i x_is² = 3`.

The Challenge docstring reports these exact values. The definition docstring calls
the array a counterexample, but the proposition itself is just these evaluations;
it does not contain a negated universal assertion.

Junk conventions: the zero adjoined to the finite maximum does not change any
maximum used here, since the arrays being maximized are nonnegative and the unit
set has four elements. All means divide by 4, and all halves have denominator 2.
The last `else` in the row definition is the fourth row because `i : Fin 4`;
there is no unaccounted default row. There are no roots, logarithms, real powers,
infinite values, integrals, infima/suprema, limits, or empty index sets.
The natural-number literals are embedded exactly into ℝ.

Closure auxiliaries were also read using `#print`: `augmented.match_1` is ordinary
Option case analysis, `maximum._proof_1` proves the maximum's set nonempty by the
inserted zero, and `T16Statement._proof_1`/`_proof_2` provide the numeric
`AtLeastTwo` instances for the real numerals 2 and 3. These add no assumptions.

## SAP.P002b.T17

Sources: Challenge/Part1.lean:12-14; Defs/Part5.lean:20-34;
Defs/Part3.lean:19-21; Defs/Part2.lean:12-20; Defs/Part1.lean:31.

The proposition is a conjunction of a finite bound and a sequence bound.

First, for every pair of natural numbers n,k, every real array
`x : Fin n → Fin k → ℝ`, assuming `n>0`, and then every real A, assuming `A≥0`
and `(Σ_i x_is^4)/n ≤ A` for every s, all three conclusions hold:

1. For every s, `max_i |x_is| ≤ sqrt(sqrt(A n))`.
2. `max_i (1+Σ_s x_is²) ≤ 1+Σ_s max_i x_is²`.
3. `1+Σ_s max_i x_is² ≤ 1+k sqrt(A n)`.

Second, for every natural k and real A with `A≥0`, for every sequence of arrays
`x_j : Fin (j+1) → Fin k → ℝ`, if every j,s satisfies
`(Σ_i (x_j)is^4)/(j+1) ≤ A`, then
`j ↦ max_i (1+Σ_s (x_j)is²)` is O(`j ↦ sqrt(j+1)`) at infinity.
Unfolding Mathlib `IsBigO`, this means there exists a real constant C and an
integer threshold J such that for every natural `j≥J`, the absolute value of
the former function is at most C times the absolute value of `sqrt(j+1)`.
C is existentially quantified after the fixed parameters and the sequence.
No centering, independence, covariance lower bound, or positivity of k is assumed.

Here the mean is sum/n, augmentation inserts a leading 1, squared norm is the
sum of squared coordinates, and every maximum is the maximum after adjoining
zero, as in T16. The Challenge and definition docstrings describe the finite
corrected inequalities and this fixed-dimension order consequence.

Junk conventions: `n>0` and `j+1>0` exclude empty unit sets and zero mean
denominators. k=0 is allowed; the coordinate assertions are then empty, their
sums are 0, and the augmented norm maximum is 1. The inserted zero does not
alter the maxima of absolute values, squares, or augmented squared norms.
Every square root has a nonnegative argument since A≥0 and sample sizes are
positive; `Real.sqrt`'s value 0 on negative inputs is unused. A=0 is allowed and
forces every coordinate to vanish; it is not a division convention.
All Nat casts are exact; `(j+1 : ℕ)` is taken before its cast to ℝ.
There are no partial functions, real noninteger powers, log, integrals, extended
reals, infima/suprema, or limsup/liminf. `IsBigO` uses a boundedness assertion,
not a potentially undefined quotient or limit. Its index filter is the proper
natural-number atTop filter. The closure's Option matcher and finite-maximum
nonemptiness proof have the meanings stated for T16.

## SAP.P002b.T18

Sources: Challenge/Part1.lean:16-18; Defs/Part5.lean:36-50;
Defs/Part1.lean:14-21,23,31-34,52-53,62-66,78-85;
Defs/Part2.lean:12-18,22-64.

The quantifiers are: for every natural n,k, every population P with real
potential outcomes `y_i(d)` indexed by a Boolean receipt d, Boolean potential
receipts `d_i(a)` indexed by Boolean assignment a, natural treated size n1, and
fixed real covariates `x_i ∈ ℝ^k`; for every real beta; and for every finite set
S of units, assume `n≥2`, `0<n1<n`, `|S|=n1`, and both arm augmented Gram
determinants nonzero. The conclusion is two exact identities.

The following notation fully expands the SAP definitions used in them.
Write `A_1=S`, `A_0=Sᶜ`, `z_i=(1,x_i)`, `z°_i=(0,x_i)`, and
`m_A(q)=(Σ_{i∈A} q_i)/|A|`. Boolean receipt d is converted to a real 0 or 1.
The potential adjusted responses are
`w_ai = y_i(d_i(a)) - beta * 1{d_i(a)=true}`.
For observed assignment S, `q_i=w_1i` on S and `q_i=w_0i` off S.
The Gram matrix is `G_A = m_A(z_i z_iᵀ)` and score `h_A(q)=m_A(z_i q_i)`.
Define `L_A(q)` as `G_A^{-1} h_A(q)` if `det G_A≠0`; otherwise choose a fixed
minimizer c of `Σ_{i∈A}(q_i-z_iᵀc)²`. If no minimizer exists, its formal last
branch is the zero vector (finite real least squares always has a minimizer).
Set `psi_a=L_all(w_a)`, `c_a=L_Aa(q)`, and `u_ai=w_ai-z_iᵀpsi_a`.
The notation `x_iᵀc_a,slopes` is `Σ_s x_is c_a(some s)`.
The feasible contrast is
`T = m_S(q_i-x_iᵀc_1,slopes) - m_Sᶜ(q_i-x_iᵀc_0,slopes)`;
the oracle contrast T* uses psi_1,psi_0 in place of c_1,c_0.

The two conclusions are

```
T - T* = -m_S[x_iᵀ(c_1-psi_1)_slopes]
          +m_Sᶜ[x_iᵀ(c_0-psi_0)_slopes],
T - T* = -m_S[(z°_i)ᵀ G_S^{-1} h_S(u_1)]
          +m_Sᶜ[(z°_i)ᵀ G_Sᶜ^{-1} h_Sᶜ(u_0)].
```

There is no centering assumption, monotonicity assumption, nonempty-complier
assumption, bound on outcomes, or positive covariate dimension. Exclusion is
built into `y_i(d)` depending on receipt alone. The docstrings describe the two
sign-corrected representations, consistent with the signs just displayed.

Junk conventions: all arm means divide by positive arm sizes. The treated
assignment support is exactly the subsets of size n1. The arm inverse matrices
are ordinary inverses because their determinants are assumed nonzero. The
population OLS is formally permitted to use its minimizer branch; in fact full
rank of either arm implies full rank of the whole population. A singular inverse
in Mathlib would be the zero matrix, but the explicit inverses here cannot take
that value as a fallback. No empty augmented coordinate type occurs: even k=0
leaves its intercept. Empty slope sums at k=0 are genuine zeros. Neither the
least-squares fallback nor arbitrary minimizer choice encodes either conclusion.
There are no roots, integrals, infinite quantities, extrema, or limits.
The Population/CovPopulation constructors and projections in the closure are
ordinary record construction and field selection; they add no constraints.
The augmented Option matcher is ordinary case analysis.

## SAP.P002b.T19

Sources: Challenge/Part1.lean:20-22; Defs/Part5.lean:52-64;
Defs/Part1.lean:14-21,23,31-34,52-53,62-66,78-85;
Defs/Part2.lean:12-14,22-49.

For every natural n,k, population P, real beta, finite unit set S, and Boolean
arm a, assume `n≥2`, `0<n1<n`, and `|S|=n1`. Then put A=S if a=true and A=Sᶜ
if a=false; assume `det G_A≠0`. The conclusion is the conjunction

```
psi_a - c_a = -G_A^{-1} h_A(u_a),
-2 m_A[u_ai z_iᵀ(c_a-psi_a)] = -2 h_A(u_a)ᵀ G_A^{-1} h_A(u_a).
```

In these formulas P consists of real `y_i(d)`, Boolean `d_i(a)`, n1, and real
covariates x_i. Receipt d is converted to its 0/1 value, the potential response
is `w_ai=y_i(d_i(a))-beta*1{d_i(a)=true}`, and observed q_i is w_1i on S and
w_0i off S. Augmented rows are `z_i=(1,x_i)`.
`m_A(q)=Σ_{i∈A}q_i/|A|`, `G_A=m_A(z_i z_iᵀ)`, and `h_A(q)=m_A(z_i q_i)`.
The coefficient psi_a is the whole-population least-squares coefficient of w_a
on z, while c_a is the arm-A coefficient of observed q. Least squares uses the
inverse normal equations for nonzero determinant and otherwise a fixed minimizer
of the finite sum of squared residuals, with a formal zero branch if no minimizer
exists. Finally `u_ai=w_ai-z_iᵀpsi_a`. Matrix/vector subtraction, negation and
dot products are coordinatewise subtraction, negation and finite scalar sums.

Only the selected arm's determinant is assumed nonzero; the opposite arm can be
singular. No covariance centering, compliance monotonicity, or moment hypotheses
are present. The scalar cross term is the actual residual times fitted-minus-
population prediction error. The docstrings report this sign and its factor -2.

Junk conventions: valid design and membership in the support ensure A is
nonempty, so its mean has no zero denominator. Its displayed inverse is ordinary.
Selected-arm full rank also implies population full rank. The unused opposite
arm can be singular without affecting either conclusion. The formal no-minimizer
branch cannot occur in finite real least squares. k=0 leaves a single intercept,
so no empty matrix is silently inverted. There are no roots, extrema, integrals,
extended reals or limits. Natural sizes are cast to ℝ before real division.
The structure constructor/projection auxiliaries and Option matcher carry no
extra assumptions. The closure's `T16Statement._proof_1` is just the numeral-2
typeclass proof used in the coefficient -2.

## SAP.P002b.T20

Sources: Challenge/Part1.lean:24-32; Defs/WholeW1.lean:13-56;
Defs/Part1.lean:14-43,52-53,62-85,128-129;
Defs/Part2.lean:12-64,83-94; Defs/Part3.lean:34-41.

This is `T20WholeStatement`, not the older `T20Statement` in Part5.
It is a conjunction of a finite algebraic assertion and a sequence limit.

For the finite part: for every n,k and P, assume valid design (`n≥2` and
`0<n1<n`), monotone receipt (`d_i(0)=1` implies `d_i(1)=1` for every i), a
nonempty set C of compliers (`d_i(0)=0`, `d_i(1)=1`), centered covariates
(`Σ_i x_is=0` for every s), and invertible whole-population augmented Gram.
Let `L = Σ_{i∈C}(y_i(1)-y_i(0))/|C|`.
For every Boolean a and every real beta, the population intercept psi_a(beta)_0
equals the mean of w_a(beta), and for every real beta,

```
mean(w_1(beta)) - mean(w_0(beta)) = (|C|/n) * (L-beta).
```

It also asserts that this mean contrast and the population-intercept contrast
are zero at beta=L. For every treated set S of size n1 it then asserts the chain

```
T*(L,S)
 = m_S[w_1(L)-xᵀpsi_1(L)_slopes] - m_Sᶜ[w_0(L)-xᵀpsi_0(L)_slopes]
 = m_S[w_1(L)-psi_1(L)_0-xᵀpsi_1(L)_slopes]
      - m_Sᶜ[w_0(L)-psi_0(L)_0-xᵀpsi_0(L)_slopes]
 = m_S[u_1(L)] - m_Sᶜ[u_0(L)].
```

P has the types of outcomes, receipts, sample size and covariates given in T18.
Explicitly, w_ai(beta)=y_i(d_i(a))-beta*1{d_i(a)=1}, mean is sum/n,
m_A is sum/|A|, z_i=(1,x_i), and `G_A=m_A(z_i z_iᵀ)`.
`h_A(q)=m_A(z_i q_i)`, psi_a(beta) is whole-population least squares of w_a(beta)
on z, and u_ai(beta)=w_ai(beta)-z_iᵀpsi_a(beta). Least squares is the inverse
normal equations at nonsingular Gram and otherwise a fixed finite-sum
least-squares minimizer, with an unreachable zero branch if no minimizer exists.
T* uses the observed w_i(beta) (w_1 on S, w_0 off S) with population slopes.
The two middle expressions are the complete expansions of
`oraclePotentialContrast` and `oracleCenteredContrast`.

For the limit part, the quantifiers are, in order: for every map
`sizes : ℕ → ℕ` that is strictly increasing; every natural fixed dimension k;
every sequence `P_j` of populations with sizes(j) units and k covariates; and
every five real parameters delta,e,A,B,r, assume `k>0`, `delta<1`, `e>0`,
`A>0`, `B>0`, `0<r≤1/2`, and every j satisfies the following conditions:

* Valid design, monotone receipt, and a nonempty complier set.
* `r n ≤ n1 ≤ (1-r)n`, where n=sizes(j).
* `cov(u_1(L),u_0(L)) ≥ -delta sqrt(var(u_1(L))) sqrt(var(u_0(L)))`.
* For a=0 and a=1,
  `sqrt(sqrt(mean(u_a(L)^4))) ≤ B sqrt(var(u_a(L)))`.
* Every x coordinate is population-centered and `mean(x_s^4) ≤ A`.
* For every real vector b of length k,
  `e Σ_s b_s² ≤ mean((Σ_s x_is b_s)²)`.

These are the full expansion of Xi. Here
`var(q)=Σ_i(q_i-mean(q))²/(n-1)` and
`cov(q,t)=Σ_i(q_i-mean(q))(t_i-mean(t))/(n-1)`;
the covariance condition concerns the entire population, not just compliers.
The parameter called fourthNorm is the fourth root of the uncentered fourth
moment, expressed as two nonnegative square roots. There is no additional
assumption that residual variance or oracle variance is strictly positive.
There is no assumption that every arm regression is invertible.

The assignment support Ω is all subsets S of n units with |S|=n1. For every
function f on those subsets,
`E_design f = Σ_{S∈Ω} f(S)/|Ω|` and
`V_design f = E_design[(f-E_design f)²]`.
For any event E, its probability is `|{S∈Ω : E(S)}|/|Ω|`.
Let z°_i=(0,x_i). The control remainder is

```
R(P,S) = m_Sᶜ[(z°_i)ᵀ G_Sᶜ^{-1} h_Sᶜ(u_0(L))]
           / sqrt(V_design[T*(L,·)]).
```

For every real kappa>0, the conclusion is
`Pr_design,j(kappa ≤ |R(P_j,S)|) → 0` as j→∞.
Unfolding Tendsto to `nhds 0`, for every tolerance eta>0, these probabilities
eventually have absolute value less than eta. This is an ordinary real limit;
no supremum over models or uniform rate is asserted.

Junk conventions: the finite part excludes empty populations, empty compliers,
empty arms and singular population Gram. In the limit part valid design excludes
zero denominators in means, covariance/variance, and design expectations and
probabilities; Ω is nonempty. Centering plus the Rayleigh lower bound with e>0
ensure a nonsingular population Gram. All fourth-root inputs and variances are
nonnegative. However, zero residual and oracle variances are permitted.
`Real.sqrt(0)=0`, and real division by zero is 0, so R is defined to be 0 whenever
its oracle variance is zero, regardless of its numerator. Also Mathlib's inverse
of a singular real square matrix is the zero matrix, so R is 0 for a singular
control-arm Gram. These are genuine totalizations that can affect its finite
meaning, and both the remainder and theorem docstrings disclose them. At positive
variance and nonsingular control Gram the expression is the ordinary one.
The alternative singular-arm OLS convention uses a least-squares minimizer;
it does not replace the explicit inverse inside R. Fixed k is positive in the
limit and can be zero only in the separate finite part. Nat casts are exact;
the n-1 in variances is real subtraction after casting, not Nat truncation.
Strict increase of sizes forces sample sizes to diverge and does not involve
a truncated difference. There is no logarithm, noninteger rpow, Bochner integral,
infinite toReal, empty extremum, limsup/liminf, or default partial function.
The structure/Option auxiliaries have the meanings given above, and
`T20WholeStatement._proof_1` is the numeral-2 `AtLeastTwo` proof for 1/2.

## Closure coverage

Every entry of the supplied closure was read. Source definitions cover the
statement wrappers, arrays, maximum, means, norms, population records, receipt
conditions, complier set and LATE, observed and potential responses, support,
design expectation/variance/probability, all regression components, Xi,
controlRemainder, and the two new oracle expressions. Generated entries without
source lines were inspected with `#print` in `scratch/BlindCheck.lean`, including
the ordinary record constructors and projections. Mathlib's real-matrix inverse
was checked in `LinearAlgebra/Matrix/NonsingularInverse.lean`: singular matrices
have inverse zero. Its Big-O definition was checked in
`Analysis/Asymptotics/Defs.lean`.
