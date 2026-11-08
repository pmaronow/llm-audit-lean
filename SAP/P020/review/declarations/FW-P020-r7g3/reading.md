# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. Sources: all entries of the five closures in
`closure.json`, their source definitions and Challenge docstrings. Generated
auxiliaries were also printed with Lean in `scratch/Inspect.lean` (successful).
The notation below expands the SAP definitions into finite sets, sums, real
arithmetic, and Mathlib derivatives; it is part of each section using it.

## Common expanded notation and types

A population is the record `(M,t,n,y0,y1)` where `M,t : ℕ`, `0<t<M`,
`n : Fin M → ℕ`, every `n(j)>0`, and `y0,y1 : Fin M → ℝ` are arbitrary fixed
cluster potential totals. Thus `M≥2`. Write `c=M-t` (natural subtraction,
exact here), `J=Fin M`, `N=Σ(j∈J)n(j)>0`, and `x(j)=(n(j):ℝ)`.
Integers in real arithmetic are cast to ℝ. No individual potential-outcome
record is required by any of these five statements. Arbitrary real cluster
totals are representable by individual outcomes because each cluster is
nonempty (for example, constant individual outcome `ya(j)/n(j)`).

The assignment set is `S={s⊆J : |s|=t}`, implemented as
`Finset.univ.powersetCard t`. It is finite and nonempty since `t≤M`. For any
subset `s`, let `s1=s`, `s0=J\s`; `m1=t`, `m0=c`. Complete randomization
is uniform on S, with mass `1/|S|`. Its expectation is
`E f = Σ(s∈S) f(s)/|S|`.

More generally a finite law on an arbitrary type Ω consists of a finite
support F and a real weight function w, with `w≥0` on F and
`Σ(ω∈F)w(ω)=1`. Define
`E_L f=Σ(ω∈F)w(ω)f(ω)`, `Bias_L(f,d)=E_L f-d`,
`Var_L f=E_L[(f-E_L f)^2]`, and
`Cov_L(f,g)=E_L[(f-E_L f)(g-E_L g)]`.
Weights outside F are unrestricted and ignored. F cannot be empty.

For any real vector z on J define
`μ(z)=Σj z(j)/M`, `V(z)=Σj(z(j)-μ(z))²/M`, and
`C(z,w)=Σj(z(j)-μ(z))(w(j)-μ(w))/M`.
These are population moments with divisor M, not divisor M−1.
Define `A_a(z,s)=Σ(j∈sa)z(j)`, `Q_a(s)=A_a(x,s)`, and
`barQ_a(s)=Q_a(s)/ma`. For `s∈S`, both sa have positive cardinality and
both Q_a(s)>0. The parameter is
`Δ=(Σj y1(j)−Σj y0(j))/N`.

The individual difference in means is
`D(s)=A_1(y1,s)/Q_1(s)−A_0(y0,s)/Q_0(s)`.
HT total estimators are `H_a(s)=M/ma * A_a(ya,s)` and
`H(s)=(H_1(s)−H_0(s))/N`.
For any fixed real k define differenced potential totals
`r_a(k,j)=ya(j)−k(x(j)−μ(x))`,
`R_a(k,s)=M/ma * A_a(r_a(k),s)`, and
`R(k,s)=(R_1(k,s)−R_0(k,s))/N`.

For a natural A, arbitrary fixed `X : Fin A → J → ℝ`, a fixed real ks,
and fixed `ka : Fin A → ℝ`, the covariate differenced totals are
`rX_a(j)=ya(j)−ks(x(j)−μ(x))−Σ(l∈Fin A)ka(l)(X(l,j)−μ(X(l)))`.
Their total estimators are `RX_a(s)=M/ma * A_a(rX_a,s)` and
`RX(s)=(RX_1(s)−RX_0(s))/N`.

The closure's record constructor and projections contain precisely the
population/law data and proof fields above; they add no conclusions as
assumptions. `assignments_nonempty` is the finite-set cardinality proof.
`uniformLaw._proof_1` and `._proof_2` certify nonnegative normalized masses.
Other generated proofs in the closures are the numeral instance `2≥2`, the
standard `ContinuousSMul ℝ ℝ` instance for `HasDerivAt`, or the product
assignment's nonemptiness witness. They do not introduce hidden premises.

## SAP.P020.T11

Challenge lines 60–63; `T11Statement`, Part4 lines 60–79. It asserts a
conjunction of two independently universally quantified statements.

1. For every type Ω, every finite law L on Ω, every `u,v : Ω→ℝ`, and a
   proof `∀ω∈F, 0<v(ω)`,
   `E_L(u/v) = (E_L u−Cov_L(u/v,v))/E_L v`.
   The positive denominator hypothesis is only on the support, including
   support points of zero weight. Quantifier order is Ω,L,u,v,positivity.
2. For every population as above, put
   `B=Cov(A_1(y1)/Q_1,Q_1)/t−Cov(A_0(y0)/Q_0,Q_0)/c`.
   Then `E D=Δ−(M/N)B` and `E D−Δ=−(M/N)B`.
   Covariances and expectations are the design finite sums defined above.

The docstring explicitly restricts the first part to finite probability
laws; the second part is for all these complete randomized populations.

Junk-value audit: real division is total, with `z/0=0`. In part 1 v is
positive on F and `E_L v>0` follows from normalization and nonnegative weights.
Values of u/v outside F can involve zero denominators but never enter any
sum, including the covariance's internal expectations. In part 2 all random
ratios are evaluated only on S where Q_a>0. N,t,c,M and |S| are positive.
Subsets outside S can have empty arms and junk individual means, but their
values are ignored. Natural subtraction c is exact. All casts are exact.
No integrals, infinite values, logarithms, square roots, real powers,
infima/suprema, limits, or partial-function defaults occur.

## SAP.P020.T12

Challenge lines 65–67; `T12Statement`, Part4 lines 81–99. Five conjuncts:

1. For every `n : ℕ`, `Y : Fin n→ℝ`, then `b0,b1 : ℝ`,
   `Σi(b0+b1Y(i))=n*b0+b1ΣiY(i)`. The sum is the complete finite sum.
2. For every population, `E H_0=Σj y0(j)`, `E H_1=Σj y1(j)`, and
   `E H=Δ`.
3. For every population, then b0,b1, then subset s and proof s∈S, transform
   each potential total to `ya'(j)=n(j)*b0+b1*ya(j)` while leaving every
   population count unchanged. If H' is HT in that transformed population,
   `H'(s)=b0*(M/N)*(barQ_1(s)−barQ_0(s))+b1*H(s)`.
4. With the same quantifier order and support proof, additionally assume
   b0≠0 and `barQ_1(s)≠barQ_0(s)`. Then `H'(s)≠b1*H(s)`.
5. There exist a population, then real b0,b1 and a subset s, such that
   `s∈S` and `H'(s)≠b1*H(s)`. The existential conjunct does not separately
   state b0≠0 or unequal means; they follow from the shift identity.

The docstring calls this unbiasedness, affine transformation, conditional
failure of location invariance, and an admissible counterexample.

Junk-value audit: n=0 is allowed in conjunct 1; both sums and n*b0 vanish
and the identity is meaningful. No division by n occurs there. In the
remaining conjuncts all N,M,t,c,|S| denominators are positive by the
population record. The shift is individual affine transformation rendered
at the cluster-total level, not a constant shift of each cluster total.
Arbitrary subsets off S do not enter the expectation; supported s is
explicitly required where counts matter. No division by outcome variance
is present. Natural subtraction is exact, casts lose no information, and
there are no other analytic junk conventions.

## SAP.P020.T13

Challenge lines 69–83; `T13WholeStatement_W3`, WholeW3 lines 13–55, including
`T13Statement`, Part4 lines 101–111. The first conjunct asserts:

1. For every population then fixed `k : ℝ`,
   `E R_0(k)=Σj y0(j)`, `E R_1(k)=Σj y1(j)`, `E R(k)=Δ`.
2. For every population, then natural A, fixed X, fixed ks and ka,
   `E RX_0=Σj y0(j)`, `E RX_1=Σj y1(j)`, `E RX=Δ`.

The four further conjuncts assert:

3. For every population, arm `a : Bool`, then fixed k,
   `E[k(barQ_a−N/M)]=k E[barQ_a−N/M]`,
   `E[barQ_a−N/M]=0`, and `E[k(barQ_a−N/M)]=0`.
4. For every population, A, X, ks, ka, then arm a, let
   `Z_a(z,s)=A_a(z,s)/ma−μ(z)`. This unfolds `centeredArmMeanW3`.
   Then `E[ks Z_a(x)+Σl ka(l)Z_a(X(l))]=0`.
5. For every population, a, then k, `E R_a(k)=E H_a`.
6. For every population, A, X, ks, ka, then a, `E RX_a=E H_a`.

All coefficients and features precede the random assignment argument:
they are fixed vectors/scalars, not fitted random coefficients. There is
no nonzero variance condition, no independence assumption on fixed X,
and no restriction on signs. The docstring's centering concerns the selected
arm's random mean; no fixed-label centered size is asserted to have mean zero.

Junk-value audit: A=0 is allowed; the covariate sum is an empty sum, zero.
This does not make any universal population statement vacuous. The
population remains nonempty with positive M,N,t,c and support cardinality.
No coefficient divides by size or covariate variance, so zero variances
are meaningful. The arm denominators are fixed positive counts even for
the off-support function values. There are no integrals, limit operations,
∞ conversions, or other partial analytic values. The choice a has exactly
the two Boolean values, with true selecting y1 and false selecting y0.

## SAP.P020.T14

Challenge lines 85–91; `T14WholeStatement`, WholeW1 lines 63–169, including
`T14Statement`, Part4 lines 113–152, and Part2 lines 56–67.
Use the expanded sums above and abbreviate
`s=V(x)`, `q0=C(x,y0)`, `q1=C(x,y1)`,
`c0=(M−c)/c=t/c`, `c1=(M−t)/t=c/t`,
`v=(M−1)N²/M²`, `L=M²/(N²(M−1))`,
`ka*=qa/s`, `κ=(t/M)k0*+(c/M)k1*`,
`Q(k)=c0 V(r_0(k))+c1 V(r_1(k))+2 C(r_0(k),r_1(k))`, and
`G=L(c0+c1+2)s`.
These are respectively all of W1Sizes, W1SizeVariance,
W1SizeCovariance, W1c, W1t, W1v, W1ArmVariance,
armOptimalCoefficient, optimalCoefficient, rajMomentObjective, and
rajVarianceCurvature unfolded into finite moments and real arithmetic.

The initial `T14Statement` has seven conjuncts with separate quantifiers:

1. For every P, arm a, a proof s>0, then k,
   `V(r_a(k))=V(r_a(ka*))+s(k−ka*)²`.
2. For every P, proof s>0, arm a, then k,
   `V(r_a(ka*))≤V(r_a(k))`, with equality iff k=ka*.
3. For every P then k, `Var R(k)=L Q(k)`.
4. For every P, k, proof s>0,
   `Var R(k)=Var R(κ)+G(k−κ)²`.
5. For every P, k, proof s>0,
   `Var R(k)−Var H=G k(k−2κ)`.
6. For every P, proof s>0, then k,
   `Var R(κ)≤Var R(k)`, equality iff k=κ;
   `Var R(k)<Var H` iff `k²<2kκ`;
   `Var R(k)=Var H` iff `k=0 or k=2κ`.
7. For all real k then star, `k²<2k*star` iff
   `(star>0 and 0<k<2star) or (star<0 and 2star<k<0)`.

The added conjuncts are:

8. For every P then a, and every k,
   `μ(r_a(k))=μ(ya)`,
   `V(r_a(k))=Σj(ya(j)−k(x(j)−N/M)−μ(ya))²/M`, and
   `V(r_a(k))=V(ya)+k²s−2kqa`.
9. For every P and every k,
   `v Var R(k)=Q(k)` and
   `Q(k)=c0(V(y0)+k²s−2kq0)+c1(V(y1)+k²s−2kq1)
          +2(C(y0,y1)−kq0−kq1+k²s)`.
10. For every P, every a,k, the function `k↦V(r_a(k))` has Mathlib
    `HasDerivAt` derivative `2ks−2qa` at k; its actual first derivative
    function has derivative 2s at k. For every k, Q has derivative
    `c0(2ks−2q0)+c1(2ks−2q1)+2(−q0−q1+2ks)`;
    `deriv Q k=2(c0+c1+2)ks−2((c0+1)q0+(c1+1)q1)`;
    and the actual function `deriv Q` has derivative `2(c0+c1+2)s`.
11. For every P, if s≠0, all of the following hold (W1OptimalAlgebra):
    s>0, v>0, c0+c1+2>0; for each a, 2s>0 and for every k the arm
    derivative vanishes iff k=ka*; for every k Q' vanishes iff k=κ;
    `2(c0+c1+2)s>0`; and this entire chain of equalities:

    `0=c0(2κs−2q0)+c1(2κs−2q1)+2(−q0−q1+2κs)`;
    `c0κs+c1κs+2κs=c0q0+c1q1+q0+q1`;
    `(c0+c1+2)κs=(c0+1)q0+(c1+1)q1`;
    `((M−c)/c+(M−t)/t+c/c+t/t)κs
      =((M−c)/c+c/c)q0+((M−t)/t+t/t)q1`;
    `(M/c+M/t)κs=(M/c)q0+(M/t)q1`;
    `κ=(1/c+1/t)⁻¹((1/c)(q0/s)+(1/t)(q1/s))`;
    `κ=(1/c+1/t)⁻¹(k0*/c+k1*/t)`;
    `κ=(t/M)k0*+(c/M)k1*`.
    Also for every k, Q(κ)≤Q(k), with equality iff k=κ.
12. Under the same quantifier P then hypothesis s≠0, for every real k
    all successive comparisons below are equivalent (W1EfficiencyChain):

    `Var R(k)<Var H`;
    `(c0+c1+2)k²s<2k((c0+1)q0+(c1+1)q1)`;
    `(c0+c1+2)k²<2k((c0+1)(q0/s)+(c1+1)(q1/s))`;
    `(c0+c1+2)k²<2k((c0+1)k0*+(c1+1)k1*)`;
    `k²<2k((t/M)k0*+(c/M)k1*)`;
    `k²<2kκ`;
    `(κ>0 and 0<k<2κ) or (κ<0 and 2κ<k<0)`.
13. For every P, natural n, then proof every cluster size equals n,
    every real k and every subset u⊆J (support membership is not required),
    `R(k,u)=H(u)`.

The docstring describes unconditional expansions/derivatives, unique
stationary minima conditional on nonzero size variance, efficiency
intervals, and the equal-size case.

Junk-value audit: the definitions ka* and κ are total even when s=0,
because Lean makes 0⁻¹=0. Every stationary/minimum/coefficient-division
assertion using them is guarded by s>0 or s≠0; V(x)≥0 makes these
conditions equivalent. No zero-variance junk is used to claim uniqueness
in the equal-size case. All Q and variance polynomial identities and their
derivatives make sense at s=0 without division by s. M,N,t,c,M−1,v and
c0+c1+2 are strictly positive; `1/c+1/t` is positive. Subtractions M−c,
M−t and M−1 in the formulas are real subtraction after casting. The
one natural subtraction c=M−t is exact. Mathlib's `deriv` defaults to zero
where differentiability fails, but the displayed `HasDerivAt` conclusions
certify differentiability at every argument, including for the actual
first derivative functions; the default cannot be the source of the result.
Equal sizes entail n>0 even though it is not a separate hypothesis.
Finite sums and casts have their ordinary meaning; no other listed
junk-value operations occur.

## SAP.P020.T15

Challenge lines 93–95; `T15Statement`, Part4 lines 154–201.
Define, entirely in the notation of finite moments above,

`F=M²/N² * [ M/(M−1)(V(y0)/c+V(y1)/t)
               +(2C(y0,y1)−V(y0)−V(y1))/(M−1) ]`;
`A(z0,z1)=M³/(N²(M−1)) * (V(z0)/c+V(z1)/t)`;
`Vhat(z0,z1,u)=M²/N² * [
    Σ(j∈u0)(z0(j)−A_0(z0,u)/c)²/(c(c−1))
   +Σ(j∈u1)(z1(j)−A_1(z1,u)/t)²/(t(t−1)) ]`.

These unfold htVarianceFormula, approximateVariance, and
combinedVarianceEstimator. They use selected-arm sample variances, not
population variances masquerading as statistics. The conjunction is:

1. For every P,
   `Var H=(Var H_0+Var H_1−2Cov(H_0,H_1))/N²`,
   `Var H_0=M²/c * (M−c)/(M−1) * V(y0)`,
   `Var H_1=M²/t * (M−t)/(M−1) * V(y1)`, and
   `Cov(H_0,H_1)=−M²/(M−1) C(y0,y1)`.
2. For every P, `Var H=F` and `Var H≤A(y0,y1)`.
3. For every P, `2C(y0,y1)−V(y0)−V(y1)≤0`.
4. For every P, proof t≥2, then proof c≥2,
   `E Vhat(y0,y1)=A(y0,y1)` and `Var H≤E Vhat(y0,y1)`.
5. For every P, fixed real k, proof t≥2, then proof c≥2,
   `E Vhat(r_0(k),r_1(k))=A(r_0(k),r_1(k))` and
   `Var R(k)≤E Vhat(r_0(k),r_1(k))`.
6. For every natural B, proof B>0, then block populations
   `P : Fin B→ClusterPopulation`, let `Nall=Σb N_b` and let the assignment
   type be all functions choosing a valid assignment from each S_b.
   blockLaw is uniform on this full finite Cartesian product; it therefore
   gives independent uniform coordinates. `blockedSize=Nall`,
   `blockedHT(u)=Σb (N_b/Nall) H_b(u_b)`, and
   `blockedATE=(Σb(Σj y1_b(j)−Σj y0_b(j)))/Nall`.
   Then `E blockedHT=blockedATE` and
   `Var blockedHT=Σb (N_b/Nall)² Var H_b`.
7. For every B, proof B>0, block family P, then arbitrary family
   `Vhat_b : (subsets of Fin M_b)→ℝ`, assume for every block
   `Var H_b≤E_b Vhat_b`. Then
   `Var blockedHT≤E_product[Σb (N_b/Nall)² Vhat_b(u_b)]`.
   The hypotheses concern blockwise bounds, not the asserted global bound.

The docstring describes the exact components and upper bound, conservative
estimators with at least two clusters per arm, and independent blocks.

Junk-value audit: c−1 and t−1 can be zero in the definition of Vhat for
one-cluster arms, and real division would then replace their contributions
by zero. Both estimator conclusions explicitly require c,t≥2, so do not
use that convention. F,A and the exact variances require only M≥2 and
N,c,t>0, all supplied. B=0 would give an empty product with one empty
assignment and zero total size, so blocked ratios would be junk zero;
both blocked conclusions explicitly require B>0. This ensures Nall>0
and each block support is nonempty. The choice witness used in blockLaw
only proves product nonemptiness; it does not select one random assignment
or repeat it. The law is uniform over the entire product, so independence
is substantive and present. Off-support subsets do not enter any expected
sample variance. All arithmetic is finite, real subtractions in the
sample denominators are untruncated, the c natural subtraction is exact,
and there are no integrals or other listed analytic junk conventions.
