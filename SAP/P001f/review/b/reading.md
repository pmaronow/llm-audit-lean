# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. Sources read: all supplied
`SAP/P001f/Defs*.lean`, `Defs/Part1` through `Part5`, and both Challenge files.
There are eighteen theorem stubs. This reading describes their types, not their
`sorry` proofs or the claims made by their docstrings.

## Conventions and definition expansion

All real functions and arithmetic below have their Lean meanings. In particular,
real division by zero is zero; a real Bochner integral is zero if its integrand
is not integrable; `ENNReal.toReal` sends infinity to zero; and `deriv` is zero
at a point where a derivative does not exist. Whether the hypotheses avoid
these conventions must therefore be checked separately.

For a probability measure μ write Eμ[Z] for its real Bochner integral and Pμ(A)
for `(μ A).toReal`. Sets of probability one and almost-everywhere equalities are
with respect to the displayed measure. On finite-dimensional real spaces,
volume is the usual Lebesgue measure (and on products the usual product volume).
`MemLp Z 2 μ` means almost-everywhere strong measurability and finite second
absolute moment. `Integrable` means almost-everywhere strong measurability and
finite first absolute moment. `variance Z μ` is the real value of the nonnegative
extended integral of |Z−Eμ[Z]|²; it is zero if that integral is infinite. Standard
deviation in these statements is the nonnegative real square root of variance.
`Polynomial.natDegree` is ordinary degree for nonzero polynomials and zero for
the zero polynomial. `Summable` for a real indexed family means convergence of
the net of finite subsums (thus absolute summability); `∑'` is its sum when
summable, and zero otherwise.

The following abbreviations fully expand the SAP predicates used below.

* CM(μ,X,Y,m), namely `ConditionalMean`, says: m is measurable, Y is μ-integrable,
  m∘X is μ-integrable, and for every measurable A in the covariate space,
  ∫_{X∈A}Y dμ = ∫_{X∈A}m(X) dμ. It does **not** separately assert measurability
  of X. All uses except T107 and algebraic definitions supply that elsewhere.
  CM also applies to a finite restricted measure without renormalizing it.
* CIμ(Y,Z | X), namely `ConditionallyIndependent`, takes a supplied proof that
  X is measurable. For every measurable A in Y's codomain and B in Z's,
  Eμ[1_{Y∈A,Z∈B} | σ(X)] = Eμ[1_{Y∈A} | σ(X)] Eμ[1_{Z∈B} | σ(X)] μ-a.e.
  The conditioning algebra is exactly `MeasurableSpace.comap X`. Mathlib's
  conditional expectation is zero for a nonintegrable input, a non-subalgebra,
  or a non-sigma-finite trimmed measure. Here measurable bounded indicators,
  measurable conditioning variables, and probability measures avoid those cases.
* IIDμ(Z_i), namely `IndependentCopies`, means that each Z_i, i∈ℕ, is measurable;
  the generated sigma algebras are jointly independent (finite intersections of
  events factor into products); and each pushforward law equals that of Z_0.
  `IdentDistrib` additionally includes a.e. measurability, already implied here.
  `IndepFun` is the analogous two-function independence.
* RD(ν,f), namely `RealDensity`, says that f is volume-a.e. measurable,
  pointwise nonnegative, volume-integrable, and ν(A)=∫_A f dx for measurable A,
  expressed by `volume.withDensity (ENNReal.ofReal ∘ f)`. The definition alone
  does not normalize f; a probability pushforward does.
* `sampleAverage Z n` is n⁻¹∑_{i=0}^{n−1}Z_i. Every substantive use below has n>0.
* EM(μ,X,Y,x), namely `eventMean`, is ∫_{X=x}Y dμ / Pμ(X=x).
* The censored observation is Y*=YR−99(1−R). The realized potential outcome
  is Y=Y₁D+Y₀(1−D).
* For weights w on Fin n: FM_w(V)=∑_i w_i V_i;
  FP_w(A)=∑_{i:A(i)}w_i; FEM_w(V,X,x)=∑_{i:X_i=x}w_i V_i / FP_w(X=x).
  Finite CI of U,V given X means, for every x,u,v whose X-cell has positive
  weight, FP(X=x,U=u,V=v)FP(X=x)=FP(X=x,U=u)FP(X=x,V=v).
  This finite definition does not itself require normalized nonnegative weights.
* Let ℓ(a,b,x)=exp(a+bx)/(1+exp(a+bx)). For j=0,1,2 put x_j=−1,0,1 and
  L(N,r;a,b)=∑_j[r_j log ℓ(a,b,x_j)+(N_j−r_j)log(1−ℓ(a,b,x_j))].
* For a finite type E define I(n,q,s,t)=n⁻¹∑_x[s_x/q_x−t_x/(1−q_x)] and
  S(n,n_t,n_c,s,t)=n⁻¹∑_x(n_t(x)+n_c(x))[s_x/n_t(x)−t_x/n_c(x)].
* The coordinate derivative ∂_k m(x) is the ordinary derivative at t=0 of
  t↦m(x with coordinate k replaced by x_k+t). `samplePDA X mhat n ω k`
  is, by definition, this coordinate derivative of mhat(n,ω) at the vector of
  sample covariate means.

Mathlib definitions were followed in
`MeasureTheory/Function/ConditionalExpectation/Basic.lean:102`,
`MeasurableSpace/Basic.lean:84`, `Integral/Bochner/Basic.lean:158`,
`Function/L1Space/Integrable.lean:59`, `Function/LpSeminorm/Defs.lean:152`,
`Measure/Map.lean:99`, `Measure/WithDensity.lean:38`, `Measure/Restrict.lean:50`,
`Probability/Independence/Basic.lean:92–148`, `Probability/IdentDistrib.lean:71`,
`Probability/Moments/Variance.lean:59–64`,
`Analysis/Calculus/Deriv/Basic.lean:130–154`,
`Analysis/Calculus/FDeriv/Defs.lean:145`,
`Topology/Algebra/InfiniteSum/Defs.lean:89–146` (additive definitions generated
from the product definitions), and `Algebra/Polynomial/Degree/Defs.lean:52`.
All these paths are relative to the supplied Mathlib source root.

## SAP.P001f.T96

This is a closed conjunction, with no assumptions. Set N=(6,6,6), r=(3,1,5),
treated outcome sums s=(12,3,20), and control outcome sums t=(9,10,3). It says:

1. For every pair a,b∈ℝ, L(N,r;a,b)≤L(N,r;0,log 2), with equality iff
   a=0 and b=log 2.
2. For every j∈Fin 3, 0<r_j<N_j and ℓ(0,log 2,x_j)=(1/3,1/2,2/3)_j.
3. I(18,ℓ(0,log 2,·),s,t)=59/36; S(18,r,N−r,s,t)=1; and 59/36≠1.
4. For every j, r_j/N_j=(1/2,1/6,5/6)_j.
5. 3−6(1/3)=1, 1−6(1/2)=−2, 5−6(2/3)=1, 1−2+1=0, and −1+0+1=0.
6. [(3·4/(1/3)−3·3/(2/3))+(1·3/(1/2)−5·2/(1/2))+
   (5·4/(2/3)−1·3/(1/3))]/18=59/36;
   (6/18)(4−3)+(6/18)(3−2)+(6/18)(4−3)=1; and 59/36≠1.
7. 59/36−1=23/36 and 23/36≠0.

## SAP.P001f.T97

For every finite type E (with decidable equality), every natural n>0, and then
every three functions n_t,n_c,q:E→ℝ, assume ∀x n_t(x)>0, ∀x n_c(x)>0, and
∀x 0<q(x)<1. Then

  [∀s,t:E→ℝ, I(n,q,s,t)=S(n,n_t,n_c,s,t)]
  iff [∀x, q(x)=n_t(x)/(n_t(x)+n_c(x))].

The outcome-sum quantifiers lie inside the left side of the equivalence.
There is no integer-count premise, no relation n=∑(n_t+n_c), and no raw-unit
sample. E is allowed to be empty; the assertion also covers nonempty E.

## SAP.P001f.T98

For every probability space Ω, measurable space E, and sequences X_i:Ω→E,
D_i:Ω→ℝ, first assume IIDμ((X_i,D_i)). For every p:E→ℝ assume
CM(μ,X_0,D_0,p), ∀i∀ω D_i(ω)∈{0,1}, and ∃ε>0 ∀i∀ω
ε<p(X_i(ω))<1−ε. Conclude the conjunction:

* CM(μ,X_0,D_0/p(X_0),1) and CM(μ,X_0,(1−D_0)/(1−p(X_0)),1).
* Eμ[D_0/p(X_0)]=1 and Eμ[(1−D_0)/(1−p(X_0))]=1.
* For every natural n>0, Eμ[n⁻¹∑_{i<n}D_i/p(X_i)]=1 and
  Eμ[n⁻¹∑_{i<n}(1−D_i)/(1−p(X_i))]=1.
* Eμ[1/p(X_0)]>1 and Eμ[1/(1−p(X_0))]>1.

## SAP.P001f.T99

A closed finite-law conjunction. On Fin 2 use w=(3/4,1/4), D=(0,1), X≡0,
and (Y₀,Y₁)≡(0,1). It asserts w_i≥0 for every i, ∑w_i=1,
FP(D=0)=3/4, FP(D=1)=1/4, finite CI of (Y₀,Y₁) and D given X,
FEM_w(D,X,0)=1/4, 1/8<1/4<1−1/8, and 1/4<3/8<1.
It further asserts FM_w((1/4)(1−0))=1/4, FEM_w(1,D,1)=1,
FM_w((1/4)(1−0))≠FEM_w(1−0,D,1), and
FM_w((1/4)·1)/FM_w(1/4)=FEM_w(1,D,1).

## SAP.P001f.T100

For every probability space Ω, measurable space E, measurable X:Ω→E and
measurable Y₀,Y₁,D:Ω→ℝ, assume Δ=Y₁−Y₀ is integrable, D∈{0,1} a.e.,
and 0<Pμ(D=1)<1. Next, for every p:E→ℝ assume CM(μ,X,D,p) and
CIμ((Y₀,Y₁),D | X). Define P=Pμ(D=1), W=Eμ[p(X)Δ], and
A=EM(μ,D,Δ,1). Then Eμ[p(X)]=P, P>0, W=Eμ[DΔ], W=P A,
A=W/Eμ[p(X)], and (W=A iff P=1 or A=0).
No uniform overlap or separate integrability of Y₀ and Y₁ is assumed.
Although P=1 is included in the last algebraic equivalence, the hypotheses
already impose P<1.

## SAP.P001f.T101

For every type Ω and every A,B⊆Ω, A\B={s:s∈A and s∉B} and A\B=A∩Bᶜ.
There are no measure, finiteness, or nonemptiness assumptions.

## SAP.P001f.T102

A conjunction of the negation of the following universal assertion and an
independent estimator identity.

The negated assertion (`PDAWellDefined`) quantifies, in order, over every
probability space Ω, every natural K, every measurable X:Ω→ℝ^K and Y:Ω→ℝ
with each coordinate X_j and Y integrable; then over f:ℝ^K→ℝ and
q:ℝ^K×ℝ→ℝ with RD(law(X),f) and RD(law(X,Y),q); then over m₀,m₁:ℝ^K→ℝ
with CM(μ,X,Y,m₀) and CM(μ,X,Y,m₁); then over k∈Fin K. It assumes
both t↦m_i(x with x_k+t) are differentiable at zero for **every x with f(x)>0**.
Writing xbar_j=Eμ[X_j], it concludes that there exists a single real a which
is the derivative at zero of both t↦m_i(xbar with xbar_k+t). T102 asserts that
this universal assertion is false. It does not merely negate equality of two
totalized derivative values: it negates the universal existence of a common
actual derivative. The density values and CM versions are arbitrary subject
to their predicates; no positivity of f at xbar is assumed.

Separately, for every type Ω, K∈ℕ, sequence X_i:Ω→ℝ^K, estimator family
mhat:ℕ→Ω→(ℝ^K→ℝ), natural n>0, ω∈Ω, and k∈Fin K, assume the
coordinate path of mhat(n,ω) at the sample-mean vector is differentiable at zero.
Then samplePDA X mhat n ω k equals ∂_k mhat(n,ω) at that vector. This is an
unfolding of `samplePDA`; no sampling or measurability assumptions occur.

## SAP.P001f.T103

The negation of this universal maximizer assertion: for every natural n>0 and
every y:Fin n→ℝ with ∀i y_i>0, there exists θ:Fin 7→ℝ satisfying
θ₀≥0, θ₁≥0, θ₀+θ₁≤1, θ₃>0, θ₅>0, θ₆>0, and for every valid θ′,
∏_i h_{θ′}(y_i)≤∏_i h_θ(y_i).

Here h_θ(y)=θ₀g(θ₂,θ₃,y)+θ₁l(θ₄,θ₅,y)+(1−θ₀−θ₁)e(θ₆,y),
g(m,s,y)=exp(−(y−m)²/(2s²))/(s√(2π)),
l(m,s,y)=g(m,s,log y)/y for y>0 and zero otherwise, and
e(r,y)=r exp(−r y) for y≥0 and zero otherwise. θ₂ and θ₄ are unrestricted.
The actual theorem therefore says some positive, nonempty sample has no
global likelihood maximizer in this parameter set.

## SAP.P001f.T104

The negation of the following universal equivalence. For every t,c:ℕ→ℝ,
assume ∀k t_k≥0, ∀k c_k≥0, Summable t, Summable c, ∑t>0, ∑c>0, and
∑t+∑c=1. Then

  {k:t_k>0}={k:c_k>0}
  iff ∃ε>0 ∀k with t_k+c_k>0,
       ε<t_k/(t_k+c_k)<1−ε.

t and c are joint cell masses. Neither side asserts equality of topological
closures of supports. Ratios are tested only in cells of positive total mass.

## SAP.P001f.T106

For every probability space Ω, the following two universal assertions hold.

1. For every pair of μ-integrable real functions X,Y and every a,b,c∈ℝ,
   Eμ[aX+bY+c]=aEμ[X]+bEμ[Y]+c.
2. For every X∈L²(μ) and every a,c∈ℝ: Var(X)=Eμ[X²]−Eμ[X]²;
   Var(X+c)=Var(X); Var(aX)=a²Var(X);
   √Var(X+c)=√Var(X); √Var(aX)=|a|√Var(X).
   If Var(X)>0, then for every ε>0,
   Pμ(ε√Var(X)≤|X−Eμ[X]|)≤1/ε².

## SAP.P001f.T107

For every probability space Ω, every measurable space E, and every pair of
functions X:Ω→E and Y:Ω→ℝ, assume Y is integrable. For every m:E→ℝ,
CM(μ,X,Y,m) implies Eμ[Y]=Eμ[m(X)]. Measurability of X is not an explicit
premise; the definition of CM still requires all its integral identities.

## SAP.P001f.T108

For every probability space Ω and every sequence X_i:Ω→ℝ, assume IIDμ(X_i)
and integrability of X_0. For every natural n>0, the sample mean has expectation
Eμ[X_0]. If X_0∈L²(μ), its variance is Var(X_0)/n. Further, if Var(X_0)>0,
then for every ε>0,
Pμ(ε≤|n⁻¹∑_{i<n}X_i−Eμ[X_0]|)≤Var(X_0)/(ε² n).
The second-moment and positive-variance assumptions are nested implications,
not assumptions for the expectation equality.

## SAP.P001f.T109

The conjunction of these assertions:

1. For every real a,b with a≤b, every f:ℝ→ℝ continuous on [a,b], and every
   ε>0, some real polynomial p satisfies ∀x∈[a,b], |f(x)−p(x)|<ε.
2. For every probability space Ω and X,Y:Ω→ℝ, assume X measurable and
   Y∈L²(μ). For every a,b∈ℝ, assume X∈[a,b] a.e. and either:
   (a) some f is RD(law(X),f) with {x:f(x)>0}=[a,b], or
   (b) range(X) is countable and for **every real x**,
       Pμ(X=x)>0 iff x∈[a,b].
   Then for every m:ℝ→ℝ with CM(μ,X,Y,m) and continuous on [a,b]:
   (i) there exists a sequence p_J of polynomials with natDegree(p_J)≤J
   for every J, each minimizing Eμ[(Y−q(X))²] over all q of natDegree≤J;
   and (ii) for **every** such degree-bounded minimizing sequence and every
   ε>0, there exists J such that **every** J′≥J satisfies
   Eμ[(m(X)−p_{J′}(X))²]<ε.

There is no explicit a≤b premise in (2), but its probability and support premises
rule out an empty interval. The discrete branch uses actual atoms, not closure
of the set of atoms. Minimizers are supplied by an existence conclusion, not
assumed for the entire assertion.

## SAP.P001f.T110

For every natural n>0 and every Y:Fin n→Bool, let k be the number of indices
with Y_i=true and a=k/n. Then a∈[0,1], a=n⁻¹∑_i1_{Y_i=true}, and for
every t∈[0,1], (1−t)^(n−k)t^k≤(1−a)^(n−k)a^k, with equality iff t=a.
Here n−k is natural subtraction; the definition of k ensures k≤n, so it is
the actual failure count. Endpoint cases use the usual empty-product rule 0⁰=1.
Separately, for every t∈[0,1], (1−t)t²≤(1−2/3)(2/3)², with equality iff t=2/3.

## SAP.P001f.T111

A conjunction of three universally quantified identification statements and
two fixed-sample arithmetic equalities:

1. MCAR: for every probability space and measurable integrable Y, measurable
   R with R∈{0,1} a.e., Pμ(R=0)>0, Pμ(R=1)>0, and IndepFun Y R μ,
   Eμ[Y]=EM(μ,R,Y*,1).
2. Discrete MAR: for every probability space, every countable measurable E
   with measurable singletons, measurable X:Ω→E, measurable integrable Y,
   and measurable binary-a.e. R with both marginal arms positive; for every p
   with CM(μ,X,R,p), ∃ε>0 p(X)>ε a.e., and CIμ(Y,R | X); for every m with
   CM(μ restricted to {R=1},X,Y*,m) **and** Integrable(m∘X,μ), conclude
   CM(μ,X,Y,m), Summable(x↦m(x)Pμ(X=x)), and
   Eμ[Y]=∑'_x m(x)Pμ(X=x).
3. Vector MAR: for every probability space, K∈ℕ, measurable X:Ω→ℝ^K,
   measurable integrable Y, measurable binary-a.e. R with both marginal arms
   positive; for every p,m:ℝ^K→ℝ, assume CM(μ,X,R,p), ∃ε>0 p(X)>ε a.e.,
   CIμ(Y,R | X), CM(μ restricted to {R=1},X,Y*,m), and
   Integrable(m∘X,μ). Conclude CM(μ,X,Y,m) and Eμ[Y]=Eμ[m(X)].
4. For the six units Y*=(1,−99,1,0,1,−99), R=(1,0,1,1,1,0),
   X=(0,0,0,0,1,1) valued in Fin 2, the respondent estimator
   ∑Y*_i R_i/∑R_i is 3/4 and the poststratified estimator
   ∑_{t∈Fin 2}[(∑_{X_i=t}Y*_iR_i)/(∑_{X_i=t}R_i)]·#{i:X_i=t}/6
   is 7/9. Both cells have respondents and the total respondent count is four.

## SAP.P001f.T112

For every probability space, K∈ℕ, measurable X:Ω→ℝ^K, and measurable
Y,R:Ω→ℝ, assume R∈{0,1} a.e. and both marginal response arms have positive
probability. For every p with hp:CM(μ,X,R,p), assume CIμ(Y,R | X).
For every ε>0 with p(X)>ε a.e., conclude
CIμ(R,X | p(X)), CIμ(Y,R | p(X)), CM(μ,p∘X,R,id), and
∃η>0 id(p(X))>η a.e. No outcome integrability is assumed.

## SAP.P001f.T113

For every probability space, K∈ℕ, measurable X:Ω→ℝ^K, measurable integrable
Y, and measurable R with R∈{0,1} a.e. and both marginal response arms
positive, take every p with CM(μ,X,R,p), ∃ε>0 p(X)>ε a.e., and
CIμ(Y,R | X). For every m,q:ℝ^K→ℝ assume m and q measurable and
m(X) μ-integrable. Assume further the disjunction:

* CM(μ restricted to {R=1},X,Y*,m) and ∃η>0 η<q(X)<1−η a.e.; or
* q(X)=p(X) μ-a.e.

Then Eμ[Y]=Eμ[m(X)+R(Y*−m(X))/q(X)]. The integrability premise on m(X)
is outside the disjunction and applies in both branches. The q-overlap premise
is inside the first branch. No estimator sequence or convergence statement occurs.

## SAP.P001f.T114

For every probability space and measurable Y₀,Y₁,D:Ω→ℝ, then every a,b∈ℝ,
assume Y₀,Y₁∈[a,b] a.e., D∈{0,1} a.e., P₀=Pμ(D=0)>0, and
P₁=Pμ(D=1)>0. Define Y=Y₁D+Y₀(1−D),
L=EM(μ,D,Y,1)P₁+aP₀−[EM(μ,D,Y,0)P₀+bP₁], and
U=EM(μ,D,Y,1)P₁+bP₀−[EM(μ,D,Y,0)P₀+aP₁]. Then
Eμ[Y₁−Y₀]∈[L,U], U−L=b−a, and for every c∈[L,U] there exist measurable
Z₀,Z₁:Ω→ℝ, each a.e. in [a,b], such that the law of
(Z₁D+Z₀(1−D),D) equals the law of (Y,D), and Eμ[Z₁−Z₀]=c.
The same underlying space, measure, and treatment variable are retained.

Separately, for the fixed six outcomes Y=(1,1,1,0,1,0) and
D=(1,0,1,1,1,0), the averages of
Y D+0(1−D)−Y(1−D)−1D and
Y D+1(1−D)−Y(1−D)−0D are −2/6 and 4/6 respectively.
