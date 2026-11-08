# Blind reading

This file was saved before opening claims.json or record.json. The sources for this reading are SAP/P001e/Defs.lean, its six imported Parts, and SAP/P001e/Challenge.lean and Challenge/Part1.lean. The Challenge exports exactly the nineteen theorems T77–T95. Each theorem asserts the corresponding defined proposition; its proof is a stub. No assertion about a Solution or a Comparator is used here.

## Common meanings, expanded to Mathlib

All real-valued random variables below live on a specified measurable space (Ω, F). Unless explicitly qualified otherwise, μ is a probability measure. Real spaces and finite products of reals carry their Borel/product measurable structures; Bool has the discrete sigma algebra. A statement about almost every ω refers to μ unless another measure is written. Fin n is the set {0,…,n−1}; a vector Fin K → ℝ is an element of ℝ^K. Natural parameters can be zero unless explicitly required positive.

* Pμ(A) means (μ A).toReal. For probability or restricted probability measures this is the ordinary, finite probability. Mathlib's ENNReal.toReal sends infinity to zero; no infinite measure is being interpreted as a probability in the asserted probability formulas.
* Eμ[Z] means the real Bochner integral ∫ Z dμ. Mathlib defines this as zero when Z is not integrable. Integrable means almost-everywhere strong measurability and finite integral of the norm. Bounded measurable real functions on these finite measures are integrable.
* CM(μ,X,Z,m), the exact abbreviation used here for IsConditionalMean, means: (i) m is measurable on the codomain of X, (ii) Z is μ-integrable, (iii) m∘X is μ-integrable, and (iv) for EVERY measurable set A in the codomain of X, ∫_{X∈A} Z dμ = ∫_{X∈A} m(X) dμ. The definition does not independently assert measurability of X; the theorems using it supply that separately. μ need not be normalized in CM.
* CIμ(Y,Z|X), for CondIndependent, means: for EVERY measurable A in the codomain of Y and EVERY measurable B in the codomain of Z, Eμ[1_{Y∈A,Z∈B}|σ(X)] = Eμ[1_{Y∈A}|σ(X)] Eμ[1_{Z∈B}|σ(X)] almost everywhere. Here σ(X) is exactly MeasurableSpace.comap X of the codomain sigma algebra. Conditional expectations are Mathlib condExp; their exceptional zero convention applies for a non-sub-sigma algebra, a non-sigma-finite trimmed measure, or a nonintegrable function. In these statements X is measurable, μ is finite, and the indicators of the supplied measurable variables are bounded, so those exceptional conventions do not supply the independence. For a process ω↦(t↦Y(t,ω)), its codomain is ℝ^ℝ with the product sigma algebra; coordinatewise measurability is supplied.
* IIDμ(Z_i) means each Z_i is measurable, the full countable family of generated sigma algebras is independent (finite intersection probabilities factor for every finite set of distinct indices), and for every i the pushforward laws of Z_i and Z_0 coincide. The last clause is Mathlib IdentDistrib, which additionally includes almost-everywhere measurability of both functions.
* Av(Z,n)=n⁻¹∑_{i=0}^{n−1}Z_i, with Av(Z,0)=0 under real division by zero. The unbiasedness statements use n>0; the convergence statements take n→∞, so the value at zero is irrelevant.
* Z_n→c in probability means: for every real ε>0, the sequence Pμ{ε≤dist(Z_n,c)} tends to 0 along n→∞. The real-valued distance is absolute difference.
* A cell mean Cμ(X,Z;x) is ∫_{X=x}Z dμ / Pμ(X=x). At a null cell this is the totalized quotient 0, not a conditional-mean version. Where these means have substantive conditional interpretations below, cell masses are explicitly positive or terms from null covariate cells are suppressed.
* Recorded outcome rcd(y,r)=yr−99(1−r); completion cmp(y*,r,c)=y*r+c(1−r). For binary r, recorded values are y on response and −99 on nonresponse, and completion is y on response and c on nonresponse. Realized outcome obs(y0,y1,d)=y1d+y0(1−d).
* L(y,d;a,b)=yd+a(1−d)−y(1−d)−bd and U(y,d;a,b)=yd+b(1−d)−y(1−d)−ad.
* A finite weighted probability is P_w(A)=∑_i 1_A(i)w_i, and E_w Z=∑_i w_iZ_i. Finite conditional independence of Y,Z given X means: for every x, every y, every z, if P_w(X=x)>0, then P_w(X=x,Y=y,Z=z)P_w(X=x)=P_w(X=x,Y=y)P_w(X=x,Z=z). The only instantiated weights are six positive weights 1/6, so these are genuine probabilities. Finite conditional means divide the corresponding weighted outcome sum by P_w(X=x,D=d).
* Infinite sums ∑' use Mathlib tsum, which is zero for a nonsummable real family. For the standardized dose means, countability and the integrability/identification hypotheses are intended to give absolutely summable cell-mean contributions; this requires checking, rather than assuming that every tsum converges.
* Matrix inverse is Mathlib's nonsingular inverse (zero when the determinant is not a unit). The OLS examples explicitly assert a unit determinant; over ℝ this means a nonzero determinant. Matrix-vector multiplication and all sums are finite.

Relevant Mathlib source definitions inspected: MeasureTheory/Function/ConditionalExpectation/Basic.lean (condExp); MeasureTheory/Integral/Bochner/Basic.lean (integral); MeasureTheory/Function/L1Space/Integrable.lean; Probability/Independence/Basic.lean and Independence/Kernel/IndepFun.lean (iIndepFun); Probability/IdentDistrib.lean; MeasureTheory/MeasurableSpace/Basic.lean (comap); MeasureTheory/MeasurableSpace/Instances.lean (Bool); MeasureTheory/Measure/Map.lean (pushforward); LinearAlgebra/Matrix/NonsingularInverse.lean (inverse). All pushforward maps in the assertions are measurable, so map's exceptional nonmeasurable convention is inactive.

## T77 — SAP.P001e.T77

For every type Ω and natural τ, every subset Θ⊆ℝ^τ, every Y:Ω→ℝ, then every natural K, every X:Ω→ℝ^K, and every g:ℝ×ℝ^K×ℝ^τ→ℝ satisfying g(y,x,t)≥0 for ALL y,x and ALL t∈Θ, there exists L:Ω→(Θ→ℝ≥0) such that for EVERY ω∈Ω and EVERY t∈Θ, the real coercion of L(ω,t) equals g(Y(ω),X(ω),t). ℝ≥0 is the subtype of finite nonnegative reals, not extended reals. There are no sigma algebras, measurability, density normalization, sampling assumptions, or Gaussian functions in this assertion. Θ and Ω are permitted to be empty. L is chosen after all the preceding data and the nonnegativity condition.

## T78 — SAP.P001e.T78

For every n,K∈ℕ with n>0, every real n×(K+1) matrix X, every Y∈ℝ^n, and every b*∈ℝ^{K+1} satisfying Q(b*)≤Q(b) for EVERY b∈ℝ^{K+1} and Q(b*)>0, set Q(b)=∑_i(Y_i−(Xb)_i)^2 and s*=sqrt(Q(b*)/n). Then s*>0, (s*)²=Q(b*)/n, and for EVERY b∈ℝ^{K+1} and EVERY real s>0,

−n log s−(n/2)log(2π)−Q(b)/(2s²) ≤ −n log s*−(n/2)log(2π)−Q(b*)/(2(s*)²).

No column of X is required to be an intercept, and no rank assumption is imposed. This is a deterministic log-likelihood optimization statement; b* is supplied as a minimizer. It asserts neither zero-mean residuals nor a centered residual variance formula.

## T79 — SAP.P001e.T79

For every n,K∈ℕ with n>0, every list X_0,…,X_{n−1}∈ℝ^K, and every list of real probability measures ν_0,…,ν_{n−1}, the measure Fhat=n⁻¹∑_i(ν_i⊗δ_{X_i}) on ℝ×ℝ^K is a probability measure. In addition, for EVERY real y and EVERY x∈ℝ^K,

P_Fhat{(z,v):z≤y and v_k≤x_k for EVERY k}=n⁻¹∑_i 1_{X_{ik}≤x_k for EVERY k}P_{ν_i}((−∞,y]).

No density, common parameter, optimization, population identity, or statistical functional is assumed or asserted. K may be zero, in which case the coordinate comparison is legitimately automatic and the assertion is the CDF of a mixture on ℝ.

## T80 — SAP.P001e.T80

The conjunction of the following universal result and a fixed numerical calculation:

For every Ω with a measurable structure, every probability measure μ, every measurable Y,R:Ω→ℝ, then every a,b∈ℝ such that Y(ω)∈[a,b] for EVERY ω and R(ω)∈{0,1} for EVERY ω, put L=Eμ[cmp(rcd(Y,R),R,a)] and U=Eμ[cmp(rcd(Y,R),R,b)]. Then L≤EμY≤U. Moreover, for EVERY real c∈[L,U] there exists a measurable Y':Ω→ℝ such that Y'(ω)∈[a,b] for EVERY ω, EμY'=c, and rcd(Y'(ω),R(ω))=rcd(Y(ω),R(ω)) for EVERY ω. The same Ω, μ and R are used for all these completions. No strict response positivity or a<b is assumed. Existence of μ and the pointwise bounds implies a≤b.

For the fixed six recorded values (1,−99,1,0,1,−99) with responses (1,0,1,1,1,0), the mean completion at 0 is 1/2 and at 1 is 5/6.

## T81 — SAP.P001e.T81

A hypothesis-free assertion about six indices 0,…,5. Scores are s=(.33,.14,.73,.35,.78,.70); respondent candidates are {0,2,3,4}. The eight exact distances to nonrespondents 1 and 5 are respectively (.19,.21,.59,.64) for respondents ordered (0,3,2,4), and (.37,.03,.35,.08) for respondents ordered (0,2,3,4). Respondent 0 is the UNIQUE nearest candidate to index 1; respondent 2 is the UNIQUE nearest candidate to index 5. For every respondent k≠0, |s_3−s_1|≤|s_k−s_1|, and |s_3−s_1|−|s_0−s_1|=.02. Donor map (0,0,2,3,4,2) applied to data (2,0,3,10,12,0) produces exactly (2,2,3,10,12,3), whose arithmetic mean is 16/3. There is no estimation or asymptotic assertion.

## T82 — SAP.P001e.T82

For EVERY pair of measurable types Ω,E, every probability measure μ on Ω, every measurable X:Ω→E and R:Ω→Bool with 0<Pμ(R=true)<1, there exist p:E→ℝ, THEN κ:E→Measures(Bool), such that all the following hold jointly:

1. p is measurable and 0≤p(x)≤1 for EVERY x, including x outside the range of X.
2. Each κ(x) is a probability measure. For every measurable B⊆Bool, x↦κ(x)(B) is measurable.
3. For EVERY measurable A⊆E and EVERY measurable B⊆Bool, μ{X∈A,R∈B}=∫_A κ(x)(B) d(μ.map X)(x), as an extended nonnegative integral.
4. For EVERY x, P_{κ(x)}{true}=p(x) and E_{κ(x)}[1_{true}]=p(x).
5. CM(μ,X,1_{R=true},p).
6. For EVERY m:E→ℝ, if CM(μ,X,1_{R=true},m), then m(X)=p(X) μ-almost everywhere.
7. For EVERY real q, q∉[0,1] iff q>1 or q<0.

Separately, unconditionally, for EVERY real q, q>0 or q<1. This last disjunction is a tautology; it is not the characterization of invalid predictions (that is clause 7). No regularity assumption on E beyond a measurable structure is made. The nondegenerate response marginal is a genuine explicit hypothesis of the universal component.

## T83 — SAP.P001e.T83

For every measurable Ω,E, probability μ, measurable X:Ω→E, then measurable Y,R:Ω→ℝ with Y integrable, R(ω)∈{0,1} for EVERY ω, then p:E→ℝ with CM(μ,X,R,p), such that there exists ε>0 with ε<p(X(ω)) for EVERY ω, and with CIμ(Y,R|X), conclude

EμY=Eμ[rcd(Y,R)R/p(X)].

The right integrand is exactly YR/p(X) under binary R. p is supplied, measurable through CM, and is only constrained above by 1 almost everywhere through its conditional-mean property, not by a separate pointwise hypothesis. There is no IID assumption or sample estimator. The positivity requirement is uniform and pointwise.

## T84 — SAP.P001e.T84

A hypothesis-free assertion about cells x_j=(−1,0,1), sizes N_j=4, respondent counts r=(2,3,2), and respondent outcome sums S=(3/4,3/2,3/4). Define q(a,b,x)=exp(a+bx)/(1+exp(a+bx)) and l(a,b)=∑_j[r_j log q(a,b,x_j)+(N_j−r_j)log(1−q(a,b,x_j))]. For EVERY real a,b, l(a,b)≤l(log(7/5),0), and equality holds iff a=log(7/5) and b=0. For EVERY j, 0<r_j<N_j and q(log(7/5),0,x_j)=7/12. Further,

(1/12)∑_j S_j/q(log(7/5),0,x_j)=3/7;
(1/12)∑_j N_jS_j/r_j=5/12;
3/7≠5/12; and 3/7−5/12=1/84.

All logistic probabilities lie strictly between 0 and 1 for finite a,b, so the logarithms are ordinary logarithms here.

## T85 — SAP.P001e.T85

For every finite type E with decidable equality, every N,r,q:E→ℝ, then every real n>0, such that N_x>0, r_x>0, q_x>0 for EVERY x and ∑_xN_x=n, define I(S)=n⁻¹∑_x S_x/q_x, P(S)=n⁻¹∑_x N_xS_x/r_x, W=n⁻¹∑_x r_x/q_x, and H(S)=I(S)/W. Then:

1. For EVERY S:E→ℝ, I(S)−P(S)=n⁻¹∑_xS_x(1/q_x−N_x/r_x).
2. [For EVERY S:E→ℝ, I(S)=P(S)] iff [for EVERY x, q_x=r_x/N_x].
3. If q_x=r_x/N_x for EVERY x, then W=1 and for EVERY S:E→ℝ, both I(S)=P(S) and H(S)=P(S).

S is quantified after N,r,q,n and their hypotheses. There is no requirement that N or r be integers, r≤N, or q≤1. These are algebraic identities extending the sample-cell setting. E cannot actually be empty under ∑N=n>0. All displayed denominators are positive, including W.

## T86 — SAP.P001e.T86

For every measurable Ω,E, probability μ, measurable X:Ω→E, then measurable R:Ω→ℝ with R(ω)∈{0,1} for EVERY ω, then p:E→ℝ such that CM(μ,X,R,p) and there exists ε>0 with ε<p(X(ω))≤1 for EVERY ω, conclude jointly:

CM(μ,X,R/p(X),constant 1), Eμ[R/p(X)]=1, Eμ[1/p(X)]≥1, and Eμ[1/p(X)]=1 iff p(X)=1 μ-almost everywhere.

Thus the conditional and unconditional mean-one conclusions concern R/p, while the lower bound concerns 1/p. The bounds give integrability of both weight variables. No sample-size, fitted propensity, consistency, or efficiency assertion occurs.

## T87 — SAP.P001e.T87

The conjunction of two independently universally quantified assertions (their supplied functions m need not be the same):

Stable component: for every measurable Ω,E, probability μ, measurable X, then measurable Y,R:Ω→ℝ with Y integrable, R binary at EVERY ω, Pμ(R=1)>0 AND Pμ(R=0)>0, then m:E→ℝ such that CM(μ restricted to {R=1},X,Y,m), conclude both CM(μ restricted to {R=1},X,rcd(Y,R),m) and CM(μ,(R,X),rcd(Y,R),h), where h(r,x)=m(x) if r=1 and h(r,x)=−99 otherwise. No MAR hypothesis appears in this component. m∘X is assumed integrable only on respondents here.

MAR component: for every measurable Ω,E, probability μ, measurable X, then measurable Y,R with Y integrable and R pointwise binary, then p,m:E→ℝ such that CM(μ,X,R,p), there exists ε>0 with ε<p(X(ω)) for EVERY ω, CIμ(Y,R|X), CM(μ restricted to {R=1},X,rcd(Y,R),m), AND m∘X is μ-integrable on the full population, conclude CM(μ,X,Y,m). The conditional mean is supplied under a restriction of μ, rather than a normalized respondent measure; the defining equalities and integrability have the same interpretation when its mass is positive. No regression estimator is constructed.

## T88 — SAP.P001e.T88

For every measurable Ω and probability μ, every three sequences Y0_i,Y1_i,D_i:Ω→ℝ with EACH coordinate measurable, then every a,b∈ℝ with a≤b, such that for EVERY i, almost every ω satisfies Y0_i,Y1_i∈[a,b] and D_i∈{0,1}; 0<Pμ(D_0=1)<1; and the sequence (Y_i,D_i) is IID, where Y_i=obs(Y0_i,Y1_i,D_i), put

L_i=L(Y_i,D_i;a,b), U_i=U(Y_i,D_i;a,b), p=Pμ(D_0=1), m_1=Cμ(D_0,Y_0;1), m_0=Cμ(D_0,Y_0;0),
ℓ=m_1p+a(1−p)−[m_0(1−p)+bp],
u=m_1p+b(1−p)−[m_0(1−p)+ap].

Here Y_0 denotes the OBSERVED outcome at index zero in these endpoint formulas, not the control-potential sequence Y0. Conclude all of: EμL_0=ℓ; EμU_0=u; u−ℓ=b−a; Eμ[Y1_0−Y0_0]∈[ℓ,u]; for EVERY real t∈[ℓ,u], there exist measurable A0,A1:Ω→ℝ such that almost everywhere they both lie in [a,b] and obs(A0,A1,D_0)=Y_0, and Eμ[A1−A0]=t; for EVERY natural n>0, EμAv(L,n)=ℓ and EμAv(U,n)=u; and Av(L,n)→ℓ and Av(U,n)→u in probability as n→∞.

Only observables, not the latent triple, are required IID. The compatible alternatives A0,A1 are for index zero, not new full IID latent sequences. Sharpness is with respect to the same observable variables and measure, up to null sets. Both conditioning masses in m_0,m_1 are nonzero.

## T89 — SAP.P001e.T89

A hypothesis-free assertion about the uniform law on six states. The arrays, in index order 0,…,5, are Y=(0,1,1,0,1,1), X=(0,0,1,0,1,1), D=(0,0,0,1,1,1), X0=(0,0,1,0,0,1), X1=(0,1,1,0,1,1). It asserts all of:

* (Y,Y,X1,X0) and D are conditionally independent given the constant unit-valued variable (equivalently independent); P(D=1)=1/2.
* For EVERY state i, obs(X0_i,X1_i,D_i)=X_i. E(Y−Y)=0.
* (Y,Y) and D are NOT conditionally independent given X.
* P(Y=1,X=1,D=1)=1/3; P(X=0)=P(X=1)=1/2.
* For EVERY x∈{0,1} and EVERY d∈{0,1}, P(X=x,D=d)>0.
* E[Y|X=0,D=1]=0, E[Y|X=1,D=1]=1, E[Y|X=0,D=0]=1/2, E[Y|X=1,D=0]=1.
* The X-standardized observed contrast ∑_{x=0,1}(E[Y|X=x,D=1]−E[Y|X=x,D=0])P(X=x) equals −1/4.

The latent potential outcomes are both the same fixed Y. The independence assertions use the cross-multiplied finite definition expanded above. Only the listed probability values are conclusions, though the arrays determine the entire joint law.

## T90 — SAP.P001e.T90

A hypothesis-free equality and inequalities. Let λ be Lebesgue measure restricted to [0,1] and let s(d)=1 if d=1/2 and 0 otherwise. The pushforward of λ by d↦(0,d,0) equals its pushforward by d↦(s(d),d,0). Further s(1/2)−s(0)=1, s(1/2)−s(1/4)=1, and 0≠1 as real numbers. Thus the two explicitly defined observable triple laws coincide, while their deterministic dose-response differences differ at the named pairs. The assertion itself does not package these as a general identification predicate, and does not separately assert process independence or moments; these can be inspected directly in this deterministic construction.

## T91 — SAP.P001e.T91

For every measurable Ω,E with E countable and EACH singleton in E measurable, every probability μ, measurable X:Ω→E and D:Ω→ℝ, then a dose-indexed family Y:ℝ→Ω→ℝ such that for EVERY real t the coordinate Y(t,·) is measurable AND integrable, and such that the diagonal observed outcome O(ω)=Y(D(ω),ω) is measurable AND integrable; assume CIμ((t↦Y(t,ω)),D|X). Then for EVERY supplied pair d,d'∈ℝ such that for EVERY x with Pμ(X=x)>0, BOTH Pμ(X=x,D=d)>0 AND Pμ(X=x,D=d')>0, conclude:

* For EVERY such positive-mass x, Cμ(X,Y(d);x)=Cμ((X,D),O;(x,d)) AND Cμ(X,Y(d');x)=Cμ((X,D),O;(x,d')).
* EμY(d)=M(d) AND EμY(d')=M(d'), where M(t)=∑'_x [Cμ((X,D),O;(x,t))Pμ(X=x)] on cells with Pμ(X=x)>0, with summand 0 on all other cells.
* Eμ[Y(d')−Y(d)]=M(d')−M(d).

The two doses may coincide; there are also instances with distinct doses. Continuous/non-atomic assignment at a target dose fails the positive-mass hypothesis. Integrability is imposed at ALL real doses, not merely the two target doses. There is no continuity hypothesis. The unused PositiveMassDose definition is a related one-dose proposition; it is not itself a separate Challenge theorem.

## T92 — SAP.P001e.T92

A hypothesis-free assertion. Use six-unit vectors Y=(2,5,3,10,2,0), D=(1,0,1,1,1,0), X1=(1,8,10,3,5,7), X2=(7,2,3,1,2,0), design rows (1,D_i,X1_i,X2_i), and β=(13563,6178,−759,−1778)/2437. The Gram matrix XᵀX has a unit/nonzero determinant, and (XᵀX)⁻¹XᵀY=β. Predictions use f(x1,x2,d)=β_0+β_1d+β_2x1+β_3x2.

For the MODIFIED vector x1'=(1,8,9,3,5,7), define A(x1')=six-unit average of [Y_i−f(x1'_i,X2_i,0)] on treated units and [f(x1'_i,X2_i,1)−Y_i] on controls, and B(x1')=six-unit average of f(x1'_i,X2_i,1)−f(x1'_i,X2_i,0). Then A(x1')=12103/4874, B(x1')=6178/2437, A(x1')−B(x1')=−253/4874, and A(x1')≠B(x1'). The coefficient is fit on X1 with entry 10, then evaluated with entry 9; no refitting on the modified covariate is asserted.

## T93 — SAP.P001e.T93

Conjunction of a universal algebraic result and fixed OLS calculations. Universally, for EVERY natural n>0, EVERY Y,D,g∈ℝ^n, and EVERY β∈ℝ, such that D_i∈{0,1} for EVERY i, ∑_i(Y_i−g_i−βD_i)=0, AND ∑_iD_i(Y_i−g_i−βD_i)=0, conclude

n⁻¹∑_i[D_i(Y_i−g_i)+(1−D_i)(g_i+β−Y_i)]=β,
and n⁻¹∑_i[(g_i+β)−g_i]=β.

Separately, for the fixed original design and outcomes in T92: det(XᵀX) is a unit; its inverse-form OLS coefficient is β above; A(X1)=β_1; B(X1)=β_1; and β_1=6178/2437. The residual normal equations are hypotheses of the universal part. No universal derivation of them from a minimizer or population causal assertion is included.

## T94 — SAP.P001e.T94

Conjunction of two independently universally quantified assertions.

Population component: for EVERY measurable Ω and probability μ, EVERY K,τ∈ℕ, EVERY measurable X:Ω→ℝ^K and D:Ω→ℝ, EVERY integrable Y0,Y1:Ω→ℝ, with D binary at EVERY ω, then p:ℝ^K→ℝ such that CM(μ,X,D,p), there exists ε>0 with ε<p(X(ω))<1−ε for EVERY ω, and CIμ((Y0,Y1),D|X); then EVERY real function g(y,d,x,θ) with θ∈ℝ^τ fixed such that for EACH d∈{0,1}, for almost EVERY ω the function y↦yg(y,d,X(ω),θ) is Lebesgue-integrable; put m(d,x)=∫_ℝ yg(y,d,x,θ)dy. Assume CM(μ,(D,X),obs(Y0,Y1,D),m) and, for EACH d∈{0,1}, μ-integrability of ω↦m(d,X(ω)). Conclude EμY0=Eμm(0,X) AND EμY1=Eμm(1,X).

No nonnegativity or normalization of g is asserted or required: its integrated values are supplied as a correct observed conditional mean. Integrability of Y0,Y1 gives almost-everywhere measurability, not an additional explicit everywhere-measurability hypothesis. The conditional-mean definition supplies measurability of (d,x)↦m(d,x).

Estimator component: for EVERY n,K,τ∈ℕ with n>0, EVERY g of the same signature, EVERY real d, EVERY list X_i∈ℝ^K, EVERY θ∈ℝ^τ, THEN EVERY free x∈ℝ^K, assuming y↦yg(y,d,X_i,θ) Lebesgue-integrable for EVERY i and y↦yg(y,d,x,θ) Lebesgue-integrable, conclude fittedPotentialAverage(g,d,X,θ)=n⁻¹∑_i∫yg(y,d,X_i,θ)dy, AND n⁻¹∑_i m(d,x)=m(d,x). The first equality unfolds a definition; the second averages the same free-covariate value n times. It does NOT assert these two expressions are equal or exhibit an example where they differ. θ is not assumed to be an MLE.

## T95 — SAP.P001e.T95

A hypothesis-free fixed-data assertion using the scores and distances of T81 and the outcome/treatment data of T92. It includes ALL eight distance identities and ALL hot-deck nearest/second-nearest/gap assertions from T81. It also asserts UNIQUE nearest controls for each treated index: 0→1, 2→5, 3→1, 4→5, with control candidate set {1,5}. The donor map for all six units is (1,0,5,1,5,2). Keep a unit's own observed outcome in its observed arm and fill its other arm with the donor's observed outcome. The resulting control column is (5,5,0,5,0,0), the treatment column is (2,2,3,10,2,3), their means are respectively 15/6 and 22/6, and the mean difference is 7/6. Donors for control units 1 and 5 are exactly the hot-deck nearest-treated assertions already included, so both directions are certified.
