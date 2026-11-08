# Blind reading of the Challenge statements

This reading was saved before opening `claims.json` or `record.json`. It uses only the Challenge, its SAP definitions, and the Mathlib definitions they invoke. All theorem names below are in namespace `SAP.P027b`. The Challenge contains T14 through T24, with no other theorem stubs.

## Shared mathematical vocabulary

A `Design U Ω` consists of finite types U (population units) and Ω (sample outcomes), nonnegative real weights p(ω) with sum 1, and a Boolean selection rule. Write I_k(ω) = 1 when k is selected and 0 otherwise. The definitions are

* E_D f = Σ_ω p(ω) f(ω), π_k = E_D I_k, π_kl = E_D(I_k I_l), and Δ_kl = π_kl − π_k π_l.
* `Positive D` means π_k > 0 for every k. It does not require π_kl > 0 for distinct k,l, nor positive weight on every sample outcome.
* Var_D f = E_D[(f − E_D f)²]. All design expectations and variances are finite sums.
* T_y(ω) = Σ_k I_k(ω)y_k/π_k is `htTotal`; `htMean` is T_y/|U|.
* H_y(ω) = Σ_{k,l: π_kl>0} I_k I_l (Δ_kl/π_kl)(y_k/π_k)(y_l/π_l) is `htVarianceEstimator`. The sum includes diagonal terms and uses **ordered** pairs.
* Z_D = {(k,l): k ≠ l and π_kl = 0}. A_D(y) = Σ_{Z_D} y_k y_l is `biasA`.
* For real exponent arrays a_kl,b_kl, A*(y;a,b) = Σ_{Z_D} (|y_k|^{a_kl}/a_kl + |y_l|^{b_kl}/b_kl), and its sample correction B*(ω) = Σ_{Z_D} [I_k |y_k|^{a_kl}/(a_kl π_k) + I_l |y_l|^{b_kl}/(b_kl π_l)]. `conservativeEstimator` is H+B*.
* B₂(ω) = Σ_{Z_D}[I_k y_k²/(2π_k)+I_l y_l²/(2π_l)], `c2Estimator` C₂ = H+B₂, and `quadraticA` is Σ_{Z_D}(y_k²+y_l²)/2.
* `wrEstimator D y m` is Σ_k I_k[y_k/(π_k/m)−T_y]² / [|U|² m(m−1)]. Here the annotated subtraction in the denominator is real subtraction.

Mathlib's `Real.HolderConjugate a b` means a>0, b>0 and a⁻¹+b⁻¹=1; these imply a,b>1. Powers with a real exponent mean `Real.rpow`. They are applied to nonnegative absolute values in the corrections. Finite sums are over all elements of their finite types.

`outcomeE μ f` is the real Bochner integral ∫f dμ, distinct from E_D. Mathlib defines a nonintegrable Bochner integral to be zero, so the integrability clauses matter. `NoiseMoments μ ε σ²` explicitly requires, for every coordinate k, integrability and mean zero of ε_k, and, for every k,l, integrability of ε_k ε_l with expectation σ² when k=l and zero otherwise. In particular it supplies integrable squares. Each use of this predicate in the theorem statements also has a probability measure hypothesis.

The special two-stratum design D_M has U = {0,…,M−1}×{0,1}, Ω = {0,…,M−1}², and assigns probability 1/M² to (i,j). It selects precisely (i,0) and (j,1). It is defined only with an explicit proof M>0. Its stratum means are μ_0=α and μ_1=−α. `stratumOutcomes α ε ξ (k,s)` is μ_s+ε_(k,s)(ξ), using the **stratum** coordinate for μ. For an arbitrary fixed population y,

* v_s = Σ_k y_(k,s)²/M − (Σ_k y_(k,s)/M)² is `stratumVariance` (divisor M).
* CS_y(i,j) = (y_(i,0)−y_(j,1))²/4 is `collapsedEstimator`.
* The variance of the two means defined by `stratumMeansVariance` has divisor 2−1: Σ_s[μ_s−(μ_0+μ_1)/2]²/(2−1).
* h(α) = α²/(α²+1/2) is `heterogeneity`; c(α) = α²/(α²+1) is `pairCorrelationFormula`.

Mathlib limits below are filter limits in the usual real topology. `atTop` on natural numbers means M→∞; `𝓝[<] 1` means q→1 from below. `StrictMonoOn f [0,1)` means that, for every q₁,q₂ in that interval with q₁<q₂, f(q₁)<f(q₂).

## T14

There are no hypotheses or free parameters. Use D₅ and the explicit population y_α(k,s)=μ_s+d_k, where d=(3/2,−3/2,1/2,−1/2,0). Define V(α)=Var_D₅(htMean y_α), H(α)=E_D₅[H_yα/100], C(α)=E_D₅[C₂_yα/100], and CS(α)=E_D₅ CS_yα. The theorem is the conjunction

* V(0)=V(2)=1/2;
* H(0)=2/5, C(0)=4/5, CS(0)=1/2; H(2)=2, C(2)=4, CS(2)=9/2;
* C(0)−V(0)=3/10, CS(0)−V(0)=0, C(2)−V(2)=7/2, CS(2)−V(2)=4;
* CS(0)−V(0)<C(0)−V(0) and C(2)−V(2)<CS(2)−V(2).

It asserts these concrete fixed-population calculations; it contains no outcome-model expectation or large-M clause.

## T15

This is a conjunction of three universally quantified assertions.

1. For every natural M, then every proof M≥2, then every population y on U_M, use D_M and N=2M. For **every** sample (i,j), with u=y_(i,0), v=y_(j,1), the mean estimate is (u+v)/2, H/N²=(M−1)(u²+v²)/(4M), C₂/N²=(M−1)(u²+v²)/(2M), C₂/N²=2H/N², and CS=(u−v)²/4. Also Var_D_M(htMean y)=(v_0+v_1)/4.
2. For every type Ξ, measurable structure on Ξ, measure μ and probability measure instance, then every M≥2, real α and error family ε indexed by U_M, **if** `NoiseMoments μ ε 1`, define y(ξ)=μ_s+ε_(k,s)(ξ). Set V=∫Var_D_M(htMean y(ξ))dμ, H=∫E_D_M(H_y(ξ)/N²)dμ, C=∫E_D_M(C₂_y(ξ)/N²)dμ, CS=∫E_D_M CS_y(ξ)dμ. Set BH=H−V, BC=C−V, BS=CS−V. The conclusion is every one of:
   * V=(M−1)/(2M), H=(M−1)(1+α²)/(2M), C=(M−1)(1+α²)/M, CS=α²+1/2;
   * BH=(M−1)α²/(2M), BC=(M−1)(1+2α²)/(2M), BS=α²+1/(2M), and BH,BC,BS≥0;
   * BC−BS=(M−2−2α²)/(2M)=1/2−(1+α²)/M;
   * BC<BS iff M<2(1+α²); BC=BS iff M=2(1+α²); BS<BC iff 2(1+α²)<M;
   * BC<BS iff (M−2)/(M−1)<h(α);
   * C/CS=(1−1/M)(1+α²)/(1/2+α²)=(1−1/M)(2−h(α)); C−CS=1/2−(1+α²)/M.
3. For every fixed real α, as natural M→∞, (1−1/M)(2−h(α))→2−h(α), 1/2−(1+α²)/M→1/2, and (M−1)/(2M)→1/2. These functions are defined on all naturals by Lean's real division, including M=0; the limits depend only on the tail M≥2.

The error assumptions assert uncorrelated unit-variance errors with integrable products, rather than a Gaussian distribution or full independence.

## T16

There are no hypotheses. On Ω={0,1}³, `pairLaw` assigns each point weight 1/8. Its selection rule always says false; only its probability weights are used here. Let S,E,E′ be −1 for coordinate 0 and +1 for coordinate 1 in the first, second and third coordinates respectively. Thus these are three independent fair signs by the explicit product law. Let Y=S/2+E, Y′=S/2+E′.

The theorem asserts that S,E,E′ each have mean zero and design variance 1; E_D(SE)=E_D(SE′)=E_D(EE′)=0; Y,Y′ each have mean zero and variance 5/4; Cov_D(Y,Y′)=E_D(YY′)−E_D(Y)E_D(Y′)=1/4; Corr_D(Y,Y′)=Cov_D(Y,Y′)/sqrt(Var_D(Y)Var_D(Y′))=1/5; h(1/2)=1/3; and h(1/2)−Corr_D(Y,Y′)=2/15. It makes no Gaussian-law assertion or assertion about the divisor used for the variance of the two means.

## T17

There are four groups of assertions, joined by conjunction.

1. For every type Ξ, measurable space, probability measure μ, then every real α and functions S,ε,ε′:Ξ→R, assume `PairMoments`: S∈{1,−1} almost surely; ∫S=0 and S is integrable; ε and ε′ are integrable and have mean zero; ε² and ε′² are integrable with integral 1; Sε, Sε′ and εε′ are integrable with integral zero. Put Y=αS+ε, Y′=αS+ε′. Then ∫Y=∫Y′=0; ∫Y²=∫Y′²=α²+1; ∫YY′=α²; and ∫YY′/sqrt((∫Y²)(∫Y′²))=c(α).
2. For every real α: (μ_0+μ_1)/2=0; the divisor-1 variance of μ_0,μ_1 is 2α²; h(α)=that variance/(that variance+1)=2α²/(2α²+1); h(α)−c(α)=α²/[(α²+1)(2α²+1)]≥0; h(α)=c(α) iff α=0; c(α)=h(α)/(2−h(α)); and α²=h(α)/[2(1−h(α))].
3. q↦q/(2−q) is strictly increasing on [0,1), and tends to 1 as q→1 from below.
4. Exact conversions at decimal real arguments: .33/(2−.33)=33/167; .50/(2−.50)=1/3; .67/(2−.67)=67/133; .82/(2−.82)=41/59; .90/(2−.90)=9/11; .99/(2−.99)=99/101.

## T18

For every natural M, then every proof M>0, use D_M. The theorem asserts, for all units k, π_k=1/M; for every ordered pair k,l, π_kl is 1/M if k=l, zero if k≠l are in the same stratum, and 1/M² if they are in different strata; Δ_kl is (1/M)(1−1/M) if k=l, −1/M² for distinct units in the same stratum, and zero otherwise. Also every indicator has design variance (1/M)(1−1/M). Conjoined to this universal claim is the concrete identity π_(0,0),(0,0)=1/2 for D₂. No equality involving `stratumOutcomes` is a conjunct of this theorem.

## T19: vocabulary and full assertion

For natural r>0 and m≥2 there are q=2r groups G={0,…,r−1}×{0,1}, each containing m units. The population type is the disjoint union K=Σ_g Fin m, of size N=mq. A sample is a single group g, selected with probability p_g=1/(6r) for g's second coordinate 0 (low) and 5/(6r) for coordinate 1 (high). Every one of its m units is selected. This is `phaseOriginal`; `phaseGrouped` is the underlying single-group draw. `phaseSize` x_k equals 2 in low groups and 10 in high groups.

For any population z write Y_g=Σ_j z_(g,j), Q_g=Σ_j z_(g,j)² and Q=Σ_k z_k². Define V(z)=Var_D(htMean z), H(z)=E_D[H_z/N²], C(z)=E_D[C₂_z/N²], W(z)=E_D wrEstimator(D,z,m). Let R(q)=5(q−1)/(9q−5), c(q)=6q/(9q−5), and T(z)=C(z)−(1+R(q))H(z). `populationSquareNorm` is the Euclidean sum of squares, without normalization.

The centered space consists of vectors whose total is zero. The within space consists of vectors with zero sum in **each** group. The signal space is span{x−6}. The low space consists of vectors constant within each group, zero in high groups, and with total zero; the high space is the reverse. `phaseComponentSpace` labels these four spaces by 0,1,2,3. A `PhaseDecomposition r m z` consists of four vectors w,s,l,h with w in the within space, s=b(x−6) for some real b, l constant on groups and supported on low groups with sum of group constants zero, h analogously supported on high groups, and z=w+s+l+h. The two descriptions of low/high total zero are equivalent because m>0.

For errors on a probability space, `GaussianNoise μ ε σ²` explicitly asserts every ε_k is almost everywhere measurable, has pushforward law `gaussianReal 0 σ².toNNReal`, and that the whole family (over population units) is mutually independent (`iIndepFun`). Mathlib's Gaussian has variance parameter, not standard deviation; zero variance gives a Dirac mass. In every use of this predicate here σ²>0, so the real-to-nonnegative truncation changes nothing. `chiSquaredLaw d` is exactly the pushforward of the product of d standard N(0,1) laws under the sum of coordinate squares. In particular d=0 gives the genuine point mass at zero. Mathlib's pushforward is the usual pushforward for almost everywhere measurable maps. `ENNReal.toReal` is used for probabilities; those values are finite because μ is a probability measure. Finite-dimensional submodule `finrank` is ordinary real dimension, rather than its infinite-rank default convention.

For x,β,ε define raw outcomes βx_k+ε_k and centered outcomes z_k=βx_k+ε_k−(Σ_l(βx_l+ε_l))/N.

T19 is the conjunction of **eight** propositions:

1. **PeriodicFixed.** For every r,m, proof r>0, proof m≥2, and fixed vector z, if Σ_k z_k=0, then
   V(z)=Σ_g(Y_g²/p_g)/N²; H(z)=V(z)−Σ_gY_g²/N²; Σ_gY_g²/N²≥0; C(z)−H(z)=(N−m)Q/N²; and W(z)=[mΣ_g(Q_g/p_g)−N²V(z)]/[N²(m−1)].

2. **PeriodicModel.** For every type Ξ, measurable space and probability measure μ, then r,m,r>0,m≥2, reals β,σ², assume σ²≥0; then for every error family ε indexed by K assume `NoiseMoments μ ε σ²`. Use the centered outcomes above with x=phaseSize. Let L=16m²β²+mσ²(1−1/q), B(ξ)=Σ_gY_g(ξ)²/N²; let V,H,C,W now denote the μ expectations of the corresponding design quantities, and let Q denote ∫Σ_k z_k². Then
   * ∫Y_g²=L for every group g;
   * ∫B=16β²/q+σ²(N−m)/N²;
   * V=(9q/5)∫B, H=V−∫B, and **if V>0** then (H−V)/V=−5/(9q);
   * Q=16Nβ²+(N−1)σ², C=H+(N−m)Q/N², and W=(9/5)σ²/m;
   * for every real ρ, if σ²=900(1−ρ²) and β²=900ρ²(N−1)/(16N), then (V,H,C,W)=`periodicModelPredictions N m ρ` and Q=900(N−1).

   The prediction function first sets q=N/m, σ²=900(1−ρ²), β²=900ρ²(N−1)/(16N), B=16β²/q+σ²(N−m)/N², and returns V=(9q/5)B, H=V−B, C=H+(N−m)[16Nβ²+(N−1)σ²]/N², W=(9/5)σ²/m. It is a total algebraic function, but the model identity uses only positive m,N.

3. **PeriodicDiagonalization.** For every r,m,r>0,m≥2,z, assume Σz=0. Then the centered, within, signal, low and high spaces have dimensions N−1, N−q, 1, r−1, r−1 respectively. For all distinct indices i,j in Fin 4 and all vectors v,w, membership in the respective component spaces implies Σ_k v_kw_k=0. There exists a PhaseDecomposition of z; any two such decompositions have equal four component vectors. For **every** decomposition (w,s,l,h),
   T(z)=(N−m)/N² [||w||²+c(q)(||h||²−||l||²)]
   and T(z)≥−(N−m)c(q)||l||²/N².
   For every real β, T(β(x−6)+z)=T(z). Dimension subtractions are natural-number subtraction, but the parameter bounds make all operands ordered as displayed.

4. **PeriodicGaussian.** For every Ξ, measurable space, probability μ, then r,m,r>0,m≥2 and reals β,σ², assume σ²>0; then for every ε assume `GaussianNoise μ ε σ²`. Use centered z, a=(N−m)σ²/N², c=c(q). There exist **on this same probability space** three mutually independent functions X_0,X_1,X_2:Ξ→R whose pushforward laws are respectively χ²_(N−q), χ²_(r−1), χ²_(r−1), and such that almost surely T(z)=a[X_0+c(X_1−X_2)]. Also ∫T(z)=a(N−q)>0. No separate measurability clause for the existential X is written, beyond their laws and independence; the input errors do have explicit almost everywhere measurability.

5. **PeriodicTail.** For every Ξ, measurable space, probability μ, then naturals r,m,K with r>0,m≥2,K>0, reals β,σ²,ℓ with σ²>0 and ℓ>0, then every error family ε indexed first by i∈Fin K and then by population units, assume `GaussianNoise μ (ε i) σ²` for **each i**. No independence across different populations i is required. Let a=(N−m)σ²/N², c=c(q), k=ac, d=r−1 as a real, Tbar=Σ_i T(z_i)/K, J=floor(ℓ/(4k))∈Z, h=ceil(d/2)∈Z. Then
   μ{Tbar≤−ℓ} ≤ exp(−ℓ/(4k))·2^{d/2},
   and if h<J then exp(−ℓ/(4k))·2^{d/2} ≤ 2^{−(J−h)}.

6. **PeriodicRows.** For every Ξ, measurable space, probability μ, then row∈Fin 4, K>0, real β, and family of K populations of errors on the corresponding row's units, assume each population's errors satisfy `GaussianNoise` with variance 17.91. Set Hbar=Σ_iH(z_i)/K and Cbar=Σ_iC(z_i)/K. The probability of the simultaneous closed rounding event |Hbar−Hrow|≤.005 and |Cbar−Crow|≤.005 is ≤2^{−erow}, with rows:

   | row | r | m | Hrow | Crow | Trow | erow |
   | --- | --- | --- | --- | --- | --- | --- |
   | 0 | 2 | 30 | 1412.15 | 2029.28 | −102561/1550 | 189 |
   | 1 | 10 | 30 | 1564.34 | 2396.58 | −29703/1750 | 213 |
   | 2 | 2 | 60 | 1430.59 | 2032.07 | −281297/3100 | 522 |
   | 3 | 10 | 60 | 1562.38 | 2395.86 | −25671/1750 | 371 |

7. **PeriodicNumerics.** With no hypotheses, the predictions at (N,m,ρ)=(120,30,.99),(600,30,.99),(240,60,.99),(1200,60,.99) respectively equal
   (1575.3366,1356.53985,2025.91485,1.0746),
   (1586.1366,1542.07725,2395.65225,1.0746),
   (1581.5493,1361.889675,2034.077175,.5373),
   (1586.9493,1542.867375,2397.154875,.5373).
   Also −5/(9·4)=−5/36 and −5/(9·20)=−1/36. For every row, Crow−(1+R(2r))Hrow=Trow; .005(2+R(2r)) equals 77/6200 when r=2 and 89/7000 otherwise; and 2^{−erow}≤10^{−56},10^{−64},10^{−157},10^{−111} respectively. These are exact rational decimal identities/inequalities.

8. **PeriodicRowCertificates.** For every row let R=R(2r), N=m(2r), ℓ=−Trow−.005(2+R), k=(N−m)17.91 c(2r)/N². Then ℓ>0, k>0; R=15/31 if r=2 and 19/35 otherwise; floor(ℓ/(4k))−ceil((r−1)/2)=erow as integers; and **for every pair of real numbers H,C**, if |H−Hrow|≤.005 and |C−Crow|≤.005, then C−(1+R)H≤−ℓ.

No deterministic impossibility is asserted for the four rounding events. The tail and row bounds are uniform over any positive number K of generated populations and any real signal coefficient β.

## T20

This is a conjunction of a universal statement and an existential example.

For every pair of finite types U,Ω and design D, assume π_k>0 for every k; **then for every** y:U→R, E_D H_y=Var_D T_y+A_D(y). Also, **if** either all y_k≥0 or all y_k≤0, then A_D(y)≥0 and E_D H_y−Var_D T_y≥0.

Separately, there exist a design D on U=Fin 3, Ω=Fin 2 and two populations yPos,yNeg such that all first-order inclusion probabilities are positive, A_D(yPos)>0, A_D(yNeg)<0, E_D H_yPos−Var_D T_yPos>0, and E_D H_yNeg−Var_D T_yNeg<0. The existential does not require yPos to have nonnegative coordinates, despite its name. The definitions provide an available design selecting {0,1} or {2} each with probability 1/2, and populations (1,1,1) and (1,1,−1/4), but the statement does not demand those particular witnesses.

## T21

For every finite U,Ω and design D, assume π_k>0 for every k. Then for every population y and real exponent arrays a,b, assume, **on every ordered pair in Z_D only**, a_kl>0, b_kl>0, and 1/a_kl+1/b_kl=1. The conclusion is the conjunction A_D(y)≤A*(y;a,b), −A_D(y)≤A*(y;a,b), E_D B*=A*, E_D(H+B*)=Var_D T_y+A_D(y)+A*, and Var_D T_y≤E_D(H+B*). Exponents on pairs outside Z_D are unconstrained and unused.

## T22

For every finite U,Ω and design D assume π_k>0 for every k; then for every population y and exponent arrays a,b assume conjugacy on every ordered pair in Z_D as for T21. Next assume, for every such pair, |y_k|^{a_kl}=|y_l|^{b_kl}; next assume, for every such pair, −y_k y_l=|y_k||y_l| (equivalently y_k y_l≤0). Then E_D(H+B*)=Var_D T_y. These are sufficient conditions, not a claim of necessity.

## T23

For every finite U,Ω and design D assume π_k>0 for every k; then for every population y, the function C₂_y:Ω→R equals the function H_y+B*(y;2,2):Ω→R (extensional equality at all sample outcomes), and Var_D T_y≤E_D C₂_y.

## T24

For every finite U,Ω and design D assume π_k>0 for every k; then for every population y and **every sample outcome ω, including zero-weight outcomes**, (H+B*(2,2))(ω)=C₂(ω). Next, for every pair of **constant** real numbers a,b, if a,b>0 and 1/a+1/b=1, then C₂(ω)≤(H+B*(a,b))(ω). This compares all positive constant conjugate pairs; it does not compare arbitrary pair-dependent arrays. The first equality gives an attained minimum at (2,2).

## Mathlib definitions checked

The semantic endpoints checked in Mathlib are `Basic/Real/ConjExponents.lean` (positive real Hölder conjugacy), `Analysis/SpecialFunctions/Pow/Real.lean` (real powers), `MeasureTheory/Integral/Bochner/Basic.lean` (Bochner integral), `Probability/Independence/Basic.lean` (mutual independence of the generated sigma algebras), `Probability/Distributions/Gaussian/Real.lean` (normal law, variance parameter), `MeasureTheory/Measure/Map.lean` (pushforward including its nonmeasurable fallback), `LinearAlgebra/Dimension/Finrank.lean` (finite dimension), `Order/Monotone/Defs.lean` (strict monotonicity), and `Basic/ENNReal/Basic.lean` (real conversion of extended nonnegative numbers). All paths are under the permitted Mathlib source root. No Challenge definition uses an integral of absolute continuity, a limsup, or an infinite index sum.
