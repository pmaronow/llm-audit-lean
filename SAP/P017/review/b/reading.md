# Blind reading of SAP.P017

This reading was saved before opening `claims.json` or `record.json`. It reads the theorem types, including all the `T*Statement` definitions, rather than treating the Challenge docstrings as their types. Every theorem is universally quantified over the parameters below unless described as a conjunction about a fixed example. All limits of sequences are as the natural sample size tends to infinity. Finite-sample assertions explicitly qualified by positive sample size do not include size zero.

## Definitions and Mathlib semantics

An unspecified population is a measurable space Ω, a probability measure G on Ω, and a real function τ. Its mean is μ = ∫τ dG. The population hypotheses in the theorems require τ measurable and integrable. Write S = supp(G ◦ τ⁻¹), L = inf S and U = sup S in the extended real line, and C = max(0, min(U − μ, μ − L)), viewed in [0,∞]. The infimum and supremum are taken after embedding S in the extended reals. The support is the closed measure support: x belongs precisely when every neighborhood of x has positive pushforward measure. It is not the pointwise range of τ.

For a real d, K_d(x) = min(μ+d, max(μ−d,x)); when the center needs to be explicit write K_{μ,d}. For C in [0,∞], K_C means this finite clip using C.toReal if C is finite, and means the identity function if C = ∞. `inside μ C x` means ofReal(|x−μ|) ≤ C, equivalently |x−μ| ≤ C with an extended bound. Strict-inside means the corresponding strict inequality. The real-radius residual is R_{μ,d}(x) = x − K_{μ,d}(x).

A weight w is admissible if it is measurable, nonnegative at **every** point, integrable under G, has ∫w dG > 0, and wτ is integrable. Its weighted mean is (∫wτ dG)/(∫w dG). Write Rep(t) for the existence of such a weight with weighted mean t. No restriction to weights depending only on τ is imposed. The predicate E(t) means (L < t < U) or ((t=L or t=U) and G(τ=t)>0).

For a measure P and a set A, `pr P A` is (P A).toReal. For probabilities this is the ordinary probability, including for all the events used below. Without measurability this is the measure's outer value. For general infinite measures this conversion sends ∞ to zero; all probabilistic conclusions here have probability hypotheses, except the identically zero error assertion in T8, which needs none.

Write q_n = √n. `LittleOp P V a` means: for every real η>0, P(|V_n|>ηa_n) → 0. It does not itself assume a_n>0. `BoundedInProbability P V` means: for every ε>0 there is a real M>0 such that eventually P(|V_n|>M)<ε. `Consistent P hat μ` means: for every b>0, P(|hat_n−μ|>b)→0. `RootNNormal P hat μ` means there exists a **positive variance** v in the nonnegative reals such that q_n(hat_n−μ) converges in distribution to N(0,v). Mathlib's convergence-in-distribution structure includes almost-everywhere measurability of every scaled random variable (also at n=0), almost-everywhere measurability of the limit variable, and weak convergence of the pushforward probability measures. It does not require exact measurability of hat itself.

`NormalRemainder P hat Z ε μ v` means, for every integer n≥1: Z_n is measurable with law N(0,v); ε_n is measurable with ε_n² integrable; and q_n(hat_n−μ)=Z_n+ε_n almost surely. It asserts no independence. `SmallRemainderMS` means q_n E[ε_n²]→0. `SmallMSE P V` means n E[V_n²]→0. These are limits of Mathlib's real Bochner integrals. Such integrals are defined as zero for a nonintegrable function; the reading does not silently insert an integrability hypothesis into these predicates.

Let Φ(x)=N(0,1)((−∞,x]). The definition T_n(c,σ) called `normalTail` is the **Lebesgue integral**

    2 ∫_{x>c} x² [√n/(σ√(2π))] exp(−x²n/(2σ²)) dx.

The normal distribution's second parameter in Mathlib is variance, not standard deviation. At variance zero it is a point mass. Integrable on real-valued functions means almost-everywhere strongly measurable with finite absolute integral. Pushforward is the usual pushforward for almost-everywhere measurable functions; Mathlib has an arbitrary Dirac fallback for a non-a.e.-measurable function and nonzero measure. All population pushforwards here explicitly require τ measurable. The infinite product used below is the countable product probability measure, with its product sigma algebra. Mathlib defines it to be zero outside its probability-measure case, which is excluded by the hypotheses or supplied instances here.

The underlying Mathlib definitions were followed in `MeasureTheory/Measure/Support.lean`, `MeasureTheory/Measure/Map.lean`, `MeasureTheory/Function/ConvergenceInDistribution.lean`, `MeasureTheory/Function/L1Space/Integrable.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, `Probability/Distributions/Gaussian/Real.lean`, `Probability/ProductMeasure.lean`, `Probability/Independence/Basic.lean`, `Data/EReal/Basic.lean`, `Data/Nat/Log.lean`, and `Algebra/Order/Floor/Defs.lean`.

## Explicit examples shared by the statements

`fairPair(a,b)` puts mass 1/2 at a and 1/2 at b. A sequence s is always an arbitrary point of the whole infinite product space, unless an almost-sure qualification is stated. Thus pointwise formulas also cover sample coordinates outside a distribution's support.

**IPW example.** A population observation is (A,(B,D)) in ℝ³, with independent A uniform on (0,1), B uniform on {−1,1}, and D uniform on {0,1}. The population measure is `ipwPopulation`. Potential outcomes are Y₀=B, Y₁=B+A, effect τ=A, observation O=(D,DY₁+(1−D)Y₀), and summand X=2DO₂−2(1−D)O₂. Let Xbar_n=n⁻¹∑_{i<n}X(s_i). Define B_b(n) to be the event that B_i=b and D_i=0 for every i<n; it places no condition on A_i. The empirical observed measure is n⁻¹∑_{i<n}δ_{O(s_i)} for n≥1. In the source its normalization is extended-real inversion; its zero-size value is zero because the empty sum is zero. Sample means use real division, with zero-size value zero.

**Normal example.** A population observation is (X,B) with independent X∼N(0,1) and B uniform on {−1,1}; Y₀=0, Y₁=B and τ=B. Let m_n=n⁻¹∑X_i, h_n=m_n+1/n, D_n=m_n−K_{0,1}(h_n), Z_n=q_n m_n, and ε_n=1/q_n, constant in the sample.

**Rare-outlier example.** A population observation is (X,(V,(T,D))), with independent X∼N(0,1), V uniform on [0,1), D uniform on {0,1}, and T of law (1/4)δ_{−1}+(1/4)δ_1+(1/4)Lebesgue|[−1,1]. This last measure has total mass one. Y₀=0, Y₁=T, τ=T; the observation map, though not used as a hypothesis in T12/T13, is (X,V,D,DY₁+(1−D)Y₀). Let m_n be the mean of the X coordinates, V_n=fract(∑_{i<n}V_i), J_n=1 if V_n<p_n and 0 otherwise, b_n=K_{0,1/2}(m_n), h_n=b_n+10J_n, and e_n=q_n(b_n−m_n+10J_n). Fractional part is x−floor(x). Write ℓ_n=1/(1+floor(log₂ n)) for n≥1, with source value ℓ_0=1. The floor logarithm is `Nat.log 2 n`.

## SAP.P017.T1

This is a conjunction about the fixed IPW example, without an outer conditional hypothesis. The effect is measurable and integrable, μ=1/2, S=[0,1], C=1/2>0, and both endpoints have mass zero. Almost surely 0<τ<1 and |X|<4. E[X]=1/2, E[X²]=14/3, and E[(X−1/2)²]=53/12. For every n≥1, E[Xbar_n]=1/2 and E[(Xbar_n−1/2)²]=53/(12n). The sequence q_n(Xbar_n−1/2) converges in distribution to N(0,53/12).

For **every** measurable pointwise nonnegative integrable w with positive integral, the weighted mean of τ is strictly between zero and one. This clause does not explicitly assume integrability of wτ. For every n≥1 the two disjoint events B_{−1}(n) and B_1(n) each have probability (1/4)^n>0. For every sample in the first event, every X_i=2, Xbar_n=2, the clip is 1, the empirical observed law is δ_(0,−1), and the clipped value is not representable. For every sample in the second, every X_i=−2, Xbar_n=−2, the clip is 0, the empirical law is δ_(0,1), and the clipped value is not representable.

## SAP.P017.T2

For every measurable Ω, probability G, and measurable integrable τ, all the following hold. For every real t, Rep(t) iff G(τ=t)>0 or both G(τ<t)>0 and G(τ>t)>0. For every real t with L<t<U, Rep(t). For every real t equal to L or U, Rep(t) iff G(τ=t)>0. For every t<L or t>U, not Rep(t). Finally, for every t with positive atom mass, there exists an admissible w with ∫w dG=1 and weighted mean t. No formula, size bound, or other moments for this witness are asserted.

## SAP.P017.T3

Quantifier order: for every measurable population Ω, probability G, measurable integrable τ, assumption C>0, then every measurable sample space Ξ, probability P, and sequence hat_n:Ξ→ℝ with **each hat_n measurable**, the following conjunction holds:

1. For every real x, L≤K_C(x)≤U, and Rep(K_C(x)) iff E(K_C(x)).
2. For every x strictly inside, Rep(K_C(x)).
3. If C=∞, or if every real t that is a finite clipping endpoint μ±C.toReal **and** is a support endpoint L or U has positive effect atom mass, then for every real x, Rep(K_C(x)). This is an implication, not an iff asserting necessity of that condition.
4. If additionally RootNNormal(P,hat,μ), then P(ofReal(|hat_n−μ|)<C)→1 and P(Rep(K_C(hat_n)))→1.
5. For every x strictly inside, K_C(x)=x.

## SAP.P017.T4

For every measurable population Ω, probability G, measurable integrable τ, and assumption C>0:

1. There exists a real d>0 with ofReal(d)<C.
2. For every real d>0 with ofReal(d)<C, every real x has Rep(K_d(x)), |K_d(x)−μ|≤|x−μ|, and K_d(x)=x iff |x−μ|≤d. For **every** measurable space Ξ, probability P and arbitrary function hat:Ξ→ℝ (no measurability required at this point), for every real η,a>0,
   P(|hat−K_d(hat)|>ηa)≤P(|hat−μ|>d).
   If hat is measurable and max(sup supp(P◦hat⁻¹)−μ, μ−inf supp(P◦hat⁻¹))≤d, then P(hat=K_d(hat))=1. Also, for every real c>d, there exists real x with |x−μ|≤c, K_c(x)=x and K_d(x)≠x.
3. If C is finite, C.toReal/2>0 and ofReal(C.toReal/2)<C. If C=∞, every real d>0 satisfies ofReal(d)<C.
4. For every t: interior support points are representable, support endpoints are representable iff they are atoms, and points outside [L,U] are not representable, with the same quantifiers as T2.
5. The same sufficient endpoint-atom condition as in T3 implies that every real input clipped at the original radius C is representable.

## SAP.P017.T5

For the fixed normal example, the effect is measurable and integrable, μ=0, S={−1,1}, C=1. The shifted estimator h is RootNNormal about zero. The specified Z,ε give NormalRemainder with v=1, and the deterministic q_n/n is little-o in probability of 1.

For every n≥1, m_n∼N(0,1/n). For every sample,

    D_n = m_n+1        if m_n < −1−1/n,
          −1/n        if −1−1/n ≤ m_n ≤ 1−1/n,
          m_n−1       otherwise.

For every sample D_n=0 iff m_n=1; P(D_n≠0)=1; P(|m_n|>1)=2Φ(−q_n)<1, and this tail probability is ≤1/n. For every n≥2 and every sample with |m_n|≤1/2, D_n=−1/n and h_n−K_{0,1}(h_n)=0; the central event has probability at least 1−4/n, and P(|D_n|/(1/n)≥1/2)≥1−4/n. Finally nD_n+1 is little-o in probability of 1, but D_n is **not** little-o in probability of the sequence 1/n (whose source value at zero is zero).

## SAP.P017.T6

For the same normal population, measurable integrable effect, μ=0, S={−1,1}, and C=1, the specified shifted estimator, Z and ε satisfy NormalRemainder and SmallRemainderMS. For every n≥1, E[ε_n²]=1/n. At n=25, on every sample with |m_25|≤1/2, K_{0,1}(h_25)=h_25 and D_25²=1/625. The event has probability at least 21/25, hence E[D_25²]≥21/15625.

The assertions further give T_25(1,1)=E[m_25² 1_{|m_25|>1}]≤E[m_25⁶]=15/15625, so E[D_25²]−T_25(1,1)≥6/15625>0. On every central sample, −23/50≤h_25≤27/50. Both n E[(h_n−K_{0,1}(h_n))²]→0 and n E[D_n²]→0 are asserted. This statement does not separately assert RootNNormal, though its explicit construction is the same as T5.

## SAP.P017.T7

For every measurable population Ω, probability G, measurable integrable τ and C>0, then every measurable Ξ, probability P and sequence hat with RootNNormal(P,hat,μ), all of the following hold. No extra exact-measurability hypothesis on hat is imposed.

The scaled deviations q_n(hat_n−μ) are bounded in probability; hat is consistent for μ; for **every deterministic real sequence a with a_n>0 for every n including zero**, hat_n−K_C(hat_n) is little-o in probability of a. If C=∞, the error is zero for every n and every sample.

For every n and every sample inside the clipping interval, the error is zero. For every n and every pair of real numbers η,a>0, the event {|hat_n−K_C(hat_n)|>ηa} is contained in the complement of the inside event, and its probability is bounded by the probability of that complement. The latter probability tends to zero. Finally q_n(hat_n−K_C(hat_n)) is little-o in probability of 1. All these conclusions are under RootNNormal; there is no separate implication from consistency alone.

## SAP.P017.T8

This has four independently universally quantified parts.

**Finite-sample part.** For every measurable Ξ, probability P, sequences hat,Z,ε, real μ,c with c>0, nonnegative-real variance v>0, exact measurability of every hat_n, NormalRemainder(P,hat,Z,ε,μ,v), and then every n≥1, put t=μ+Z_n/q_n. The conclusions are:

1. For all real x,y, |K_{μ,c}(x)−K_{μ,c}(y)|≤|x−y| and |R_{μ,c}(x)−R_{μ,c}(y)|≤|x−y|.
2. Almost surely |R(hat_n)|≤|R(t)|+|ε_n|/q_n, and E[R(hat_n)²]≤2E[R(t)²]+2E[ε_n²]/n.
3. For every real x, R(x)²=max(|x−μ|−c,0)²≤(if |x−μ|>c then (x−μ)² else 0)≤(x−μ)⁴/c².
4. E[(t−μ)⁴]=3v²/n², and E[R(hat_n)²]≤6v²/(c²n²)+2E[ε_n²]/n.
5. Almost surely |t−K(hat_n)|≤|R(t)|+|ε_n|/q_n, and E[(t−K(hat_n))²]≤6v²/(c²n²)+2E[ε_n²]/n.
6. E[R(t)²]≤E[(t−μ)² 1_{|t−μ|>c}], and the latter integral equals T_n(c,√v).

**Limits part.** Independently, for every measurable Ξ, probability P, the same parameters and hypotheses and in addition SmallRemainderMS(P,ε), SmallMSE holds for both R(hat_n) and μ+Z_n/q_n−K_{μ,c}(hat_n).

**Triangle part.** For all real μ,c,x,y, without positivity assumptions, |x−K_{μ,c}(y)|≤|R_{μ,c}(x)|+|K_{μ,c}(x)−K_{μ,c}(y)|.

**Infinite-radius part.** For every measurable Ξ, arbitrary measure P, arbitrary sequence hat and real μ: for all real x,y, x−K_∞(x)=0 and y−K_∞(x)=y−x; and SmallMSE(P,hat_n−K_∞(hat_n)).

## SAP.P017.T9

This is the **negation of a universal implication**. The negated assertion quantifies, in this order, over measurable spaces Ω,D,Ξ (all in the base type universe), probability population G, measurable integrable real effect τ, hypothesis C>0, measurable observation O:Ω→D, probability sample law P on Ξ, a measurable map data:Ξ→(ℕ→Ω), estimator sequence hat and arbitrary maps H_n from measures on D to ℝ. Its hypotheses say, for every n≥1 and every sample s,

    hat_n(s) = H_n(n⁻¹ ∑_{i<n} δ_{O(data(s)_i)}),

and RootNNormal(P,hat,μ). Its conclusion is: for every n≥1 and every sample s, Rep(K_C(hat_n(s))). T9 says this universal implication is false. There is **no hypothesis that data has IID law G**, no separate measurability requirement on H or hat, and the failed conclusion concerns all sample points rather than almost every sample point. A counterexample must satisfy all of the explicitly listed hypotheses and fail at some positive sample size and some sample point.

## SAP.P017.T10

Three independently quantified parts:

1. For every measurable population Ω, probability G, measurable integrable τ, then measurable Ξ, probability P and measurable real hat, **assume**
   max(sup supp(P◦hat⁻¹)−μ, μ−inf supp(P◦hat⁻¹))≤C.
   Then supp(P◦hat⁻¹) is contained in the clipping interval, P(inside(hat))=1, the sets {hat=K_C(hat)} and {inside(hat)} are equal, and P(hat=K_C(hat))=1. Also, **under this same support-bound assumption**, if P(inside(hat))=0 then P(hat=K_C(hat))=0.
2. For every measurable probability population with measurable integrable τ and S=ℝ, C=∞ and K_C(x)=x for every real x.
3. For every measurable probability population with measurable integrable τ and S=[0,∞), then every measurable probability sample space with measurable hat and P(hat<0)>0: C=ofReal(μ); the support-bound assumption in part 1 fails; P(hat=K_C(hat))≤1−P(hat<0)<1.

The probability-zero implication in part 1 is not separately quantified outside its support-bound assumption.

## SAP.P017.T11

For every natural n≥1, real c>0 and real σ>0,

    T_n(c,σ) = cσ√(2/π) exp(−c²n/(2σ²))/√n
               + (2σ²/n) Φ(−c√n/σ).

Separately, for every c>0 and σ>0, nT_n(c,σ)→0 and, for every real k>0, n^k T_n(c,σ)→0. Here the power is real exponentiation on the real cast of n. There is no separate assertion identifying T_n with a truncated Gaussian moment or a standardized density integral.

## SAP.P017.T12

This is a conjunction about the fixed rare-outlier construction.

**For every sequence p with 0<p_n≤1 for n≥1 and p_n→0:** the effect is measurable and integrable, μ=0, S=[−1,1], C=1; h is RootNNormal about zero. For every n≥1:

1. V_n has uniform law on [0,1); P(J_n=1)=p_n; J_n and m_n are independent; q_n m_n∼N(0,1).
2. For every sample q_n h_n=q_n m_n+e_n. For every real δ>0, P(|e_n|>δ)≤4/n+p_n.
3. The following three sets are each exactly {J_n=1}: {h_n∉S}, {|h_n|>1}, and {h_n≠K_{0,1}(h_n)}. Thus the last event has probability p_n and P(h_n∈S)=1−p_n.
4. For every sample with J_n=0, h_n=b_n and its clipping error is zero. For every sample with J_n=1, 19/2≤h_n≤21/2, its clip is 1, and its clipping error is b_n+9.
5. (289/4)p_n≤E[(h_n−K_{0,1}(h_n))²]≤(361/4)p_n.

For every n≥4, E[e_n²]≥100(n−4)p_n. The sequences e_n and q_n(h_n−K_{0,1}(h_n)) are each little-o in probability of 1.

**The specified logarithmic sequence ℓ:** 0<ℓ_n≤1 for n≥1 and ℓ_n→0; h constructed with ℓ is RootNNormal. The same population properties μ=0,S=[−1,1],C=1 are asserted again. For every n≥1 its failure probability is ℓ_n. The exact values are ℓ_1000=1/10, ℓ_(10^12)=1/40, and ℓ_(2^k)=1/(k+1) for every natural k. For every real α>0, (2^k)^α ℓ_(2^k)→∞; there is no positive C₀ with ℓ_n≤C₀/n^α eventually. SmallRemainderMS fails for its e.

**Domination:** for every real sequence r with r_n>0 for n≥1 and r_n→0, there exists p with 0<p_n≤1 for n≥1, p_n→0, h constructed with p RootNNormal, failure probability exactly p_n for every n≥1, and p_n/r_n→∞. The statement specifies no formula for p.

**Unconditional pointwise assertions:** for every sequence p, every n≥1 and every sample, −1/2≤b_n≤1/2; if J_n=1 then 17/2≤h_n−K_{0,1}(h_n)≤19/2; if |m_n|≤1/2 and J_n=0 then e_n=0. Finally there is no real C₀>0 with ℓ_n≤C₀·2Φ(−q_n) eventually.

## SAP.P017.T13

Three independently quantified parts:

1. For every measurable probability population with measurable integrable τ and C>0, then every measurable probability sample space, sequence hat with every hat_n measurable and RootNNormal about μ: for every n the inside event equals {hat_n=K_C(hat_n)}, and P(inside(hat_n))→1.
2. For every p with 0<p_n≤1 for n≥1 and p_n→0, the rare-outlier population has measurable integrable effect, μ=0, S=[−1,1], C=1; its h is RootNNormal; for every n≥1 both P(|h_n|>1)=p_n and P(h_n≠K_{0,1}(h_n))=p_n.
3. For every measurable probability space, measurable real functions t,u, reals μ,c,σ with c,σ>0, natural n≥1, and hypothesis t∼N(μ,σ²/n),
   P(|t+u−μ|>c)≤2Φ(−c√n/(2σ))+P(|u|>c/2).
   No independence or moment hypothesis on u is imposed.

## SAP.P017.T14

For every measurable population Ω, probability G, measurable integrable τ with C>0, then every measurable Ξ, probability P and sequence hat with RootNNormal(P,hat,μ), q_n(hat_n−K_C(hat_n)) is little-o in probability of 1. Explicitly, for every real η>0, P(|q_n(hat_n−K_C(hat_n))|>η)→0. There is no separate exact-measurability hypothesis on hat and no finite-radius hypothesis.

## SAP.P017.T15

For every measurable population Ω, probability G, measurable integrable τ with C>0, then every measurable Ξ, probability P, sequences hat,Z,ε with every hat_n measurable, positive variance v, NormalRemainder(P,hat,Z,ε,μ,v), and SmallRemainderMS(P,ε), one has SmallMSE(P,hat_n−K_C(hat_n)). Explicitly n E[(hat_n−K_C(hat_n))²]→0. There is no independence hypothesis and no additional RootNNormal hypothesis. C=∞ is permitted; C=0 is excluded.

## SAP.P017.T16

For every measurable population Ω, probability G, measurable integrable τ (with **no positivity requirement on C**), then every measurable Ξ, probability P and sequence hat with RootNNormal(P,hat,μ), the sequence q_n(K_C(hat_n)−μ) is bounded in probability. Also, for every natural n and every sample ω,

    |K_C(hat_n(ω))−μ| ≤ |hat_n(ω)−μ|.

Both zero and infinite radius are included. There is no separate exact-measurability hypothesis on hat.
