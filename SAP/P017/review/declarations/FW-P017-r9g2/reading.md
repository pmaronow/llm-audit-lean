# Blind reading of P017-T6 through P017-T10

This file was saved before reading `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. The Challenge docstrings, all source declarations in the five closures, and the generated auxiliary declarations were inspected. This is a reading of the statements, not a fidelity decision.

## Conventions unfolded to Mathlib

All real integrals below are Mathlib Bochner integrals; a set integral is an integral for the restricted measure. `pr P A` is `(P A).toReal`. `sqrtN n` is `Real.sqrt (n : ℝ)`. All limits use the natural-number filter `atTop` and the real neighborhood filter at zero.

For a measurable real effect τ on a population probability space (Ω,G), write μ = ∫τ dG and S = support(G.map τ). Mathlib measure support consists of the real points whose every neighborhood has positive measure; it is closed. Let L = inf{x as an extended real : x ∈ S} and U = sup{x as an extended real : x ∈ S}, both in EReal. The radius c is `toENNReal (min (U-μ) (μ-L))`. Thus it is the smaller distance from μ to the support bounds, allowing +∞. `EReal.toENNReal` preserves nonnegative values and +∞ and sends negative values and -∞ to zero. For finite real d, define C(μ,d,x) = min(μ+d,max(μ-d,x)). For an extended nonnegative radius c, C∞(μ,c,x) = x if c=+∞, and C(μ,c.toReal,x) otherwise. Being inside means `ENNReal.ofReal |x-μ| ≤ c`, equivalent at finite radius to |x-μ|≤c.toReal, and automatic at infinite radius. The finite-radius residual is R(μ,d,x)=x-C(μ,d,x).

For a probability measure P, `LittleOp P V a` means: for every real η>0, P(|V_n|>ηa_n), converted to a real number, tends to zero. `BoundedInProbability P V` means: for every real δ>0 there is a real M>0 such that eventually P(|V_n|>M)<δ. `Consistent P hat μ` means: for every real b>0, P(|hat_n-μ|>b)→0. `RootNNormal P hat μ` means: there exists a strictly positive v in NNReal such that √n(hat_n-μ) converges in distribution to the identity variable on the real Gaussian probability space N(0,v). Mathlib's Gaussian parameter v is the variance. Convergence in distribution includes almost-everywhere measurability of the variables and convergence of their induced probability measures in the weak topology.

`NormalRemainder P hat Z ε μ v` is a conjunction, for every n≥1: Z_n is measurable with pushforward law N(0,v); ε_n is measurable with integrable square; and √n(hat_n-μ)=Z_n+ε_n almost surely. Independence of Z_n and ε_n, or across n, is not required. `SmallRemainderMS P ε` means √n∫ε_n² dP→0. `SmallMSE P V` means n∫V_n² dP→0.

The generated closure constants were printed in `scratch/BlindClosure.lean`. The auxiliaries T5Statement._proof_3, T6Statement._proof_1 through _proof_9, fairPair._proof_2, normalTail._proof_1, and T8Statement._proof_1 through _proof_3 certify the ordinary numeral instances `AtLeastTwo` (respectively 2; 625,21,25,15625,15,6,23,50,27; 2; 2; and 2,3,6). `fairPair._proof_1` is the standard ENNReal scalar-tower instance. `RootNNormal._proof_1` supplies the Borel measurable-open-space instance on ℝ, and `_proof_2` the probability-measure instance for N(0,v). None introduces a statistical assumption.

## SAP.P017.T6

Sources: Challenge/Part1.lean:46–50; Defs/Part4.lean:40–62; the listed definitions from Defs/Part1.lean and Defs/Part2.lean.

This is a closed conjunction about specific data, with no outer user-supplied hypotheses. Let a full-data observation be (X,B)∈ℝ×ℝ, with population G=N(0,1)⊗(½δ₋₁+½δ₁), and let P be the countable independent product of G on sample sequences s:ℕ→ℝ×ℝ. Potential outcomes are Y₀=0 and Y₁(X,B)=B, so τ=B. For n∈ℕ, put m_n(s)=(∑_{i=0}^{n-1}(s_i).1)/n, h_n=m_n+1/n, Z_n=√n m_n, ε_n=1/√n, and D_n=m_n-C(0,1,h_n). `fairPair` is literally the sum of the two half-weighted Dirac measures; `iidSamples` is Mathlib `Measure.infinitePi` with every coordinate law G; `sampleMean` is the finite sum divided by the natural number cast to ℝ.

The assertion is all of the following:

1. τ is measurable and integrable, ∫τ dG=0, support(G.map τ)={-1,1}, and the extended radius defined above equals 1.
2. For every n≥1, Z_n is measurable with law N(0,1), ε_n is measurable with integrable square, and √n h_n=Z_n+ε_n almost surely. Also √n∫ε_n²dP→0, and for every n≥1, ∫ε_n²dP=1/n.
3. For every sample sequence s, if |m_25(s)|≤1/2, then C(0,1,h_25(s))=h_25(s) and D_25(s)²=1/625. The probability of that central event is at least 21/25, and ∫D_25²dP≥21/15625.
4. Let T=2∫_{x>1}x²(5/√(2π))exp(-25x²/2)dx, a Lebesgue integral on ℝ. Then T=∫1_{|m_25|>1}m_25²dP, T≤∫m_25⁶dP=15/15625, ∫D_25²dP-T≥6/15625, and 0<6/15625.
5. For every s with |m_25(s)|≤1/2, -23/50≤h_25(s)≤27/50.
6. Both n∫(h_n-C(0,1,h_n))²dP→0 and n∫D_n²dP→0.

The normal-tail definition generally is 2∫_{x>c}x²[√n/(σ√(2π))]exp[-x²n/(2σ²)]dx; here n=25,c=σ=1. The intermediate D_n is based on m_n; it is not the actual error h_n-C(0,1,h_n). The docstring calls this a counterexample to a printed intermediate bound while retaining both mean-square limits. The theorem itself does not explicitly assert an observed-data factorization or root-n convergence in distribution.

Junk conventions: at n=0, the finite sum is empty, real division by zero gives m_0=h_0=ε_0=0, and √0=0. All fixed-sample Gaussian/decomposition assertions are restricted to n≥1, while the asymptotic limits ignore n=0. All nonzero numerical denominators and positive-sample √n are positive. The probability measures are finite, so `P.real` never uses the ∞↦0 convention. The displayed Gaussian and polynomial functions have finite moments; the integrals therefore have their ordinary meanings rather than the nonintegrability default. Population support is explicitly the nonempty set {-1,1}; its finite infimum/supremum and radius avoid empty-set and unbounded-set conventions. No logarithm, real power, truncated subtraction, limsup/liminf, or partial-function default is present.

## SAP.P017.T7

Sources: Challenge/Part1.lean:52–64; all of Defs/WholeW3.lean:16–77 and the listed Defs/Part1.lean dependencies. This target uses `T7WholeStatement_W3`, not the older unused `T7Statement`.

Quantifier order: for every pair of types Ω,Ξ with measurable spaces, population probability measure G on Ω, and τ:Ω→ℝ, assume τ measurable and G-integrable and c=toENNReal(min(U-μ,μ-L))>0, with μ=∫τdG and L,U the extended bounds of support(G.map τ). Then for every probability measure P on Ξ and estimator sequence hat:ℕ→Ξ→ℝ measurable at every n≥1, all three assertions below hold. There is no data law or empirical-statistic factorization hypothesis. Let E_n(ω)=hat_n(ω)-C∞(μ,c,hat_n(ω)).

1. Finite facts, without any consistency or asymptotic-normality hypothesis: for every n≥1 and every ω, E_n(ω)=0 iff ENNReal.ofReal|hat_n(ω)-μ|≤c. For every n≥1 and η,a∈ℝ with η>0 and a>0, {|E_n|>ηa} is a subset of {ENNReal.ofReal|hat_n-μ|>c} (written as the negation of inside), and its real probability is no larger. If c=+∞, for every n≥1 and ω the target equals hat_n, E_n=0, and √nE_n=0.
2. If for every b>0 the fixed-radius tail P(|hat_n-μ|>b)→0, then this same consistency assertion holds, P(not inside)→0, and for every deterministic a:ℕ→ℝ with a_n>0 for all n≥1 and every η>0, P(|E_n|>ηa_n)→0. Also, for every η>0, P(|√nE_n|>η)→0.
3. If there exists v>0 with √n(hat_n-μ) converging in distribution to N(0,v), then √n(hat_n-μ) is bounded in probability in the explicit δ,M,eventual sense given above, and every conclusion in item 2 holds, including consistency.

Junk conventions: μ is not a junk Bochner integral because integrability is explicit. On real probability laws with measurable τ the support is nonempty and has full measure; L,U are genuine extended endpoints, including ±∞. The subtracted mean is finite, so no ∞-∞ occurs in the radius. `toENNReal` truncation does not change the nonnegative distances supplied by a population mean, and c>0 explicitly excludes zero radius. The extended infinity case is branched before `toReal`, so +∞ is not silently replaced by zero. `ENNReal.ofReal` is applied to a nonnegative absolute value. P is a probability measure, so real probabilities are finite and correct. n=0 and a_0 are unrestricted and irrelevant to these limits; exact facts are stated only for n≥1. Arbitrarily small positive a_n are allowed, with no convergence or rate condition. No expectation of the estimator, independence assumption, limsup/liminf, empty index, log, rpow, or partial default is used.

## SAP.P017.T8

Sources: Challenge/Part1.lean:66–70; Defs/Part5.lean:15–54 and all listed Defs/Part1.lean dependencies.

This is a conjunction of four universally quantified assertions. In the first, for every measurable space Ξ, probability measure P on Ξ, functions hat,Z,ε:ℕ→Ξ→ℝ, μ,c∈ℝ, v∈NNReal, assume c>0, v>0, every hat_n measurable, and the exact Gaussian-plus-remainder conditions above for every n≥1. Then for every n≥1 let t(ω)=μ+Z_n(ω)/√n. All the following hold, with C=C(μ,c,·), R=R(μ,c,·):

1. For every real x,y, |C(x)-C(y)|≤|x-y| and |R(x)-R(y)|≤|x-y|.
2. Almost surely, |R(hat_n)|≤|R(t)|+|ε_n|/√n. Consequently ∫R(hat_n)²dP≤2∫R(t)²dP+2∫ε_n²dP/n.
3. For every x∈ℝ, R(x)²=[max(|x-μ|-c,0)]²≤1_{|x-μ|>c}(x-μ)²≤(x-μ)⁴/c².
4. ∫(t-μ)⁴dP=3v²/n², and ∫R(hat_n)²dP≤6v²/(c²n²)+2∫ε_n²dP/n.
5. Almost surely, |t-C(hat_n)|≤|R(t)|+|ε_n|/√n, and ∫(t-C(hat_n))²dP≤6v²/(c²n²)+2∫ε_n²dP/n.
6. ∫R(t)²dP≤∫1_{|t-μ|>c}(t-μ)²dP, and the latter equals 2∫_{x>c}x²[√n/(√v√(2π))]exp[-x²n/(2(√v)²)]dx.

The second assertion independently quantifies over a measurable space and exactly the same P,hat,Z,ε,μ,c,v and hypotheses, then additionally assumes √n∫ε_n²dP→0. It concludes both n∫R(hat_n)²dP→0 and n∫(μ+Z_n/√n-C(hat_n))²dP→0.

The third assertion, independently for every real μ,c,x,y (without c>0), is the triangle inequality |x-C(μ,c,y)|≤|R(μ,c,x)|+|C(μ,c,x)-C(μ,c,y)|.

The fourth assertion independently quantifies over every measurable space Ξ, every measure P (not necessarily a probability measure or σ-finite), arbitrary hat:ℕ→Ξ→ℝ, and μ∈ℝ. It states for all real x,y that x-C∞(μ,+∞,x)=0 and y-C∞(μ,+∞,x)=y-x, and n∫(hat_n-C∞(μ,+∞,hat_n))²dP→0.

Junk conventions: c>0, v>0, and n≥1 guard every finite-bound denominator and √v; all real square roots are on nonnegative inputs. At n=0 the quotient Z_0/√0 is zero in Lean, but this value occurs only as a single irrelevant term of a limit. The fourth assertion is valid even for infinite P and nonmeasurable hat because its integrand is identically zero, a measurable integrable function for every measure. The remainder-square integrability is explicit and the Gaussian polynomial moments are finite; the decomposition and Lipschitz bounds give square integrability for both errors, so the displayed means are not Bochner defaults. The unrestricted c in the triangle inequality may be negative, in which case this particular min/max map is constant at μ+c; the inequality is still just the ordinary triangle inequality. No support extrema, probability `toReal` on infinite mass, log/rpow, truncated natural subtraction, or limsup/liminf is involved.

## SAP.P017.T9

Sources: Challenge/Part1.lean:72–80; Defs/Part5.lean:116–138; the closure definitions in Defs/Part1.lean and Defs/Part2.lean. The target is `T9SamplingStatement`, not the earlier unused `T9Statement`.

The assertion is the negation of one universal implication. Equivalently, there exist ordinary small types Ω,D,Ξ with measurable spaces, a probability population G on Ω, a measurable integrable τ:Ω→ℝ with the positive extended radius c defined from the closed effect support, a measurable record function O:Ω→D, a probability measure P on Ξ, a measurable data map data:Ξ→(ℕ→Ω), estimator hat:ℕ→Ξ→ℝ, and empirical functional H:ℕ→(Measure D→ℝ), satisfying all of these:

1. P.map data is exactly the countably infinite independent product of G.
2. For every n≥1, H_n is measurable for Mathlib's measurable space on `Measure D`; for every n∈ℕ, hat_n is measurable.
3. For every n≥1 and every s∈Ξ, hat_n(s)=H_n((1/n)∑_{i=0}^{n-1}δ_{O((data s)_i)}). The coefficient 1/n here is in ENNReal, and the expression is a finite empirical measure.
4. There exists v∈NNReal, v>0, such that √n(hat_n-μ) converges in distribution to N(0,v), μ=∫τdG.

For some n≥1 and some s∈Ξ, however, C∞(μ,c,hat_n(s)) is not representable. Explicitly there is no function w:Ω→ℝ which is measurable, everywhere nonnegative, G-integrable with ∫w dG>0, has wτ G-integrable, and satisfies (∫wτdG)/(∫wdG)=C∞(μ,c,hat_n(s)).

The outer negation permits choosing all types, spaces, measures, functions, and sample sizes. Inside it the universal conclusion is pointwise in every s, not merely almost sure and not restricted to points in the support of P. No positive probability of representation failure is required. There is no explicit potential-outcome structure in this statement, and O may be any measurable record function. Its docstrings explicitly label this a refutation of the printed claim in an IID sampling setting. No witness itself is named by this negated universal statement.

Junk conventions: admissibility requires an integrable numerator and an integrable strictly positive denominator, so a purported representation cannot use zero-division or default integrals. Integrable τ makes μ finite. Measurability guards the population and data pushforwards. Probability measures and measurable real τ make effect support nonempty with ordinary extended endpoints; unbounded effect support is allowed, and infinite radius uses the identity branch. At n=0 the empirical measure uses ENNReal inversion 1/0=∞ and the empty sum 0, whose product is 0; the conclusion and factorization exclude n=0. The asymptotic normality ignores the initial value. No arbitrary means of nonintegrable estimator functions are used. Empty Ω or Ξ cannot carry probability measures; empty D cannot be the image of the nonempty Ω under O. There is no log, sqrt on negative numbers, rpow, limsup/liminf, or partial-function default.

## SAP.P017.T10

Sources: Challenge/Part1.lean:82–87; Defs/Part5.lean:72–103; all listed Defs/Part1.lean dependencies.

This is the conjunction of three independent universal statements. First, for every two measurable types Ω,Ξ, probability G on Ω, measurable integrable effect τ, probability P on Ξ, and measurable real estimator hat:Ξ→ℝ, set μ=∫τdG and c equal to the extended population effect radius. Write A=support(P.map hat), Lhat=inf{x as an EReal:x∈A} and Uhat=sup{x as an EReal:x∈A}. Assume max(Uhat-μ,μ-Lhat)≤c, interpreted in EReal. There is no explicit strict positivity hypothesis on c. Then:

1. A⊆{x:ENNReal.ofReal|x-μ|≤c}.
2. P(inside(hat))=1.
3. The event {hat=C∞(μ,c,hat)} equals the event {inside(hat)}, as sets of Ξ.
4. P(hat=C∞(μ,c,hat))=1.
5. If P(inside(hat))=0 then P(hat=C∞(μ,c,hat))=0.

Item 5 remains scoped under the support-containment inequality. Since item 2 has already forced the antecedent probability to be 1, this particular zero-probability implication has an impossible antecedent. The exact equality of events in item 3 holds pointwise and is stronger than equality of their probabilities, but is also placed under that support condition.

Second, independently for every probability G and measurable integrable τ with support(G.map τ)=ℝ, c=+∞ and for every real x, C∞(μ,c,x)=x.

Third, independently for every two measurable types, probability G with measurable integrable τ and effect support exactly [0,+∞), and probability P with measurable real hat, assume P(hat<0)>0. Then c=ENNReal.ofReal μ; max(Uhat-μ,μ-Lhat)≤c is false; P(hat=C∞(μ,c,hat))≤1-P(hat<0); and P(hat=C∞(μ,c,hat))<1. This assumes exact half-line support, not merely an effect which is nonnegative almost surely.

Junk conventions: the Bochner population integral is guarded by integrability. All measures used in real probabilities are probabilities. Real pushforward supports are nonempty, though they may be unbounded; EReal infimum and supremum correctly retain infinite endpoints. The finite μ prevents ∞-∞ in the endpoint differences. Nonnegative distances for a probability mean prevent harmful `toENNReal` truncation. Zero radius is allowed and makes C∞ the constant μ; the support-bound hypothesis is then satisfiable with a constant estimator at μ. Infinite radius explicitly clips identically, avoiding `ENNReal.toReal ∞=0`. The full-real and half-line support branches impose nonempty supports, and real probability 0 or 1 has no conversion anomaly. No natural-number scale or empty index type, log, sqrt, rpow, limsup/liminf, or partial-function default is used.
