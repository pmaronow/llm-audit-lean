# Blind mathematical reading

This file was written from `SAP/P001a/Defs*.lean`, `SAP/P001a/Defs/*.lean`, and `SAP/P001a/Challenge*.lean` / `SAP/P001a/Challenge/*.lean`, before opening either `claims.json` or `record.json`. The declarations are `SAP.P001a.T1` through `SAP.P001a.T19`; their types are the correspondingly numbered `TnStatement` definitions. Descriptive comments do not add hypotheses or conclusions.

## Conventions, expanded definitions, and Mathlib endpoints

All sample sizes, polynomial indices, and dimensions are natural numbers, including zero unless explicitly excluded. `Fin n` means the n-element set {0,...,n-1}. Sums over `Fin n` include all its elements; sums over `range n` have the same indices. Vectors `Fin d → ℝ` have the usual finite product topology and the maximum norm/metric. Quantification over a probability space below means: for every type Ω (in the displayed universe), every measurable space on Ω, every measure μ, and an instance asserting μ(Ω)=1. Independence means independence of all finite subfamilies, not just pairwise independence.

* Pμ(A) denotes `(μ A).toReal`. A measure is evaluated on arbitrary sets using its associated outer measure; measurability of A is not part of this definition. Under a probability measure it is a number in [0,1]. `toReal ∞=0` generally.
* Eμ H is Mathlib's real Bochner integral. It is **zero by definition when H is not integrable**, including failure of almost everywhere strong measurability. Restricted integrals use the restricted measure. Vμ H is `ProbabilityTheory.variance`: `(∫⁻ω, ‖H(ω)-EμH‖ₑ² dμ).toReal`; in particular infinite extended variance becomes zero. When H is in L² on a probability space these are the ordinary mean and variance. `MemLp H 2 μ` asserts almost everywhere strong measurability and finite second moment. Cov(H,G) is the Bochner integral of `(H-EH)(G-EG)`.
* `IID μ Z` asserts (in this order) that every Zᵢ is measurable, that the family is independent, and that each Zᵢ and Z₀ are identically distributed. Mathlib `IdentDistrib` includes a.e. measurability of both functions and equality of pushforward measures.
* `CP μ Z c` means: for every real ε>0, Pμ{ε≤dist(Zₙ,c)}→0 as n→∞. No measurability is included in this predicate. For scalars the distance is absolute difference. `CD μ Z ν` means convergence of Pμ{Zₙ≤x} to ν((-∞,x]) at every continuity point of the real CDF of ν. `WeakLimit μ Z ν` means Eμ[f(Zₙ)]→Eνf for every continuous real f with a global finite bound on |f|. Its definition likewise does not assert measurability.
* The sample mean is n⁻¹Σᵢ<n Zᵢ. At n=0 this is zero. The empirical measure is n⁻¹Σᵢ<n δZᵢ with the inverse taken in ℝ≥0∞; for n>0 it is the ordinary empirical probability measure.
* `HasPDF ν f`, `HasJointPDF ν f`, and `HasVectorPDF ν f` assert that f is a.e. measurable with respect to the relevant Lebesgue volume, f is pointwise nonnegative, f is integrable, and ν has density `ofReal f` with respect to that volume. The predicate itself does not impose total mass one. `uniformLaw a b` has density `(b-a)⁻¹ 1[a,b]`; it is uniform probability when a<b.
* `IsCEF μ X Y m` asserts that m is globally measurable, Y and m(X) are integrable, and for every measurable covariate set A, ∫{X∈A}Y dμ=∫{X∈A}m(X)dμ. Whenever X is measurable, this is the usual integrable conditional expectation representative. `CI μ X hX W D` means, for every measurable A,B, E[1{W∈A,D∈B}|σ(X)]=E[1{W∈A}|σ(X)]E[1{D∈B}|σ(X)] a.s., where σ(X) is Mathlib's comap measurable space. The finite-law version `FCondIndep P W D X` requires the corresponding product identity for every x,w,d with P(X=x)>0. `fcond P Y X x` is Σ1{Xᵢ=x}wᵢYᵢ/P(X=x), with division by zero defined as zero. `conditionalMeanAt` uses the analogous restricted Bochner integral divided by P(X=x).
* A `FiniteLaw n` supplies n nonnegative real weights summing to one. `fmean` is the weighted finite sum, `fprob` the weighted sum of an event, and `finiteLawMeasure` is the corresponding weighted sum of Dirac measures. There is no such law for n=0.
* `IsSieveLS X Y J fit` means **for every n and every ω**, fitₙ(ω) is a real polynomial of natural degree at most Jₙ, and its residual sum of squares is no larger than that of every polynomial of degree at most Jₙ. This does not assert any measurability of fit. The zero polynomial has natural degree zero.
* `partialAt m x k` is the derivative at t=0 of m with coordinate k replaced by xₖ+t. Mathlib `deriv` and `fderiv` are zero if the corresponding derivative does not exist; `HasDerivAt` asserts actual differentiability with the given derivative.
* A real square matrix inverse is the adjugate multiplied by the ring inverse of its determinant; it is the **zero matrix when singular**. Over ℝ `IsUnit(det A)` means det A≠0. Matrix `PosDef` includes symmetry and strictly positive quadratic form for every nonzero vector. `normalVectorLaw S` is the coordinate pushforward of the centered multivariate Gaussian constructed from the functional-calculus square root of S. For positive semidefinite S it has covariance S; otherwise Mathlib's construction collapses to δ₀. `gaussianReal m v` uses **variance v**, and is δm if v=0.
* `sampleGram p X n` has entries n⁻¹Σᵢ<n pⱼ(Xᵢ)pₖ(Xᵢ). `gramDeviation G` is sup{|vᵀGv-1|:Σvₖ²=1}, a real conditional supremum. A positive dimension makes this a nonempty compact optimization with a finite supremum; in dimension zero its displayed defining set is empty. `Filter.liminf` on ℝ is the supremum of eventual lower bounds, so boundedness matters.
* OLS coefficients are `(RᵀR)⁻¹RᵀD`, residual sum of squares is Σ(Dᵢ-(Rβ)ᵢ)², and `robustCov R e` is the HC0 matrix `(RᵀR)⁻¹Rᵀdiag(eᵢ²)R(RᵀR)⁻¹`. Singular designs use the matrix-inverse convention above. `placeboFStatistic` compares R=(1,X) and F=(1,X,W) and equals `((RSS_R-RSS_F)/L)/(RSS_F/(n-(K+L+1)))`; the last subtraction is in ℝ. `fReference k v` is the pushforward of k+v independent N(0,1) coordinates by the ratio of the first k squared coordinates divided by k to the last v squared coordinates divided by v. It is the usual F(k,v) law for k,v>0.
* A conditional density family g(y,x,t) determines `Q_t=conditionalModelLaw νX κ g t`, namely the measure with density g with respect to νX⊗κ (using `ofReal`). `conditionalKL` is ∫f(y,x)log(f(y,x)/g(y,x,t))dκ(y) and `averageKL` integrates this real Bochner integral over νX. `averageKLExt` instead integrates Mathlib's extended KL of the two conditional density measures over νX. Mathlib KL is ∞ if absolute continuity or integrability of its log likelihood ratio fails; otherwise it is `ofReal(∫ log(dP/dQ)dP+Q(Ω)-P(Ω))`. For probability measures it is the ordinary nonnegative extended KL. `Real.log 0=0`, and division by zero in ℝ is zero, so the real formula needs the integrability and domination hypotheses actually supplied.
* Write M(t)=E log g(Y₀,X₀,t), Lₙ(t)=n⁻¹Σᵢ<n log g(Yᵢ,Xᵢ,t), and ℒₙ(t)=Πᵢ<n g(Yᵢ,Xᵢ,t). In particular L₀=0 and ℒ₀=1. For mixtures h(y,x,t)=Σₘpₘ(t)gₘ(y,x,t). The score sⱼ(y,x,t) is the j-coordinate Frechet derivative of log g; Hⱼₖ is the k derivative of sⱼ. Iⱼₖ(t)=E(sⱼsₖ), Aⱼₖ(t)=EHⱼₖ, and Aₙ,ⱼₖ(t)=n⁻¹ΣHⱼₖ(Yᵢ,Xᵢ,t). These definitions do not themselves enforce differentiability or integrability.
* `iidObservationLaw Q n` is Q to the n-fold finite product. `SampleCP Q T θ` means P_{Q^n}{ε≤dist(Tₙ,θ)}→0 for each ε>0. `SampleWeakLimit Qₙ Z γ` tests bounded continuous real functions of Zₙ under Qₙ^n. `RegularAL Q θ T ψ` requires: measurable Tₙ and ψ; each ψⱼ in L²(Qθ) with mean zero; √n(Tₙ-θ)-(√n)⁻¹Σᵢψ(sᵢ)→0 in Qθ^n probability; and, for **every** vector h, √n(Tₙ-(θ+h/√n)) under Q_{θ+h/√n}^n converges weakly to N(0,Cov_{Qθ}ψ). This local-alternative limit is a hypothesis of regularity.
* `QuadraticMeanModel νX κ g θ` means: for every ε>0 there exists δ>0 such that for every t with dist(t,θ)<δ, the integral against νX⊗κ of `[√g_t-√g_θ-(1/2)Σⱼ(tⱼ-θⱼ)sⱼ(θ)√g_θ]²` is at most ε dist(t,θ)². By itself this uses the total Bochner integral; T12 separately imposes local integrability of this squared remainder.

Mathlib definitions were checked in `Probability/Moments/{Variance,Covariance}.lean`, `Probability/IdentDistrib.lean`, `Probability/Independence/Basic.lean`, `Probability/Distributions/Gaussian/{Real,Multivariate}.lean`, `MeasureTheory/Function/LpSeminorm/Defs.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, `MeasureTheory/Function/ConditionalExpectation/Basic.lean`, `InformationTheory/KullbackLeibler/Basic.lean`, `Analysis/Calculus/{Deriv/Basic,FDeriv/Defs}.lean`, `LinearAlgebra/Matrix/{NonsingularInverse,PosDef}.lean`, and `Order/LiminfLimsup.lean`.

## T1

Define q(k)=2^(-k-1), F_q(x)=Σₖ≥0 1{k≤x}q(k), m(q)=Σkq(k), s₂(q)=Σk²q(k), and qₙ(k)=(1-n⁻³)q(k)+n⁻³1{n≤k}q(k-n). The subtraction k-n is natural subtraction but occurs only in the branch n≤k. `FiniteMomentLaw` means pointwise nonnegative, summable normalized masses with summable first- and second-moment series.

Without hypotheses, the theorem asserts: q is such a law, m(q)=1, s₂(q)=3; for **every natural n≥2**, qₙ is such a law, every qₙ(k)>0, m(qₙ)=1+n⁻², s₂(qₙ)=3+n⁻¹+2n⁻², and `(m(qₙ)-m(q))/n⁻²=1`. As n→∞, s₂(qₙ)-m(qₙ)²→2 and n⁻²→0. Finally, for **every ε>0** there exists an eventual threshold N such that **every n≥N and every real x** satisfy `|(F_qₙ(x)-F_q(x))/n⁻²|<ε`. This is uniform convergence of the scaled CDF differences to zero. No abstract differentiability predicate is concluded.

## T2

Two unconditional conjuncts. First, for **every probability space, iid real sequence X**, with X₀ in L² and V(X₀)>0: (a) for **every n>0 and every ω**, E_{empirical(X,n,ω)}id equals the sample mean; (b) √n(sampleMeanₙ-E X₀) converges in the CDF sense to N(0,V(X₀)). Second, all of T1, with the fixed masses above, holds. No derivative or negated Hadamard-differentiability proposition appears beyond that explicit witness.

## T3

Let f(x)=(1/2)1{[-2,-1]∪[1,2]}(x), Q be the product of its density law and Uniform[-1,1], and b(x)=x(1-x²)² for |x|<1 and zero otherwise.

The theorem negates this universally quantified contract: **for every type Ω, measurable space, measure μ with μ(Ω)=1, real X,Y**, if X,Y are measurable, X is integrable, fX is a PDF for law(X), and m,m' are CEFs of Y given X which are each differentiable at every x with fX(x)>0, then **there exists one real a** with actual derivatives a for both m,m' at E X.

The remaining conjuncts assert directly that Q is a probability with joint PDF f(x)·(1/2)1[-1,1](y); Q equals the product of its marginals; its X marginal has PDF f and its Y marginal is Uniform[-1,1]; |X|≤2 and |Y|≤1 Q-a.s.; E_Q X=0 and f(0)=0; the zero function is a CEF; b is globally C¹ and zero wherever f>0; the zero derivative at 0 is zero; and **for every real a**, ab is also a CEF and has derivative a at E_Q X. Some of these assertions are repeated with a=1. The zero function is globally C¹, and {f>0} is exactly the two closed intervals, including their endpoints. No assumptions precede these fixed-witness assertions.

## T4

For **every probability space, natural K, measurable vector X, integrable real Y**, assuming every X-coordinate is integrable, law(X) has PDF f, U is open and contains EX, f is pointwise positive on U, m,m' are globally measurable integrable CEFs, and each is continuous on U: for **every coordinate k and real a**, **if** the function t↦m(EX+t eₖ) has derivative a at 0, **then** m=m' everywhere on U, t↦m'(EX+t eₖ) has derivative a at 0, and their `partialAt` values agree. Thus equality on U is also behind the derivative premise and a choice of coordinate; there is no independent derivative-free equality clause.

## T5

For **every probability space and iid measurable pair sequence (Xᵢ,Yᵢ)** whose common law is Uniform[0,1]⊗N(0,1), and **every supplied fit** satisfying the all-samples least-squares property with Jₙ=⌊n^(3/4)⌋: Jₙ→∞, Jₙ/n→0, and for **every real δ with 0<δ≤1 and every ε>0**, `liminf_{t→∞} Pμ{ε<∫[0,δ]fit_{t⁴}(x)²dx}≥1/2`. The liminf concerns probabilities in [0,1], so it is bounded. The integral is over a compact interval of a polynomial square and is finite for each fit. There is no fit-measurability premise, selection existence conclusion, or bound for Jₙ=⌊√n⌋.

## T6

The theorem is the conjunction of four separate universal implications, with independent probability spaces.

1. For every iid pair sequence (X,Y), real a<b and V≥0, assume Y₀∈L², X₀∈[a,b] a.s., m is continuous on [a,b] and is a CEF, and for **every measurable A**, ∫{X₀∈A}(Y₀-m(X₀))²≤V·P(X₀∈A). Supply polynomials pₖ of degree exactly k with E[pⱼ(X₀)pₖ(X₀)]=1{j=k}; a natural sequence J with Jₙ→∞ and (Jₙ+1)/n→0; a real c>0; and a fit satisfying `IsSieveLS X Y J`. Assume the probabilities of the events `∀v∈ℝ^(Jₙ+1), cΣv²≤n⁻¹Σᵢ<n(Σₖvₖpₖ(Xᵢ))²` tend to one. Conclusion: the random integrated squared error ∫(fitₙ(x)-m(x))²d law(X₀)(x) tends to zero in probability.
2. For every iid scalar X, polynomial sequence p orthonormal for law(X₀), natural sequence J and real sequence ζ², assume **for every n**, Σₖ<Jₙ+1pₖ(X₀)²≤ζ²ₙ a.s. and ζ²ₙ(Jₙ+1)/n→0. Conclusion: the above lower Gram event with c=1/2 has probability tending to one. No degree, increasing-J, or support premise is imposed in this clause.
3. For every iid scalar X with Uniform[a,b] law, a<b, polynomials p of degree exactly k orthonormal for this law, and natural sequence J with (Jₙ+1)³/n→0: the c=1/2 lower Gram event has probability tending to one. J need not diverge.
4. For every iid Uniform[0,1] sequence X, **positive integers K,n**, and K polynomials pₖ of degree k orthonormal for this law: **for every x∈[0,1]**, Σₖ<Kpₖ(x)²≤K², and P{gramDeviation(sampleGram)>1/2}≤4(K³-K)/n.

## T7

Define K(p,t)=p log(p/t)+(1-p)log((1-p)/(1-t)), C(z)=max(1/10,min(9/10,z)), and Tₙ=C(sampleMean Y n).

First implication: for **every probability space and iid pair sequence (X,Y)** with atom probabilities 3/8 at (0,0), 1/8 at (0,1), 1/8 at (1,0), 3/8 at (1,1), all the following hold. For p∈{1/4,3/4} and t∈[1/10,9/10], K(p,t)≥0 and K(p,t)=0 iff t=p. For **every n>0, every binary sample y of length n, every t in that interval**, its Bernoulli likelihood is maximized at C(mean y), and equality with that maximum holds iff t=C(mean y). E Y₀=1/2 and V Y₀=1/4. For every n>0 and ε>0, P{|Tₙ-1/2|≥ε}≤1/(4nε²). For every n>0, each of P{|Tₙ-1/4|>1/8} and P{|Tₙ-3/4|>1/8} is at least 1-16/n. Tₙ→1/2 in probability and converges to neither 1/4 nor 3/4. On the parameter interval, t=1/2 is the unique minimizer of [K(1/4,t)+K(3/4,t)]/2.

Second implication: universally over **q∈[0,1]** and iid pairs with atom masses (1-q)3/4,(1-q)/4,q/4,3q/4 in that same order: Tₙ→1/4+q/2 in probability; **for every n>0**, a.s. Tₙ lies in the parameter interval and is the unique maximizer of the binary likelihood on it. If 0<q<1, the defined conditional means at X=0 and X=1 are respectively 1/4 and 3/4, and T converges to neither. Conditional means are not asserted at a zero-probability covariate value.

## T8

Four independent universally quantified clauses.

1. For every probability space, natural K,τ, measurable (X,Y), probability νX, s-finite measure κ, measurable joint density functions f(y,x),g(y,x,t) for a supplied t, assume: both densities are pointwise nonnegative and normalized in y **for every x**; law(X,Y)=(νX⊗κ)f; f>0 implies g_t>0 almost everywhere for νX⊗κ; and f log f and f log g_t are integrable for νX⊗κ. Conclusion: averageKLExt(t) is finite; its real value is ∫∫f log f dκdνX-M(t); and averageKL(t) equals that real value.
2. For every iid measurable pair sequence, νX,κ,f as above with the stated true joint law, parameter set Θ, and conditional family g, assume **for every t∈Θ** joint measurability, pointwise nonnegativity, normalization for every x, a.e. domination of f by positive g_t, and integrability under μ of log g_t(Y₀,X₀). Supply t*∈Θ, and assume **for every ε>0 there exists δ>0 such that every t∈Θ with dist(t,t*)≥ε has M(t)≤M(t*)-δ**. Supply measurable estimators thatₙ taking values in Θ **for every n,ω** and real random sequences e,Δ. Assume eₙ(ω)≥0 everywhere, e→0 and Δ→0 in probability, and **for every natural n (including 0), every ω and every t∈Θ**, |Lₙ(ω,t)-M(t)|≤Δₙ(ω). Finally assume **either** all sample likelihoods ℒₙ are globally maximized by thatₙ, for every n,ω,t∈Θ, **or** Lₙ(t)-eₙ≤Lₙ(thatₙ) for all such n,ω,t. Conclusion: that→t* in probability. If, in addition, f log f is jointly integrable and f log g_t is jointly integrable for every t∈Θ, then t* is the unique minimizer of averageKLExt over Θ. No compactness, finite entropy, or positivity of sample densities at every exceptional ω is separately required for consistency.
3. For every metric space E, compact Θ⊆E, θ∈Θ, real M continuous on Θ with M(t)≤M(θ) and equality only at θ: **for every ε>0** there exists δ>0 such that M(t)≤M(θ)-δ whenever t∈Θ and dist(t,θ)≥ε.
4. For every νX probability, κ s-finite, Θ and θ,t*∈Θ, normalized nonnegative jointly measurable densities g_t for t∈Θ: if t* is the unique global minimizer of averageKLExt(g_θ,g_t), then this divergence is zero at θ, t*=θ, and it is zero exactly at θ. Uniqueness of the KL minimizer is an explicit premise of this clause.

## T9

For t=(p,q,m,s,ℓ,v,r), the mixture density is p·φ_{m,s}(y)+q·1{y>0}φ_{ℓ,v}(log y)/y+(1-p-q)·1{y≥0}r exp(-ry), where φ_{m,s}(y)=exp(-(y-m)²/(2s²))/(s√(2π)). Admissibility is p,q≥0, p+q≤1, s,v,r>0.

Without hypotheses, **for every real B** there exists s>0 such that t=(1/2,1/4,1,s,0,1,1) is admissible and the product likelihood on sample (1,2,3) exceeds B. There is no admissible global maximizer on that sample. No specific scale or lower-bound constant is specified.

## T10

Using that mixture, (1) for **every n>0 and every real sample with all observations positive**, the likelihood is unbounded above over admissible t and has no global maximizer; (2) for **every natural n (possibly zero), every all-positive sample, every real B,S,δ,a,b**, if δ>0, a>0 and the restriction R is nonempty, then R is compact, the sample likelihood is continuous on R, and there exists a maximizer in R. Here R consists of admissible t with |m|,|ℓ|≤B, δ≤s,v≤S, and a≤r≤b. No further inequalities on B,S,b are imposed; nonemptiness supplies the necessary compatibility.

## T11

The four-point probability vector is q(p,a,b)=(p(1-a),pa,(1-p)(1-b),(1-p)b). Θ=[0,1]×[0,1]×[1/4,3/4], θ₀=(1,1/3,1/4), θ₁=(1,1/3,3/4), and ℒₙ(y,t)=Πᵢq(t)(yᵢ). Finite sample event probability sums ℒₙ over all samples. `FiniteMixtureConsistent T θ` means: **for every coordinate k and every ε>0**, Pθ{|Tₙ,k-θₖ|<ε}→1.

Without premises: Θ is compact and contains θ₀,θ₁; q(θ₀)=q(θ₁)=(2/3,1/3,0,0); **for every n and sample y** the likelihood has a maximizer in Θ and is continuous on the entire parameter vector space. For **every n and every sample estimator T** the θ₀ sample masses are nonnegative and sum to one, the θ₀ and θ₁ sample masses are identical pointwise, and Pθ₀{|T₂-1/4|<1/8}+Pθ₁{|T₂-3/4|<1/8}≤1. For **every estimator sequence T**, it is impossible to be consistent at both θ₀ and θ₁. Finally, **there exists an estimator sequence T** selecting a global maximizer in Θ for every n,y and failing consistency at at least one of θ₀,θ₁. There is no asserted uniform upper likelihood bound or special binomial representation.

## T12

Three independent universal implications, with h=Σₘpₘgₘ as above.

1. For every natural M,K,τ, probability νX, s-finite κ, weights p and component family g, distinct θ,θ', and j∈Fin M, assume p(θ)=p(θ'), pⱼ(θ)=0, weights at θ are nonnegative and sum to one, and all components k≠j are pointwise equal at θ,θ'. At both parameter values assume each component is jointly measurable, pointwise nonnegative, and normalized in y for every x. Also assume log h_θ is integrable under Qθ. Conclusion: h_θ=h_θ' pointwise; Qθ=Qθ'; **for every n** their n-fold product laws coincide; their expected own log likelihoods coincide; and **for every measurable estimator sequence T** it is impossible that both SampleCP Qθ T θ and SampleCP Qθ' T θ' hold.
2. For every probability space, iid measurable pair sequence (X,Y), dimensions M,K,τ, νX probability and κ s-finite, p,g, compact Θ, θ∈Θ: assume nonnegative normalized weights on Θ; every component on Θ is measurable, nonnegative and conditionally normalized; law(X₀,Y₀)=Qθ; log h_t(Y₀,X₀) is integrable for every t∈Θ; h_t(Y₀,X₀)>0 a.s. for each such t; M(t) is continuous on Θ with unique global maximizer θ. Supply measurable Θ-valued thatₙ, pointwise global maximizers of Lₙ for **every n,ω**. Supply real Δ with **for every n,ω,t∈Θ**, |Lₙ-M(t)|≤Δₙ and Δ→0 in probability. Conclusion: that→θ in probability.
3. For every probability space, iid measurable pair sequence, νX,κ,p,g and dimensions as before, Θ,θ and real δ>0 with ball(θ,δ)⊆Θ, assume the following, all jointly:
   * weights are nonnegative normalized on Θ and components on Θ are measurable, nonnegative and normalized in y for every x; the true law is Qθ;
   * there is a measurable S⊆covariate×outcome space of probability one under the true law; h(y,x,t)>0 for every (x,y)∈S and t∈ball(θ,δ); log h is C² on that ball at each observation in S;
   * each score coordinate at θ is in L²(μ) and has mean zero; I(θ) is positive definite; A(θ)=-I(θ); A is continuous at θ; and each Hⱼₖ(t) is integrable for every t in that ball;
   * a real envelope ΔH satisfies |Aₙ,ⱼₖ(ω,t)-Aⱼₖ(t)|≤ΔHₙ(ω) for **every n,ω,t in the ball and j,k**, and ΔH→0 in probability;
   * thatₙ is measurable, belongs to Θ everywhere, and maximizes the product likelihood ℒₙ pointwise over Θ for **every n,ω**;
   * Θ is compact and contains θ; every log h_t(Y₀,X₀) is integrable for t∈Θ; h_t is positive on **S×Θ**; M is continuous on Θ and uniquely maximized at θ;
   * a real envelope Δ→0 in probability bounds |Lₙ-M| for **every n,ω,t∈Θ**, including n=0;
   * there exists r>0 such that the squared square-root-density remainder in the expanded `QuadraticMeanModel` definition is integrable for every t with dist(t,θ)<r; and that quadratic-mean condition itself holds.
   Conclusions, under **all** these hypotheses: that→θ in probability; √n(thatₙ-θ) converges weakly to N(0,I(θ)⁻¹); and **for every estimator sequence T and influence function ψ satisfying RegularAL(Q,θ,T,ψ), and every vector a**, aᵀ(Cov_{Qθ}ψ-I(θ)⁻¹)a≥0. The QMD premises are outside the conjunction of conclusions and therefore apply also to the normal limit.

## Matching definitions for T13–T16

A unit is (p,d,e)∈ℝ×Bool×Bool. Its law Q has density 1{p∈[1/4,3/4]}·(p if d=true, otherwise 1-p) with respect to Lebesgue measure on p and counting measure on each Boolean. Equivalently p∼Uniform[1/4,3/4], d|p∼Bernoulli(p), and e is a fair independent sign. Write ε(e)=1 for true and -1 for false. This density includes no extra factor 1/2: summing over e gives the factor 2 required for the uniform score density.

`nearestDonor p r i` is `none` if there is no r=true donor, otherwise `some` of one nearest donor minimizing |pⱼ-pᵢ|. A fixed classical choice on its defining predicate resolves ties. For a length-n sample s, `hotDeck` H(s) averages 50+ε for respondents d=true and the donor's 50+ε for nonrespondents; with no respondent it is defined as 50. `causalMatch` C(s) is -n⁻¹ times the sum of εᵢ for controls d=false and the ε of a nearest control for treated d=true; treated observations contribute zero if no control exists. `firstSample Z n` takes the first n observations. For donor flags r, wⱼ(p,r)=0 for a nondonor and otherwise 1 plus the number of nondonors selecting j.

For a sample statistic T, its bootstrap mean is n^(-n)ΣₐT(s∘a), summing over all maps a:Fin n→Fin n. Its bootstrap variance B_T(s)=n^(-n)Σₐ[T(s∘a)-bootstrapMean_T(s)]². For n>0 this is the ordinary centered n-out-of-n resampling variance with multiplicities; at n=0 the denominator is 0^0=1 and there is one empty resampling map. `signProductLaw n` is the n-fold product of the fair Boolean sign law.

Set V=3 log 3-1/4, s=1-exp(-1), A=2/s-s/(2-s), B=3/(2s)-(4-s)/(2(2-s)), and VB=1/2+A/2+B(2 log 3-3/2).

`MatchingFailure μ Z causal` expands to five conclusions for T=C and θ=0 if causal=true, or T=H and θ=50 if false: **for every n>0**, ET(firstSampleₙ)=θ; n Var(T(firstSampleₙ))→V; E[n B_T(firstSampleₙ)]→VB; 0<VB<V; and n B_T(firstSampleₙ) does **not** converge in probability to V.

The estimated intercept is α̂(s)=clip[1/8,3/8](n⁻¹Σᵢ[dᵢ-(pᵢ-1/4)]). Estimated scores are α̂(s)+pᵢ-1/4; C_est(s) applies C after replacing p by these scores.

## T13

1. For **every probability space and iid Q-distributed Z**, assume **for every natural n**, H(firstSampleₙ) and B_H(firstSampleₙ) each belong to L²(μ). Then MatchingFailure(false) holds.
2. Independently, for every such probability space, sequence and both L² premises, **there exists one finite real C≥0 such that for every n**, E[(n B_H(firstSampleₙ))²]≤C.
3. Without premises: 0<s<1, A<3, B<3/2, and VB<V.

## T14

First, the same universally quantified MatchingFailure(false) implication and both per-n L² premises as in T13. Second, **for every n>0, every deterministic score vector p and respondent flags r**, for **every sign vector e**, H(p,r,e)-50=n⁻¹Σⱼwⱼ(p,r)ε(eⱼ); signProductLaw n is a probability; under that law E H=50 and Var H=Σⱼwⱼ²/n². This includes the case of no respondents, where all weights are zero.

## T15

First, for **every probability space and iid Q-distributed Z**, if C(firstSampleₙ) and B_C(firstSampleₙ) are each in L² for **every n**, MatchingFailure(true) holds. Second, independently, for **every iid Q-distributed Z on a probability space**, the clipped estimated intercept α̂(firstSampleₙ) converges in probability to 1/4, with no extra moment premises on this second clause.

## T16

Five clauses. (1) For every iid Q-distributed Z on a probability space, with C_est(firstSampleₙ) and B_C_est(firstSampleₙ) in L² for every n: E C_est=0 for every n>0, n Var C_est→V, E[n B_C_est]→VB, 0<VB<V, and n B_C_est does not converge in probability to V. (2) Under just the iid Q law, α̂→1/4 in probability. (3) For **every natural n, every sample s, every donor-flag vector r and index i**, nearestDonor using the estimated scores equals nearestDonor using the original scores. (4) For **every natural n and every sample s**, C_est(s)=C(s); this universal equality also applies to every resample. (5) For **every n>0, score vector p and treatment vector d**, for every sign vector e, C(p,d,e)=-n⁻¹Σⱼwⱼ(p,not d)ε(eⱼ); signProductLaw n is a probability and under it E C=0, Var C=Σwⱼ²/n². This includes no-control samples.

## Placebo definitions for T17–T18

The 12 states i have X=-1,0,1 according as ⌊i/4⌋=0,1,2; Z=-1 for i mod 4<2 and +1 otherwise; D=i mod 2; W=X²+Z/2. Each middle-group even state has probability 1/8, each middle-group odd state 1/24; the outside groups reverse these probabilities. Thus X is uniform on {-1,0,1}, Z is a conditionally independent fair sign, and treatment success probabilities are 3/4,1/4,3/4. The regressor vector R=(1,X,W) has moment matrix G=E RRᵀ, and r(a,b,c)=E(D-a-bX-cW)², all finite sums.

For an iid state sequence Zᵢ, Fₙ is the ordinary one-placebo F statistic comparing D on (1,X) to D on (1,X,W), as defined above; Wₙ is β̂_W² divided by the W,W entry of the HC0 covariance matrix of that full regression. Definitions assign totalized values even to singular or zero-residual samples.

## T17

First, for **every probability space and iid measurable state sequence with common law placeboLaw**, the theorem asserts the two finite conditional independences W ⟂ D | X and (2+Z,3+Z) ⟂ D | X; det G=17/54; and **for every real a,b,c**, r(29/68,0,4/17)≤r(a,b,c) with equality iff (a,b,c)=(29/68,0,4/17). Almost surely Fₙ/n→64/531 and Wₙ/n→18496/135315 (the a.s. assertions are separate). For **every α∈(0,1) and every real critical-value sequence cₙ**, if **for every n>3**, P_{F(1,n-3)}{z≤cₙ}=1-α, then Pμ{Fₙ>cₙ}→1. For **every fixed real c**, Pμ{Wₙ>c}→1. In addition, 240r(7/12,0,0)=175/3, 240r(29/68,0,4/17)=885/17, and the displayed one-restriction F arithmetic with residual divisor 237 equals 5056/177.

Second, **without hypotheses on a sample sequence**, both conditional independences hold; for every state i, the conditional treatment mean given its X lies strictly between 1/8 and 7/8, and Var(W|X=Xᵢ)=1/4 (using the finite conditional means); det G=17/54; the full unique risk minimizer is (29/68,0,4/17); the restricted c=0 unique minimizer is (7/12,0,0); their risks are 59/272 and 35/144 respectively, with strict improvement and 4/17≠0. The 240 equalities are identities of population risks, not an existential assertion about an actual finite sample.

## T18

For **every probability space, natural K,L, measurable vector X,W and real D**, assume D∈{0,1} everywhere, 0<P(D=1)<1, every coordinate of X and W belongs to L², W ⟂ D | X in the indicator conditional-expectation sense, and a supplied γ∈ℝ^(K+1) has m(X)=γ₀+Σγₖ₊₁Xₖ as a CEF of D given X. Also assume the full population moment matrix of (1,X,W) has nonzero determinant. Then (a) m(X) is a CEF of D given (X,W); (b) **for every intercept a, vector b and vector c**, E(D-m(X))²≤E(D-a-b·X-c·W)²; (c) equality of those risks holds **iff** a=γ₀, each bₖ=γₖ₊₁, and every cₖ=0.

An independent unconditional conjunct asserts W ⟂ D | X for the fixed placeboLaw above, 4/17≠0, and that its full unique risk minimizer is (29/68,0,4/17). No sample asymptotic or joint-test calibration conclusion occurs.

## T19

Without hypotheses, define tₖ=(1/3)^(k+1), cₖ=(1/2)^(k+2), and eₖ=tₖ/(tₖ+cₖ). The theorem asserts both mass sequences are summable, each sums to 1/2, **for every natural k** both cell masses are positive and 0<eₖ<1, and **there does not exist a real ε>0 such that for every k**, ε<eₖ<1-ε. This is an explicit countable mass witness without a separately defined support predicate, a specified covariate embedding, or an asserted numerical rate for eₖ.
