# Blind reading

Written before opening `claims.json` or `record.json`. Sources read: the two target docstrings and statements in `SAP/P015a/Challenge/Part1.lean`; all source declarations listed in each target's `closure.json` entry; the relevant Mathlib definitions of conditional expectation and convergence in measure. All 24 generated proof auxiliaries in the closures were printed by `scratch/ClosureProofs.lean` and read. They are numeral/nonzero-index instances and the scalar-tower instance for extended nonnegative real multiplication, with no statistical assumptions. There is no workspace `AGENTS.md`.

## SAP.P015a.T4

### Objects, definitions, and quantifiers

There are no outer data hypotheses: this is a closed conjunction of universal assertions and assertions about explicit finite examples. The universal assertions range over arbitrary types Ω and B (at the declared universes), measurable spaces on both, a measurable-singleton structure and a countability instance on B, a probability measure P on Ω, measurable maps X : Ω → B and D : Ω → ℝ, and `MemLp D 2 P` (D is almost everywhere strongly measurable and its L² seminorm is finite). Every cell assertion subsequently ranges over x : B with P(X=x)>0. Endpoint assertions subsequently quantify over arbitrary real d,d′ with d≠d′.

Here are the measure-based definitions, fully expanded into Mathlib operations. Put Cₓ={s | X(s)=x} and Qₓ=P(Cₓ)⁻¹·(P restricted to Cₓ), with the inverse and scalar multiplication in ℝ≥0∞. Put μₓ=∫D dQₓ, vₓ=∫(D−μₓ)² dQₓ, and pₓ(d)=(Qₓ{D=d}).toReal. The weight at s is w(s)=(D(s)−μ_{X(s)})². Write Z=∫w dP. The effective measure is Q=(ENNReal.ofReal Z)⁻¹·P.withDensity(s↦ENNReal.ofReal(w(s))). None of these definitions imposes its own hypotheses.

For every set of data just described the conjunction asserts:

1. For every positive-probability x and every distinct d,d′, pₓ(d)>0 and pₓ(d′)>0 imply vₓ>0. If vₓ=0, then D=μₓ Qₓ-almost surely. A second universal clause explicitly gives vₓ=0 ⇒ ¬(pₓ(d)>0 ∧ pₓ(d′)>0) for every distinct pair.
2. If D∈{0,1} P-almost surely, then for every positive-probability x, vₓ=pₓ(1)(1−pₓ(1)), and vₓ>0 iff 0<pₓ(1)<1. The additional clause states pₓ(0)=1−pₓ(1) and vₓ>0 iff pₓ(0)>0 and pₓ(1)>0.
3. If Z>0 and w is P-integrable, then for every positive-probability x,
   Q(Cₓ).toReal=P(Cₓ).toReal·vₓ/Z, and Q(Cₓ)=0 iff vₓ=0. If D is binary and 0<pₓ(1)<1, its conditional probabilities under Q are Q(D=1 | Cₓ)=1−pₓ(1) and Q(D=0 | Cₓ)=pₓ(1), where conditioning again uses the normalized restricted measure. The second universal clause also asserts Q is a probability measure; if D is binary and Q(Cₓ)>0, then vₓ>0 and both Q-conditional endpoint probabilities are positive.

These facts appear in two separately quantified blocks (`positivityRepair` and the remaining conjunct of `T4Statement`); their hypotheses are the same except for the explicitly displayed branch hypotheses. `positivityRepair` also contains each of the following three finite examples as unconditional conjuncts, independently of the universal data.

### Finite definitions used by all examples

For a finite type A, real weights p:A→ℝ and Z:A→ℝ, the mean is exactly Σₐ p(a)Z(a); a probability vector means every p(a)≥0 and Σₐp(a)=1. The mass of an event E is Σₐ(if E(a) then p(a) else 0). The conditional mean at x is Σₐp(a)(if X(a)=x then Z(a) else 0) divided by the event mass of X=x. A conditional treatment probability is the mass of X=x,D=d divided by the mass of X=x. The residual weight is (D(a)−conditional mean of D at X(a))². The effective vector is p(a) times this weight divided by its p-mean. Conditional independence means, for every x,u,d, mass(X=x,U=u,D=d)·mass(X=x)=mass(X=x,U=u)·mass(X=x,D=d). This is finite conditional independence expressed without denominators.

The effect contrast at d,d′ is [Y(a,d′)−Y(a,d)]/(d′−d). The IPW random variable at a is D(a)Y(a)/e(a)−(1−D(a))Y(a)/(1−e(a)). Variance of Z is Σₐp(a)(Z(a)−Σᵦp(b)Z(b))². Population OLS coefficients for a real matrix W indexed by finite observation and coefficient types are G⁻¹b, where Gⱼₖ=Σᵢp(i)WᵢⱼWᵢₖ and bⱼ=Σᵢp(i)WᵢⱼYᵢ. Sample least squares is (WᵀW)⁻¹WᵀY. These are Mathlib's total matrix inverses. A fitted residual for controls V and coefficient vector ω is D−Vω. The law on a sample a:Fin n→A is ∏ᵢp(aᵢ); its empirical mean is (ΣᵢZ(aᵢ))/(n:ℝ).

In all finite examples A=Fin 4, X=(0,0,1,1), and the binary treatment is D=(0,1,0,1). Fin 4 means exactly the four indices 0,1,2,3.

### Rare-overlap example, including all embedded assertions

Put pε=((1−ε)/2, ε/2, 1/4, 1/4), Y(a,d)=2X(a)+(1+X(a))d, eε(a)=ε+(1/2−ε)X(a), and Hε(a)=D(a)Y(a,D(a))/eε(a)−(1−D(a))Y(a,D(a))/(1−eε(a)). Let ε₀=1/1000000.

At ε₀ the assertion is the following conjunction:

- pε₀ is a probability vector; Y(a,d)=Y(a,0)+(1+X(a))d for every a and real d; (Y(a,0),1+X(a)) is conditionally independent of D given X in the finite mass-product sense above.
- For x∈{0,1}, E[D|X=x]=ε₀+(1/2−ε₀)x and both endpoint conditional probabilities are strictly positive.
- E[w|X=0]=999999/1000000000000, E[w|X=1]=1/4; the nominal mass of X=0 is 1/2 and its effective mass is 999999/250000999999<1/250000.
- Hε₀=(0,1000000,−4,8). The nominal mean effect E[1+X]=3/2 equals E[Hε₀]. E[Hε₀²]=500020 and Var(Hε₀)=2000071/4. The effective mean effect is 500000999999/250000999999, which differs from 3/2.
- With Wᵢ=(1,Dᵢ,Xᵢ), the nominal population Gram determinant is nonzero and the actual population OLS treatment coordinate (index 1) equals 500000999999/250000999999.
- For every natural n≥1, the n-fold product sample weights are a probability vector, the sample mean of Hε₀ has expectation 3/2 and variance 2000071/(4n), and for every real δ>0 the mass of |sample mean−3/2|≥δ is at most 2000071/(4nδ²).
- For every real δ>0, that deviation mass tends to zero along n→∞. This last limit quantifies over all n:ℕ in the sequence (including the harmless n=0 term), with the usual `atTop` filter and real neighborhood of zero.

Separately, for every real ε, first assuming 0<ε and then ε<1/2, pε is a probability vector, the same potential-outcome decomposition and conditional independence hold, and at x∈{0,1} its conditional treatment mean is ε+(1/2−ε)x and both endpoint probabilities are positive. The effective mass of X=0 is ε(1−ε)/(ε(1−ε)+1/4), is strictly positive, and is less than 4ε. The theorem does not state estimator moment or consistency formulas for every ε.

### Multivalued-support example, including all embedded assertions

Use p=(1/4,1/4,1/4,1/4), X=(0,0,1,1), and now D=(0,1,0,2). World A has Y_A(a,d)=d. World B has Y_B(a,d)=3 if X(a)=1 and d=1, and Y_B(a,d)=d otherwise. Observed triples are (X(a),D(a),Y(a,D(a))).

The theorem asserts p is a probability vector, E[D|X=X(a)]=1/2+X(a)/2 at every a, the residual weights are (1/4,1/4,1,1), all are strictly positive, their mean is 5/8, and the effective vector is (1/10,1/10,2/5,2/5) with covariate masses 1/5 and 4/5. The conditional probability of D=1 at X=1 is zero under each law. In each world the triple (Y(a,0),Y(a,1),Y(a,2)) is conditionally independent of D given X. Every observed outcome in both worlds equals D. The nominal 0-to-1 mean contrasts are respectively 1 and 2, and their effective means are respectively 1 and 13/5.

For every real d, positive conditional probability of D=d at both x=0 and x=1 is equivalent to d=0, both under p and under the effective vector.

There is also a universal no-common-consistency assertion (its sample-space universe is instantiated at 0 in T4). For every measurable sample space Ω, probability P, draw:ℕ→Ω→Fin 4, and statistic family T assigning a real value to each finite sequence of observed real triples, assume every draw is measurable, the draws are mutually independent (`iIndepFun draw P`), and P(drawᵢ=a)=ENNReal.ofReal(1/4) for all i,a. It is impossible that the world-A statistic converges in P-measure to 1 and the world-B statistic converges in P-measure to 2; likewise impossible with world-B target 13/5. Convergence in measure here is Mathlib's condition that, for every positive extended-real distance threshold, the measure of the set whose extended distance from the constant target is at least that threshold tends to zero. The observed data fed to T are pointwise identical across worlds. T itself has no explicit measurability hypothesis; its domain at each n is finite, and the resulting statistic on measurable draws is measurable. Independent replicates are required rather than implicitly replaced by repetitions of one draw.

### Fitted-zero example, including all embedded assertions

The population has uniform p and the binary X,D vectors. Every conditional endpoint probability at x∈{0,1} is 1/2 and every conditional residual second moment there is 1/4. The explicit ordered sample of population indices is a=(0,0,2,3). Its product-law probability is (1/4)^4=1/256>0. Its controls matrix V has rows (1,0),(1,0),(1,1),(1,1); its treatment vector is (0,0,0,1). Each row's covariate and treatment are explicitly related to X(aᵢ),D(aᵢ).

VᵀV=[[4,2],[2,2]], VᵀD=(1,1), and [[4,2],[2,2]](0,1/2)=(1,1). Its determinant is nonzero. The fitted residual at (0,1/2) is (0,0,−1/2,1/2), whose componentwise square is (0,0,1/4,1/4). Actual total-inverse least squares equals (0,1/2) and gives those same residuals. The full matrix with rows (1,0,0),(1,0,0),(1,0,1),(1,1,1) has Gram matrix [[4,1,2],[1,1,1],[2,1,2]] with determinant 2. No response vector or causal outcome model is asserted for this fitted-zero example.

### Junk-value and boundary conventions

- Real division by zero is zero. The finite conditional definitions give zero at zero-mass cells, the effective vector gives zero if the weight mean is zero, IPW is total at propensities 0 or 1, and effect contrasts are zero when d=d′. In the actual example assertions all evaluated conditioning cells have positive mass, every IPW propensity is strictly between zero and one, every contrast uses 0,1, and the effective-weight means are positive. No such zero division affects those assertions.
- The probability-vector definition itself allows zero atom masses. For an empty finite type its sum is 0, so its probability-vector condition cannot hold. Here every example has four strictly positive atom masses; sample spaces (Fin n→Fin 4) are nonempty, also when n=0.
- The sample mean at n=0 is 0/0=0 and the empty product sample law assigns its unique sample weight 1. All exact sample-size moment and bound assertions assume n≥1. The consistency statement includes n=0 as one initial term, which cannot alter an `atTop` limit. Casts of n into ℝ are the ordinary nonnegative natural casts, strictly positive under n≥1. There is no natural/integer truncated subtraction in these formulas.
- In ℝ≥0∞, 0⁻¹=∞ and ∞⁻¹=0; multiplying a zero measure by ∞ yields a zero measure. Thus the normalized restricted law at a null cell is a zero-law convention, and an infinite-mass cell would also be problematic. Every asserted original cell has 0<P(Cₓ)≤1. Effective-cell probabilities used by the reversal formula have positive, finite normalizers. Nonempty effective profiles are explicitly required or follow from binary overlap.
- Bochner integrals of nonintegrable functions are defined as zero. For a positive original cell, global L² and finite P imply that D and its centered square are integrable for the normalized cell. The effective-law branches additionally require w integrable and Z>0. Finite examples have finite sums and finite values, so no nonintegrable integral is used there.
- `ENNReal.ofReal` truncates negative real arguments to zero. The squared weight is nonnegative and its asserted normalizer is positive. `ENNReal.toReal ∞=0`; the converted probabilities are finite under the probability and normalization hypotheses. No ∞ conversion is used to create a meaningful zero cell probability.
- Mathlib's nonsingular matrix inverse is total and returns zero for a singular real square matrix. Both uses that matter assert nonzero Gram determinant (the population rare example, and the fitted controls); the full sample Gram has determinant 2. The inverse convention does not masquerade as a fitted coefficient.
- Arbitrary decidable equality on finite conditional cells and predicates is supplied classically. No default choice of a partial function is used. No logarithm, square root, real power outside its domain, supremum/infimum, or limsup/liminf occurs in this closure. The only limits are ordinary filter limits and convergence in measure.

The target docstring describes discrete covariates and finite second moments, advertises the three formal positivity clauses and the explicit examples, and discloses that estimator assertions are fixed at ε₀ and that an empirical country-contribution claim is omitted. This paragraph records the docstring only, without judging it against an unseen claim.

## SAP.P015a.T19

### Objects, quantifier order, and full expansion

For all types Ω:Type u and B:Type v, measurable spaces on each, a measure P on Ω with a probability-measure instance, D:Ω→ℝ, and X:Ω→B, assume in order that D is measurable, X is measurable, and D belongs to L²(P). No finiteness, countability, or measurable-singleton hypothesis on B is imposed.

Let m be the pullback σ-algebra `MeasurableSpace.comap X` of B's measurable space: its sets are preimages under X of measurable sets in B. Let e=P[D|m], Mathlib's conditional expectation as a chosen Ω→ℝ representative. `populationResidualWeight` is the function w(s)=(D(s)−e(s))². `conditionalTreatmentVariance` is the function v=P[w|m]. After fully unfolding these SAP definitions the conclusion is

1. P[(s↦(D(s)−P[D|m](s))²)|m] = P[(s↦(D(s)−P[D|m](s))²)|m], as equality of functions (pointwise, not merely almost everywhere);
2. if D(s)=0 or D(s)=1 for P-almost every s, then P[(s↦(D(s)−P[D|m](s))²)|m](s) = P[D|m](s)(1−P[D|m](s)) for P-almost every s.

The first equality is definitional because the chosen conditional-variance notion is the usual conditional centered second moment. The binary formula is an additional assertion. The theorem docstring describes precisely the conditional squared-residual identity and the binary propensity formula for general measurable covariates and square-integrable treatment.

### Junk-value and representative conventions

Mathlib conditional expectation is a total function. It is zero if the conditioning σ-algebra is not a sub-σ-algebra of the ambient one, if P trimmed to it is not σ-finite, or if the input is not integrable. Otherwise it returns the function itself when already strongly measurable for that σ-algebra, and a chosen strongly measurable representative of the L¹ conditional expectation in the remaining case. These defaults must be checked twice, for D and for w. Here measurable X gives m≤the ambient σ-algebra, probability implies finite and hence σ-finite trimmed measure, and L² gives integrability of D and of its squared centered residual. Thus the defaults do not affect the probabilistic meaning. Choices on null sets are possible; the first equality uses the identical chosen expression, and the binary formula is only almost everywhere, so neither depends on equating arbitrary conditional-expectation versions pointwise.

There are no SAP finite averages, real divisions, matrix inverses, `toReal`, logarithms, square roots, variable real powers, extrema, sequence bounds, partial maps, or index-set sums in this target's closure. The exponent 2 is an ordinary fixed natural exponent. The probability-measure instance excludes an empty Ω (its total measure would be zero), and an X into an empty B cannot exist from a nonempty Ω. Ordinary probability spaces and measurable square-integrable real variables satisfy the assumptions.

The sole generated auxiliary shared into this closure, `T1Statement._proof_2`, states that the numeral 2 is at least two. It changes none of the statistical content.
