# Blind reading of SAP.P010.T6–T10

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. Sources: `closure.json`, the current Challenge docstrings and statements, every source definition in the five closures, and Lean `#print` of every generated closure declaration in `scratch/BlindPrint.lean`. No proof implementation was used to infer a statement's meaning.

## Shared notation, fully expanded definitions

For natural numbers K,d, the measurable state space is
Ω = (Fin K → ℝ) × (Fin K → Bool) × Fin K × (Fin d → ℝ), with its product measurable structure. Write a state as (y,s,z,x). Thus y is a finite vector of real potential responses, s a vector of Boolean potential check results, z the assigned arm, and x a finite real covariate vector. The definitions used below are:

- `potentialOutcome a` = y(a); `potentialCheck a` = s(a); `arm` = z; `response` = Y = y(z); `check` = S = s(z).
- `assigned a` = Z_a = {z=a}; `passed` = P = {s(z)=true}; `wouldPass a` = P_a = {s(a)=true}; `allPass` = A = {∀a, s(a)=true}; `sameCheck` = C = {∀a b, s(a)=s(b)}.
- For any measure μ, real measurable function f and event E, write m_μ(f;E) = (∫ f d(μ restricted to E))/(μ(E)).toReal. This is exactly `meanOn`, a restricted Bochner integral divided by a real event mass, not a conditional-expectation random variable.
- `passRate μ a` = p_a = μ(P∩Z_a).toReal / μ(Z_a).toReal.
- `randomAssignment μ` means, for every arm a separately, the random pair (y(a),s(a)) is independent of z, and μ(Z_a)>0 for every a. Mathlib `IndepFun` means independence of the inverse-image sigma-algebras; equivalently the probability factorization for all measurable events of these random variables. It does not assert independence of the whole vector ((y(a),s(a)))_a from z.
- `positivePassRates μ` means ∀a, 0<p_a. `populationAssumptions μ` is the conjunction: μ is a probability measure, `randomAssignment μ`, and `positivePassRates μ`.
- `conditionalLaw μ f E` = μ(E)⁻¹ • (μ restricted to E).map f. In probabilistic notation this is the distribution of f conditional on E, when 0<μ(E)<∞ and f is measurable. `passerDistribution μ a` = F_a = conditionalLaw μ Y (P∩Z_a).
- `trimmingRatio μ a` = r_a = (∑_{b∈Fin K, b≠a}(1-p_b))/p_a. The subtraction here is real subtraction.
- `noAtoms F` means F({t})=0 for every real t. In particular `noAtoms (μ.map Y)` is continuity of the entire observed response law, not merely of the passer law.
- `fullRealSupport μ f` means μ({l<f<u})>0 for every real l<u.
- `leftQuantile F u` = Q_F(u) = inf {t∈EReal : u ≤ F({y∈ℝ : (y:EReal)≤t}).toReal}, an extended-real infimum. For a probability law and 0<u<1 it is the ordinary left quantile.
- `lowerEndpoint μ a` = L_a = m_μ(Y; P∩Z_a∩{Y≤Q_{F_a}(1-r_a)}), where Y is cast to EReal for the comparison.
- `upperEndpoint μ a` = U_a = m_μ(Y; P∩Z_a∩{Q_{F_a}(r_a)≤Y}).
- `upperTailMean F u` = (∫_{Q_F(u)≤y} y dF)/F({Q_F(u)≤y}).toReal.
- `passerEssentialInf μ a` = e_a = essInf_{F_a}(y↦(y:EReal)); `passerEssentialSup μ a` = f_a = essSup of the same function. These use the a.e. filter's liminf/limsup in the complete lattice EReal, so unbounded endpoints really can be −∞ or +∞.
- `compatiblePopulations μ ν` means ν satisfies the population assumptions, ν(A)>0, and ν.map (Y,S,z)=μ.map (Y,S,z). Covariates are absent from this observed-law equality.
- `compatibleMeans μ a` = M_a = {m∈ℝ : ∃ν on the same Ω, ν satisfies those compatibility conditions and m_ν(y(a);A)=m}. `extendedCompatibleMeans μ a` = { (m:EReal) : m∈M_a }.
- `correctedEndpoints μ a` = (L_a,U_a), embedded into EReal, if r_a<1, and (e_a,f_a) otherwise.
- For K=2,d=0, `effectIntervalWidth μ` = W(μ) = (U_1−L_0)−(L_1−U_0). This is the width formed from the finite trimmed endpoints; its definition does not switch to essential endpoints.

These expansions apply independently to each of the following sections.

## SAP.P010.T6

Location: Challenge/Part1.lean:30–32; statement Defs/Part6.lean:74–90. The docstring calls these corrected else-branch bounds, identifies them with passer essential endpoints, and says they are sharp as extrema and unattained when finite.

Quantifiers, in order: for every K,d∈ℕ, every measure μ on Ω, every proof that μ is a probability measure with the per-arm independence and positive arm/pass probabilities above, every a∈Fin K, every proof μ(A)>0, every proof that μ.map Y has no atoms, every proof that Y is Bochner integrable for μ restricted to P∩Z_a, and every proof 1≤r_a, the following conjunction holds:

1. 1≤r_a iff ∑_b p_b ≤ (K:ℝ)−1.
2. e_a ≤ (m_μ(y(a);A):EReal) ≤ f_a.
3. For every real l, e_a=(l:EReal) implies l<m_μ(y(a);A). Separately, for every real u, f_a=(u:EReal) implies m_μ(y(a);A)<u.
4. e_a is a greatest lower bound and f_a a least upper bound of { (m:EReal) : ∃ν satisfying the population assumptions, ν(A)>0, equality of the observable joint laws (Y,S,z), and m=m_ν(y(a);A) }.
5. Every finite e_a or f_a, written as a real l or u respectively, is absent from M_a.
6. The assertions that −∞ is a greatest lower bound and +∞ a least upper bound of that same set are jointly equivalent to the two-sided tail condition: for every real M, F_a((−∞,M))>0 and, separately, for every real M, F_a((M,∞))>0.

The statement does not assert that M_a is an interval, that either finite essential endpoint is attained, or that the endpoints are always infinite. Integrability of every compatible mean is not an explicit field of compatibility; the source puts only population assumptions, positive always-passer mass and observable-law equality there. Whether integrability follows from those and the target's integrable observed passer law needs to be checked during fidelity review.

Junk-value audit: all actual μ masses are finite by the probability assumption; μ(Z_a)>0 and p_a>0 prevent all displayed pass-rate divisions and conditional-law normalizations from having zero denominators. μ(A)>0 prevents a zero conditioning mass for the target mean and for every compatible mean. A nonintegrable Bochner integral is nevertheless defined as zero in Lean; the assumed observed passer integrability and independence must be used to justify the target and compatible potential means. Nonatomicity excludes atoms at finite essential extrema. EReal infima/suprema preserve genuine infinite bounds; no EReal.toReal is used for these extrema. Empty/unbounded sets have their complete-lattice infima/suprema, but the sharpness set has the original μ as a candidate, subject to its integrable mean. K=0 gives an empty population space, admitting no probability measure; K=1 gives r_a=0 and cannot satisfy this else-branch hypothesis. These do not render K≥2 cases empty. d=0 is harmless. `(K:ℝ)−1` casts K first and then subtracts in ℝ; there is no truncated natural subtraction. No logarithm, square root, real power, or partial-function default appears in this closure.

## SAP.P010.T7

Location: Challenge/Part1.lean:34–38; statement Defs/Part6.lean:92–102. The docstring describes a four-state counterexample to a joint-vector independence step while preserving Corollary 1's mean identity.

There are no input hypotheses or universal data variables. Define μ on Population 2 0 by summing four Dirac measures, each with extended-nonnegative-real weight ENNReal.ofReal(1/4):

| (y(0),y(1)) | (s(0),s(1)) | z |
|---|---|---|
| (0,0) | (true,true) | 0 |
| (1,1) | (true,true) | 0 |
| (0,1) | (true,true) | 1 |
| (1,0) | (true,true) | 1 |

The covariate function has domain Fin 0, hence is uniquely the empty function. `finitePopulation atoms mass` is exactly Measure.sum (i↦mass(i) • Measure.dirac(atoms(i))); the definition alone imposes no normalization but these four weights sum to one.

The conclusion is the conjunction:

1. μ is a probability measure, each (y(a),s(a)) is independent of z, each arm has positive mass, and each arm has positive observed passing rate.
2. μ(C)=1 and μ(A)=1.
3. The pair ((y(a))_{a∈Fin 2},S) is NOT independent of z.
4. μ({y(0)=0,y(1)=0,S=true,z=0})=1/4.
5. μ({y(0)=0,y(1)=0,S=true})·μ(Z_0)=1/8.
6. m_μ(Y;P∩Z_0)=1/2; m_μ(Y;P∩Z_1)=1/2; m_μ(y(0)−y(1);A)=0.

Thus the observed contrast and always-passer contrast coincide, despite failure of independence of the entire potential-outcome vector. The statement refutes the vector independence inference, not the equality of these contrasts.

Junk-value audit: the only ENNReal.ofReal argument is positive 1/4, so no negative-weight truncation occurs. Fin 2 indices 0,1 and the four-entry vector are in range. The finite summation is nonempty and all displayed events have masses 1,1/2, or1/4 as appropriate. All outcomes are bounded and thus integrable. All actual conditional means have positive masses; no division-by-zero, infinite toReal, empty infimum, quantile, sqrt, log or rpow occurs. d=0 affects only the unused covariate vector. The negative independence assertion is certified by an ordinary positive-mass factorization failure, not by missing measurability.

## SAP.P010.T8

Location: Challenge/Part1.lean:40–42; statement Defs/Part4.lean:50–61. The docstring asserts arm-by-arm independence, positive passing probabilities and the conditional-mean identities used in Corollary 1.

Quantifiers, in order: for every K,d∈ℕ, every μ on Ω, proof of the population assumptions, proof μ(C)=1, every a∈Fin K and proof that y(a) is Bochner integrable for μ, the following conjunction holds:

1. S=s(a), μ-almost everywhere.
2. (y(a),S) is independent of z under μ.
3. For every t∈Fin K, p_t=μ(P).toReal and 0<p_t.
4. P=A μ-almost everywhere (equality of the event indicators).
5. m_μ(Y;P∩Z_a) = m_μ(y(a);P∩Z_a).
6. m_μ(y(a);P∩Z_a) = m_μ(y(a);P).
7. m_μ(y(a);P) = m_μ(y(a);A).

There is no independence assertion for the full vector of potential outcomes. It does not separately state an equality between the difference of two observed means and an expected difference of potentials, though its per-arm identities imply that under the corresponding integrability assumptions.

Junk-value audit: probability and positive arm/pass rates give positive finite μ(P∩Z_a); common checks plus positive passing give μ(P)=μ(A)>0. The integrability of y(a) for μ implies integrability on the displayed subsets. Y=y(a) on Z_a, so observed integrability for that restricted arm also follows without assumptions on other arms' outcomes. No mean is taken on a null event. K=0 cannot support the required probability; for K≥1 these assumptions are plainly satisfiable. d=0 is permitted without affecting any event. There are no quantiles, extrema, real powers, logarithms, square roots, truncated subtraction, or partial-function defaults in this closure.

## SAP.P010.T9

Location: Challenge/Part1.lean:44–47; statement Defs/Part6.lean:104–129. The docstring describes the specified two simulation designs, their different observable passer laws, and different population bound widths, as a counterexample to a printed comparison.

The simulation definitions, expanded: for real p₁,p₂,ρ,λ,σ put
b=√(p₁(1−p₁)p₂(1−p₂)), a=p₁p₂+ρb. Let ε have the Gaussian probability measure `gaussianReal 0 ⟨σ²,sq_nonneg σ⟩` (mean zero, variance σ²) and let z be independent with mass 1/2 at each arm. For each Boolean stratum (s₁,s₂), push this product law forward to the state with s=(s₁,s₂), y(0)=y(1)=λ(1_{s₂}−1_{s₁})+ε, and the same z. `simulationPopulation` sums these four pushforwards with weights ENNReal.ofReal(1−p₁−p₂+a), ENNReal.ofReal(p₁−a), ENNReal.ofReal(p₂−a), ENNReal.ofReal(a), in the order (false,false), (true,false), (false,true), (true,true). The covariate vector is empty. `fairArmDistribution` is the two Dirac masses of size 1/2 just described.

`checkCorrelation μ 0 1` is [μ(P_0∩P_1).toReal−μ(P_0).toReal·μ(P_1).toReal]/√[μ(P_0).toReal(1−μ(P_0).toReal)μ(P_1).toReal(1−μ(P_1).toReal)]. This is Pearson correlation of the two Bernoulli checks when their variances are positive.

Write μ_ρ for that simulation at p₁=p₂=4/5, λ=σ=1. Define N_w=(1−w)·N(0,1)+w·N(−1,1), with scalar coefficients formally ENNReal.ofReal. Define l(w)=(∫_{y≤Q_{N_w}(3/4)}y dN_w)/N_w({y≤Q_{N_w}(3/4)}).toReal and u(w)=(∫_{Q_{N_w}(1/4)≤y}y dN_w)/N_w({Q_{N_w}(1/4)≤y}).toReal.

There are no hypotheses. The conclusion is:

1. For every real ρ in the two-element set {1/4,1/2}, μ_ρ satisfies the population assumptions, μ_ρ(A)>0, μ_ρ.map Y is atomless with positive mass in every nonempty open interval, checkCorrelation(μ_ρ,0,1)=ρ, p_0=p_1=4/5 and r_0=r_1=1/4.
2. μ_{1/4}(A)=17/25 and μ_{1/2}(A)=18/25.
3. F_0 for these two designs is respectively N_{3/20} and N_{1/10}; F_1 is respectively the reflection y↦−y of those same laws.
4. The two mixture means are −3/20 and −1/10. The integrals of (y+3/20)² and (y+1/10)² for their respective mixtures are 451/400 and 109/100.
5. W(μ_{1/4})=2(u(3/20)−l(3/20)) and W(μ_{1/2})=2(u(1/10)−l(1/10)). Here W is the endpoint expression (U_1−L_0)−(L_1−U_0) fully expanded in the shared definitions, with passer-conditioned lower 3/4 and upper 3/4 response means.
6. W(μ_{1/4}) lies in the closed real interval [1798577298898/10¹²,1798577299027/10¹²], and W(μ_{1/2}) lies in [1767983385194/10¹²,1767983385319/10¹²].
7. Their difference W(μ_{1/4})−W(μ_{1/2}) is strictly greater than 30593913580/10¹².

This is about population widths, not averages of finite-sample estimates. Both true potential outcomes agree pointwise, so the true unit treatment effect is zero in these designs.

Junk-value audit: for the two specified correlations, b=4/25, a=17/25 or18/25. Stratum weights are respectively (2,3,3,17)/25 and (3,2,2,18)/25, so ENNReal.ofReal truncates nothing and all strata have positive mass. Arm masses are 1/2 and passer masses are2/5. Gaussian variance is one; all moments used here exist. The Bernoulli correlation denominator b is strictly positive. Every Gaussian mixture has a positive continuous density on ℝ, making its 1/4 and3/4 quantiles finite and its selected tail masses exactly3/4. Thus no endpoint mean uses a null event or nonintegrable integral. EReal quantiles are not converted to reals. Every rational displayed has positive denominator (including10¹²). No empty index types other than the unused Fin 0 covariates, no natural truncated subtraction, no log/rpow, no empty/unbounded real infima, and no partial-function defaults affect these calculations.

## SAP.P010.T10

Location: Challenge/Part1.lean:49–52; statement Defs/Part6.lean:131–160. The docstring says bounds are invariant at a fixed observable law, that a feasible correlation change with λ≠0 changes the simulation's passer laws and means, and that the two specified designs have different widths.

Quantifiers, in order: for every real p₁,p₂,ρ,λ,σ, proofs 0<p₁<1 and0<p₂<1, proof0≤σ, and the four feasibility inequalities
0≤1−p₁−p₂+a, a≤p₁, a≤p₂, 0≤a,
where a=p₁p₂+ρ√(p₁(1−p₁)p₂(1−p₂)), the following conjunction holds:

1. For all natural K,d and measures μ,ν on Population K d, if both satisfy the population assumptions, then for every arm t, equality of the entire pass-rate functions p(μ)=p(ν) and equality of that arm's conditional observed passer distributions F_t(μ)=F_t(ν) imply equality of `correctedEndpoints`. Explicitly, compute r_t from all pass rates; when r_t<1 the pair is the two restricted tail integrals divided by their masses described above, and otherwise it is the EReal essential infimum/supremum of the identity for F_t. This universal assertion is nested under the outer scalar feasibility hypotheses, even though its content does not depend on the scalars.
2. Put w₁=1−a/p₁, w₂=1−a/p₂ and μ=simulationPopulation p₁ p₂ ρ λ σ, expanded exactly in the T9 section. Then μ satisfies the population assumptions, μ(A).toReal=a, its check correlation isρ, and its arm passing rates arep₁,p₂. Its passer law in arm0 is (1−w₁)N(0,σ²)+w₁N(−λ,σ²); in arm1 it is (1−w₂)N(0,σ²)+w₂N(λ,σ²), with all coefficients formally ENNReal.ofReal. The two corresponding conditional observed means are −λw₁ andλw₂.
3. If λ≠0, then for every real ρ′ with ρ′≠ρ, both of the real expressions
−λ(1−[p₁p₂+ρ′b]/p₁) and λ(1−[p₁p₂+ρ′b]/p₂)
are unequal to their respective values atρ. No feasibility assumption is made aboutρ′ in this algebraic clause. For feasibleρ′ the preceding simulation formula applies a second time, so these expression inequalities imply different conditional means and hence different passer laws.
4. W(simulationPopulation(4/5,4/5,1/4,1,1)) ≠ W(simulationPopulation(4/5,4/5,1/2,1,1)), independently of the outer scalar data. W is the finite-endpoint width, not an empirical width or an unqualified assertion that every correlation change changes width.

Junk-value audit: 0<p_i<1 makes b strictly positive; all real divisions byp_i are valid. The four feasibility inequalities make all stratum weights nonnegative and their sum one, so ENNReal.ofReal introduces no artificial deletion. Zero stratum weights and a=0 are allowed: the statement does not form a conditional mean on A for this simulation, and does not require μ(A)>0 here. Each arm still has positive mass and each observed passer event has massp_i/2>0. σ=0 is allowed and Mathlib's gaussianReal with zero variance is the Dirac mass at its mean, a proper probability law with finite moments; it is not an undefined density. The correlation's denominator is positive. The comparison expressions at infeasibleρ′ remain defined real affine expressions; the statement does not identify them with means of infeasible simulations. The inner fixed-law assertion has no nonatomicity or integrability hypothesis: its `correctedEndpoints` uses the same Lean-totalized integrals and quantiles on both sides; on laws where ordinary tail means do not exist it remains a formal equality of these totalized definitions. Usual integrability would make those actual ordinary bounds. Finite endpoints are computed only in the r<1 branch, but at atoms the inclusive quantile definitions need separate semantic scrutiny as bounds. All finite selected examples in the last clause have nonzero variance and continuous positive densities as in T9. No EReal.toReal is used, no natural truncated subtraction/log/rpow/partial-function default appears. Empty K cannot satisfy the inner probability assumptions; d=0 is legitimate.

## Closure completeness and totalization checklist

All source declarations named by closure.json were read. In addition, all30 line-zero generated declarations were printed and read using scratch/BlindPrint.lean: the T3Statement proof1–4, T5Statement proof6 and9, T7Statement proof1, T8Statement proof1, T9Statement proof1–14, T10Statement proof1–2, and the conditionalLaw, jointDependenceAtoms, jointDependencePopulation, laplaceDistribution, selectionPopulation and simulationPopulation proof auxiliaries. They supply only numeral/index instances (`NeZero`, `AtLeastTwo`), the measure's `OuterMeasureClass`, scalar associativity, or the proof σ²≥0 used to construct a nonnegative Gaussian variance. They impose no statistical assumptions and encode no substantive conclusion. Their reused source names do not add those unrelated statements to these targets.

General totalizations audited above: real division by zero gives zero; ENNReal.toReal(∞)=0; ENNReal.ofReal clips negative real inputs to zero; an ENNReal inverse at zero is∞, and a zero-event conditionalLaw is the zero measure under the measurable maps used here. Measure.map is totalized in Mathlib outside its a.e.-measurable domain; all maps in these closures are measurable coordinate/finite-branch continuous maps. A nonintegrable Bochner integral is zero. EReal sInf of the empty set is+∞ and sSup of the empty set is−∞. For a probability law Q(u)=−∞ when u≤0, can be+∞ at u=1 for unbounded support, and is+∞ when u>1; these extended endpoints preserve the intended comparison sets rather than being silently cast to zero. essInf/essSup in EReal give genuine unbounded extrema rather than the real conditionally-complete-lattice junk values. None of these targets uses sequence limsup/liminf, an unsafe cast of an infinite EReal, a logarithm, rpow, or a partial function.
