# Blind mathematical reading

This file was written from `SAP/P015b/Defs*.lean`, `SAP/P015b/Defs/Part*.lean`, and `SAP/P015b/Challenge/Part1.lean`, before opening either `claims.json` or `record.json`. The declarations below are statements, not evidence supplied by their `sorry` proofs. Universally quantified objects in each paragraph are chosen before the hypotheses and conclusions that follow. Separate conjuncts have their own quantifiers.

## Conventions traced to Mathlib

All numerical scalars below are real unless indicated otherwise. A `Fin n` index has exactly n elements, including no elements when n=0. Matrix multiplication, matrix-vector multiplication, and dot products are ordinary finite sums; matrix `1` is the identity matrix, not an all-ones matrix. Real positive semidefiniteness includes symmetry and a nonnegative quadratic form (`LinearAlgebra/Matrix/PosDef.lean:60`).

`sampleCoefficients(W,Y)` is `(WᵀW)⁻¹WᵀY`. Mathlib's square-matrix inverse is the actual inverse for a nonsingular real matrix and the zero matrix for a singular one (`LinearAlgebra/Matrix/NonsingularInverse.lean:169`). This definition alone does not assert a least-squares minimizing property for singular W. The population version is `(E_p[WWᵀ])⁻¹E_p[WY]`, with the same singular convention.

For a finite index set A, `E_p[Z]=Σ_a p(a)Z(a)`. `IsFiniteLaw p` means every p(a) is nonnegative and their sum is one. `mass_p(E)=Σ_{a:E(a)}p(a)`. A cell mean is `Σ_{X(a)=x}p(a)Z(a)/mass_p(X=x)`; a cell probability is `mass_p(X=x,D=d)/mass_p(X=x)`. Both use real division, so are zero at a zero-mass denominator. Put `w_p(a)=(D(a)-cellmean_p(D|X=X(a)))²`; effective masses are `p*(a)=p(a)w_p(a)/E_p[w_p]`. `finiteUnconfounded p X U D` means, for every x,u,d, `mass_p(X=x,U=u,D=d) mass_p(X=x) = mass_p(X=x,U=u) mass_p(X=x,D=d)`. This is finite conditional independence on positive cells; the identity also makes sense on zero cells. `finiteVariance p Z=E_p[(Z-E_p Z)²]`.

For general probability P, E and conditional E below are Mathlib's Bochner integral and conditional expectation. The integral is defined as zero for nonintegrable functions (`MeasureTheory/Integral/Bochner/Basic.lean:158`). Conditional expectation is defined as zero if the conditioning σ-algebra is not a subalgebra, the trimmed measure is not σ-finite, or the function is not integrable (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:102`). With a measurable X and probability P the first two problems are absent. `P[f|σ(X)]` is a chosen version, and `=ᵐ[P]` means equality outside a P-null set. `σ(X)` is the comap of the target's specified measurable structure, which for real vectors is its Borel structure. `MemLp D 2 P` means almost-everywhere strong measurability and finite L² norm. Mathlib's real variance is the real value of the nonnegative extended integral of `(D-E D)²`; conversion would return zero at infinity, but the L² hypotheses used here exclude that case (`Probability/Moments/Variance.lean:58–64`).

`TendstoInMeasure P f atTop g` means that for every positive extended-real ε, `P{ s : ε ≤ edist(f_n(s),g(s)) } → 0` as n tends to infinity; on real-valued functions and a probability space this is convergence in probability (`MeasureTheory/Function/ConvergenceInMeasure.lean:57`). It does not itself include a measurability hypothesis. Independence means independence of the generated σ-algebras, for all finite subfamilies in `iIndepFun`; `IdentDistrib` includes almost-everywhere measurability and equality of pushforward measures. `CondIndepFun` is conditional independence through the conditional-expectation kernel; on these standard Borel probability spaces it is the usual conditional factorization of event probabilities (`Probability/Independence/{Basic,Conditional}.lean`). A standard Borel measurable space admits a compatible Polish topology (`MeasureTheory/Constructions/Polish/Basic.lean:83`).

Write `s(η)=1/(1+exp(-η))`, the real sigmoid (`Analysis/SpecialFunctions/Sigmoid.lean:63`). `logOdds(p)=log(p/(1-p))`. Real log is log of the absolute value away from zero and zero at zero; all sigmoid likelihood log arguments are strictly positive. `ℓ_m(n,k,η)=k log(m(η))+(n-k)log(1-m(η))`, with no binomial-constant term. For design W, counts n,k, and coefficient vector θ, `L_m(θ)=Σ_i ℓ_m(n_i,k_i,(Wθ)_i)` and `R_m(θ)_j=Σ_i W_ij(k_i-n_i m((Wθ)_i))`. The link-score multiplier is `m'(η)/(m(η)(1-m(η)))`, though the challenged statements do not invoke it. `deriv` is zero at a nondifferentiable point, whereas `HasDerivAt f b x` asserts an actual derivative b. The functions differentiated in these statements are smooth or have an explicit `HasDerivAt` assertion.

For a specified intercept coordinate j₀, `affineCoefficients(j₀,b,c,θ)_j = b 1_{j=j₀}+cθ_j`.

## Regression definitions shared below

For K controls, let `v(x)=(1,x_0,…,x_{K-1})` and `z(d,x)=(1,d,x_0,…,x_{K-1})`. The first n observations have control design V_n with rows v(X_i), and regression design W_n with rows z(D_i,X_i). Define `ω̂_n=(V_nᵀV_n)⁻¹V_nᵀD`, `r̂_ni=D_i-v(X_i)·ω̂_n`, and `β̂_n` as coordinate 1 of `(W_nᵀW_n)⁻¹W_nᵀY`, where `Y_i=Y₀_i+τ_iD_i`. Indices are i=0,…,n−1. Let `w=(D_0-E[D_0|X_0])²`.

For a sequence Z_i, `MC(Z)` means **both** every Z_i is P-integrable and `n⁻¹Σ_{i<n}Z_i → E[Z_0]` in probability. Thus the following regularity definitions include convergence hypotheses, not just the existence of moments.

`RegressionRegularity` is the conjunction of MC for all members of these eight families:

1. `v_j(X_i)v_k(X_i)` for every j,k∈Fin(K+1);
2. `v_j(X_i)D_i` for every j;
3. `D_i²`;
4. `D_iY₀_i`;
5. `v_j(X_i)Y₀_i` for every j;
6. `D_i²τ_i`;
7. `v_j(X_i)D_iτ_i` for every j;
8. `v_j(X_i)v_k(X_i)τ_i` for every j,k.

It additionally requires `det E[v(X_0)v(X_0)ᵀ]≠0`, integrability of w, and `E[w]>0`.

Given ω, put `r_i=D_i-v(X_i)·ω`. `EffectiveMeanRegularity` is MC for these seven families: `v_jv_k`, `v_jD`, `r²Z`, `r²`, `rZv_j`, `rv_j`, and `Zv_jv_k`, with all j,k as above. It also requires the same nonsingular control moment matrix and `E[r_0²]>0`.

`EventuallyDefinedRegression` means `∃n₀ ∀n≥n₀, P(det(W_nᵀW_n)≠0)=1`. The deterministic n₀ precedes the almost-sure statement. `EventuallyDefinedEffectiveMean` similarly means `∃n₀ ∀n≥n₀`, almost surely both `det(V_nᵀV_n)≠0` and `Σ_{i<n}r̂_ni²>0`. These are stronger than requiring sample nonsingularity with probability tending to one, or requiring a sample-dependent almost-sure threshold.

## SAP.P015b.T9

This is a closed conjunction, with no external assumptions. Put
`Z₁=[[1,0],[1,1],[1,1]]`, `Z₂=[[1,0],[1,0],[1,1]]`,
`P₁=[[5/8,1/4],[1/4,1/2]]`, `P₂=[[5/7,1/7],[1/7,3/7]]`, and
`Hinv=[[52/61,-22/61],[-22/61,75/61]]`.

It says the two Gram determinants equal 2; the OLS coefficient vectors for y₁=(0,0,0), y₂=(2,2,2) are respectively (0,0) and (2,0); `P_g=(I+(Z_gᵀZ_g)⁻¹)⁻¹`; `(P₁+P₂)⁻¹=Hinv`; the pooled vector is `(68/61,-10/61)`; and for every real a₁,a₂, `a₁·0+a₂·0≠-10/61`. For every pair of arbitrary vectors t₁,t₂∈ℝ² its slope coordinate is
`[Hinv(P₁t₁+P₂t₂)]_1 = (5/61)t₁₀-(5/61)t₂₀+(32/61)t₁₁+(29/61)t₂₁`.

In a second, independent closed conjunct set `V_g=Z_g I Z_gᵀ+I`. The covariance matrix I is positive semidefinite; the raw GLS expression `(Σ_g Z_gᵀV_g⁻¹Z_g)⁻¹Σ_g Z_gᵀV_g⁻¹y_g` equals `(68/61,-10/61)`; both individual OLS slopes equal zero; and for every real a₁,a₂ the raw GLS slope is different from a₁ times the first individual slope plus a₂ times the second.

## SAP.P015b.T10

First universally choose positive integers G,q, a natural sample size n_g for each of G groups, real n_g×q matrices Z_g and outcomes y_g, a q×q positive semidefinite S, and positive real σ²_g. Assume every `det(Z_gᵀZ_g)≠0`. Set `Q_g=Z_gᵀZ_g`, `P_g=(S+σ²_g Q_g⁻¹)⁻¹`, `H=Σ_gP_g`, `A_g=H⁻¹P_g`, `t_g=Q_g⁻¹Z_gᵀy_g`, `t*=H⁻¹Σ_gP_gt_g`, and `V_g=Z_gSZ_gᵀ+σ²_gI`. The conclusions, in order, are:

1. For every m∈ℝ^q, `Σ_g(t_g-t*)ᵀP_g(t_g-t*) ≤ Σ_g(t_g-m)ᵀP_g(t_g-m)`.
2. For every m, equality of these losses implies m=t*.
3. `t*=Σ_g A_gt_g` and `Σ_gA_g=I`.
4. For every g, `Z_gᵀV_g⁻¹Z_g=P_g` and `Z_gᵀV_g⁻¹y_g=P_gt_g`.
5. `t*=(Σ_g Z_gᵀV_g⁻¹Z_g)⁻¹Σ_g Z_gᵀV_g⁻¹y_g`.
6. For every coordinate b, if for every g,j≠b both `(P_g)_{bj}` and `(P_g)_{jb}` vanish, and every `(P_g)_{bb}>0`, then for every g,j, `(A_g)_{bj}` is `(P_g)_{bb}/Σ_h(P_h)_{bb}` when j=b and zero otherwise.

The second conjunct universally chooses G,q,n,Z,S,σ² under the same assumptions (there are no outcomes y in this conjunct), then arbitrary real a_g and a coordinate b. With the same P,A, the identity `Σ_gΣ_j(A_g)_{bj}t_{gj}=Σ_ga_gt_{gb}` for **every** array t∈ℝ^(G×q) holds if and only if for every g,j, `(A_g)_{bj}=a_g` when j=b and zero otherwise. There is no asymptotic or causal assertion here.

## SAP.P015b.T20

This is a closed four-point calculation. Set `p=(1/20,1/5,11/20,1/5)`, `X=(0,0,1,1)`, `D=(0,1,0,1)`, W with rows (1,D,X), and `M=E_p[WWᵀ]`. It asserts p is a probability law; the conditional means of w_p given X=0,1 are respectively 4/25 and 44/225; and
`M=[[1,2/5,3/4],[2/5,2/5,1/5],[3/4,1/5,3/4]]`,
`M⁻¹=[[52/7,-30/7,-44/7],[-30/7,75/14,20/7],[-44/7,20/7,48/7]]`.
The scaled leverage `h_i=W_iᵀM⁻¹W_i` is `(52/7,59/14,12/7,59/14)`; its conditional means at X=0,1 are 34/7 and 50/21. The weight ratio `(44/225)/(4/25)=11/9` and relative leverage reduction `1-(50/21)/(34/7)=26/51`.

`RoundsWithin(x,display,resolution)` means strict error `<resolution/2`. It asserts this for `(4/25,.160,.001)`, `(44/225,.196,.001)`, `(52/7,7.43,.01)`, `(59/14,4.21,.01)`, `(12/7,1.71,.01)`, `(34/7,4.86,.01)`, `(50/21,2.38,.01)`, `(100(11/9-1),22,1)`, and `(100·26/51,51,1)`. These exact values imply opposite profile orderings, though no separate ordering predicate is included.

## SAP.P015b.T14

For every real α,β,x,d,d′,p, if β≠0 and d≠d′, then it is impossible that both `p=s(α+βd+x)` and `p=s(α+βd′+x)`. Here x is just a fixed additive real term. No probability space, conditional model, or existence of parameters is asserted.

## SAP.P015b.T21

The first conjunct chooses any natural N,K, any real N×(K+2) matrix W with W_i0=1 for every i, any real b,c, any θ∈ℝ^(K+2), and any outcome vector Y∈ℝ^N. It asserts for every i that `W(b e₀+cθ)_i=b+c(Wθ)_i`, and the vector identity `Wᵀ(Y-b-cWθ)=Wᵀ(Y-W(b e₀+cθ))`. Neither rank nor c≠0 nor binary Y is required in this conjunct.

The second conjunct chooses N,K,W,Y, assumes each Y_i∈{0,1}, W_i0=1, and `det(WᵀW)≠0`, and then chooses b,c with c≠0. It asserts:

1. For every θ,v, the map `t↦L_s(θ+tv)` with counts n_i=1 has an actual derivative at t=0 equal to `Σ_i(Y_i-s((Wθ)_i))(Wv)_i`.
2. There exists exactly one θ solving `Wᵀ(Y-b-cWθ)=0`.
3. For every such root θ, `b e₀+cθ=(WᵀW)⁻¹WᵀY`, and the OLS treatment coefficient is cθ₁.

The rank and nonzero-c assumptions scope over the derivative statement as well. The existence assertion is for the affine substituted equation, not for logistic ML.

## SAP.P015b.T11

Let `L=log 99`, `θ*=(-L,2L)`, and `ℓ(θ)=ℓ_s(100,1,θ₀)+ℓ_s(100,99,θ₀+θ₁)`. A closed conjunction asserts:

- For every θ∈ℝ², `ℓ(θ)≤ℓ(θ*)`; for every θ, equality implies θ=θ*.
- `s(-L)=1/100`, `s(L)=99/100`, `logOdds((1+99)/200)=0`, and `π<9/2<L`.
- Let `T_N(c,a)=Σ_{k=0}^N s^(k)(c)(a-c)^k/k!`, using derivatives on all of ℝ (`Analysis/Calculus/Taylor.lean:62–76`). For every natural N, both `|T_N(0,L)-s(L)|` and `|T_N(0,-L)-s(-L)|` are at least 49/100, and `|100(99/100-T_N(0,L))|≥49`.
- There exists a complex formal continuous multilinear power series at zero for `z↦(1+exp(-z))⁻¹` whose norm convergence radius is exactly `ENNReal.ofReal π`. `HasFPowerSeriesAt` says the series actually sums to that function on some positive neighborhood; its radius is the supremum of radii at which the coefficient norms times radius^n are bounded (`Analysis/Analytic/{Basic,ConvergenceRadius}.lean`).
- With `W=[[1,0],[1,1]]`, `det(100(WᵀW))=10000`, both counts 1 and 99 are strictly between zero and 100, and `R_s(θ*)=0` for n=(100,100), k=(1,99).
- Some preceding sigmoid, log-odds, π, and L identities are repeated, and `|T_0(0,L)-s(L)|=49/100` is asserted.

The second top-level conjunct asserts `Wθ*=(-L,L)`, `(1+99)/200=1/2`, and for every N the treatment coordinate of `R_{T_N(0,·)}(θ*)` is exactly `100(99/100-T_N(0,L))`. These are binomial sufficient statistics for two rows repeated 100 times each; the design represented explicitly has two rows with binomial counts.

## SAP.P015b.T15

The first conjunct is the following universal implication, called `CausalOLSConvergence`. Choose any standard Borel measurable Ω, probability P, natural K, sequences D_i,Y₀_i,τ_i:Ω→ℝ and X_i:Ω→ℝ^K, all measurable. Assume the tuples `(D_i,Y₀_i,τ_i,X_i)` are jointly independent across i, and each has the same distribution as the tuple at i=0. Assume `(Y₀_0,τ_0)` is conditionally independent of D_0 given X_0. Choose ω∈ℝ^(K+1) and assume `E[D_0|X_0]=v(X_0)·ω` almost surely. Assume all of `RegressionRegularity`, `EventuallyDefinedRegression`, integrability of D_0, and integrability of wτ_0. The conclusion is `β̂_n → E[wτ_0]/E[w]` in probability. Linear outcomes `Y_i=Y₀_i+τ_iD_i` are built into β̂, rather than separately hypothesized.

The second conjunct, `UnconfoundedMoments`, is independently universal. Choose a standard Borel measurable Ω, probability P, K, measurable single-observation D,Y₀,τ,X, conditional independence `(Y₀,τ) ⟂ D | X`, and ω with `E[D|X]=m=v(X)·ω` almost surely. It requires the following **seven** functions to be integrable: `D`, `Y₀`, `τ`, `DY₀`, `mY₀`, `(D-m)τ`, and `(D-m)mτ`. Its four conclusions are

1. `E[DY₀|X]=E[D|X]E[Y₀|X]` almost surely;
2. `E[(D-m)τ|X]=0` almost surely;
3. `E[DY₀]-E[mY₀]=0`;
4. `E[(D-m)mτ]=0`.

There is no sample sequence or regularity requirement in the second conjunct, and no separate asserted conditional product factorization for `(D-m)τ`.

## SAP.P015b.T22

This is exactly `CausalOLSConvergence`, with every object, hypothesis, quantifier, estimator, and conclusion specified in the first conjunct of T15 above. It does not include T15's independently quantified moment statements.

## SAP.P015b.T23

Choose any measurable Ω (no standard Borel instance required), probability P, natural K, measurable sequences D_i,Z_i:Ω→ℝ and X_i:Ω→ℝ^K. Assume the tuples `(D_i,Z_i,X_i)` are jointly independent across i and each has the same law as the tuple at zero. Choose ω and assume `E[D_0|X_0]=v(X_0)·ω` almost surely. Require `EffectiveMeanRegularity(P,D,Z,X,ω)` and `EventuallyDefinedEffectiveMean`, and separately require integrability of D_0, integrability of `w=(D_0-E[D_0|X_0])²`, integrability of wZ_0, and E[w]>0. Then
`(Σ_{i<n} r̂_ni² Z_i)/(Σ_{i<n}r̂_ni²) → E[wZ_0]/E[w]`
in probability. Fitted residuals use actual OLS regression of D on the intercept and X; Z does not enter that fit. The redundant-looking positivity and integrability assumptions remain hypotheses of the statement.

## SAP.P015b.T24

Its first conjunct chooses standard Borel Ω, probability P, natural K, and measurable D_i,Y₀_i,τ_i,X_i with independent identically distributed tuples as in T15. It assumes unconditional independence `D_0 ⟂ (Y₀_0,τ_0,X_0)`, `RegressionRegularity`, `EventuallyDefinedRegression`, and integrability of τ_0. The conclusion is `β̂_n → E[τ_0]` in probability. It does not explicitly assume ω, a linear conditional mean, integrability of D_0 or wτ_0; those have to follow from the other premises if needed.

The second conjunct chooses any measurable Ω (no standard Borel requirement), probability P, K, measurable D,Y₀,τ,X, independence `D ⟂ (Y₀,τ,X)`, D∈L²(P), integrable τ, and `Var_P(D)>0`. With `w=(D-E[D|X])²`, it concludes `E[D|X]=E[D]` almost surely, `w=(D-E[D])²` almost surely, `E[wτ]=E[w]E[τ]`, and `E[wτ]/E[w]=E[τ]`. It does not explicitly conclude independence of w and τ or any fitted-weight intermediate limit.

## SAP.P015b.T18

First, for all natural N,K, any real N×(K+2) W, any binary Y_i, and any finite real coefficient vector θ, **if** θ globally maximizes the logistic likelihood with n_i=1 over every real coefficient vector γ, **then** `R_s(θ)=0`. There is no intercept/rank hypothesis and no assertion that a maximizer exists.

Second comes a closed square-link construction. On six points take `x=(-1,-1,0,0,1,1)`, `d=(0,1,0,1,0,1)`, `p=(1/4,1/12,1/6,1/6,1/12,1/4)`. Define `e(x)=1/2+x/4`, `q_a(x)=1/4+a(3x²-2)`, design rows `z_i=(1,d_i-e(x_i),x_i)`, probabilities `k_i(a,ε)=q_a(x_i)+ε(d_i-e(x_i))`, link `m(η)=η²`, and weighted population objective `L(a,ε,θ)=Σ_i p_i ℓ_m(1,k_i(a,ε),z_i·θ)`. A coefficient is admissible exactly when **all six** predictors lie strictly between 0 and 1.

`SquareMLDerivative(a,b)` asserts existence of a function θ:ℝ→ℝ³, with θ(0)=(1/2,0,0), and then existence of a real r with `0<r≤1/16` such that for **every** |ε|<r, θ(ε) is admissible and is the unique global maximizer over **all admissible** t of this population objective. Finally ε↦θ₁(ε) has actual derivative b at zero. The branch outside that neighborhood has no maximizing requirement.

The closed construction asserts p is a probability law, `E_p[zzᵀ]=diag(1,5/24,2/3)` and its determinant is nonzero, `SquareMLDerivative(1/16,120/119)`, and `SquareMLDerivative(0,1)`. For every |ε|≤1/16 it asserts `E_p[k(1/16,ε)]=1/4` and the OLS population coefficient of d-e(x) is ε. It also asserts m′(1/2)=1 and 120/119≠1.

To realize potential outcomes, put U-law equal to Lebesgue measure restricted to [0,1] and let P on `((ℝ×ℝ)×ℝ)` be `Σ_i(p_i).toNNReal (δ_(x_i,d_i) × U-law)`. Set X,D,U to the coordinate projections, `Y_d=1_{U≤q_a(X)+ε(d-e(X))}`, and `τ=Y_1-Y_0`. The statement supplies an instance witnessing that P is a probability measure and asserts both laws are probabilities. For **every** real a,ε with `a=0 or a=1/16` and |ε|≤1/16, it further asserts:

- each X∈{-1,0,1} has mass 1/3; D is almost surely 0 or 1; U is almost surely in [0,1]; for every u∈[0,1], `P(U≤u)=ofReal(u)`;
- `U ⟂ (X,D)` and `(Y_0,τ) ⟂ D | X`;
- `E[D|X]=e(X)` almost surely;
- `Y_D=Y_0+τD` almost surely;
- `E[Y_D|X,D]=q_a(X)+ε(D-e(X))` almost surely;
- `E[Y_D]=1/4`.

The square-link claim concerns a population likelihood maximizer branch, not a finite-sample estimator limit. The potential response formula is given at all real d, but only its binary observed response is asserted to have the displayed affine representation.

## SAP.P015b.T17

For positive-mass discrete profiles define `P_x=P(X=x)⁻¹·P|{X=x}`, `μ_x=∫D dP_x`, `v_x=∫(D-μ_x)²dP_x`, and `p_x(d)=P_x(D=d).toReal`. In the actual definitions these are totalized even on zero profiles. Define `w(s)=(D(s)-μ_(X(s)))²`, and effective law `P*=(ofReal(∫w dP))⁻¹·P.withDensity(ofReal∘w)`; reciprocal and scalar operations here are extended-nonnegative-real ones. The uses below assert positive relevant cell masses, finite weights, or explicit values.

The first conjunct chooses arbitrary measurable Ω and B, with B countable and all its singletons measurable, probability P, measurable X:Ω→B and D:Ω→ℝ, and D∈L²(P). Choose x∈B and assume `P(X=x)>0`. Then for every distinct real d,d′, if p_x(d)>0 and p_x(d′)>0, then v_x>0. No assertion for continuous non-atomic conditional treatment values or noncountable B is present.

The second conjunct universally quantifies ε with 0<ε<1/2. On four points define X=(0,0,1,1), D=(0,1,0,1), `p_ε=((1-ε)/2,ε/2,1/4,1/4)`, and `Y_a(d)=2X_a+(1+X_a)d`. It asserts p_ε is a probability law; for every a,d, `Y_a(d)=Y_a(0)+(1+X_a)d`; finite conditional independence of `(Y(0),1+X)` and D given X; and for each x∈{0,1}, the treatment cell mean equals `ε+(1/2-ε)x` and both D=0 and D=1 have positive conditional probability. The effective mass of X=0 is exactly `ε(1-ε)/(ε(1-ε)+1/4)`, is positive, and is less than 4ε.

The third conjunct fixes ε=1/1000000. It asserts the average effect `E_p(1+X)=3/2`. Define `H(a)=D(a)Y_a(D(a))/e(a)-(1-D(a))Y_a(D(a))/(1-e(a))`, where `e(a)=ε+(1/2-ε)X(a)`. For every δ>0 the finite product mass, with n independent draws and probability `Π_{i<n}p(a_i)`, of `|n⁻¹Σ_{i<n}H(a_i)-3/2|≥δ` tends to zero. The n=0 average is totalized by real division; the limit is as n→∞.

The fourth conjunct is a closed fitted-zero-weight example. The underlying four population points have uniform masses 1/4, X=(0,0,1,1), D=(0,1,0,1). For both profile values, both treatment cell probabilities are 1/2 and the conditional mean weight is 1/4. The ordered four-draw sample of population indices is a=(0,0,2,3), with positive probability (1/4)^4=1/256. Its control design is `V=[[1,0],[1,0],[1,1],[1,1]]`, sample treatment `(0,0,0,1)`, and full design `W=[[1,0,0],[1,0,0],[1,0,1],[1,1,1]]`. It asserts `VᵀV=[[4,2],[2,2]]`, `VᵀD=(1,1)`, this Gram matrix maps (0,1/2) to (1,1), and its determinant is nonzero. The residual using (0,1/2) is `(0,0,-1/2,1/2)` and its squared coordinates are `(0,0,1/4,1/4)`. It asserts `WᵀW=[[4,1,2],[1,1,1],[2,1,2]]` and determinant 2; the **actual** `sampleCoefficients V D` equal (0,1/2), with the same residual; and for every sample index i the design profile and treatment equal X(a_i),D(a_i).

Finally take the literal measure `P=(1/4)(δ₀+δ₁+δ₂+δ₃)` on Fin 4, profile X=(0,0,1,1) valued in Fin 2, and treatment D=(0,1,0,2). The last conjunct asserts X,D measurable, D∈L²(P), 0≠1, and both marginal events D=0 and D=1 have positive P-mass. It asserts w is integrable with positive mean, `P*(X=1)>0`, yet the conditional probability under P* of D=1 at X=1 equals zero. It does not assert pair-specific positivity initially within that profile, nor a universal identification theorem.
