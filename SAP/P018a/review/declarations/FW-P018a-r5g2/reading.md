# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. I read the five Challenge declarations and every named declaration in their `closure.json` closures. Source definitions were read in Part1–Part4, WholeW1, and WholeW2. The 51 line-0 auxiliary declarations were also printed and typechecked in `scratch/ClosureChecks.lean` (output: `scratch/closure-checks.log`). Their statements supply numeral instances, nonempty endpoint sets, outer-measure interfaces, and the decidable overlap instance, rather than additional statistical assumptions. The declarations use only Mathlib notions after the expansions below.

## Common fully expanded notation

Here and below a vector in dimension k is a function `Fin k → ℝ`, and a square matrix is a function `Fin k → Fin k → ℝ`. Products, transposes, determinants, inverses and matrix-vector multiplication are Mathlib's finite matrix operations. Write xyᵀ for the matrix with entry x_a y_b, and x·y for Σ_a x_a y_a. All finite sums over coordinates include every element of the indicated finite type. Scalar multiplication multiplies every entry. The norms are the finite function-space supremum norms (with the elementwise matrix norm scope).

The units are indexed by `Fin N`, i.e. integers 0,…,N−1. The dyads are exactly the two-element subsets of this index set, implemented as elements of `Finset.univ.powersetCard 2`. If d={i,j}, then `firstUnit d` is min(d) and `secondUnit d` is max(d), so i<j. Their nonemptiness proofs follow from cardinality two, so neither endpoint is chosen by a default. Write d~f when d∩f is nonempty. A neighbor is an overlapping dyad other than d itself. The meat for any finite family of endpoint sets and vector scores q is

    M(q) = Σ_d Σ_f 1_{d∩f≠∅} q_d q_fᵀ.

Both orders of a distinct overlapping pair occur, and a diagonal occurs once. The sandwich of P and M is PMP, with no transpose on the right P. All breads used statistically here are symmetric, as are their ordinary inverses.

For a measurable space U, a kernel is a measure μ on U, a map X:U×U→ℝ^k, and a map Y:U×U→ℝ. Put P_N=μ^N, the finite product measure on samples ω:Fin N→U. Define

    Q = ∫ X(u,v)X(u,v)ᵀ d(μ⊗μ),
    b = Q⁻¹ ∫ X(u,v)Y(u,v) d(μ⊗μ),
    e(u,v) = Y(u,v)−X(u,v)·b,
    s(u,v) = e(u,v) X(u,v),
    g(u) = ∫ s(u,v) dμ(v),
    Γ = ∫ g(u)g(u)ᵀ dμ(u),
    Hs = ∫ s(u,v)s(u,v)ᵀ d(μ⊗μ).

All these integrals are coordinatewise real Bochner integrals. On a sample, X_d=X(ω_i,ω_j) and Y_d=Y(ω_i,ω_j), where d={i<j}. Then

    A = Σ_d X_d X_dᵀ,
    b̂ = A⁻¹ Σ_d Y_d X_d,
    r̂_d = Y_d−X_d·b̂,
    V̂ = A⁻¹ M((r̂_d X_d)_d) A⁻¹,
    S = Σ_d e(ω_i,ω_j) X_d,
    D_N = (N:ℝ)((N:ℝ)−1)/2,
    V_N = (N/D_N²) Q⁻¹ Cov_{P_N}(S,S) Q⁻¹,
    V_* = 4 Q⁻¹ Γ Q⁻¹.

Here `Cov(F,G)_{ab}=∫(F_a−∫F_a)(G_b−∫G_b)`; `Var` for a vector means this covariance matrix with itself. Scalar `ProbabilityTheory.variance` is instead the extended integral of the squared centered value, converted with `ENNReal.toReal`. In all finite/bounded statistical applications below these agree with ordinary finite covariance/variance. No centering is built into the raw meat M.

The predicate called Standing is precisely: μ is a probability measure; X and Y are measurable on U×U; X(u,v)=X(v,u) and Y(u,v)=Y(v,u) for every u,v; there is one finite C≥0 bounding both ‖X‖ and |Y| μ⊗μ-almost everywhere; some coordinate of X is identically 1 for every u,v; and det Q≠0. Thus k cannot be zero under Standing. It has no sample-rank or positive-definite Γ requirement. SampleRank means there is N₀ such that, for every N≥N₀, det A≠0 P_N-almost surely.

Convergence in probability of F_N to zero means: for every real ε>0, `P_N{ε≤‖F_N‖}.toReal → 0` along the natural numbers atTop. Weak convergence to ν means each F_N is almost everywhere measurable, ν is a probability measure, and for every bounded continuous real function h, ∫h(F_N)dP_N→∫h dν. A centered Gaussian vector law with matrix V is a probability measure with V positive semidefinite whose image under every real linear contrast c·x is `gaussianReal 0 (c·Vc).toNNReal`. Zero contrast variances give Dirac Gaussian laws, not an implicit positivity assumption.

For repeated records, data are μ, deterministic natural counts T_{N,d}, and maps X_{N,d,t}(u,v),Y_{N,d,t}(u,v) for 0≤t<T_{N,d}. Let P_N=μ^N, evaluate each map on the increasing endpoints of d, and put

    L_N=Σ_d T_{N,d},
    A_R=Σ_d Σ_t X_dt X_dtᵀ,
    b_R=(E A_R)⁻¹ E[Σ_dt Y_dt X_dt],
    H_R=L_N⁻¹ E A_R,
    b̂_R=A_R⁻¹ Σ_dt Y_dt X_dt,
    q_d(b)=Σ_t (Y_dt−X_dt·b)X_dt,
    V̂_R=A_R⁻¹ M((q_d(b̂_R))_d) A_R⁻¹,
    V_R,N=(N/L_N²) H_R⁻¹ Var(Σ_d q_d(b_R)) H_R⁻¹.

For deterministic real record weights w_dt, replace A_R by A_w=Σ_dt w_dt X_dtX_dtᵀ, the cross product by B_w=Σ_dt w_dtY_dtX_dt, b_R by b_w=(E A_w)⁻¹E B_w, and the block score by q_w,d(b)=Σ_t w_dt(Y_dt−X_dt·b)X_dt. Then b̂_w=A_w⁻¹B_w, H_w=D_N⁻¹ E A_w,

    V̂_w=A_w⁻¹ M((q_w,d(b̂_w))_d) A_w⁻¹,
    V_w,N=(N/D_N²) H_w⁻¹ Var(Σ_d q_w,d(b_w)) H_w⁻¹.

The single-record weighted definitions use precisely these formulas with one record and the symmetric X,Y kernel, and use P_N=μ^N. The population beta there is the inverse of the *unnormalized* expected weighted Gram times the expected weighted cross product. The normalization cancels when nonzero.

## SAP.P018a.T6

The statement is a conjunction of three independently universally quantified results.

1. For every natural N≥2, and every dyads d,f, define Z₁(d,i)=1 if i=min d and 0 otherwise, Z₂(d,i)=1 if i=max d and 0 otherwise. Then (Z₁Z₁ᵀ)_{df}, (Z₂Z₂ᵀ)_{df}, (Z₁Z₂ᵀ)_{df}, and (Z₂Z₁ᵀ)_{df} equal respectively the indicators of min d=min f, max d=max f, min d=max f, and max d=min f. The entry of (Z₁+Z₂)(Z₁+Z₂)ᵀ is |d∩f|, cast into ℝ. For every real τ,σ,

       C_shared=τ(Z₁+Z₂)(Z₁+Z₂)ᵀ+σI
               =τ(Z₁Z₁ᵀ+Z₂Z₂ᵀ+Z₁Z₂ᵀ+Z₂Z₁ᵀ)+σI.

   If also N≥3, for every real τ>0 and every real σ,t₁,t₂,s, C_shared≠t₁Z₁Z₁ᵀ+t₂Z₂Z₂ᵀ+sI. No positivity hypotheses on σ or the competing parameters are imposed.
2. For every measurable probability space (Ω,μ), natural dimensions m,N, deterministic real m×N matrix Z, and random vectors a:Ω→ℝ^N and ν:Ω→ℝ^m: if every coordinate is in L², a and ν are independent as vector-valued functions, and for real τ,σ their covariance matrices are τI_N and σI_m, then Var(Za+ν)=τZZᵀ+σI_m. Neither centeredness nor Gaussianity is required. The quantification of τ,σ occurs after the independence hypothesis. No relationship between this arbitrary Z and the preceding dyadic incidence matrices is imposed.
3. For every natural m,k, real m×m matrix C and real m×k matrix F: if det C is a unit (over ℝ, nonzero), Cᵀ=C, and det(FᵀC⁻¹F) is a unit, put G=FᵀC⁻¹F and L=G⁻¹FᵀC⁻¹. Then LF=I_k and LCLᵀ=G⁻¹. This is an algebraic covariance transport identity; no random response or Gauss–Markov optimality is quantified, and C is not required positive definite.

Junk conventions: inverse at singular matrices is Mathlib's zero matrix, but the GLS identities guard both inverses with nonzero determinants. Zero dimensions are allowed in parts 2 and 3, with empty sums and the empty matrix determinant 1; nonempty dimensions are also allowed. All random covariance integrals are genuine L² covariances. No division, log, square root, rpow, infimum, supremum or limiting-sequence convention enters the dyad identities. Endpoints are actual members. Cardinality casts are exact nonnegative integer casts.

## SAP.P018a.T7

This is a closed conjunction about one concrete probability model, not a universal conditional claim. U=Bool×Bool has the product of the two uniform Bool laws; sign(true)=1, sign(false)=−1. For iid units write their independent signs (Z_i,W_i). The kernel is X_ij=(1,1+Z_iZ_j), Y_ij=W_i+W_j. In addition to Standing it asserts the following explicit extra predicate: one finite constant bounds all fitted residuals almost surely for every N; every entry of Q is nonzero; every entry of E[X_12X_13ᵀ] is nonzero; and eventually, at each N, every fitted residual second moment is nonzero and every distinct overlapping fitted residual product expectation is nonzero.

The remaining complete assertions are:

- Q=[[1,1],[1,2]], det Q=1, Q⁻¹=[[2,−1],[−1,1]], b=0, Γ=[[1,1],[1,1]], V_*=diag(4,0). E[XY]=0 and e(u,v)=Y(u,v) for every pair. Every fitted residual has absolute value ≤4 for every N, every sample and every dyad.
- For every N≥3, det A=0 iff all first Bool coordinates of the sample coincide; its probability is exactly `ENNReal.ofReal(2/2^N)`. For every distinct overlapping d,f, E e_d²=2, E e_de_f=1, E X_dX_fᵀ=[[1,1],[1,1]], and E[(e_dX_d)(e_fX_f)ᵀ]=[[1,1],[1,1]]. Also Hs=2Q, and Var S=2D_N Q+N(N−1)(N−2)Γ. The exact target is [[4N/(N−1),−4/(N−1)],[−4/(N−1),4/(N−1)]], and it tends to diag(4,0).
- The explicitly enumerated 28 dyads on 8 units are all pairs in increasing lexicographic order. The fixed signs are Z=(1,1,−1,−1,1,1,−1,−1), W=(1,−1,1,−1,1,−1,1,−1), and the corresponding X,Y follow the same kernel. Their Gram is [[28,24],[24,48]], determinant 768, OLS vector zero, fitted meat [[240,160],[160,64]], and sandwich [[3/8,−1/48],[−1/48,−13/288]]. The slope variance is negative. The actual sample in (Bool×Bool)^8 with these signs is asserted to have probability (1/4)^8>0; its Gram, OLS, meat and sandwich are again asserted with the genuine dyad index type.
- Jointly, (N b̂_slope, N² V̂_slope,slope) converges weakly to (2AB,4(A²+B²−1)) where A,B are independent standard real Gaussians. Formally the limit law is the pushforward of their finite product measure by this polynomial map.
- P_N{V̂_slope,slope<0}→1−exp(−1/2). The independent Gaussian probability P{A²+B²<1} is that same strictly positive number. For every N and sample with negative slope variance there is no real r with r² equal to that variance. If the estimated slope variance is ≤0 the real-division/sqrt pivot is exactly zero. This completed pivot has no standard-normal weak limit.
- N V̂−diag(4,0)→0 in probability, and N V̂−V_N→0 in probability.

Junk conventions: the actual sample Gram can be singular with the displayed small positive probability. A⁻¹ is zero there, so b̂=0 and V̂=0 there. The docstring explicitly states that completion and uses ordinary inverses on the other samples. This affects finite values but its probability tends to zero. For N=0,1 there are no dyads, the Gram is singular and all sample sums and sample fits are zero. V_N has N/D_N² with D_N=0 at those two sizes; real division makes it zero. The target formula with N−1 is asserted only for N≥3 and all limits ignore initial sizes. √N is only used for natural N, so it is nonnegative. For negative variance Real.sqrt is zero and a/0=0: the theorem explicitly distinguishes the lack of a real square root from this zero completion, and makes its nonnormal conclusion about the completed pivot. Product measures are finite probability measures, so `.toReal` never converts ∞ to zero. All finite-sample random variables live on finite sets, so their moments exist even though inverse values need not be uniformly bounded across N. Natural casts and finite enumerations have their literal meanings, including the full 28-element list. There are no log/rpow, sInf/sSup or limsup/liminf definitions in this closure.

## SAP.P018a.T8

For every measurable U, natural k, kernel K, assuming precisely Standing as expanded above, simultaneously:

1. Γ equals ∫s(u,v)s(u,w)ᵀ dμ(u)dμ(v)dμ(w), with three independent unit draws.
2. There exists a centered Gaussian probability law with covariance V_* such that √N(b̂−b) converges weakly to it. The covariance may be singular.
3. V_N→V_* and N V̂−V_*→0 in probability.
4. For every c:Fin k→ℝ with cᵀV_*c>0, the pivot c·(b̂−b)/sqrt(cᵀV̂c) converges weakly to N(0,1); P_N{cᵀV̂c≤0}→0; and for every real α with 0<α<1,

       P_N{0≤cᵀV̂c and |c·(b̂−b)|≤z_(1−α/2) sqrt(cᵀV̂c)}→1−α.

   The order is K, Standing K, then all c satisfying positive limiting variance, then all α in (0,1). There is no eventual almost-sure positivity hypothesis on sample variances. The normal quantile is defined as the real infimum of {z | p≤P(N(0,1)≤z)}.

A separate closed conjunct supplies the same sign-pair model as T7: Standing, b=0, V_*=diag(4,0), limiting negative slope-variance probability 1−exp(−1/2), and failure of a standard-normal weak limit for the zero-completed slope pivot.

Junk conventions: every pivot uses sqrt(t)=0 for t≤0 and real a/0=0; the docstring explicitly identifies this zero extension. Positive limiting contrast variance forces the probability of such completion samples to vanish in the general positive-variance conclusion; it does not do so in the slope counterexample. Finite-sample singular Gram inversion has the zero convention, as above; Standing does not posit almost-sure rank at each N. The population inverse is guarded by det Q≠0. All `.toReal` probabilities are finite. Quantiles are used only at p=1−α/2∈(1/2,1); here the defining set is nonempty and bounded below, so real sInf is its ordinary infimum. Outside 0<p<1 the infimum could use a totalized value, but those inputs do not occur. PSD of V_* prevents `.toNNReal` from clipping a negative contrast variance in the Gaussian definition. Empty coordinate dimensions are excluded by the intercept condition. N=0,1 target completions have no effect on atTop limits. No log/rpow, unbounded limsup/liminf or additional partial-function defaults occur. Integrability follows for population scores from the bounded probability model; weak convergence explicitly includes sample-map measurability and uses bounded continuous test integrals.

## SAP.P018a.T9

This is a closed counterexample in the intercept model X_ij=1, Y_ij=Z_i+Z_j for iid fair signs Z_i. For one-based labels i,j its weights are 2^(−i−j); in the actual zero-based Fin types, q_i=2^(−i−1), w_ij=q_i q_j, so the largest dyad weight is 1/8. Put x_N=2^(−N), S_N=Σ_i q_i, W_N=Σ_d w_d, c_i=q_i(S_N−q_i)/W_N, and τ_N²=Var(b̂_w). The theorem asserts all of the following.

- Standing and eventual almost-sure unweighted sample rank hold, b=0, and for every N≥2 the weighted population beta is zero. For every sample D_N⁻¹A=1, every population residual has absolute value ≤2, and every weighted fitted residual has absolute value ≤4. Equal endpoint labels give the same weights at every N,M (fixed weights across sample sizes).
- For every N≥2 and every dyad, 0<w_d≤1/8. For every N (including 0,1), S_N=1−x_N, W_N=(1−x_N)(1−2x_N)/3, τ_N²=Σ_i c_i², and b̂_w=Σ_i c_iZ_i on every sample. For every N≥2, Σ_i c_i=2 and c_0=3/[4(1−x_N)]≥3/4.
- For every N≥2, τ_N²≥9/16, and τ_N²→36/35. The coefficients b̂_w do not converge to zero in probability. Nτ_N²→+∞, W_N/D_N→0, and 3/[4(1−x_N)]→3/4.
- For every N≥8, let E_N be the event that the first eight signs are +1. Its probability is exactly 1/256 and W_N≥1/8. Let t_N=Σ_{d:max(d)≥8}w_d and q̂_d=w_d(Y_d−b̂_w). Then 0≤t_N≤1/256, and on E_N,

       0≤2−b̂_w≤4t_N/W_N,
       Σ_d|q̂_d|≤8t_N,
       |V̂_w|≤64(t_N/W_N)²≤1/16,
       |V̂_w−τ_N²|≥1/2.

  In particular P_N{N/2≤|N V̂_w−Nτ_N²|}≥1/256. There is no deterministic sequence V(N) with both Nτ_N²−V(N)→0 and N V̂_w−V(N)→0 in probability.
- For N≥2 the scalar sandwich equals W_N^(−2)Σ_{d~f}q̂_dq̂_f, using an integer negative power.
- A repeated model has T_{ij}=2^(i+j) for one-based labels and identical X=1,Y=Z_i+Z_j in every record. For every N≥2 its fit and sandwich are jointly identically distributed with the weighted model's fit and sandwich. More strongly, on every sample their pair equals the weighted pair on the label-reversed sample i↦N−1−i. For every natural B there are N≥2 and a dyad with T_{N,d}>B. Thus every count is finite, but no uniform bound is asserted.
- If instead every dyad is replaced by two identical records, both carrying its original concentrated weight, the record-weighted OLS and sandwich equal the original weighted OLS and sandwich on every sample for every N≥2. The two records are grouped together by the unordered endpoint block.

Junk conventions: at N=0,1 there are no dyads and W_N=0. Real division defines every c_i there as zero; the singular inverse makes b̂_w=0 and τ_N²=0, so the all-N linear and variance identities explicitly include those zero completions. All nonzero denominator bounds, c_0 statements, and finite separation assertions are guarded by N≥2 or N≥8. The apparent 1/(1−x_N) at N=0 in the limit sequence is totalized but affects no limit. Powers use natural exponents for q_i,x_N and counts, and integer exponents for weights and W_N^(−2); bases 2 and 1/2 are positive and W_N>0 on N≥2. There is no domain-sensitive real rpow. N/2 in this section's probabilistic separation is real division; the only N/2 in the later T10 witness is natural division. All probabilities and moments are finite on finite sample spaces. Reversal is an actual permutation, not default indexing. No square root, log, infimum/supremum or limsup/liminf occurs in this closure.

## SAP.P018a.T10

The statement is a conjunction of five parts. The general parts quantify arbitrary measurable U (in the specified Lean universe), natural k, and the data, then hypotheses, then a positive definite limiting matrix H.

1. For any repeated kernel, assume: μ is a probability measure; every block at N≥2 has a positive count; every record X,Y is measurable; one C≥0 bounds ‖X‖,|Y| almost everywhere uniformly over N,d,t; one coordinate of all X is identically 1; there exist common maps fX_t,fY_t independent of N,d such that each record t uses these maps; there is one natural T₀ bounding all counts; H is positive definite; H_R,N→H; and

       (N/L_N²) Σ_{d~f} m_d m_fᵀ → 0,
       m_d=E q_d(b_R,N).

   Then N V̂_R−V_R,N→0 in probability. The means m_d are not assumed individually zero. The displayed overlap-mean condition is an explicit substantive hypothesis in addition to the stacked population normal equations.
2. For any ordered kernel K with probability μ, measurable bounded X,Y and an intercept (no symmetry or nonsingular unweighted Q is assumed), take any repeated kernel R with the same μ and any deterministic direction map dir_{N,d}:Fin(T_{N,d})→Bool that is injective. Each record must use K(u,v) in the false direction and K(v,u) in the true direction, for both X and Y. Thus counts are at most two, and empty blocks are allowed. For every deterministic real record-weight array w and every positive sequence a_N, assume one real C bounds 0<w_dt/a_N≤C for all N,d,t. If H is positive definite and D_N⁻¹ E A_{w/a_N}→H, then N V̂_w−V_w,N→0 in probability. No lower bound away from zero for the normalized weights, no dense observation assumption, and no intercept-free alternative is stated.
3. For every fixed N≥2 and repeated kernel on a probability measure, assume every record X,Y measurable and bounded almost everywhere by one finite constant at that size (empty blocks permitted). For every fixed real record-weight array w, real a>0, and every sample ω with det A_w(ω)≠0 and det H_w≠0, replacing w by a w leaves b̂_w(ω), V̂_w(ω), and V_w,N all unchanged. The weights themselves need not be positive in this identity; a is positive. The target is independent of ω, even though the combined implication is quantified after the sample-rank guard.
4. The concentrated positive fixed weights of T9 are ≤1/8 for N≥2; the unweighted sign kernel satisfies Standing and SampleRank; no deterministic sequence simultaneously approximates NVar(b̂_w) in ordinary convergence and N V̂_w in probability. This is an explicit closed obstruction to conclusions based on these weak assumptions alone.
5. There is a fixed deterministic witness over Unit with μ=δ_(), X_dt=1, first record response +1 and second response −1, and T_{N,d}=1 when max(d)<floor(N/2), otherwise T_{N,d}=2. It satisfies all the repeated standing conditions, has counts ≤2 and common fX,fY. For every N≥2, H_R,N=1 and Σ_d E q_d(b_R,N)=0. Nevertheless its scaled raw overlap product of block means fails to tend to zero and N V̂_R−V_R,N fails to converge to zero in probability. The witness does not satisfy the extra overlap-mean hypothesis of part 1 and therefore does not negate part 1.

Junk conventions: for N≥2 all positive-count repeated models have L_N>0. For the directed model there may be no records at particular N, giving A_w=0, H_w=0, b̂_w=0 and V̂_w=0 via totalized inverses; positive definite H and normalized-design convergence control sufficiently large N for the asymptotic result. At all N the targets and coefficients use zero at a singular matrix, and D_0=D_1=0 gives zero normalized quantities. These initial completions do not determine any atTop conclusion. The scale identity has N≥2, a>0 and both determinant guards, so no denominator or singular-inverse junk is used in its substantive identities. All population integrals are bounded-data integrals on probability spaces; record weights are fixed finite reals and each record family at a fixed N is finite. The witness's N/2 is truncated natural division, intentionally floor(N/2), and its response uses t.val=0, otherwise −1 (only two records can exist). The intercept assumptions exclude k=0; general zero-dimensional algebra in the scale identity is harmless. All `.toReal` probabilities are bounded by one. There are no log, sqrt, rpow, sInf/sSup or limsup/liminf conventions in this closure.
