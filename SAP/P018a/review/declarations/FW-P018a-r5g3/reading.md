# Blind reading of P018-T11–T14

This file was written and saved before opening either `claims.json` or `record.json`. It records the elaborated statements, not a reconstruction of any paper claim. Sources: every closure entry in `closure.json`, the indicated definitions and Challenge docstrings, and Mathlib definitions. All 43 distinct generated proof constants in the closures were printed by `scratch/ClosureProofs.lean` and inspected. They establish numeral denominator/index side conditions, the measure outer-measure instance, or nonemptiness of a two-element dyad; they introduce no statistical assumptions.

## SAP.P018a.T11

The declaration at `SAP/P018a/Challenge/Part2.lean:52` asserts the closed proposition `T11WholeStatement` (`Defs/WholeW1.lean:399`). Its docstring calls the scalar expressions literal unsummed repeated/weighted targets, describes their discrepancy from the scaled fit variance, the repeated block-bread defect, and the two-regressor bread discrepancy. There are no hypotheses on the theorem itself. The following definitions and conjunctions give its complete content.

### Objects and fully expanded notation

For each natural number N, the units are indexed by `Fin N` (integers 0 through N−1), and E_N consists of the two-element subsets of `Fin N`. A dyad's first and second units are its minimum and maximum. These are defined using proved nonemptiness, with no default endpoint. Write d~f if their endpoint sets intersect, and n(d) for the dyads f≠d with d~f. All sums over dyads and neighbors are finite; double sums are ordered. Let D=N(N−1)/2, where N is cast to the reals before subtracting 1.

A k-vector is a function `Fin k → ℝ`, a k-matrix a real square matrix indexed by `Fin k`. Write x·b=Σ_a x_a b_a, xyᵀ for the matrix with entry x_a y_b, and A⁻¹ for Mathlib's nonsingular matrix inverse. A sandwich is exactly A M A, with no transpose inserted in the definition.

For a probability measure μ on a measurable unit space U and functions X:U²→ℝ^k and Y:U²→ℝ, independent sampled units have law P_N=μ^N, Mathlib `Measure.pi`. At sample ω, x_d=X(ω_min(d),ω_max(d)), y_d=Y(ω_min(d),ω_max(d)). Define Q=∫XXᵀ d(μ×μ), b=Q⁻¹∫XY d(μ×μ), e(u,v)=Y(u,v)−X(u,v)·b, q(u,v)=e(u,v)X(u,v). Let H=∫qqᵀ d(μ×μ), p(u)=∫q(u,v)dμ(v), and Γ=∫p(u)p(u)ᵀdμ(u). All vector/matrix integrals are entrywise real Bochner integrals. For vector functions f,g, Cov(f,g) has entry ∫(f_a−∫f_a)(g_b−∫g_b); Var(f)=Cov(f,f).

The sample Gram is G=Σ_d x_d x_dᵀ, OLS is b_hat=G⁻¹Σ_d x_d y_d, fitted residual r_d=y_d−x_d·b_hat, overlap meat M=Σ_dΣ_f 1_{d~f} r_d r_f x_d x_fᵀ, and sample variance V_hat=G⁻¹ M G⁻¹. For fixed deterministic weights w_d, G_w=Σ_d w_d x_d x_dᵀ, b_hat_w=G_w⁻¹Σ_d w_d x_d y_d, and V_hat_w=G_w⁻¹[Σ_{d~f} w_d w_f (y_d−x_d·b_hat_w)(y_f−x_f·b_hat_w)x_d x_fᵀ]G_w⁻¹.

The sigma-algebra F_X is the inverse image of the Borel sigma-algebra under the entire design map ω↦(x_d)_d. Let m_d=E[e_d|F_X], C_df=E[(e_d−m_d)(e_f−m_f)|F_X], and T_df=E[C_df x_d x_fᵀ]. The conditional row A_d=T_dd+Σ_{f∈n(d)}T_df; the unconditional score-covariance row B_d=Cov(e_dx_d,e_dx_d)+Σ_{f∈n(d)}Cov(e_dx_d,e_fx_f). Conditional expectations are Mathlib `condExp`, hence are versions with almost-everywhere meaning where indicated. The cross-Gram J is ∫X(u,v)X(u,w)ᵀdμ(u)dμ(v)dμ(w).

For repeated records, T_Nd is a natural count, X_Ndt:U²→ℝ^k and Y_Ndt:U²→ℝ; t ranges over `Fin T_Nd`. The law remains μ^N. Let L=Σ_d T_Nd, G_r=Σ_dt x_dt x_dtᵀ, H_r=L⁻¹ E G_r, b_r=(E G_r)⁻¹ EΣ_dt x_dt y_dt, b_hat_r=G_r⁻¹Σ_dt x_dt y_dt, q_d(b)=Σ_t x_dt(y_dt−x_dt·b). The repeated fitted sandwich is G_r⁻¹[Σ_{d~f}q_d(b_hat_r)q_f(b_hat_r)ᵀ]G_r⁻¹ and the repeated target is (N/L²) H_r⁻¹ Var(Σ_d q_d(b_r)) H_r⁻¹. A singleton-record construction has every T_Nd=1 and copies X,Y. The block design X_d is a T_Nd by k matrix. The wrong block Gram is E[X_d X_dᵀ], a T_Nd by T_Nd matrix; the coefficient block Gram is E[X_dᵀX_d], a k by k matrix.

The property called Standing requires: μ is a probability measure; X and Y are measurable on U²; both kernels are symmetric for every u,v; there is a real C≥0 bounding both ‖X‖ and |Y| μ²-almost everywhere; some coordinate of X is identically 1 for every u,v; det Q≠0.

Convergence in probability of a sequence Z_N on possibly different sample spaces means: for every real ε>0, P_N{ε≤‖Z_N‖}.toReal→0 as N→∞. Vector/matrix norms here are finite-coordinate supremum norms (the matrix norm is the elementwise supremum norm). Every Tendsto below is ordinary topological convergence along the natural-number atTop filter.

### All asserted clauses and quantifiers

The fixed scalar model has U=Bool with each Boolean assigned probability 1/2; s(true)=1, s(false)=−1; X=1 and Y(u,v)=s(u)+s(v). Write S=Σ_i s(ω_i), m=S/N, Z_N=N(V_hat)_00.

1. This model satisfies Standing and has b=0. For every N≥3, every sample satisfies b_hat_0=2S/N. For every dyad d, m_d=0 almost everywhere and A_d=[2N−2]. For every d and every f, Cov(e_d,e_f)=|d∩f| and C_df=|d∩f| almost everywhere. Q=1. The singleton record model has L=D; its OLS and fitted sandwich equal the single-record versions at every sample. OLS and the fitted sandwich with all weights 1 also equal those versions at every sample.
2. For every N≥3, N Var(b_hat_0)=4; N(2N−2)/D²=4/D; N[N(N−1)²]/D²=4; and N(2N−2)/D²≠4. As N→∞, 4/D→0, and Z_N−4→0 in probability.
3. For every N≥3 and every sample, Z_N=[4(N−2)(N−3)/(N−1)²](1−m²). Its expectation is 4(N−2)(N−3)/[N(N−1)].
4. For every N≥3, Var(Σ_d q_d)=[N(N−1)²], N(N−1)²=D(2N−2), and N(2N−2)/D²=8/[N(N−1)]. The deterministic sequence N Var(b_hat_0)−4/D tends to 4; Z_N−4/D−4 tends to zero in probability.
5. For every natural T, then every natural N, if T≥1 and N≥3, the model with T identical copies of the scalar record on every dyad has L=TD, b_r=0, H_r=1, and Var(Σ_d q_d(0))=[T²N(N−1)²]. For every dyad its coefficient block Gram is [T] and its wrong block Gram is the T by T all-ones matrix. Applying the unnormalized coefficient-block inverse sandwich with prefactor N/L² to this total-score variance gives [4/T²]; the repeated target defined with H_r gives [4]. For every N≥3 and dyad d, the wrong block Gram at T=2 has determinant zero, while the coefficient block Gram is [2]. These are identical within-dyad records, not claimed independent repetitions.
6. A second fixed model has U=ℝ×Bool, with independent Z uniform on [−1,1] and fair sign W. Its X(u,v)=(1,Z_u+Z_v) and Y(u,v)=W_u+W_v. The real uniform law is the measure `(volume [−1,1])⁻¹ • volume.restrict [−1,1]`. This model satisfies Standing and b=0; Q=diag(1,2/3), J=diag(1,1/3), E[X·X]=5/3, H=diag(2,4/3), Γ=diag(1,1/3). For every N≥3 and every d, A_d=B_d=diag(2N−2,2N/3).
7. For every N≥3 and every d in the second model, (N/D²)Q⁻¹(D A_d)Q⁻¹=diag(4,3N/(N−1)). Replacing the left inverse by the scalar (5/3)⁻¹, while retaining the right Q⁻¹, gives diag(12/5,6N/[5(N−1)]). No general inequality between these expressions is separately quantified, but the displayed values differ.

### Junk-value audit

Real inversion and division send a zero denominator to zero. The displayed finite scalar formulas are guarded by N≥3, and the T-dependent divisions by T≥1, so their denominators are positive. D at N=0,1 is zero; global sequences and probability limits therefore include harmless zero-completed initial terms. N−1,N−2,N−3 in the formulas are **real**, not truncated natural subtraction. Counts, finite indices and their casts are exact; no negative count or silent modular indexing is used for dyads. The literal finite matrix/vector syntax has valid coordinate indices, supported by the generated `NeZero`/`AtLeastTwo` constants.

Matrix inverses over ℝ are det(A)⁻¹ times the adjugate, and are zero matrices when singular. The scalar model's sample Gram is positive for N≥3; so are its population and repeated coefficient Grams. The wrong T=2 block Gram is deliberately singular, but its inverse is never used in the disputed arithmetic. The mixed population Q is nonsingular. Thus the substantive discrepancy does not rely on singular-inverse completion.

Bochner means and covariance integrals would be zero for nonintegrable integrands. Mathlib real `variance` first takes the nonnegative extended integral of the squared centered variable, then `toReal`, which sends infinity to zero. Both fixed models have bounded kernels and the statistics being integrated here have finite moments, so these completions do not generate the stated discrepancies. Conditional expectation would be zero if the conditioning sigma-algebra were not a subalgebra, its trimmed measure not sigma-finite, or the integrand not integrable. Measurability and finite probability laws make those valid here. Conditional expectations use selected versions, but the assertions about them are almost everywhere or inside expectations. Uniform conditioning divides an extended measure by the interval measure 2, which is finite and nonzero. Probability `toReal` is only applied to finite probabilities.

For N<2, the dyad type is empty; all dyad sums are zero. For T=0, record indices are empty, but T-dependent assertions exclude it. The probability limits tolerate finitely many empty initial samples. The general template definitions allow k=0 or empty U; Standing cannot hold with k=0 (it requires an intercept coordinate), or with an empty probability unit space. Both actual models are nonempty with k=1 or 2. There is no sqrt, logarithm, rpow, infimum/supremum, limsup/liminf, or partial-function default in the semantic content of this statement.

## SAP.P018a.T12

The declaration at `Challenge/Part2.lean:63` asserts the closed conjunction `T12WholeStatement` (`Defs/WholeW2.lean:91`). The docstring describes corrected normalized expected-Gram targets, exact linearized covariances, sparse block covariance, conditional conversion to raw moments, reductions, normalization invariance, and check models. The finite record counts, laws, entries, integrals, covariance, endpoints, overlaps, and inverses below have precisely the mathematical expansions given here; no properties of similarly named propositions are assumed.

### Objects, definitions, hypotheses, and quantifier order

For any measurable space U (universe-polymorphic), k,N natural, take a measure μ, deterministic natural counts T_d for each two-element subset d of `Fin N`, and measurable functions X_dt:U²→ℝ^k, Y_dt:U²→ℝ for each t<T_d. Sample P=μ^N independently across units. A record uses its dyad's minimum and maximum endpoints. A block can be empty. Let L=Σ_d T_d (as a real). For fixed real weights w_dt define

G_w(ω)=Σ_dt w_dt x_dt x_dtᵀ,
a_w(ω)=Σ_dt w_dt x_dt y_dt,
b_w=(E G_w)⁻¹ E a_w,
b_hat_w(ω)=G_w(ω)⁻¹a_w(ω),
q_d(b,ω)=Σ_t w_dt x_dt(y_dt−x_dt·b),
S(ω)=Σ_d q_d(b_w,ω).

Here x_dt=X_dt(ω_min(d),ω_max(d)), y_dt=Y_dt at the same endpoints; each mean and covariance is entrywise. Cov has entries E[(f_a−Ef_a)(g_b−Eg_b)]. Write G=G_1, b=b_1, S_1=S with unit weights, and H=L⁻¹ E G. The repeated target is V_r=(N/L²)H⁻¹ Var(S_1)H⁻¹. For record weights define H_w=D⁻¹ E G_w with D=N(N−1)/2 (real arithmetic). A sandwich means A M A. The standing finite-record hypothesis here is exactly: μ is a probability measure; all X_dt,Y_dt at this N are measurable on U²; there exists a finite real C≥0 such that ‖X_dt‖≤C and |Y_dt|≤C μ²-almost everywhere for every d,t at this N. It does not require positive counts in each block, symmetry, a common kernel, an intercept, any sign condition on weights, or independent records within a block.

The statement is the conjunction of these six items:

1. Universally quantify U, its measurable structure, k,N, then the entire record data. If finite-record regularity holds, N≥2, L>0, and det H≠0, let w_dt=1 and c=L. Then E S=0, E[c⁻¹G_w]=H, and
   (N/c²)H⁻¹ Var(S)H⁻¹ = Var[H⁻¹((sqrt(N)/c)S)].
   For **every** sample ω, if det G_w(ω)≠0, then
   sqrt(N)(b_hat_w(ω)−b_w)=[c⁻¹G_w(ω)]⁻¹[(sqrt(N)/c)S(ω)].
   This is an exact covariance of the population-bread linearized score, not an asserted equality to the covariance of the OLS error with random sample bread.
2. Independently universally quantify U, structure, k,N, data; if finite-record regularity and N≥2 hold, then for **every** fixed real weight array w, if det H_w≠0, the same four assertions hold with c=D and H=H_w. There is no requirement L>0 in this weighted part, nor positivity/nonzero restrictions on individual w_dt.
3. Independently universally quantify U, structure, k,N, data. If finite-record regularity holds, then for **every** w and **every** deterministic coefficient b (not just b_w), disjoint blocks have covariance zero; and
   Var(Σ_d q_d)=Σ_d[Var(q_d)+Σ_{f≠d,d~f}Cov(q_d,q_f)].
   Further, **if every individual block** has E q_d=0, then for every d,f,
   Cov(q_d,q_f)=E[q_d q_fᵀ], and Var(Σ_d q_d)=E[Σ_{d~f}q_d q_fᵀ].
   This part has no N≥2, L>0, or rank hypotheses. The block-centering premise applies only to raw-moment replacement.
4. Independently universally quantify U, structure, k,N and a single pair of kernels X,Y. Assume μ is a probability, both kernels measurable and symmetric, jointly bounded μ²-a.e., some coordinate of X identically 1, and det Q≠0 for Q=E XXᵀ. If N≥2, then V_r for singleton records equals
   V_0=(N/D²)Q⁻¹ Var[Σ_d x_d(y_d−x_d·b_0)]Q⁻¹,
   where b_0=Q⁻¹E XY. Also the single-record weighted target with all weights 1 equals V_0. For general single-record weights w_d that target is defined by H_w=D⁻¹EΣ_d w_dx_dx_dᵀ, b_w=(EΣ_d w_dx_dx_dᵀ)⁻¹EΣ_d w_dx_dy_d, and (N/D²)H_w⁻¹ Var[Σ_d w_dx_d(y_d−x_d·b_w)]H_w⁻¹.
5. Independently universally quantify U, structure, k,N and arbitrary repeated data. If N≥2, L>0, and det(E G)≠0, then
   V_r=(N/D²)(D⁻¹EG)⁻¹ Var(S_1)(D⁻¹EG)⁻¹.
   No measurability, boundedness, or probability condition is explicitly assumed in this algebraic normalization identity. It is an equality of the defined integrals and matrices even if those integrals use their totalized conventions.
6. Checks: for every N and then m, if N≥3 and m>0, m identical fair-sign intercept records per dyad have V_r=[4]. For every N≥3 the single-record unit-weight sign target is [4]. The mixed model with independent uniform Z on [−1,1] and fair sign W, X=(1,Z_i+Z_j), Y=W_i+W_j, satisfies all the single-kernel standing assumptions, Q=diag(1,2/3), b_0=0; for every N≥3 its unit-weight target is diag(4,3N/(N−1)).

### Junk-value audit

The expected-Gram rank and positive normalization hypotheses in items 1 and 2 exclude substantive zero-denominator completions when k>0. The algebraic item 5 guards both normalizations and its expected Gram. For k=0 the determinant of the unique empty square matrix is 1 and all vector/matrix conclusions are the zero-dimensional identities; this is allowed and does not remove the nonempty-dimension cases. In item 2, all counts could be zero only in this k=0 case, since H_w would otherwise be singular. Empty individual blocks are intentional. In item 3, N<2 gives an empty dyad type and genuine zero-sum identities. All counts are cast from naturals; N−1 in D is real subtraction.

All fixed weights are finite reals. Finite-record boundedness at fixed N and the probability law imply every required record, score, and score-product integral exists. Sample inverse integrability is **not** assumed or needed, since the covariance formula concerns the population-bread linearized score, not b_hat. The exact sample linearization is restricted by det G_w(ω)≠0, and is asserted for every such sample, even on null sets. On singular samples b_hat uses the zero matrix inverse but no linearization is asserted. Item 5's purely algebraic equality remains valid even if entrywise Bochner integrals or covariances have completed values; it does not by itself assert existence of genuine moments.

sqrt(N) is the nonnegative real square root of a natural cast; its input cannot be negative. N≥2 makes it positive in the linearization clauses. ENNReal.toReal is used by real covariance-related conventions as described for T11, but all genuine-model moments are finite. The conditional uniform distribution has finite nonzero normalization. There is no log, rpow, sInf/sSup, limsup/liminf, infinite sequence limit, or partial-function default in T12's statement. The finite-array and generated instance proofs have no extra mathematical content.

## SAP.P018a.T13

The declaration at `Challenge/Part2.lean:69` asserts `T13Statement` together with global strict concavity of the likelihood, through `Defs/WholeW1.lean:31`. There are no outer hypotheses or existentially chosen witnesses. All data are explicitly fixed finite real arrays.

### Complete mathematical statement

There are four units 0,1,2,3 and six dyads, in order {0,1},{0,2},{0,3},{1,2},{1,3},{2,3}. The row vectors are x_d=(1,z_d) with z=(0,2,5,5,1,1); the binary outcomes are y=(1,1,1,0,0,0), and the residual array r=(1/2,1/2,1/2,−1/2,−1/2,−1/2).

For any real t, π(t)=1/(1+exp(−t)). For b∈ℝ², the log-likelihood is ℓ(b)=Σ_d[y_d(x_d·b)−log(1+exp(x_d·b))]. The individual score q_d(b)=(y_d−π(x_d·b))x_d and bread B(b)=Σ_d π(x_d·b)(1−π(x_d·b))x_dx_dᵀ. For any vector scores q define M(q)=Σ_dΣ_{f:d~f}q_dq_fᵀ, including diagonal terms, and M_diag(q)=Σ_dq_dq_dᵀ. For each unit i define U_i(q)=Σ_{d:i∈d}q_d. The printed meat for x and scalar residual array r is P=Σ_{d~f}r_d r_f x_dx_dᵀ. The corrected estimator is V(b)=B(b)⁻¹M(q(b))B(b)⁻¹. These are finite deterministic formulas, not actual sampling covariances defined from an unspecified probability model.

Let H=[[3/2,7/2],[7/2,14]], J=[[8/5,−2/5],[−2/5,6/35]], C=[[38/25,−64/175],[−64/175,192/1225]], K=[[3/2,7/2],[7/2,27/2]]. The asserted conjunction is:

1. For every dyad d, y_d=0 or 1. For every b∈ℝ², ℓ(b)≤ℓ(0). For every b∈ℝ², ℓ(b)=ℓ(0) implies b=0.
2. det B(0)=35/4; B(0)⁻¹ P B(0)⁻¹=J; V(0)=C; and those two sandwiches differ.
3. Σ_d r_d x_d=0; Σ_d(1/4)x_dx_dᵀ=H; det H=35/4; JH=I; P=H; M((r_dx_d)_d)=K; JHJ=J; JKJ=C; and JHJ≠JKJ.
4. J and C are positive definite in Mathlib's real matrix sense: they are symmetric and xᵀJx>0, xᵀCx>0 for every nonzero vector x.
5. For every d, q_d(0)=r_dx_d. The unit-incidence identity M(q(0))=Σ_i U_i(q(0))U_i(q(0))ᵀ−M_diag(q(0)) holds.
6. The printed sandwich minus V(0) is [[2/25,−6/175],[−6/175,18/1225]].
7. For every d, π(x_d·0)=1/2 and y_d−π(x_d·0)=r_d. B(0)=H and B(0)⁻¹=J. The unweighted Gram Σ_dx_dx_dᵀ has determinant 140. For every dyad d, Σ_{f≠d,d~f}r_f=0.
8. The full set ℝ² is convex and for all distinct b,c∈ℝ², then all real a,t>0 with a+t=1, aℓ(b)+tℓ(c)<ℓ(ab+tc). This is exactly Mathlib `StrictConcaveOn ℝ Set.univ ℓ`.

### Junk-value audit

Every logistic denominator 1+exp(−t) is strictly positive. Every log argument 1+exp(t) is strictly positive; Mathlib's totalized real logarithm at zero or on negative reals is never reached. Real exp is mathematical exp without floating-point overflow. All displayed rational denominators are nonzero. B(0) has positive determinant, so all inverses used are ordinary real inverses. Likelihoods at arbitrary b use no matrix inverse. The vectors, matrices, six dyads and four units have fixed positive finite sizes, valid indices, and no empty-index issue. There are no integrals, extended measures, square roots, powers with domain issues, infima/suprema, limsup/liminf, truncated subtraction, or partial-function defaults. The counterexample is not produced by a junk-value convention.

## SAP.P018a.T14

The declaration at `Challenge/Part2.lean:73` asserts the closed proposition at `Defs/Part5.lean:14`. Its docstring calls the formula the corrected logistic score-product estimator and describes incidence, symmetry, and disagreement with the printed expression.

### Complete mathematical statement and quantifier order

First, universally quantify types V,E with specified finite enumerations, and decidable equality on each. Universally quantify s:E→finite subsets of V. Assume (i) every s(d) has exactly two elements and (ii) s is injective (no two records have the same unordered endpoint set). Then universally quantify a natural k, row vectors X:E→ℝ^k, responses Y:E→ℝ, and any coefficient b∈ℝ^k. Assume (iii) every Y_d is 0 or 1 and (iv) det B(b)≠0, where

π(t)=1/(1+exp(−t)), x·b=Σ_a x_ab_a,
r_d=Y_d−π(X_d·b), q_d=r_dX_d,
B(b)=Σ_dπ(X_d·b)(1−π(X_d·b))X_dX_dᵀ.

Define d~f by nonempty intersection s(d)∩s(f); M=Σ_{d~f}q_dq_fᵀ; U_i=Σ_{d:i∈s(d)}q_d; M_diag=Σ_dq_dq_dᵀ; V_hat=B(b)⁻¹ M B(b)⁻¹; and P=Σ_{d~f}r_dr_fX_dX_dᵀ. The conclusion is all of:

1. For every d then f, q_dq_fᵀ=r_dr_fX_dX_fᵀ (entrywise: r_d X_{da} r_f X_{fb}=r_dr_f X_{da}X_{fb}).
2. M=Σ_{i∈V}U_iU_iᵀ−M_diag.
3. Mᵀ=M.
4. V_hatᵀ=V_hat.
5. P=Σ_d[r_d Σ_{f:d~f}r_f]X_dX_dᵀ.

Second, as an independent unconditional conjunct, the fixed four-unit/six-dyad data X=((1,0),(1,2),(1,5),(1,5),(1,1),(1,1)) and r=(1/2,1/2,1/2,−1/2,−1/2,−1/2) satisfy P≠M((r_dX_d)_d). These arrays have exactly the expansions in T13. The statement does not separately assert disagreement of the two inverse sandwiches, global concavity, existence of an MLE, asymptotic consistency, or a probabilistic covariance formula. b is arbitrary and is not assumed to be an MLE or a score root.

### Junk-value audit

π always has a positive denominator, so r and B(b) are ordinary real expressions. The single inverse in each sandwich is nonsingular by the explicit determinant hypothesis; the repeated use of B⁻¹ on the right agrees with its transpose since the bread is symmetric. Empty V or E are technically allowed. If E is empty and k>0, B=0 makes the rank hypothesis impossible; for k=0, det(empty matrix)=1 and the general identities are valid zero-dimensional ones. These harmless edge cases do not exhaust the general statement, and the fixed counterexample has four units, six records and k=2 with nonsingular bread as independently asserted in T13. Finite-set intersections and cardinality use natural numbers but introduce no subtraction or cast pathology; the subtraction in the incidence formula is matrix subtraction over ℝ. There are no log, sqrt, integrals, toReal of infinity, rpow, sInf/sSup, limsup/liminf, or partial-function defaults. Generated index-size witnesses only justify the explicit finite arrays.

# Closure inspection ledger

The following lists each supplied entry, including constructor/field entries and proof constants. Structure constructors and projections are read through their structure declarations. Entries at line 0 were printed and inspected as noted above.

## SAP.P018a.T11 closure

- `SAP.P018a.Dreal` — `SAP/P018a/Defs/Part2.lean:16`.
- `SAP.P018a.Dreal._proof_1` — `SAP/P018a/Defs/Part2.lean:0`.
- `SAP.P018a.Dyad` — `SAP/P018a/Defs/Part1.lean:22`.
- `SAP.P018a.Kernel` — `SAP/P018a/Defs/Part1.lean:140`.
- `SAP.P018a.Kernel.X` — `SAP/P018a/Defs/Part1.lean:142`.
- `SAP.P018a.Kernel.Y` — `SAP/P018a/Defs/Part1.lean:143`.
- `SAP.P018a.Kernel.mk` — `SAP/P018a/Defs/Part1.lean:140`.
- `SAP.P018a.Kernel.μ` — `SAP/P018a/Defs/Part1.lean:141`.
- `SAP.P018a.Mat` — `SAP/P018a/Defs/Part1.lean:14`.
- `SAP.P018a.RepeatedKernel` — `SAP/P018a/Defs/Part2.lean:123`.
- `SAP.P018a.RepeatedKernel.T` — `SAP/P018a/Defs/Part2.lean:125`.
- `SAP.P018a.RepeatedKernel.X` — `SAP/P018a/Defs/Part2.lean:126`.
- `SAP.P018a.RepeatedKernel.Y` — `SAP/P018a/Defs/Part2.lean:127`.
- `SAP.P018a.RepeatedKernel.mk` — `SAP/P018a/Defs/Part2.lean:123`.
- `SAP.P018a.RepeatedKernel.μ` — `SAP/P018a/Defs/Part2.lean:124`.
- `SAP.P018a.Standing` — `SAP/P018a/Defs/Part1.lean:181`.
- `SAP.P018a.Standing._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.T11Statement` — `SAP/P018a/Defs/Part4.lean:165`.
- `SAP.P018a.T11WholeStatement` — `SAP/P018a/Defs/WholeW1.lean:389`.
- `SAP.P018a.T11WholeStatement._proof_1` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.T11WholeStatement._proof_2` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.T5Statement._proof_8` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T5Statement._proof_9` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T8WholeStatement._proof_1` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.T8WholeStatement._proof_2` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.T9Statement._proof_3` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.Vec` — `SAP/P018a/Defs/Part1.lean:12`.
- `SAP.P018a.W1BlockX` — `SAP/P018a/Defs/WholeW1.lean:296`.
- `SAP.P018a.W1CoefficientBlockGram` — `SAP/P018a/Defs/WholeW1.lean:304`.
- `SAP.P018a.W1ConditionalRow` — `SAP/P018a/Defs/WholeW1.lean:316`.
- `SAP.P018a.W1CrossGram` — `SAP/P018a/Defs/WholeW1.lean:313`.
- `SAP.P018a.W1IdenticalSign` — `SAP/P018a/Defs/WholeW1.lean:291`.
- `SAP.P018a.W1MixedKernel` — `SAP/P018a/Defs/WholeW1.lean:308`.
- `SAP.P018a.W1ScaledSignSandwich` — `SAP/P018a/Defs/WholeW1.lean:329`.
- `SAP.P018a.W1ScoreCovRow` — `SAP/P018a/Defs/WholeW1.lean:320`.
- `SAP.P018a.W1SignMean` — `SAP/P018a/Defs/WholeW1.lean:328`.
- `SAP.P018a.W1T11MixedMoments` — `SAP/P018a/Defs/WholeW1.lean:376`.
- `SAP.P018a.W1T11MixedMoments._proof_1` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.W1T11MixedRows` — `SAP/P018a/Defs/WholeW1.lean:384`.
- `SAP.P018a.W1T11Repeated` — `SAP/P018a/Defs/WholeW1.lean:360`.
- `SAP.P018a.W1T11SampleFormula` — `SAP/P018a/Defs/WholeW1.lean:353`.
- `SAP.P018a.W1T11ScalarMoments` — `SAP/P018a/Defs/WholeW1.lean:332`.
- `SAP.P018a.W1T11ScalarMoments._proof_1` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.W1T9Coefficients._proof_3` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.W1T9Tail._proof_2` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.W1WeightScore._proof_1` — `SAP/P018a/Defs/WholeW1.lean:0`.
- `SAP.P018a.W1WrongBlockGram` — `SAP/P018a/Defs/WholeW1.lean:300`.
- `SAP.P018a.conditionalResidualCov` — `SAP/P018a/Defs/Part2.lean:29`.
- `SAP.P018a.conditionalResidualMean` — `SAP/P018a/Defs/Part2.lean:25`.
- `SAP.P018a.conditionalTerm` — `SAP/P018a/Defs/Part2.lean:35`.
- `SAP.P018a.covMat` — `SAP/P018a/Defs/Part1.lean:118`.
- `SAP.P018a.design` — `SAP/P018a/Defs/Part1.lean:163`.
- `SAP.P018a.designSigma` — `SAP/P018a/Defs/Part2.lean:22`.
- `SAP.P018a.dot` — `SAP/P018a/Defs/Part1.lean:18`.
- `SAP.P018a.dyads` — `SAP/P018a/Defs/Part1.lean:20`.
- `SAP.P018a.epsilon` — `SAP/P018a/Defs/Part1.lean:171`.
- `SAP.P018a.fairLaw` — `SAP/P018a/Defs/Part2.lean:74`.
- `SAP.P018a.firstUnit` — `SAP/P018a/Defs/Part1.lean:157`.
- `SAP.P018a.firstUnit._proof_2` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.fittedResidual` — `SAP/P018a/Defs/Part1.lean:87`.
- `SAP.P018a.inProbability` — `SAP/P018a/Defs/Part1.lean:125`.
- `SAP.P018a.meanMat` — `SAP/P018a/Defs/Part1.lean:115`.
- `SAP.P018a.meanVec` — `SAP/P018a/Defs/Part1.lean:112`.
- `SAP.P018a.meat` — `SAP/P018a/Defs/Part1.lean:41`.
- `SAP.P018a.members` — `SAP/P018a/Defs/Part1.lean:24`.
- `SAP.P018a.neighbors` — `SAP/P018a/Defs/Part1.lean:29`.
- `SAP.P018a.outer` — `SAP/P018a/Defs/Part1.lean:16`.
- `SAP.P018a.populationBeta` — `SAP/P018a/Defs/Part1.lean:151`.
- `SAP.P018a.populationGram` — `SAP/P018a/Defs/Part1.lean:148`.
- `SAP.P018a.populationResidual` — `SAP/P018a/Defs/Part1.lean:154`.
- `SAP.P018a.populationScore` — `SAP/P018a/Defs/Part1.lean:175`.
- `SAP.P018a.projection` — `SAP/P018a/Defs/Part2.lean:49`.
- `SAP.P018a.projectionGamma` — `SAP/P018a/Defs/Part2.lean:52`.
- `SAP.P018a.repeatedBeta` — `SAP/P018a/Defs/Part2.lean:149`.
- `SAP.P018a.repeatedBlockScore` — `SAP/P018a/Defs/Part2.lean:156`.
- `SAP.P018a.repeatedGram` — `SAP/P018a/Defs/Part2.lean:143`.
- `SAP.P018a.repeatedH` — `SAP/P018a/Defs/Part2.lean:146`.
- `SAP.P018a.repeatedL` — `SAP/P018a/Defs/Part2.lean:132`.
- `SAP.P018a.repeatedLaw` — `SAP/P018a/Defs/Part2.lean:129`.
- `SAP.P018a.repeatedOLS` — `SAP/P018a/Defs/Part2.lean:153`.
- `SAP.P018a.repeatedTarget` — `SAP/P018a/Defs/Part2.lean:164`.
- `SAP.P018a.repeatedVariance` — `SAP/P018a/Defs/Part2.lean:160`.
- `SAP.P018a.repeatedX` — `SAP/P018a/Defs/Part2.lean:135`.
- `SAP.P018a.repeatedY` — `SAP/P018a/Defs/Part2.lean:139`.
- `SAP.P018a.response` — `SAP/P018a/Defs/Part1.lean:167`.
- `SAP.P018a.sampleGram` — `SAP/P018a/Defs/Part1.lean:81`.
- `SAP.P018a.sampleOLS` — `SAP/P018a/Defs/Part1.lean:84`.
- `SAP.P018a.sampleVariance` — `SAP/P018a/Defs/Part1.lean:90`.
- `SAP.P018a.sandwich` — `SAP/P018a/Defs/Part1.lean:37`.
- `SAP.P018a.score` — `SAP/P018a/Defs/Part1.lean:39`.
- `SAP.P018a.scoreH` — `SAP/P018a/Defs/Part2.lean:46`.
- `SAP.P018a.scoreSum` — `SAP/P018a/Defs/Part1.lean:178`.
- `SAP.P018a.secondUnit` — `SAP/P018a/Defs/Part1.lean:160`.
- `SAP.P018a.signKernel` — `SAP/P018a/Defs/Part2.lean:78`.
- `SAP.P018a.signValue` — `SAP/P018a/Defs/Part2.lean:76`.
- `SAP.P018a.singleRecord` — `SAP/P018a/Defs/Part3.lean:89`.
- `SAP.P018a.uniformUnitLaw` — `SAP/P018a/Defs/Part2.lean:61`.
- `SAP.P018a.unitSampleLaw` — `SAP/P018a/Defs/Part1.lean:145`.
- `SAP.P018a.varMat` — `SAP/P018a/Defs/Part1.lean:122`.
- `SAP.P018a.weightedGram` — `SAP/P018a/Defs/Part2.lean:92`.
- `SAP.P018a.weightedOLS` — `SAP/P018a/Defs/Part2.lean:96`.
- `SAP.P018a.weightedVariance` — `SAP/P018a/Defs/Part2.lean:113`.

## SAP.P018a.T12 closure

- `SAP.P018a.Dreal` — `SAP/P018a/Defs/Part2.lean:16`.
- `SAP.P018a.Dreal._proof_1` — `SAP/P018a/Defs/Part2.lean:0`.
- `SAP.P018a.Dyad` — `SAP/P018a/Defs/Part1.lean:22`.
- `SAP.P018a.Kernel` — `SAP/P018a/Defs/Part1.lean:140`.
- `SAP.P018a.Kernel.X` — `SAP/P018a/Defs/Part1.lean:142`.
- `SAP.P018a.Kernel.Y` — `SAP/P018a/Defs/Part1.lean:143`.
- `SAP.P018a.Kernel.mk` — `SAP/P018a/Defs/Part1.lean:140`.
- `SAP.P018a.Kernel.μ` — `SAP/P018a/Defs/Part1.lean:141`.
- `SAP.P018a.Mat` — `SAP/P018a/Defs/Part1.lean:14`.
- `SAP.P018a.RepeatedKernel` — `SAP/P018a/Defs/Part2.lean:123`.
- `SAP.P018a.RepeatedKernel.T` — `SAP/P018a/Defs/Part2.lean:125`.
- `SAP.P018a.RepeatedKernel.X` — `SAP/P018a/Defs/Part2.lean:126`.
- `SAP.P018a.RepeatedKernel.Y` — `SAP/P018a/Defs/Part2.lean:127`.
- `SAP.P018a.RepeatedKernel.mk` — `SAP/P018a/Defs/Part2.lean:123`.
- `SAP.P018a.RepeatedKernel.μ` — `SAP/P018a/Defs/Part2.lean:124`.
- `SAP.P018a.Standing` — `SAP/P018a/Defs/Part1.lean:181`.
- `SAP.P018a.Standing._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.T12Checks` — `SAP/P018a/Defs/WholeW2.lean:73`.
- `SAP.P018a.T12Checks._proof_1` — `SAP/P018a/Defs/WholeW2.lean:0`.
- `SAP.P018a.T12Checks._proof_2` — `SAP/P018a/Defs/WholeW2.lean:0`.
- `SAP.P018a.T12Checks._proof_3` — `SAP/P018a/Defs/WholeW2.lean:0`.
- `SAP.P018a.T12WholeStatement` — `SAP/P018a/Defs/WholeW2.lean:82`.
- `SAP.P018a.Vec` — `SAP/P018a/Defs/Part1.lean:12`.
- `SAP.P018a.WholeRecordRegular` — `SAP/P018a/Defs/WholeW2.lean:18`.
- `SAP.P018a.WholeRecordRegular._proof_1` — `SAP/P018a/Defs/WholeW2.lean:0`.
- `SAP.P018a.covMat` — `SAP/P018a/Defs/Part1.lean:118`.
- `SAP.P018a.design` — `SAP/P018a/Defs/Part1.lean:163`.
- `SAP.P018a.dot` — `SAP/P018a/Defs/Part1.lean:18`.
- `SAP.P018a.dyads` — `SAP/P018a/Defs/Part1.lean:20`.
- `SAP.P018a.epsilon` — `SAP/P018a/Defs/Part1.lean:171`.
- `SAP.P018a.fairLaw` — `SAP/P018a/Defs/Part2.lean:74`.
- `SAP.P018a.firstUnit` — `SAP/P018a/Defs/Part1.lean:157`.
- `SAP.P018a.firstUnit._proof_2` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.meanMat` — `SAP/P018a/Defs/Part1.lean:115`.
- `SAP.P018a.meanVec` — `SAP/P018a/Defs/Part1.lean:112`.
- `SAP.P018a.meat` — `SAP/P018a/Defs/Part1.lean:41`.
- `SAP.P018a.members` — `SAP/P018a/Defs/Part1.lean:24`.
- `SAP.P018a.neighbors` — `SAP/P018a/Defs/Part1.lean:29`.
- `SAP.P018a.outer` — `SAP/P018a/Defs/Part1.lean:16`.
- `SAP.P018a.overlap` — `SAP/P018a/Defs/Part1.lean:32`.
- `SAP.P018a.populationBeta` — `SAP/P018a/Defs/Part1.lean:151`.
- `SAP.P018a.populationGram` — `SAP/P018a/Defs/Part1.lean:148`.
- `SAP.P018a.populationResidual` — `SAP/P018a/Defs/Part1.lean:154`.
- `SAP.P018a.recordWeightedBeta` — `SAP/P018a/Defs/Part2.lean:201`.
- `SAP.P018a.recordWeightedBlockScore` — `SAP/P018a/Defs/Part2.lean:206`.
- `SAP.P018a.recordWeightedGram` — `SAP/P018a/Defs/Part2.lean:186`.
- `SAP.P018a.recordWeightedH` — `SAP/P018a/Defs/Part3.lean:13`.
- `SAP.P018a.recordWeightedOLS` — `SAP/P018a/Defs/Part2.lean:196`.
- `SAP.P018a.recordWeightedXY` — `SAP/P018a/Defs/Part2.lean:191`.
- `SAP.P018a.repeatedBeta` — `SAP/P018a/Defs/Part2.lean:149`.
- `SAP.P018a.repeatedBlockScore` — `SAP/P018a/Defs/Part2.lean:156`.
- `SAP.P018a.repeatedGram` — `SAP/P018a/Defs/Part2.lean:143`.
- `SAP.P018a.repeatedH` — `SAP/P018a/Defs/Part2.lean:146`.
- `SAP.P018a.repeatedL` — `SAP/P018a/Defs/Part2.lean:132`.
- `SAP.P018a.repeatedLaw` — `SAP/P018a/Defs/Part2.lean:129`.
- `SAP.P018a.repeatedTarget` — `SAP/P018a/Defs/Part2.lean:164`.
- `SAP.P018a.repeatedX` — `SAP/P018a/Defs/Part2.lean:135`.
- `SAP.P018a.repeatedY` — `SAP/P018a/Defs/Part2.lean:139`.
- `SAP.P018a.response` — `SAP/P018a/Defs/Part1.lean:167`.
- `SAP.P018a.sandwich` — `SAP/P018a/Defs/Part1.lean:37`.
- `SAP.P018a.score` — `SAP/P018a/Defs/Part1.lean:39`.
- `SAP.P018a.scoreSum` — `SAP/P018a/Defs/Part1.lean:178`.
- `SAP.P018a.secondUnit` — `SAP/P018a/Defs/Part1.lean:160`.
- `SAP.P018a.signKernel` — `SAP/P018a/Defs/Part2.lean:78`.
- `SAP.P018a.signValue` — `SAP/P018a/Defs/Part2.lean:76`.
- `SAP.P018a.singleRecord` — `SAP/P018a/Defs/Part3.lean:89`.
- `SAP.P018a.trueTarget` — `SAP/P018a/Defs/Part2.lean:18`.
- `SAP.P018a.uniformUnitLaw` — `SAP/P018a/Defs/Part2.lean:61`.
- `SAP.P018a.unitSampleLaw` — `SAP/P018a/Defs/Part1.lean:145`.
- `SAP.P018a.varMat` — `SAP/P018a/Defs/Part1.lean:122`.
- `SAP.P018a.weightedGram` — `SAP/P018a/Defs/Part2.lean:92`.
- `SAP.P018a.weightedPopulationBeta` — `SAP/P018a/Defs/Part2.lean:104`.
- `SAP.P018a.weightedPopulationGram` — `SAP/P018a/Defs/Part2.lean:100`.
- `SAP.P018a.weightedScoreSum` — `SAP/P018a/Defs/Part2.lean:109`.
- `SAP.P018a.weightedTarget` — `SAP/P018a/Defs/Part2.lean:118`.
- `SAP.P018a.wholeMixedKernel` — `SAP/P018a/Defs/WholeW2.lean:67`.
- `SAP.P018a.wholeRecordContract` — `SAP/P018a/Defs/WholeW2.lean:28`.
- `SAP.P018a.wholeRecordSparse` — `SAP/P018a/Defs/WholeW2.lean:45`.
- `SAP.P018a.wholeRepeatedSign` — `SAP/P018a/Defs/WholeW2.lean:62`.

## SAP.P018a.T13 closure

- `SAP.P018a.Mat` — `SAP/P018a/Defs/Part1.lean:14`.
- `SAP.P018a.T13Statement` — `SAP/P018a/Defs/Part4.lean:214`.
- `SAP.P018a.T13Statement._proof_1` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_10` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_11` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_2` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_3` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_4` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_5` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_6` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_7` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_8` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13Statement._proof_9` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T13WholeStatement` — `SAP/P018a/Defs/WholeW1.lean:27`.
- `SAP.P018a.T5Statement._proof_1` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T5Statement._proof_2` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T5Statement._proof_8` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T5Statement._proof_9` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T7Statement._proof_5` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.T9Statement._proof_5` — `SAP/P018a/Defs/Part4.lean:0`.
- `SAP.P018a.Vec` — `SAP/P018a/Defs/Part1.lean:12`.
- `SAP.P018a.dot` — `SAP/P018a/Defs/Part1.lean:18`.
- `SAP.P018a.dyadMeat` — `SAP/P018a/Defs/Part1.lean:49`.
- `SAP.P018a.expit` — `SAP/P018a/Defs/Part1.lean:52`.
- `SAP.P018a.logLikelihood` — `SAP/P018a/Defs/Part3.lean:29`.
- `SAP.P018a.logisticBread` — `SAP/P018a/Defs/Part1.lean:57`.
- `SAP.P018a.logisticScore` — `SAP/P018a/Defs/Part1.lean:54`.
- `SAP.P018a.logisticVariance` — `SAP/P018a/Defs/Part1.lean:61`.
- `SAP.P018a.logitH` — `SAP/P018a/Defs/Part1.lean:77`.
- `SAP.P018a.logitH._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitH._proof_2` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitH._proof_3` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitHinv` — `SAP/P018a/Defs/Part1.lean:79`.
- `SAP.P018a.logitHinv._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitHinv._proof_2` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitHinv._proof_3` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitR` — `SAP/P018a/Defs/Part1.lean:75`.
- `SAP.P018a.logitX` — `SAP/P018a/Defs/Part1.lean:71`.
- `SAP.P018a.logitX._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitX._proof_2` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitY` — `SAP/P018a/Defs/Part1.lean:73`.
- `SAP.P018a.meat` — `SAP/P018a/Defs/Part1.lean:41`.
- `SAP.P018a.outer` — `SAP/P018a/Defs/Part1.lean:16`.
- `SAP.P018a.printedLogisticMeat` — `SAP/P018a/Defs/Part1.lean:65`.
- `SAP.P018a.sampleGram` — `SAP/P018a/Defs/Part1.lean:81`.
- `SAP.P018a.sandwich` — `SAP/P018a/Defs/Part1.lean:37`.
- `SAP.P018a.score` — `SAP/P018a/Defs/Part1.lean:39`.
- `SAP.P018a.sixMembers` — `SAP/P018a/Defs/Part1.lean:69`.
- `SAP.P018a.sixMembers._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.unitScore` — `SAP/P018a/Defs/Part1.lean:45`.

## SAP.P018a.T14 closure

- `SAP.P018a.Mat` — `SAP/P018a/Defs/Part1.lean:14`.
- `SAP.P018a.T14Statement` — `SAP/P018a/Defs/Part5.lean:13`.
- `SAP.P018a.Vec` — `SAP/P018a/Defs/Part1.lean:12`.
- `SAP.P018a.dot` — `SAP/P018a/Defs/Part1.lean:18`.
- `SAP.P018a.dyadMeat` — `SAP/P018a/Defs/Part1.lean:49`.
- `SAP.P018a.expit` — `SAP/P018a/Defs/Part1.lean:52`.
- `SAP.P018a.logisticBread` — `SAP/P018a/Defs/Part1.lean:57`.
- `SAP.P018a.logisticScore` — `SAP/P018a/Defs/Part1.lean:54`.
- `SAP.P018a.logisticVariance` — `SAP/P018a/Defs/Part1.lean:61`.
- `SAP.P018a.logitR` — `SAP/P018a/Defs/Part1.lean:75`.
- `SAP.P018a.logitX` — `SAP/P018a/Defs/Part1.lean:71`.
- `SAP.P018a.logitX._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.logitX._proof_2` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.meat` — `SAP/P018a/Defs/Part1.lean:41`.
- `SAP.P018a.outer` — `SAP/P018a/Defs/Part1.lean:16`.
- `SAP.P018a.printedLogisticMeat` — `SAP/P018a/Defs/Part1.lean:65`.
- `SAP.P018a.sandwich` — `SAP/P018a/Defs/Part1.lean:37`.
- `SAP.P018a.score` — `SAP/P018a/Defs/Part1.lean:39`.
- `SAP.P018a.sixMembers` — `SAP/P018a/Defs/Part1.lean:69`.
- `SAP.P018a.sixMembers._proof_1` — `SAP/P018a/Defs/Part1.lean:0`.
- `SAP.P018a.unitScore` — `SAP/P018a/Defs/Part1.lean:45`.
