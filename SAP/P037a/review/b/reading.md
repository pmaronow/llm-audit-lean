# Blind reading of the Lean statements

This file was written from `SAP/P037a/Defs*.lean`, `SAP/P037a/Defs/*.lean`, and `SAP/P037a/Challenge/*.lean`, before opening either `claims.json` or `record.json`. The theorem names below are fully qualified by `SAP.P037a`. All thirteen theorems have no external parameters or hypotheses: each asserts the conjunction called `TnStatement`. The universal quantifiers and conditional hypotheses inside those conjunctions are described below.

## Common meanings and Mathlib conventions

A `Design Ω`, for a finite type Ω, is a real vector d(w) with d(w) ≥ 0 for every w and Σw d(w) = 1. Write E_d X = Σw d(w)X(w), Var_d X = E_d(X²) − (E_d X)², and Cov_d(X,Y) = E_d(XY) − E_d X E_d Y. Event probabilities are expectations of their 0/1 indicators. A design cannot exist on an empty Ω. `independentDesign d` is the finite product design on functions w with coordinate laws d_i, with mass Πi d_i(w_i); this imposes independence between coordinates. Empty products and sums have their ordinary mathematical meanings.

`Fin n` means the integers 0,…,n−1, `Finset` means a finite subset, `Nat.choose` means the binomial coefficient (zero beyond its upper argument). Natural subtraction is truncated; real and integer subtraction is not. Real division is total, with a/0 = 0. Matrix inverse is Mathlib's adjugate/determinant inverse, equal to the zero matrix for a singular matrix, not a generalized inverse (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:166–176`). `mulVec` is ordinary finite matrix-vector multiplication. None of these statements uses a limsup.

`volume` is Lebesgue measure (product Lebesgue measure on finite real coordinate spaces). `restrict`, `Measure.pi`, and `Measure.map` are restriction, finite product, and pushforward of measures, respectively. Pushforward has the intended probability meaning when its map is measurable; the maps here are continuous or Borel measurable, including real division with its total convention. Set integrals are Bochner integrals against restricted Lebesgue measure; interval integrals are oriented interval integrals. Mathlib sets a nonintegrable Bochner integral to zero; the functions appearing here are elementary integrable functions on their specified domains. An extended nonnegative measure is converted by `.toReal`; this sends infinity to zero, so finiteness matters. `gaussianReal 0 1` is the probability measure with mean zero and **variance** one; write Φ(x) for its mass on (−∞,x]. `expMeasure 1` has rate one and density exp(−x) on x ≥ 0. `Tendsto ... atTop (nhds a)` is an ordinary sequence limit as the natural index tends to infinity.

## Four-school construction used in T1, T2, and T10

There are four schools i = 0,1,2,3 and six unordered pairs (0,1),(0,2),(0,3),(1,2),(1,3),(2,3). For pair w, D_i(w) is 1 on its two members and 0 elsewhere. The uniform pair design has mass 1/6. Two independent pairs have mass 1/36 each.

Let q = (1/10,1/10,3/10,3/10), and r_i = 1 for i < 2 and 3 otherwise. For r ∈ ℕ and k = 0,…,3 define h_r(k) = choose(r,k) choose(10−r,5−k)/choose(10,5), using natural subtraction. For k = 0,…,12, let p_r(k) = Σ_{c∈{0,1,2,3}^4 : Σs c_s=k} Πs h_r(c_s). The composition assignment space consists of a pair w and two counts k,l ∈ {0,…,12}, with mass (1/6)p_{r_first}(k)p_{r_second}(l). Write E for this specific weighted sum. C_i equals k/20 on the first selected school, l/20 on the second, and zero otherwise. R_i = C_i − D_i q_i. All sums over assignments retain zero-mass assignments.

For four-vectors x,y put Q(x,y) = Σi x_i y_i − (Σi x_i)(Σi y_i)/4. Regression columns are X = (D,q,C). G_kl = E Q(X_k,X_l). The witness potential outcomes are Y_i(0,c)=3/10 and Y_i(1,c)=3/10−q_i, with observed outcome Y_i=3/10−D_iq_i. Its right side v_k is E Q(X_k,Y). The five-real-parameter schedule is Y_i(0,c)=a+gq_i, Y_i(1,c)=a+gq_i+τ+b₁(c−q_i)+b₂(q_i−1/5); its observed outcome is a+τD_i+b₁(C_i−D_iq_i)+b₂D_i(q_i−1/5)+gq_i.

## T1

The fixed construction satisfies all the following, with no premises:

* Its masses are nonnegative and sum to one. For every school i, E D_i=1/2, 2E C_i=q_i, and 2E R_i²=q_i(1−q_i)/36. For every school i and every k ∈ {0,…,12} with k ≤ 4, p_{r_i}(k)>0.
* For every i and every real c,c′, Y_i(1,c)−Y_i(1,c′)=0. For every real c, the average over four schools of Y_i(1,c)−Y_i(0,c) is −1/5.
* For every θ∈ℝ³, Gθ=v if and only if θ=(−3/31,−15/62,−16/31), and −16/31≠0.
* G has rows (1,0,1/5), (0,1/25,1/50), (1/5,1/50,151/2400); v=(−1/5,−1/50,−17/300); det G=31/60000≠0.
* For every real a,τ,b₁,b₂,g, first: for every i,c,c′ the treated potential-outcome difference is b₁(c−c′), and for every c the four-school average treatment effect is τ+b₁(c−1/5). Second: there exists θ solving the expected normal equations for that schedule; every other solution equals θ; θ₂=(15b₁+16b₂)/31; and θ₂=b₁ iff b₁=b₂.
* For every assignment and school, and every potential-outcome argument i,treated,c, the schedule with parameters (3/10,−1/5,0,−1,0) agrees with the witness's observed and potential outcomes, respectively.

There is no statement about a sequence of independently repeated blocks or sample OLS limits.

## Block regression notation used in T2

For B blocks, the school index is I=Fin B × Fin 4. Put M(x,y)=Σ_b Σ_i Σ_j (1_{i=j}−1/4)x_{bi}y_{bj}, equivalently the sum of within-block centered cross products. Write NE(d,X,Y,θ) for the equations E_d M(X_k,Y)=Σ_l θ_l E_d M(X_k,X_l), for every k. Write ENE(d,W,R,Y,δ,β) for those equations with an added column R: for every k, E_d M(W_k,Y)=Σ_l δ_l E_d M(W_k,W_l)+β E_d M(W_k,R), and also E_d M(R,Y)=Σ_l δ_l E_d M(R,W_l)+β E_d M(R,R).

CR(d,D,R) means: for **every** real-valued function f of the **entire** Boolean treatment vector D and every school i, E_d[f(D)R_i]=0. In the finite setting this expresses zero conditional mean of R_i given the full treatment vector on its positive-probability values. It is an explicit premise wherever used below.

## T2

The following thirteen assertions are conjoined:

1. For every natural H, natural vectors N,n of length H, and referent subsets refs_h ⊆ Fin(N_h), assume N_h>0 for each h, n_h≤N_h for each h, and Σh n_h>0. Set K_h=|refs_h|, μ=[Σh n_h K_h/N_h]/Σh n_h. An assignment independently selects a subset z_h of size n_h from each stratum; each complete assignment has mass [Πh choose(N_h,n_h)]⁻¹. These masses sum to one. Its referent composition C(z)=[Σh |refs_h∩z_h|]/Σh n_h has mean μ and centered second moment [Σh V_h]/(Σh n_h)², where V_h=0 if N_h=1, otherwise n_h(K_h/N_h)(1−K_h/N_h)(N_h−n_h)/(N_h−1). These are unconditional statements under this finite seed-assignment law.
2. For every H,N,K,n and real f, assuming each N_h≠0, Σh n_h≠0 as a real sum, and n_h=f N_h for every h, μ=Σh K_h/Σh N_h. No feasibility bound on K,n is required for this algebraic implication.
3. For N=(13,14,14,14), K=(2,1,0,0), n=(7,7,7,7), eligible share=3/55, μ=41/728, difference=71/40040≠0.
4. For every finite Ω,K, B, d, regressor array X, block intercepts α, coefficients θ, error err and outcome Y, assume pointwise Y_{bi}=α_b+Σk θ_kX_{k,bi}+err_{bi}, and E_d M(X_k,err)=0 for every k. Then NE(d,X,Y,θ). If, additionally, the expected Gram linear map is injective, then for every v satisfying NE(d,X,Y,v), v=θ.
5. For every six real numbers a,t,b,D,C,μ: a+Dt+bDC=a+D(t+bμ)+bD(C−μ).
6. For every finite Ω,B,d, Boolean array D and real array R satisfying CR(d,D,R), and every vector-valued function V of D, E_d M(R,V(D))=0.
7. For every finite Ω,K,B,d,D,C and fixed real school arrays μ,a,t, every nuisance-column function W of D, real b,β and vector δ, assume CR for R_i=D_i(C_i−μ_i); assume ENE(d,W(D),R,a+Dt+bDC,δ,β); and assume E_d M(R,R)>0. Then β=b.
8. For every finite Ω,K (with decidable equality), B,d,W,R,Z,Y, chosen index e∈K, assume pointwise Z=R+W_e; then for every δ,β, ENE(d,W,Z,Y,δ,β) iff ENE(d,W,R,Y,δ+βe_e,β).
9. For all real D,C,μ,q: D(C−q)=D(C−μ)+D(μ−q); if μ=q, then D(C−μ)=D(C−q) and Dμ=Dq.
10. In the fixed four-school construction E Q(R,R)=1/160. Expected normal-equation solutions are unique with the following exact coefficients, in the stated column order: witness Y on (D,q,C,Dq): (0,0,0,−1); witness Y on (D,q,R): (−1/5,−1/2,0); Y+C/5 on (D,q,C): (−3/31,−15/62,−49/155); Y+C/5 on (D,q,R): (−4/25,−2/5,1/5); Y+C/5 on (D,q,C,Dq): (0,0,1/5,−1); and outcome 3/10−D/5−q/2+C/5 on (D,q,C): (−1/5,−1/2,1/5). Each uniqueness is an iff for **every** coefficient vector.
11. Under the same quantifier order as (6), CR implies E_d Σi V(D)_i R_i=0 for every V.
12. For every finite Ω,K,B,d,D,R, assume CR; then for every vector-valued A(D), nuisance columns W(D), real b,β and δ, ENE(d,W(D),R,A(D)+bR,δ,β) implies β E_d M(R,R)=b E_d M(R,R). No positive-variation premise is imposed here.
13. For every finite Ω,K (decidable equality), B,d,D,C,μ,a,t,W,e,b,β,δ, assume W_e(D)_i=D_iμ_i, CR for R=D(C−μ), ENE(d,W(D),DC,a+Dt+bDC,δ,β), and E_d M(R,R)>0; then β=b.

## T3

For every real p, it is not the case that p<1/20 and p≥1/20. For every critical value c with 19/10≤c≤2, both (estimate,se)=(−57/1000,7/250) and (−57/1000,17/500) satisfy estimate<0, 11/200<|estimate|<13/200, and 1/40<se<7/200. Their Wald ratios |estimate|/se are 57/28 and 57/34, respectively, with 57/34<c<57/28. For every estimate,se in those strict bins, 11/7<|estimate|/se<13/5, and (6/100)/(3/100)=2. Conversely, for every z strictly between 11/7 and 13/5, there exist a,se in the strict positive magnitude and SE bins with a/se=z. No normal tail, normal quantile or P-value is specified.

## T4 and T5: weight laws and WLS notation

U is Lebesgue measure restricted to (0,1), a probability law. For n≥0 let L_n be the pushforward of n+2 independent U draws by w_i↦w_i/Σj w_j. For m≥0 define the open coordinate simplex S_m={p∈ℝ^m: each p_i>0, Σi p_i<1}. A_m appends 1−Σi p_i as its last coordinate. Define H_m=(A_m)_*(m!·Lebesgue|S_m). The ratio event E_n is {p∈ℝ^{n+2}: p_0/(p_0+p_1)<1/4}.

For finite rows I and columns K, WLS(w,X,y,b) means Σi w_i X_ik(y_i−Σl X_il b_l)=0 for every k. The coefficient function is (Xᵀdiag(w)X)⁻¹Xᵀdiag(w)y, using the total matrix inverse above.

T4 asserts:

* For **every** natural n, L_n(E_n).toReal=1/6, H_{n+1}(E_n).toReal=1/4, and L_n≠H_{n+1}. Both event measures are finite.
* For **every** positive real u,v,total, (u/total)/(u/total+v/total)=u/(u+v), and u/(u+v)<1/4 iff u<v/3.
* The iterated interval integral ∫₀¹∫₀^{v/3}1 du dv=1/6. Separately, ∫_{v>0}exp(−v)dv=1 and ∫_{v>0}exp(−4v/3)dv=3/4; also 1−3/4=1/4, 1/6≠1/4 and 1/6−1/4=−1/12.
* For **every** finite I,K with decidable column equality, weights w, matrix X, response y, vector b, assuming every w_i>0 and X.mulVec injective, and then **every** c>0: the coefficient vector for cw equals that for w, and WLS(cw,X,y,b) iff WLS(w,X,y,b).
* For **every** finite K with decidable equality, natural n, positive weights on n+2 rows, full-column-rank X and response y, normalizing weights by their sum preserves the coefficient vector.

T5 asserts the pushforward of U by v↦−log v is exactly `expMeasure 1`; for **every** natural m the integral ∫_{t>0}t^m exp(−t)dt=m!; and all of T4's law distinction, event finiteness, WLS scaling and normalization statements. It does not assert that normalized independent exponentials have law H_m, a joint independence theorem for transformed uniforms, or any simplex support/total-mass theorem.

## T6

Without premises: natural subtraction 2695−2012=683; (2695−2012)/2695=683/2695; 49/200<683/2695<51/200; 683/2695<59/200 and ≠3/10; 6830≠8085; 11/200≤683/11938<13/200; 9/40<2695/11938<23/100; 3/10−1/4=1/20 and (1/20)/(3/10)=1/6.

For every real A,B, assuming 5389/2≤A≤5391/2 and 4023/2≤B≤4025/2, 1364/5389≤1−B/A≤1368/5391, and 49/200<1364/5389 and 1368/5391<51/200. For every real e,m, assuming 11/200≤e≤13/200 and 39/200≤m≤41/200: (3/50)/(1/5)=3/10, 11/41≤e/m and 51/200<e/m.

## T7 and T8

An exposure configuration x consists of natural numbers (school,seed,peers,referentPeers). Feasibility means school≤1, seed≤school, referentPeers≤peers. There is no additional bound on peers or condition forcing peers to vanish when school=0. The five case labels are control, school, nonreferent, referent, direct.

The **printed** predicates are: control iff school=0; school iff school=1, seed=0, peers=0; nonreferent iff school=1 and referentPeers=0; referent iff school=1, seed=0 and referentPeers>0; direct iff seed=1. The **corrected** predicates change only nonreferent, to school=1, seed=0, peers>0, referentPeers=0.

T7 asserts the feasible x=(1,0,0,0) satisfies the distinct printed school and nonreferent cases, and feasible x=(1,1,0,0) satisfies the distinct printed nonreferent and direct cases. There does not exist a function f from all configurations to labels such that, for every feasible x and **every** label e whose printed predicate holds, f(x)=e. For every feasible x, its printed school predicate implies its printed nonreferent predicate; and school=1, seed=1, referentPeers=0 imply both printed nonreferent and direct predicates.

T8 asserts: for **every** feasible configuration x, there exists exactly one label e satisfying the corrected predicate. The two configurations above have corrected labels school and direct, respectively.

## T9

For **every** finite Ω, design d and decidable event E, put X=1_E and π=E_d X. Var_d X=π(1−π). For **every** J>0, under J independent copies of d, F_J=Σj X(w_j)/J satisfies E F_J=π, Var F_J=π(1−π)/J≤1/(4J); and for **every** ε>0, P(|F_J−π|>ε)≤1/(4Jε²). For **every** ε>0, these error probabilities for J+1 draws tend to zero as J→∞.

Separately, for **every** natural J>0 and real v,target, the indicator of (Σ_{j∈Fin J}v)/J=target equals the indicator of v=target. Here the summand is deliberately constant in j. The frequency function is defined as Σj 1_{draw_j=target}/J; its value for draws (0,1) and target 1 is 1/2. Also the indicators of (1+1)/2=1 and (0+1)/2=1 are 1 and 0, respectively.

## T10

The four-school treatment indicators are binary and sum to two for every pair assignment. Every school's treatment mean under the uniform six-pair design is 1/2. For **every** distinct schools i,j, E D_iD_j=1/6, Cov(D_i,D_j)=−1/12, Cov(1−D_i,1−D_j)=−1/12, and E D_iD_j≠E D_i E D_j.

Additionally, for **every** finite Ω, design d and four random real variables T_i, assuming they are binary at every outcome, sum to two at every outcome and have means 1/2 each, Var(Σi T_i)=0, Σi Var(T_i)=1, Σ_{i≠j}Cov(T_i,T_j)=−1, and there exist distinct i,j with negative covariance. The off-diagonal sum is over ordered pairs.

For the product of two uniform pair assignments the joint mass factors as the product of its marginal masses, and for **every** school i in the first block and j in the second, the treatment covariance is zero. There are 36 assignments, each with probability 1/36.

## T11: retained rows and estimators

A `RetainedRow B` supplies, for each block b∈Fin B: a natural student count n_b; a finite assignment count A_b; a design d_b on Fin A_b; a Boolean exposure I_{bi}(z); fixed real potential outcomes y_{bi} and predictions g_{bi}; probabilities π_{bi}=E_{d_b}I_{bi} strictly positive for **every** retained student. Let N=Σb n_b, h(I,π,y,g)=g+(I/π)(y−g), Z_b(z)=Σi h(I_{bi}(z),π_{bi},y_{bi},g_{bi}), V=Σb Var_{d_b}Z_b. Complete assignments have the independent product law. Define μ̂(w)=Σb Z_b(w_b)/N and μ=Σbi y_{bi}/N.

A row sequence r_B has B+1 blocks. `BlockBounds(r,m,c,η,K)` means c>0, η>0, K≥0, and for **every** B: N_B≥c(B+1), and for **every** b: n_{Bb}≤m, and for **every** student i: π_{Bbi}≥η, |y_{Bbi}|≤K, |g_{Bbi}|≤K. Thus m is a fixed natural upper bound. Write A=K+2K/η below.

A paired exposure s on a row uses the **same students, block assignments and laws**, and supplies another Boolean exposure, fixed y′,g′ and strictly positive correctly defined π′. Put Z_b^Δ=Z_b−Z′_b, μ^Δ=Σbi(y−y′)/N, μ̂^Δ=Σb Z_b^Δ/N. Exposures within a block, including the two exposures, need not be independent or disjoint.

With q fixed covariates, x_{bik} are deterministic real arrays. For positive supplied probabilities p, define F(β,p,w)=N⁻¹Σbi h(I_{bi}(w_b),p_{bi},y_{bi},Σk x_{bik}β_k). Let β̂(p,w)=G(p,w)⁻¹v(p,w), where G_kl=Σbi (I/p)x_kx_l and v_k=Σbi(I/p)x_ky. Define population Q_B,kl=N_B⁻¹Σbi x_kx_l and v_B,k=N_B⁻¹Σbi x_ky.

T11 conjoins sixteen assertions:

1. For every finite design d, real random variable I, and real π,y,g, assume π≠0 and E_d I=π; then E_d h(I,π,y,g)=y. Binary I is **not** required for this identity.
2. For every real I,π,y,g,K,η, assume I∈{0,1}, η>0, π≥η, |y|≤K and |g|≤K; then |h(I,π,y,g)|≤K+2K/η.
3. For every B,row r and block b, E_{d_b}Z_b=Σi y_{bi}.
4. For every B,row r with N>0, E μ̂=μ and Var μ̂=V/N² under its product law.
5. For every B,row r and block-specific arbitrary real functions f_b, E Πb f_b(Z_b)=Πb E_{d_b}f_b(Z_b).
6. For every row sequence r,m,c,η,K satisfying BlockBounds, and then every B,ε>0: |Z_b(z)|≤mA for every b,z; Var Z_b≤m²A² for every b; V_B/N_B²≤m²A²/[c²(B+1)]; and P(|μ̂_B−μ_B|>ε)≤m²A²/[c²(B+1)ε²].
7. Under the same bounds, for every ε>0 the last error probability tends to zero as B→∞.
8. For every such sequence and constants additionally σ²>0 and V_B≥σ²(B+1) for every B: first, for every B,ε>0 such that 2mA<ε√(σ²(B+1)), the sum over b of E[(Z_b−E Z_b)² 1_{|Z_b−E Z_b|>ε√V_B}] is exactly zero. Second, for every real x, P(N_B(μ̂_B−μ_B)/√V_B≤x)→Φ(x).
9. For every single row, m,η,K, assume η>0, K≥0, n_b≤m and the bounds π≥η, |y|,|g|≤K for every b,i. Then |Z_b(z)−E Z_b|≤2mA for every b,z.
10. For every row with N>0 and every complete assignment w, Σb[Z_b(w_b)−E Z_b]=N(μ̂(w)−μ).
11. For every row with N>0, paired exposure s, m,η,K satisfying η>0,K≥0,n_b≤m and both exposures' probability/outcome/prediction bounds: E μ̂^Δ=μ^Δ; Var μ̂^Δ=Σb Var Z_b^Δ/N²; |Z_b^Δ(z)|≤2mA; Var Z_b^Δ≤(2mA)².
12. For every row sequence satisfying BlockBounds and every paired-exposure sequence satisfying the same η,K bounds: for every ε>0, P(|μ̂_B^Δ−μ_B^Δ|>ε)→0. Moreover, for every v>0 such that Σb Var Z_{Bb}^Δ≥v(B+1) for all B, and every x∈ℝ, P(N_B(μ̂_B^Δ−μ_B^Δ)/√(Σb Var Z_{Bb}^Δ)≤x)→Φ(x).
13. Under the assumptions of (12), for every B,ε>0, Var μ̂_B^Δ≤(2mA)²/[c²(B+1)] and its ε-error probability is ≤(2mA)²/[c²(B+1)ε²].
14. Under the assumptions of (12) plus v>0 and the same lower contrast-variance bound, for every B,ε>0 such that 4mA<ε√(v(B+1)), the contrast-centered Lindeberg sum E[(Z_b^Δ−E Z_b^Δ)²1_{|Z_b^Δ−E Z_b^Δ|>ε√(Σb Var Z_b^Δ)}], summed over b, is zero.
15. For every B,q,row with N>0,covariates x,β̂,β*,supplied probabilities p,assignment w, assuming every p_{bi}>0, two exact identities hold: F(β̂,π,w)−F(β*,π,w)=Σk[N⁻¹Σbi(1−I/π)x_k](β̂_k−β*_k); and F(β̂,p,w)−F(β̂,π,w)=N⁻¹Σbi I(y−Σk x_kβ̂_k)(p⁻¹−π⁻¹).
16. For every natural q,row sequence r,covariates x,assignment-dependent probability arrays p̂,m,c,η,K,L,matrix Q∈ℝ^{q×q},vector v∈ℝ^q, assume BlockBounds; |x_{Bbik}|≤L for all indices; each entry Q_B→Q and v_B→v; aᵀQa>0 for every nonzero a; every p̂ is positive; for every ε>0, P(there exist b,i with √(B+1)|p̂−π|>ε)→0; and for every B,b,i, g_{Bbi}=Σk x_{Bbik}(Q⁻¹v)_k. Define β*=Q⁻¹v, β̂_B(w)=β̂(p̂_B(w),w), and μ̂_fit=F(β̂_B,p̂_B,w). Then: for every ε>0, P(there exists k with |β̂_{Bk}−β*_k|>ε)→0; for every ε>0, P(√(B+1)|μ̂_fit−μ̂_oracle|>ε)→0; for every ε>0, P(|μ̂_fit−μ_B|>ε)→0; and, for every σ²>0 with V_B≥σ²(B+1) for all B and every real z, P(N_B(μ̂_fit−μ_B)/√V_B≤z)→Φ(z).

For q=0 the coefficient vector is the sole empty vector; this is one permitted case of a universal result, not a requirement on all cases. On singular observed Gram matrices the fitted coefficient function is zero by the total inverse convention; sample full rank is not an explicit hypothesis.

## T12

Define e(n), for natural n, to be 40 if n≤200; otherwise 64 if n≥550; otherwise 4[10+floor((6(n−200)+175)/350)], using natural subtraction and division. For every pair of integers n,k, 350k≠3500+6(n−200)−175. For every natural n, 40≤e(n)≤64 and 4 divides e(n); e is nondecreasing. For every n, e(n)=64 iff n≥521; in particular n≥550 implies e(n)=64. The real unrounded line 40+24(n−200)/350 equals 40 at n=200 and 64 at n=550. Exact counts are e(100)=e(200)=40 and e(375)=52. Eligible shares at n=100,200,375,550,715 are respectively 2/5,1/5,52/375,64/550,64/715. No eligible-share expression at n=0 is asserted.

## T13

Let f(t,b,c)=t+bc and reduction(control,treated)=(control−treated)/control. Without premises f(4/100,−85/100,1/5)=−13/100, and reduction(1/5,8/100)=3/5.

For every real t,b,m, assume 35/1000≤t≤45/1000, −855/1000≤b≤−845/1000, and 222/1000≤m≤223/1000. Then −136/1000≤f(t,b,1/5)≤−124/1000; 86/1000≤m+f≤99/1000; m+f does not lie in [75/1000,85/1000]; 95/1000 lies in [86/1000,99/1000]; 124/223≤−f/m≤68/111; and both 57/100 and 3/5 lie in that last interval. Separately, for every real t,b in the same coefficient intervals, the same bounds on f hold without a hypothesis on m. Interval membership for 57/100,3/5,95/1000 is all that is asserted; these are not declared to be the actual prediction for every t,b,m.
