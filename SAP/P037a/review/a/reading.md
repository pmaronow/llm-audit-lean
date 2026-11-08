# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. This reads the actual propositions in `SAP/P037a/Defs`, rather than using the Challenge docstrings to supply mathematical clauses. All thirteen exported theorems are closed propositions with no external hypotheses; the conditional assertions below are conjuncts inside those propositions. All scalar arithmetic is real unless explicitly described as natural or integer arithmetic.

## Shared definitions and Mathlib semantics

A `Design Ω` is a finite set Ω with a weight p(ω) ≥ 0 for every ω and ∑ω p(ω) = 1. Write E for its weighted sum. Thus Var X = E[X²] − (EX)² and Cov(X,Y) = E[XY] − EX EY. An empty Ω cannot carry a Design. `probability` is the weighted sum of an event's indicator. `independentDesign` on a finite family of designs gives each tuple the product of its coordinate weights.

Schools are numbered 0,1,2,3. The six equally likely treatment pairs are (0,1),(0,2),(0,3),(1,2),(1,3),(2,3); D_i is their membership indicator. `blockDesign` assigns weight 1/6 to each pair. `doubleBlockDesign` assigns 1/36 to each ordered pair of pairs. For school vectors x,y let H(x,y) = ∑i x_i y_i − (∑i x_i)(∑i y_i)/4. For B blocks, H_B is the sum of H over the blocks, equivalently ∑b,i,j (1{i=j}−1/4)x_bi y_bj.

An exposure configuration x=(s,d,p,r) consists of four natural numbers with feasibility s≤1, d≤s, r≤p. There is no other feasibility restriction. The five labels are control, school, nonreferent, referent, direct. The printed predicates are, respectively: s=0; s=1 and d=0 and p=0; s=1 and r=0; s=1 and d=0 and r>0; d=1. The corrected nonreferent predicate is s=1 and d=0 and p>0 and r=0; the other four predicates are unchanged.

For J draws, `frequency` is (∑j 1{draw_j=target})/J. `contribution(I,π,y,g)` is g+(I/π)(y−g). `reduction(A,B)` is (A−B)/A. `fittedEffect(t,b,c)` is t+bc. `waldStatistic(e,s)` is |e|/s. `tableS6Bins(e,s)` means e<0, 11/200<|e|<13/200, and 1/40<s<7/200.

`uniformDraw` is Lebesgue measure restricted to (0,1), a probability measure. For a finite real vector w, `normalizedWeights(w)_i=w_i/∑j w_j`. The open m-simplex is {p in R^m: every p_i>0, ∑p_i<1}. `simplexLaw(m)` is the pushforward of m! times Lebesgue measure on that open simplex under p↦(p_0,...,p_(m−1),1−∑p_i); it is a measure on m+1 coordinates. `uniformWeightLaw(n)` is the pushforward of n+2 independent `uniformDraw`s under normalization. `ratioEvent(n)` is {p:p_0/(p_0+p_1)<1/4} on n+2 coordinates. `Measure.map` is the pushforward for measurable maps; all the maps here are measurable (normalization is a Borel rational map with totalized division). Volume on finite function spaces is the product of coordinate Lebesgue measures. `ENNReal.toReal` agrees with the real mass when finite and sends infinity to zero; T4 and T5 explicitly assert finiteness of the event masses.

`WLS(w,X,y,b)` means each normal equation ∑i w_i X_ik(y_i−∑l X_il b_l)=0. `gramWeighted` has entries ∑i w_i X_ik X_il, and `rhsWeighted` entries ∑i w_i X_ik y_i. `wlsCoefficient=G⁻¹v`. Mathlib's square matrix inverse is the genuine inverse when the determinant is nonzero and the zero matrix otherwise, not a pseudoinverse. `mulVec` is ordinary matrix-vector multiplication. Real division has 0⁻¹=0. Natural subtraction is truncated and natural division is integer floor division.

The displayed integrals use Mathlib's real Bochner integral against Lebesgue measure; set integrals restrict the measure and interval integrals are oriented. The Bochner integral is defined as zero for a nonintegrable function. The particular functions used here (constants on bounded intervals, decaying exponentials, and polynomial times a decaying exponential) are integrable. `expMeasure(1)` is the real exponential probability distribution with density e^(−x) on x≥0. `gaussianReal(0,1)` is the real N(0,1) probability distribution (second parameter is variance). `Tendsto ... atTop (nhds a)` is ordinary convergence along natural indices to a. Thus the event-probability limits below express convergence in probability or convergence of distribution functions as indicated.

Sources followed in Mathlib: `Data/Matrix/Mul.lean` (`mulVec`); `LinearAlgebra/Matrix/NonsingularInverse.lean` (`inv`, `nonsing_inv_apply_not_isUnit`); `MeasureTheory/Measure/Map.lean` and `Restrict.lean`; `MeasureTheory/Constructions/Pi.lean`; `MeasureTheory/Integral/Bochner/Basic.lean` and `Integral/IntervalIntegral/Basic.lean`; `Probability/Distributions/Gamma.lean`, `Exponential.lean`, and `Gaussian/Real.lean`. The natural `choose` is the binomial coefficient (zero outside its natural range).

## SAP.P037a.T1

The fixed design has q=(1/10,1/10,3/10,3/10). In a stratum with ten students and r referents define h_r(k)=choose(r,k)choose(10−r,5−k)/choose(10,5), k=0,1,2,3. Define a_r(k), k=0,...,12, as the fourfold convolution of this mass. Each school i has r_i=1 or 3 according as i<2 or i≥2. An assignment ω is a treatment pair together with two counts k,l∈{0,...,12}, with mass (1/6)a_(r_first)(k)a_(r_second)(l). Z_i equals k/20 or l/20 at the first or second treated school, and zero at controls. E below is this mass-weighted sum. Outcomes are Y_i(0,c)=3/10 and Y_i(1,c)=3/10−q_i, for every real c; observed Y_i=3/10−D_i q_i. The regression columns are (D,q,Z), with block-centered expected Gram G and right side v.

The theorem asserts their masses are nonnegative and sum to one; for every school i, ED_i=1/2, 2EZ_i=q_i, and 2E[(Z_i−D_iq_i)²]=q_i(1−q_i)/36. For every i and every k∈Fin 13 with k≤4, a_(r_i)(k)>0. For every i and every real c,c', Y_i(1,c)−Y_i(1,c')=0. For every real c the four-school average of Y_i(1,c)−Y_i(0,c) is −1/5. For every real three-vector θ, Gθ=v iff θ=(−3/31,−15/62,−16/31), and −16/31≠0.

It also asserts G=[[1,0,1/5],[0,1/25,1/50],[1/5,1/50,151/2400]], v=(−1/5,−1/50,−17/300), det G=31/60000≠0.

For every real a,τ,b1,b2,g, define Y_i(d,c)=a+gq_i+d[τ+b1(c−q_i)+b2(q_i−1/5)], and observed Y_i=a+τD_i+b1(Z_i−D_iq_i)+b2 D_i(q_i−1/5)+gq_i. For every i,c,c' the treated contrast is b1(c−c'); for every c the average treatment contrast is τ+b1(c−1/5). There exists a three-vector θ solving the expected regression equations for this observed Y, every other solution equals it, θ_2=(15b1+16b2)/31, and θ_2=b1 iff b1=b2. For every assignment and school, and every school/treatment Boolean/c, the parameters (a,τ,b1,b2,g)=(3/10,−1/5,0,−1,0) reproduce both earlier outcome schedules. There is no repeated-block sample-OLS limit conjunct.

## SAP.P037a.T2

The following thirteen assertions are conjoined; their parameters are independently universally quantified in the order stated.

1. For every natural H, stratum sizes N_h, sample sizes n_h, and finite referent sets F_h⊆Fin N_h, assuming each N_h>0, n_h≤N_h, and ∑h n_h>0, put K_h=|F_h|, T=∑h n_h, μ=∑h n_h(K_h/N_h)/T. Assign equal mass [∏h choose(N_h,n_h)]⁻¹ to every tuple of subsets S_h of size n_h. C(S)=∑h |F_h∩S_h|/T. These masses sum to one, EC=μ, and E[(C−μ)²]=[∑h V_h]/T², where V_h=0 if N_h=1 and otherwise n_h(K_h/N_h)(1−K_h/N_h)(N_h−n_h)/(N_h−1). This is an unconditional product-sampling statement.
2. For every H,N,K,n and real f, if all N_h≠0, ∑h (n_h:R)≠0, and n_h=fN_h for all h, then ∑h n_h(K_h/N_h)/∑h n_h = ∑h K_h/∑h N_h. No bound on K_h is imposed in this algebraic assertion.
3. For N=(13,14,14,14), K=(2,1,0,0), n=(7,7,7,7), the eligible share is 3/55, seed-composition mean is 41/728, their difference is 71/40040, and they are unequal.
4. For all finite Ω and regressor type K, natural B, design d, columns X_k(ω)_bi, block intercepts α_b, coefficient θ_k, errors e, and outcomes Y, if Y_bi=α_b+∑k θ_k X_k,bi+e_bi for every ω,b,i and E H_B(X_k,e)=0 for every k, then E H_B(X_k,Y)=∑l θ_l E H_B(X_k,X_l) for all k. If the linear expected Gram map is injective, then every coefficient vector satisfying these equations equals θ.
5. For all real a,t,b,D,C,μ, a+Dt+bDC=a+D(t+bμ)+bD(C−μ).
6. For every finite design d, B, Boolean assignment vector D, innovation vector R, assume (R): E[f(D)R_i]=0 for every real function f of the entire assignment vector and every block-school coordinate i. For every assignment-dependent vector V(D), E H_B(R,V(D))=0.
7. For every finite Ω,K,B,d,D,C, fixed school vectors μ,a,t, assignment-dependent controls W_k(D), real b,β and control coefficient vector δ, set R_i=D_i(C_i−μ_i) and Y_i=a_i+D_it_i+bD_iC_i. Assume (R), all the joint expected normal equations of Y on W and R at (δ,β), and E H_B(R,R)>0. Then β=b. No nonsingularity of the control Gram is required.
8. For every finite Ω,K,B,d, arbitrary random W,R,Z,Y, chosen e∈K, and coefficients δ,β, if Z_i=R_i+W_e,i for every ω,i, the joint normal equations for (W,Z) at (δ,β) are equivalent to those for (W,R) at (δ+β 1{coordinate=e},β).
9. For all real D,C,μ,q, D(C−q)=D(C−μ)+D(μ−q). If μ=q, also D(C−μ)=D(C−q) and Dμ=Dq.
10. In T1's fixed design, E H(R,R)=1/160 for R=Z−Dq. Write X+=(D,q,Z,Dq), Xc=(D,q,R), X=(D,q,Z). For every θ (of the corresponding dimension), the expected normal equations have exactly the following solution: (X+,Y): (0,0,0,−1); (Xc,Y): (−1/5,−1/2,0); (X,Y+Z/5): (−3/31,−15/62,−49/155); (Xc,Y+Z/5): (−4/25,−2/5,1/5); (X+,Y+Z/5): (0,0,1/5,−1); and (X,3/10−D/5−q/2+Z/5): (−1/5,−1/2,1/5).
11. For every finite Ω,B,d,D,R satisfying (R), and every assignment-dependent vector V(D), E∑i V(D)_i R_i=0.
12. For every finite Ω,K,B,d,D,R satisfying (R), every assignment-dependent A(D),W(D), every b,β,δ, if the joint expected normal equations of A(D)+bR on W,R hold at δ,β, then β E H_B(R,R)=b E H_B(R,R), including zero variation.
13. For every finite Ω,K,B,d,D,C, fixed μ,a,t, controls W(D), selected e∈K, and b,β,δ, if W_e(D)_i=D_iμ_i, (R) holds for R=D(C−μ), the joint expected normal equations of a+Dt+bDC on W,DC hold at δ,β, and E H_B(R,R)>0, then β=b.

In items 7,8,12,13, joint normal equations mean both E H_B(W_k,Y)=∑l δ_l E H_B(W_k,W_l)+β E H_B(W_k,R) for each k and E H_B(R,Y)=∑l δ_l E H_B(R,W_l)+β E H_B(R,R), using Z or DC in place of R where indicated.

## SAP.P037a.T3

For every real p, not(p<1/20 and 1/20≤p). For every real c satisfying 19/10≤c≤2, both (estimate,se)=(−57/1000,7/250) and (−57/1000,17/500) satisfy the strict bins defined above; their Wald ratios equal 57/28 and 57/34, respectively, and 57/34<c<57/28. For every estimate and se satisfying the bins, 11/7<|estimate|/se<13/5 and (6/100)/(3/100)=2. Finally for every real z∈(11/7,13/5), there exist real a,se with 11/200<a<13/200, 1/40<se<7/200 and a/se=z. No normal-tail, quantile, or P-value claim occurs.

## SAP.P037a.T4

For every n≥0, the normalized n+2-uniform law gives ratioEvent mass 1/6, the explicitly defined simplexLaw(n+1) gives mass 1/4 (via toReal), the two measures are unequal, and both event masses are finite. For every real u,v,total>0, (u/total)/(u/total+v/total)=u/(u+v), and u/(u+v)<1/4 iff u<v/3. The double integral ∫v=0..1 ∫u=0..v/3 1 du dv is 1/6. Separately ∫v>0 e^(−v)dv=1 and ∫v>0 e^(−4v/3)dv=3/4; 1−3/4=1/4, 1/6≠1/4, and 1/6−1/4=−1/12.

For all finite row and column types I,K, positive row weights w_i, matrix X with injective map b↦Xb, outcome y, candidate coefficient b, and real c>0, multiplying weights by c leaves G⁻¹v unchanged and is equivalent for the WLS normal equations at b. For every n, finite K, positive w on n+2 rows, full-column-rank X, and y, normalizing w by its sum leaves G⁻¹v unchanged. There is no normalized-exponential law assertion.

## SAP.P037a.T5

The pushforward of Lebesgue measure on (0,1) by u↦−log u equals expMeasure(1). For every natural m, ∫t>0 t^m e^(−t)dt=m!. All the normalized-uniform/simplex unequal-law and finite-event-mass assertions, WLS scaling assertions, and normalization-refit assertions of T4 also hold, with the same universal quantifiers and hypotheses. There is no multi-coordinate transformed-independence, normalized-exponential law, Jacobian, or simplex-total-mass assertion.

## SAP.P037a.T6

2695−2012=683 in naturals; reduction(2695,2012)=683/2695; 49/200<683/2695<51/200; 683/2695<59/200; 683/2695≠3/10; natural 6830≠8085; 11/200≤683/11938<13/200; 9/40<2695/11938<23/100; 3/10−1/4=1/20 and (1/20)/(3/10)=1/6.

For all real A∈[5389/2,5391/2] and B∈[4023/2,4025/2], 1364/5389≤1−B/A≤1368/5391, and 49/200<1364/5389, 1368/5391<51/200. For all real e∈[11/200,13/200] and m∈[39/200,41/200], (3/50)/(1/5)=3/10, 11/41≤e/m, and 51/200<e/m.

## SAP.P037a.T7

The configurations (1,0,0,0) and (1,1,0,0) are feasible. The first satisfies both the printed school and nonreferent predicates, whose labels are distinct. The second satisfies both the printed nonreferent and direct predicates, whose labels are distinct. There does not exist any function f from all configurations to labels such that, for every feasible x and every printed label e satisfied by x, f(x)=e. For every feasible x, its printed school predicate implies its printed nonreferent predicate; if additionally s=1,d=1,r=0, both printed nonreferent and direct predicates hold.

## SAP.P037a.T8

For every configuration x, if x is feasible, there exists exactly one of the five labels whose corrected predicate x satisfies. The corrected predicates assign school to (1,0,0,0) and direct to (1,1,0,0).

## SAP.P037a.T9

For every finite design d on Ω and every decidable event E, write X=1_E and π=EX. Then Var X=π(1−π). For every natural J>0, use the J-fold independent product design and frequency F_J=∑j X_j/J. Then EF_J=π, Var F_J=π(1−π)/J≤1/(4J), and for every real ε>0, P(ε<|F_J−π|)≤1/(4Jε²). For every ε>0, P(ε<|F_(J+1)−π|)→0 as J→∞. For every J>0 and reals v,target, 1{(∑j∈Fin J v)/J=target}=1{v=target}. With the two draws (0,1) and target 1, frequency is 1/2; 1{(1+1)/2=1}=1 and 1{(0+1)/2=1}=0.

## SAP.P037a.T10

For every six-state block assignment ω and each of four schools, D_i∈{0,1}, and ∑i D_i=2. Every school's treatment mean is 1/2. For each ordered distinct pair i,j, E[D_iD_j]=1/6, Cov(D_i,D_j)=−1/12, Cov(1−D_i,1−D_j)=−1/12, and E[D_iD_j]≠ED_i ED_j.

More generally, for every finite design d and four binary random variables T_i, if their sum is two at every assignment and each has mean 1/2, then Var(∑i T_i)=0, ∑i Var T_i=1, ∑i,j:i≠j Cov(T_i,T_j)=−1 (ordered pairs), and there exist distinct i,j with negative covariance.

In the fixed two-block design, for every u,v its joint mass is the product of the single-block masses, and for every school i in the first block and j in the second, Cov(D_i,D_j)=0. There are exactly 36 ordered assignments and each has mass 1/36.

## SAP.P037a.T11

Shared objects: A retained row r with B blocks specifies natural block student counts n_b, finite assignment sets Fin a_b with designs d_b, Boolean exposure indicators I_bi(z), fixed real y_bi,g_bi, and π_bi=E_b I_bi>0. The whole row is sampled with the independent product law of the block designs; within-block indicators may be arbitrarily dependent. N=∑b n_b, T_b(z)=∑i[g_bi+I_bi(z)(y_bi−g_bi)/π_bi], μ=∑bi y_bi/N, μ̃=∑b T_b/N, S=∑b Var_b T_b. `rowProbability` is the explicit sum with these product weights.

A sequence r_B has B+1 blocks. `BlockBounds(r,m,c,η,K)` means c>0, η>0, K≥0, and for every B, N_B≥c(B+1), every n_Bb≤m, and for every student π_Bbi≥η, |y_Bbi|≤K, |g_Bbi|≤K. Put A=K+2K/η and C=mA.

A paired exposure s uses the same students, assignment sets and designs, but has a second arbitrary Boolean exposure indicator, fixed y',g', and positive π'=E I'. There is no disjointness or sum-to-one requirement for the pair. Put V_b=T_b−T'_b, contrast θ=∑bi(y_bi−y'_bi)/N, and estimator θ̃=∑b V_b/N.

The theorem is the conjunction of the following sixteen separately quantified assertions:

1. For every finite d,I and real π,y,g, if π≠0 and EI=π, then E[g+(I/π)(y−g)]=y. Here I need not be binary.
2. For all real I,π,y,g,K,η, if I∈{0,1}, η>0, π≥η, |y|≤K, |g|≤K, then |g+(I/π)(y−g)|≤K+2K/η.
3. For every B,r,b, E_b T_b=∑i y_bi.
4. For every B,r with N>0, Eμ̃=μ and Var μ̃=S/N².
5. For every B,r and every family of functions f_b:R→R, E∏b f_b(T_b)=∏b E_b f_b(T_b).
6. For every r sequence,m,c,η,K satisfying BlockBounds, every B and every ε>0, |T_b(z)|≤C for every b,z; Var_b T_b≤C² for every b; S_B/N_B²≤C²/[c²(B+1)]; and P(|μ̃_B−μ_B|>ε)≤C²/[c²(B+1)ε²].
7. For every such bounded sequence and every ε>0, P(|μ̃_B−μ_B|>ε)→0.
8. For every such bounded sequence and every σ²>0 with S_B≥σ²(B+1) for all B: for every B and ε>0 satisfying 2C<ε sqrt(σ²(B+1)), ∑b E_b[U_b² 1{|U_b|>ε sqrt(S_B)}]=0, where U_b=T_b−E_bT_b; and for every x∈R, P[N_B(μ̃_B−μ_B)/sqrt(S_B)≤x]→P[N(0,1)≤x].
9. For every finite B,r,m,η,K with η>0,K≥0,n_b≤m and π≥η,|y|,|g|≤K, every b,z satisfies |T_b(z)−E_bT_b|≤2m(K+2K/η).
10. For every B,r with N>0 and every row assignment w, ∑b[T_b(w_b)−E_bT_b]=N(μ̃(w)−μ).
11. For every finite B,r with N>0, paired s, m,η,K satisfying the analogous bounds for both exposures, Eθ̃=θ, Var θ̃=∑b Var_b V_b/N², |V_b(z)|≤2C and Var_b V_b≤(2C)².
12. For every bounded r sequence and paired sequence satisfying the same η,K bounds, θ̃_B−θ_B→0 in probability. For every v>0 such that ∑b Var V_Bb≥v(B+1) for every B, for every x∈R, P[N_B(θ̃_B−θ_B)/sqrt(∑b Var V_Bb)≤x]→P[N(0,1)≤x].
13. For every such paired sequence, every B and ε>0, Var θ̃_B≤(2C)²/[c²(B+1)] and P(|θ̃_B−θ_B|>ε)≤(2C)²/[c²(B+1)ε²].
14. For every such paired sequence and v>0 satisfying the same variance lower bound, for every B and ε>0 such that 4C<ε sqrt(v(B+1)), the Lindeberg sum ∑b E[(V_b−EV_b)² 1{|V_b−EV_b|>ε sqrt(∑b Var V_b)}] is zero.
15. For every finite B,q,r with N>0, q-dimensional covariates x_bik, any coefficient vectors βhat,βstar, positive p_bi, and assignment w, define μhat(β,p)=N⁻¹∑bi[x_bi'β+I_bi(y_bi−x_bi'β)/p_bi]. Then μhat(βhat,π)−μhat(βstar,π)=∑k[N⁻¹∑bi(1−I_bi/π_bi)x_bik](βhat_k−βstar_k), and μhat(βhat,p)−μhat(βhat,π)=N⁻¹∑bi I_bi(y_bi−x_bi'βhat)(p_bi⁻¹−π_bi⁻¹).
16. For every fixed natural q, bounded row sequence r, deterministic x_Bbik, positive random pHat_Bbi(w), m,c,η,K,L,Q,v, assume BlockBounds, |x_Bbik|≤L for every coordinate; the population Gram N_B⁻¹∑bi x_bi x_bi' converges entrywise to Q and population RHS N_B⁻¹∑bi x_bi y_bi to v; for every nonzero real q-vector a, a'Qa>0; and for every ε>0, P[there exists b,i with sqrt(B+1)|pHat_Bbi−π_Bbi|>ε]→0. Set βstar=Q⁻¹v and also assume the row's fixed g_Bbi=x_Bbi'βstar at every B,b,i. Define βhat_B(w)=G_B(w)⁻¹v_B(w) where G_B=∑bi (I_bi/pHat_bi)x_bi x_bi' and v_B=∑bi (I_bi/pHat_bi)x_bi y_bi, with zero coefficient on singular matrices. Let μhat_B=μhat(βhat_B,pHat_B). Then βhat_B→βstar in probability (event: some coordinate error>ε); sqrt(B+1)|μhat_B−μ̃_B|→0 in probability; μhat_B−μ_B→0 in probability; and, for every σ²>0 with S_B≥σ²(B+1) for all B, for every z∈R, P[N_B(μhat_B−μ_B)/sqrt(S_B)≤z]→P[N(0,1)≤z].

There is no external assumption of a CLT, coefficient consistency, normality, or asymptotic linearization; these are conclusions. Positive size and variance assumptions protect each nontrivial estimator/standardization denominator. Zero-dimensional covariates are allowed, but nonzero dimensions are also quantified.

## SAP.P037a.T12

For all integers n,k, 350k≠3500+6(n−200)−175. Define f(n) for natural n as 40 if n≤200, 64 if n≥550, and otherwise 4[10+floor((6(n−200)+175)/350)]. For every natural n, 40≤f(n)≤64 and 4 divides f(n); for every n≤n', f(n)≤f(n'). For every n, f(n)=64 iff n≥521; in particular n≥550 implies f(n)=64. The real interpolation expression 40+24(n−200)/350 equals 40 at n=200 and 64 at n=550. f(100)=40, f(200)=40, f(375)=52. The eligible shares f(100)/100=2/5, f(200)/200=1/5, f(375)/375=52/375, f(550)/550=64/550, and f(715)/715=64/715 hold.

## SAP.P037a.T13

The fitted effect 4/100−(85/100)(1/5)=−13/100, and reduction(1/5,8/100)=3/5. For every real t,b,m in the respective closed intervals [35/1000,45/1000], [−855/1000,−845/1000], [222/1000,223/1000], let d=t+b/5. Then −136/1000≤d≤−124/1000, 86/1000≤m+d≤99/1000, and m+d does not lie in [75/1000,85/1000]. The number 95/1000 lies in [86/1000,99/1000]. Also 124/223≤−d/m≤68/111, and both 57/100 and 3/5 lie in this last interval. Separately, for every real t,b in the first two intervals, the same fitted-effect bounds hold, without assuming anything about m.
