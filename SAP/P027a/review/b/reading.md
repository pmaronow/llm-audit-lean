# Blind mathematical reading

This file was written after reading all eight Defs parts and the Challenge, and before opening claims.json or record.json. All ten Challenge declarations are closed propositions: the quantifiers and implications below are inside their definitions. Each declaration has a `sorry` proof stub; this reading concerns statements, not those proofs. Challenge docstrings do not add mathematical clauses.

## Common definitions, expanded

All populations and design sample spaces in the finite formulas are finite types. `Fin n` means the integers 0 through n−1; a dependent sum `Σ g, Fin (n g)` is a disjoint union of groups of the indicated sizes. Sums with no displayed subset range over the entire finite type. Ordered double sums include both (k,l) and (l,k).

A design D on U with atoms Ω consists of real weights w(ω) and Boolean selections. Write I_k(ω)=1 when k is selected, and 0 otherwise. Validity means every w(ω)≥0 and Σ_ω w(ω)=1. Positivity means π_k>0 for every k, where

* E_D f = Σ_ω w(ω)f(ω), π_k=E_D I_k, π_kl=E_D(I_k I_l), and Δ_kl=π_kl−π_kπ_l.
* Var_D f=E_D[(f−E_D f)²]. This is the design variance, not an independently assumed measure-theoretic variance.
* T_D(y,ω)=Σ_k I_k(ω)y_k/π_k; M_D=T_D/|U|.
* H_D(y,ω)=Σ_{k,l:π_kl>0} I_k I_l (Δ_kl/π_kl)(y_k/π_k)(y_l/π_l). The branch for π_kl≤0 contributes zero.
* Z_D is the ordered set {(k,l): k≠l and π_kl=0}.
* A_D(y)=Σ_{Z_D}y_ky_l.
* C_D(y,ω)=Σ_{Z_D}[I_k y_k²/(2π_k)+I_l y_l²/(2π_l)].
* U_D(y,ω)=H_D(y,ω)+C_D(y,ω), the object called `c2Estimator`.
* A*_D(y)=Σ_{Z_D}(y_k²+y_l²)/2, called `quadraticA`.
* W_D(y,m,ω)=[Σ_k I_k(ω)(y_k/(π_k/m)−T_D(y,ω))²]/[|U|² m(m−1)]. The final subtraction is in ℝ, not truncated natural subtraction.
* R_D(y)=Σ_{Z_D}(y_k+y_l)²/2, called `squaredZeroPairs`.

Real division is Mathlib field division, including its totalized value at zero. The hypotheses or explicit finite laws used below make the estimator denominators positive where they are substantively used. An empty finite sum is zero. No theorem here uses a `limsup`.

For a finite group set G, sizes n_g, and values y_{g,j}, let Y_g=Σ_{j<n_g}y_{g,j} and Q_g=Σ_{j<n_g}y_{g,j}². The lift of a design on G has the same weights and selects every (g,j) exactly when g is selected. `oneDraw(p)` has atoms G, weight p_g, and selects only g at atom g. Let d_g be the number of h≠g with π_gh=0 and s_g=Σ_{h≠g:π_gh=0} n_h.

For positive sizes x indexed in order by Fin N, a_k=Σ_{i<k}x_i and X=Σ_i x_i. `systematicSelected(x,m,u,k)` means that for some j∈{0,…,m−1}, a_k≤u+jX/m<a_k+x_k. The printed PPS formula is P_k(m,x)=m x_k/X.

For any measurable Ξ and measure μ, E_μ f means the real Bochner integral ∫f dμ. `IsProbabilityMeasure μ` says μ(Ξ)=1. `Integrable` means almost-everywhere strong measurability and finite integral of the norm; for real functions this is the usual absolute integrability. Mathlib sets nonintegrable real Bochner integrals to zero. Consequently the integrability hypotheses and conclusions below are part of the reading, not silently discarded. Sources inspected: Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:59, Integral/Bochner/Basic.lean:157 and :204, Measure/Typeclasses/Probability.lean:64, Measure/Sum.lean, Measure/Restrict.lean, and Analysis/SpecialFunctions/Pow/Real.lean.

`NoiseMoments(μ,ε,σ²)` means: for each k, ε_k is integrable and E_με_k=0; for every ordered pair k,l, ε_kε_l is integrable and its expectation is σ² if k=l, otherwise zero. It asserts moments, not independence or Gaussianity. `UncorrelatedNoise` has the same first moments and product integrability, and only the off-diagonal zero expectations, without a common diagonal moment. Raw values are y_k(ξ)=βx_k+ε_k(ξ). Centered values are z_k(ξ)=y_k(ξ)−(Σ_l y_l(ξ))/|U|, using the realized population mean.

The recurring periodic family is as follows. Choose natural r>0 and natural m, put G=Fin r×Fin 2, q=2r, K=G×Fin m (understood as a dependent sum), and N=mq. At atom g=(a,b), choose all m units in group g, with probability

    p_g = 1/(6r) if b=0, and 5/(6r) if b=1.

Write D_{r,m} for this original-unit law and D^c_r for its one-group draw law. Unit sizes x_{g,j} are 2 for b=0 and 10 for b=1. The order index of (a,b,j) is 2a+b+2rj. Set t_g=12a if b=0, and 12a+2 if b=1. These formulas expand `phaseProb`, `phaseGrouped`, `phaseOriginal`, `phaseSize`, `phaseIndex`, and `phaseStartLeft`.

The eight-unit laws have atoms g=0,1,2,3 and select k∈{0,…,7} when k mod 4=g. Their alternating outcomes are −1 at even k and +1 at odd k. The periodic law has weights 1/12 at even g and 5/12 at odd g, and sizes 2,10,2,10,2,10,2,10. The random8 law has weights 1/8 at even g and 3/8 at odd g, sizes 1,3,1,3,1,3,1,3, and outcomes +1 at even k and −1 at odd k. `fourLeft(a,b,g)` lists 0,a,a+b,2a+b. The general `fourPhase` constructor uses weights low/high according to atom parity, with proof arguments low,high≥0 and 2low+2high=1; only the preceding numerical instances are used here.

## SAP.P027a.T1

This is the conjunction of an eight-unit list of facts and a universally quantified family statement. There are no outer hypotheses.

For the periodic eight-unit law D and alternating z:

1. D is valid and positive. For every k, π_k=1/12 at even k and 5/12 at odd k. For every k,l, π_kl equals that same parity probability when k mod 4=l mod 4, and otherwise zero. There are exactly 48 ordered distinct zero-joint pairs.
2. For every atom g and every real u with t_g≤u<t_g+x_g, and then every unit k, systematicSelected(x,2,u,k) is equivalent to k mod 4=g. Here the four t_g are 0,2,12,14.
3. Σ_k z_k=0, A_D(z)=−16, and A*_D(z)=48.
4. For every g, M_D(z,g) is −3 at even g and 3/5 at odd g; H_D(z,g)/64 is respectively 33/4 and 21/100; U_D(z,g)/64 is respectively 21/2 and 33/50; W_D(z,2,g)=0.
5. E_D M_D=0, Var_D M_D=9/5, E_D(H_D/64)=31/20, E_D(U_D/64)=23/10, and E_D(H_D/64)−Var_D M_D=−1/4.

For every natural r, then every natural m, then every proof r>0, if m>0: use D=D_{r,m}, z_{g,j}=−1 for b=0 and +1 for b=1, q=2r, N=mq. Then Σz=0, A_D(z)=−q m², Var_D M_D(z)=9/5, and E_D(H_D(z)/N²)−Var_D M_D(z)=−1/q.

## SAP.P027a.T2

Six conjuncts, with no outer hypotheses:

1. Continuous-start identification. For every natural r,m, then r>0, if m>0, let L_s=12r, and let a_k be the sum of phase sizes at units with smaller phaseIndex. Define s(u)_k to be the Boolean truth value of ∃j<m, a_k≤u+jL_s<a_k+x_k. Let ν be L_s⁻¹ times Lebesgue measure restricted to [0,L_s), where the scalar is formed in the extended nonnegative reals. Then ν is a probability measure; every a_{g,j}=t_g+L_s j; every u∈[0,L_s) lies in exactly one [t_g,t_g+x_g); every g and u in that interval satisfy s(u)=D_{r,m}.selected(g); each interval has ν-measure p_g; and for every real-valued function F on Boolean selections K→Bool, u↦F(s(u)) is ν-integrable and its integral equals E_{D_{r,m}}[F(selected(g))].
2. Inclusions. For every natural r,m and r>0 (no m>0 hypothesis in this conjunct), D_{r,m} is valid and positive. Every unit in group g has π=p_g; every ordered pair of units has joint probability p_g if their groups agree and zero otherwise. For every atom g and unit k, selection means g=k.group. For every pair k,l, their Boolean indicators agree at all atoms if and only if their groups agree. When m=0 the assertions about units quantify over an empty type, while validity still concerns a nonempty group-atom law.
3. Deterministic bias. For every natural r,m, r>0, m>0, and real vector z on K, if Σz=0, let Y_g=Σ_jz_{g,j}, S=Σ_gY_g², V=Var_D T_D(z). Then Σ_gY_g=0; A_D(z)=−S; S≥0; S=0 iff all Y_g=0; E_DT_D(z)=0; V=Σ_gY_g²/p_g; E_DH_D(z)=V−S; every atom g has H_D(z,g)=(1−p_g)Y_g²/p_g²; [E_DH_D(z)−V]/N²=−S/N²; and if V>0 then −5/(3q)≤A_D(z)/V≤−1/(3q).
4. Outcome averages. Quantifier order: arbitrary measurable Ξ, probability measure μ, natural r,m with r,m>0, real β,σ² with σ²≥0, then ε on K×Ξ satisfying NoiseMoments. Use the centered z, its Y_g, L=16m²β²+mσ²(1−1/q), V(ξ)=Var_D T_D(z(ξ)), and H(ξ)=E_DH_D(z(ξ)). If V,H,A_D(z(·)) are μ-integrable, then for every g, Y_g² is integrable with expectation L; E_μA_D(z)=−qL; E_μV=(9/5)q²L; E_μH=E_μV−qL; if L>0 the ratio (E_μH−E_μV)/E_μV=−5/(9q); and E_μ[A_D(z)/N²]=−16β²/q−σ²(1−1/q)/N.
5. Calibration. For every measurable Ξ, probability μ, r,m>0, then real ρ,β with |ρ|≤1, then ε satisfying NoiseMoments with σ²=900(1−ρ²): assume β²=900ρ²(N−1)/(16N) and integrability of A_D(z(·))/N². Conclude that its expectation is B(q,ρ,N)=−900ρ²(N−1)/(qN)−900(1−ρ²)(q−1)/(qN).
6. Limit. For every natural r>0 and then every real ρ (no |ρ|≤1 condition here), B(2r,ρ,(m+1)2r) converges as natural m→∞ to −900ρ²/(2r). This is Filter.Tendsto from atTop to the ordinary real neighborhood filter.

## SAP.P027a.T3

There are two equally likely atoms, 0 and 1. D on three units selects {0,1} at atom 0 and {2} at atom 1. D_c on two units selects {0} and {1} respectively, each with weight 1/2. The theorem is a closed conjunction about these fixed laws.

For y=(1,1,1) and Y=(2,1): D,D_c are positive; at each atom the indicators of original units 0 and 1 agree; at every atom T_D(y)=T_{D_c}(Y); Var_D T_D(y)=1; A_D(y)=4; A*_D(y)=4; A*_{D_c}(Y)=5; E_DU_D(y)=9; E_{D_c}U_{D_c}(Y)=10; Var_{D_c}T_{D_c}(Y)=1; and the two C2 biases are respectively 8 and 9.

For y=(1,1,−1/4) and Y=(2,−1/4): both total-estimator variances are 81/16; both A values are −1; the A* values are respectively 17/8 and 65/16; the C2 expectations are respectively 99/16 and 65/8; and their biases are respectively 9/8 and 49/16. No separate samplewise total-preservation statement for this second vector is a conjunct.

## SAP.P027a.T4

Four independent universally quantified conjuncts:

1. Almost-sure grouping preservation. For every finite G, finite Ω, sizes n_g>0, then a design D on the disjoint union of groups: assume D valid and positive and, for every group g and pair of members i,j, the design expectation of their Boolean disagreement indicator is zero. For every real y on the union, define D_c on G by using D's weights and the indicator of member 0 in each group. Then D_c is positive; every member's π equals the group's π; every pair's joint equals its group pair's joint; for every atom ω with w(ω)>0 both T and H agree between original y and grouped Y; their total-estimator variances agree; and their A values agree. Atomwise T,H equality is required only at positive-weight atoms.
2. Exact grouping formulas. For every finite G,Ω, group design D, assume validity and positivity; then for every sizes n with n_g>0 and every y on their union, compare its lift D^l to D. Samplewise T and H agree for all atoms, total variances agree, and A agrees. Moreover

       A*_{D^l}(y) = (1/2) Σ_{g≠h:π_gh=0}(n_h Q_g+n_g Q_h).

   Let Δ be [E_{D^l}U_{D^l}(y)−Var_{D^l}T_{D^l}(y)] minus [E_DU_D(Y)−Var_DT_D(Y)]. Then

       Δ=(1/2)Σ_{g≠h:π_gh=0}(n_hQ_g+n_gQ_h−Y_g²−Y_h²).

   If n_g=n_h for every zero-joint edge, Δ≥0. For every real v, if all y_k=v, then Δ=−(v²/2)Σ_{g≠h:π_gh=0}(n_g−n_h)². Both C2 biases are nonnegative. Finally, Σ_g(s_g−d_g n_g)Q_g≤Δ.
3. Strict constant case. For every finite G,Ω and valid positive D, every positive sizes n, and then every v≠0: if there exist g,h with g≠h, π_gh=0, and n_g≠n_h, then the C2 bias for the lift with constant outcomes v is strictly less than the grouped C2 bias.
4. Squared-bias identities. For every finite G,Ω and valid positive D, then every n:G→ℕ (zeros allowed) and every y on the union, the lifted C2 bias equals R_{D^l}(y), and the grouped C2 bias equals R_D(Y).

These are universal statements including empty G, but also include ordinary nonempty populations. Validity disallows an empty atom space.

## SAP.P027a.T5

Three conjuncts:

1. For every row i∈{0,1,2,3}, then every real V,G with |V−v_i|≤0.005 and |G−g_i|≤0.005, V>0 and G>(1+5(q_i−2)/(3q_i))V. The exact rational decimal arrays are v=(42.55,56.35,23.14,28.58), g=(653.92,891.43,622.28,861.11), q=(4,20,4,20).
2. Let D=D_{2,30}, D_c=D^c_2, and y_{(a,b),j}=(−4 if b=0, +4 if b=1)+2j−29 for 0≤j<30. Put Y_g=Σ_j y_{g,j}. Then Σ_ky_k=0, Σ_gY_g²=57600, Σ_ky_k²=37880, Var_DT_D(y)=414720, E_DH_D(y)=357120, E_DU_D(y)=3766320, and E_{D_c}U_{D_c}(Y)=529920.
3. For the same vectors and V=Var_DT_D(y), dividing by 14400 gives respectively V/14400=144/5, E_DH_D/14400=124/5, E_DU_D/14400=5231/20, E_{D_c}U_{D_c}/14400=184/5. Relative biases (E_DU_D−V)/V and (E_{D_c}U_{D_c}−V)/V are respectively 4655/576 and 5/18.

## SAP.P027a.T6

Four conjuncts:

1. Exactly the periodic inclusion statement in T2(2), including its quantifiers and m=0 case.
2. For every r,m>0, then real z on K with Σz=0, put Y_g=Σ_jz_{g,j}, Q_g=Σ_jz_{g,j}², S=Σ_gY_g², Q=Σ_gQ_g, V=Var_DT_D(z), H=E_DH_D(z), U=E_DU_D(z), and G=E_{D_c}U_{D_c}(Y). The following all hold:

   * Σ_gY_g=0, A_D(z)=−S, S≥0, and S=0 iff every Y_g=0.
   * E_DT_D(z)=0, V=Σ_gY_g²/p_g, H=V−S, U=V−S+(N−m)Q, G=V+(q−2)S.
   * For every atom g: T_D(z,g)=Y_g/p_g; H_D(z,g)=(1−p_g)Y_g²/p_g²; C_D(z,g)=(N−m)Q_g/p_g; C_{D_c}(Y,g)=(q−1)Y_g²/p_g; and

         U_D(z,g)−U_{D_c}(Y,g)
           =(q−1)(mQ_g−Y_g²)/p_g
           =m(q−1)Σ_j(z_{g,j}−Y_g/m)²/p_g ≥0.

   * U−G=(q−1)(mQ−S), V≤G≤U, and (3q/5)S≤V≤3qS.
   * If V>0, −5/(3q)≤A_D(z)/V≤−1/(3q) and (q−2)/(3q)≤(G−V)/V≤5(q−2)/(3q).
3. For arbitrary measurable Ξ, probability μ, r,m>0, real β,σ² with σ²≥0, then ε satisfying NoiseMoments, use centered z, Y_g, L=16m²β²+mσ²(1−1/q), V(ξ)=Var_DT_D(z(ξ)), and G(ξ)=E_{D_c}U_{D_c}(Y(ξ)). If V,G and every Y_g² are integrable, then every E_μY_g²=L, E_μV=(9/5)q²L, E_μG=E_μV+(q−2)qL, and if L>0 the ratio (E_μG−E_μV)/E_μV=(5/9)(1−2/q).
4. On the one-group law with probabilities (1/12,5/12,1/12,5/12), for Y=(1,0,−1,0), ΣY²=2, Var T(Y)=24, E U(Y)=28, and (28−24)/24=1/6.

## SAP.P027a.T10

A closed statement about the random8 law D and its sizes x and outcomes y described above:

* D is valid and positive and every x_k≥1. A_D(y)=−16, A*_D(y)=48, E_DT_D(y)=0, Var_DT_D(y)=256/3, E_DH_D(y)=208/3, E_DU_D(y)=352/3.
* Σ_kx_k=16 and for every k, π_k=P_k(2,x). Var_DM_D(y)=4/3, E_D(H_D(y)/64)=13/12, their difference is −1/4, and the expected estimator is strictly smaller than the variance.
* For every atom g, T_D(y,g)=16 at even g and −16/3 at odd g; H_D(y,g)=224 at even g and 160/9 at odd g.
* For every atom g, then every real u in its interval [t_g,t_g+x_g), then every k, systematicSelected(x,2,u,k) iff D selects k at g. The starts t_g here are 0,1,4,5.
* For every real vector y' on eight units, if |y'_k−y_k|<1/8 for every k, then A_D(y')≤−13/4.

## SAP.P027a.T11

Two conjuncts:

1. Quantifier order: arbitrary finite U,Ω, measurable Ξ, probability μ, design D; assume validity, positivity, and |U|>0. Then choose any real size vector x with every x_k≥1, any real β and ε satisfying UncorrelatedNoise. Let raw y_k(ξ)=βx_k+ε_k(ξ). Assume integrability of A_D(y(·)) and of b(ξ)=E_D[H_D(y(ξ))/|U|²]−Var_DM_D(y(ξ)). Then for every distinct k,l, E_μ(y_ky_l)=β²x_kx_l; E_μA_D(y)=β²A_D(x)≥0; E_μb=β²A_D(x)/|U|²≥0.
2. For random8 and its size vector x, A_D(x)=176 and (3/2)²A_D(x)=396.

No centering, conditional-on-outcome conservativity, Gaussianity, or noise independence occurs in this statement.

## SAP.P027a.T12

Define x=(30,1,1,1,1,1,1,1) and v*=(29,0,0,0,0,0,0,0). For j≥0 let

    b_j=[(∏_{i=0}^{j−1}(18/5+i))/j!] (3/8)^(18/5) (5/8)^j.

The empty product is 1 and 0!=1. The power with exponent 18/5 is the real power (the base is positive); j powers are natural powers. For each natural N, μ_N is the countable sum, over all v:Fin N→ℕ, of [ofReal(∏_k b_{v_k})] times Dirac mass at v. `ofReal` clamps negative reals at zero; the displayed masses are positive. This is a product-form atomic measure by definition, before its normalization is asserted. μ_8 is also named nbProductLaw. Extended-real `.toReal` is finite real conversion, with value zero at infinity; the theorem's probability-measure conclusions make the measures of all these events finite.

The theorem is a conjunction of:

1. Σx=37; P_0(2,x)=60/37; Σ_kP_k(2,x)=2; P_0−1=23/37. For every finite atom type Ω' and every valid design D on eight units, it is false that all its π_k equal P_k(2,x).
2. For every k, P_k is 60/37 at k=0 and 2/37 otherwise. For every finite Ω and valid eight-unit design D, every π_k≤1. For every k, 1+v*_k=x_k.
3. μ_8 is a probability measure. For every k and then every j≥0, μ_8{v:v_k=j}=b_j (with real conversion as above). For every k, E_{μ_8}v_k=6 and E_{μ_8}(v_k−6)²=16. The mass of {v*} is b_29 b_0^7>0.
4. For every k, v↦v_k and v↦(v_k−6)² are μ_8-integrable.
5. For every row i∈Fin 6, let (N,m,L,P) be respectively

       (8,2,8,16/15), (40,2,40,80/79),
       (120,30,5,150/124), (600,30,21,630/620),
       (240,60,5,300/244), (1200,60,21,1260/1220).

   Set v_0=L−1, v_k=0 otherwise, and x_k=1+v_k. Then N≥2, 0<m<N, and L=(N−1)/(m−1)+1, where this last division and subtraction are natural-number operations. Σx=L+N−1 (in ℝ), x_0=L and other x_k=1. There exists k with k.val=0 and P_k(m,x)=P>1. The measure μ_N is a probability measure with μ_N{v}>0. For every finite atom type Ω' and valid design on Fin N, not all its marginals can equal P_k(m,x).

## SAP.P027a.T13

Four conjuncts:

1. For every natural N with N≥2, then natural m with 0<m<N, then positive real x on Fin N:

   * For every finite atom type Ω and valid D on Fin N, if every π_k=P_k(m,x), then every m x_k≤Σ_ax_a.
   * There exists a real c>0 with Σ_k min(1,cx_k)=m.
   * If every m x_k≤Σ_ax_a, then Σ_k min(1,(m/Σx)x_k)=m and for every k this capped expression equals P_k(m,x).
2. For every natural N≥2, m with 0<m<N, then real π on Fin N with 0<π_k≤1 and Σπ=m: assume for every k that the real inclusion indicator u↦1_{systematicSelected(π,m,u,k)} is integrable under Lebesgue measure restricted to [0,1). Then for every real u with 0≤u<1 the number of selected distinct units is m, and for every k the integral of that indicator on [0,1) equals π_k. In the selection definition X/m=(Σπ)/m=1; endpoints are left closed and right open.
3. For x=(30,1,…,1), Σ_k min(1,x_k/7)=2; Σ_k min(1,P_k(2,x))=51/37; and the redistributed capped vector is 1 at k=0 and 1/7 at every other k.
4. The explicit design on eight units with seven atoms, each of weight 1/7, selecting {0,ω+1} at atom ω∈{0,…,6}, is positive. Every π_k equals the redistributed capped value. For every k,l, π_kl=π_k if k=l; for distinct k,l it is 1/7 if one is 0, and zero otherwise.

No theorem stubs with labels T7, T8, or T9 occur in the Challenge. Whether these are targets is deliberately left unexamined until the next stage.
