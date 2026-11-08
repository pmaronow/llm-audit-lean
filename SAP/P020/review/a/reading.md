# Blind reading

Saved before opening `claims.json` or `record.json`. This is a reading of the proposition bodies, not an acceptance of their docstrings. The only theorem stubs are `SAP.P020.T1` through `SAP.P020.T17`; each asserts the corresponding closed `TnStatement` without additional theorem parameters.

## Common objects and fully expanded notation

`Fin M` indexes the integers 0 through M−1. All sums below are ordinary finite sums of real numbers, with natural numbers coerced to real numbers where used in real arithmetic. `Finset.univ` includes every element of its finite type. Finite-set subtraction is set difference. `powersetCard t` consists of all subsets of cardinality t: Mathlib `Data/Finset/Powerset.lean:198–203`. Thus no assignment is repeated or omitted. Finite sums have their ordinary additive meaning: `Algebra/BigOperators/Group/Finset/Defs.lean:56–69`.

A finite law L consists of a finite set S in an arbitrary type Ω and real weights p(ω), nonnegative for every ω∈S, satisfying Σ_S p=1. Values of p outside S are unrestricted and unused. Write

- E_L T = Σ_{ω∈S} p(ω)T(ω).
- B_L(T,d)=E_L T−d.
- V_L(T)=E_L[(T−E_L T)²].
- C_L(T,U)=E_L[(T−E_L T)(U−E_L U)].
- Q_L(T,d)=E_L[(T−d)²].
- e_L(T,d,ε)=Σ_{ω∈S, |T(ω)−d|>ε} p(ω).

`DesignConsistent L T d` means: for every real ε>0, e_{L_h}(T_h,d_h,ε) tends to 0 as the natural number h tends to infinity. The sample type Ω_h may depend on h. Equivalently, for every ε>0 and every η>0, eventually the error probability is less than η. `Tendsto ... atTop (nhds b)` is ordinary sequential convergence to b in ℝ; `Tendsto f atTop atTop` for natural-valued f means that for every K, eventually f(h)≥K. These follow Mathlib `Order/Filter/Defs.lean:422`, `Order/Filter/AtTopBot/Defs.lean:39`, and `Topology/Defs/Filter.lean:130`. `StrictMono f` means ∀x,y, x<y ⇒ f(x)<f(y), as in `Order/Monotone/Defs.lean:86`.

A cluster population P consists of natural numbers M,t with 0<t<M, positive natural sizes n_j for every j<M, and arbitrary real potential totals y_{0j},y_{1j}. Put c=M−t, N=Σ_j n_j, and d=(Σ_j y_{1j}−Σ_j y_{0j})/N. Here c is Lean natural subtraction, but t<M ensures it is the usual positive difference. In particular M≥2, N>0, and both arms are nonempty. There is no individual-outcome constraint on y unless an `IndividualPotentialOutcomes` object is supplied.

An admissible assignment s is a t-element subset of {0,…,M−1}; write s_1=s, s_0=its complement, m_1=t, m_0=c. `clusterLaw P`, denoted L_P, is the uniform law on all these assignments, with weight 1/binomial(M,t). Define

- S_a(v;s)=Σ_{j∈s_a}v_j; N_a(s)=S_a(n;s); n̄_a(s)=N_a(s)/m_a.
- Observed total o_j(s)=y_{1j} if j∈s, otherwise y_{0j}.
- D_P(s)=S_1(y_1;s)/N_1(s)−S_0(y_0;s)/N_0(s), the individual-weighted difference of arm means.
- H_{Pa}(s)=(M/m_a)S_a(y_a;s), and H_P(s)=(H_{P1}(s)−H_{P0}(s))/N.
- For any real array v on M indices, μ(v)=Σ_j v_j/M, σ²(v)=Σ_j(v_j−μ(v))²/M, and σ(v,w)=Σ_j(v_j−μ(v))(w_j−μ(w))/M. These cluster moments use denominator M, not M−1, and are distinct from assignment-law moments V_L,C_L.
- For arrays v,z, Δ_k(v;z)_j=v_j−k(z_j−μ(z)). Put r_{a,k}=Δ_k(y_a;n), R_{Pa,k}(s)=(M/m_a)S_a(r_{a,k};s), and R_{P,k}(s)=(R_{P1,k}(s)−R_{P0,k}(s))/N. These are `differenced`, `rajPotential`, `rajTotal`, and `desRaj`.
- The observed fitted slope is k̂_P(s)=σ(n,o(s))/σ²(n).
- P^{b0,b1} is P with the same M,t,n and totals y'_{aj}=n_j b0+b1 y_{aj}.
- For any natural A, real covariate arrays X_{qj} (q<A), real k_s, and real coefficient array k_q, r^X_{a,j}=r_{a,k_s,j}−Σ_{q<A}k_q(X_{qj}−μ(X_q)). The covariate arm total is R^X_{Pa}(s)=(M/m_a)S_a(r^X_a;s), and the covariate contrast R^X_P=(R^X_{P1}−R^X_{P0})/N.
- F_P=(M²/N²){[M/(M−1)](σ²(y_0)/c+σ²(y_1)/t)+[2σ(y_0,y_1)−σ²(y_0)−σ²(y_1)]/(M−1)} is `htVarianceFormula`.
- A_P(v_0,v_1)=M³/[N²(M−1)]·[σ²(v_0)/c+σ²(v_1)/t] is `approximateVariance`.
- W_P(v_0,v_1;s)=(M²/N²){Σ_{j∈s_0}[v_{0j}−S_0(v_0;s)/c]²/[c(c−1)]+Σ_{j∈s_1}[v_{1j}−S_1(v_1;s)/t]²/[t(t−1)]} is `combinedVarianceEstimator`.
- Z_P(s)=M⁴ σ²(o(s))/[N²(M−1)ct] is `sharpNullVarianceEstimator`.
- An individual-outcome object I for P supplies real Y_{aji} for each arm a, each j<M, and each i<n_j, with Σ_i Y_{aji}=y_{aj}. The individual sharp null means ∀j∀i, Y_{0ji}=Y_{1ji}. Observed individual outcomes use arm 1 in s and arm 0 outside s.
- k_a*=σ(n,y_a)/σ²(n), and k*= (t/M)k_0*+(c/M)k_1*.
- J_P(k)=[(M−c)/c]σ²(r_{0,k})+[(M−t)/t]σ²(r_{1,k})+2σ(r_{0,k},r_{1,k}).
- K_P=M²/[N²(M−1)]·[(M−c)/c+(M−t)/t+2]·σ²(n).

For B populations P_b, block assignments consist of one admissible assignment in each block. The block law is uniform on the full Cartesian product. Mathlib `Data/Fintype/Pi.lean:133–142` enumerates all functions in this finite dependent product, so this is independent uniform randomization across blocks. N_•=Σ_b N_b, H_•=Σ_b(N_b/N_•)H_{P_b}, and d_•=Σ_b(Σ_j y_{1bj}−Σ_j y_{0bj})/N_•.

For h copies of one P, copy assignments likewise form the full product of h admissible-assignment sets, uniformly weighted. Thus the h copies are independent. Put A_{P,a,v,h}=Σ_{r<h}S_a(v;s_r)/h. The pooled copied difference D_{P,h} is Σ_r S_1(y_1;s_r)/Σ_r N_1(s_r)−Σ_r S_0(y_0;s_r)/Σ_r N_0(s_r).

For a positive natural h, P[h] (`replicateWithin`) keeps M,t fixed and multiplies every n_j,y_{0j},y_{1j} by h. `WithinReplicationConsistent P` means design consistency of D_{P[h+1]} for d_{P[h+1]} under L_{P[h+1]}, indexed by natural h.

`logistic` is ℓ(x)=1−1/(1+exp x), and `repairedContrast` is q(n)=2/5−9n/10000. Arithmetic is in ℝ, including totalized division (x/0=0). The definitions are total even off assignment supports; the statements' relevant positivity hypotheses are recorded below rather than silently assumed.

The named populations, with indices starting at 0, are:

- E (`efficiencyPopulation`): M=3,t=1,n=(1,2,4),y_0=(0,1,1),y_1=(0,0,0).
- S (`slopePopulation`): M=3,t=1,n=(1,2,3),y_0=(0,0,0),y_1=(0,0,3).
- U (`subscriptPopulation`): M=2,t=1,n=(1,2),y_0=(0,0),y_1=(1,2).
- V (`bracketPopulation`): same M,t,n as U, but y_0=y_1=(0,2).

## SAP.P020.T1

The conjunction of all of the following, with no hypotheses:

1. For every j<3, the following individual outcomes sum to E's totals: control outcomes are 0 throughout cluster 0; in either other cluster only individual 0 has outcome 1 and all others have outcome 0. All treatment individual outcomes are 0.
2. N_E=7; d_E=−2/7. At s={0},{1},{2}, respectively, D_E=(−1/3,−1/5,−1/3) and H_E=(−3/7,−3/14,−3/14). E_{L_E}D_E=−13/45, B(D_E,d_E)=−1/315, Q(D_E,d_E)=131/33075, E H_E=d_E, and Q(H_E,d_E)=1/98.
3. For every real k: the three values of R_{E,k} are −3/7+6k/7, −3/14+3k/14, −3/14−15k/14; E R_{E,k}=d_E; Q(R_{E,k},d_E)=1/98−6k/49+9k²/14=3/686+(9/14)(k−2/21)²; Q=3/686 iff k=2/21; 3/686≤Q; and 131/33075<3/686<1/98 and Q(D_E,d_E)<Q(R_{E,k},d_E).
4. σ²(n_E)=14/9, σ(n_E,y_{E0})=4/9, σ(n_E,y_{E1})=0, and k*_E=2/21.
5. e_{L_E}(D_E,d_E,1/25)=1.
6. In order, for every natural h, every proof h>0, and every real k: N_{E[h]}=7h, d_{E[h]}=−2/7; for every s∈assignments E, D,H,R_k at E[h] equal their respective values at E; the replicated bias is −1/315; the replicated probability of error greater than 1/25 is 1; and Q(D_{E[h]},d_{E[h]})<Q(R_{E[h],k},d_{E[h]}).
7. 7h→∞ as h→∞; the constant sequence (L_E,D_E,d_E) is not design consistent; `WithinReplicationConsistent E` is false; the base bias is nonzero; and Q(D_E,d_E)<Q(H_E,d_E).

## SAP.P020.T2

A conjunction of six independent assertions:

1. For every type Ω, finite law L on Ω, real function T, and real d, Q_L(T,d)=V_L(T)+B_L(T,d)² and B²≤Q.
2. For every family of types Ω_h, laws L_h, real estimators T_h,U_h on Ω_h, real sequence d_h, real b, proof b≠0, proof B_{L_h}(T_h,d_h)→b, and proof Q_{L_h}(U_h,d_h)→0, there exists a natural h₀ such that for every natural h≥h₀, Q(U_h,d_h)<Q(T_h,d_h). The cutoff may depend on all preceding data and hypotheses.
3. For every Ω,L,T,d,ε with ε>0, e_L(T,d,ε)≤Q_L(T,d)/ε².
4. For every Ω_h,L_h,U_h,d_h, if Q(U_h,d_h)→0, then for every ε>0 its error probability tends to zero.
5. For every natural h>0, the bias of D_{E[h]} is −1/315 and its MSE is less than that of R_{E[h],0}.
6. 7h→∞.

## SAP.P020.T3

The conjunction: ℓ is strictly increasing on all ℝ; for every real n≥1, 2/5−9n/10≤−1/2; for every real base and then real n≥1, ℓ(base+2/5−9n/10)−ℓ(base)<0; for every natural N>0 and real arrays base_i,size_i on Fin N satisfying ∀i,size_i≥1, their average contrast Σ_i[ℓ(base_i+2/5−9size_i/10)−ℓ(base_i)]/N is negative; and, under the same independently quantified assumptions, that average is not 7/1000. No cluster-design or integer-size premise occurs in these last two clauses; in particular N=1 is allowed.

## SAP.P020.T4

1. For every real α,block,n,t, in that order, α+(2/5)t+(7/5)(n/1000)−(9/10)(n/1000)t+block equals α+(2/5)t+(7/5000)n−(9/10000)nt+block.
2. For every real n, q(n)>0 iff n<4000/9, and q(n)<0 iff 4000/9<n.
3. For every natural n, q(n)>0 iff n≤444, and q(n)<0 iff 445≤n.
4. For every real base and natural n, ℓ(base)<ℓ(base+q(n)) iff n≤444, and the reverse strict inequality iff 445≤n.
5. For every natural N>0, real base array and natural size array on Fin N, with every size≥1: if every size≤444, the average ℓ(base_i+q(size_i))−ℓ(base_i) is positive; if every size≥445, it is negative. Mixed populations receive no sign assertion.

## SAP.P020.T5

For every P and every real function k̂ on all finite subsets of Fin M (so its value may depend arbitrarily on the realized assignment),

E R_{P1,k̂(s)}(s)=Σ_j y_{1j}−M C_{L_P}(k̂,n̄_1),
E R_{P0,k̂(s)}(s)=Σ_j y_{0j}−M C_{L_P}(k̂,n̄_0), and
E R_{P,k̂(s)}(s)=d+(M/N)[C(k̂,n̄_0)−C(k̂,n̄_1)].

An independently universally quantified P,k̂ clause asserts the corresponding bias equals (M/N)[C(k̂,n̄_0)−C(k̂,n̄_1)]. There are no independence, unbiased-slope, or nondegenerate-size hypotheses.

## SAP.P020.T6

For the fixed S, with no hypotheses: d_S=1/2; at assignments {0},{1},{2}, the observed slope is (0,0,3/2), and the same-assignment fitted-coefficient contrast is (0,0,3/8). Its mean is 1/8, differs from d_S, and its bias is −3/8. C(k̂_S,n̄_1)=1/2 and C(k̂_S,n̄_0)=−1/4. Also N_S=6, σ²(n_S)=2/3, n̄_1=(1,2,3), n̄_0=(5/2,2,3/2) on those assignments. Finally the bias equals (M_S/N_S)[C(k̂_S,n̄_0)−C(k̂_S,n̄_1)].

## SAP.P020.T7

1. For every natural n, real array Y on Fin n, and real b0,b1, Σ_i(b0+b1Y_i)=nb0+b1Σ_iY_i. n=0 is allowed.
2. For every P, arm a∈{0,1}, real b0,b1,k and index j, r_{P^{b0,b1},a,b0+b1k,j}=b0(N/M)+b1r_{Pa,k,j}.
3. For every P,b0,b1,k,s with s an admissible assignment, R_{P^{b0,b1},b0+b1k}(s) equals (M/N){Σ_{s_1}[b0(N/M)+b1r_{1,k,j}]/t−Σ_{s_0}[b0(N/M)+b1r_{0,k,j}]/c}, and equals b1R_{P,k}(s).
4. For separately quantified P,b0,b1,k,s and admissibility, that transformed contrast also equals (M/N){b1S_1(r_{1,k};s)/t−b1S_0(r_{0,k};s)/c}; this last expression equals b1R_{P,k}(s).

## SAP.P020.T8

1. For every natural M, hypothesis M>0, real arrays v,z on Fin M, and real k, μ(Δ_k(v;z))=μ(v).
2. Under separately quantified M>0,v,z,k, σ²(Δ_k(v;z))=σ²(v)+k²σ²(z)−2kσ(v,z).
3. For every M>0, arrays v,w,z, and real k, put δ=z−μ(z) and C=σ(Δ_k(v;z),Δ_k(w;z)). All seven equalities hold:
   - C=μ(Δ_k(v;z)Δ_k(w;z))−μ(Δ_k(v;z))μ(Δ_k(w;z)).
   - C=μ((v−kδ)(w−kδ))−μ(v)μ(w).
   - C=μ(vw−vkδ−wkδ+k²δ²)−μ(v)μ(w).
   - C=μ(vw)−μ(v)μ(w)−μ(vkδ)−μ(wkδ)+μ(k²δ²).
   - C=σ(v,w)−k[σ(v,z)+μ(v)μ(δ)]−k[σ(w,z)+μ(w)μ(δ)]+k²σ²(z).
   - C=σ(v,w)−k[σ(v,z)+μ(v)·0]−k[σ(w,z)+μ(w)·0]+k²σ²(z).
   - C=σ(v,w)−kσ(v,z)−kσ(w,z)+k²σ²(z).

Here products and powers inside μ are pointwise. Arrays are arbitrary real arrays; they need not be cluster sizes or potential totals.

## SAP.P020.T9

All are closed concrete assertions. In U, {0} is admissible, R_{U^{0,1},0}({0})=2/3, but (M/N){S_1(r_{1,0};{0})/t−S_0(r_{1,0};{0})/c}=−2/3, so these expressions differ. Notice that the latter expression deliberately uses the treatment potential in both arms.

In V, {0} is admissible, σ(y_0,y_1)=1, and μ(y_0)y_{1,0}−μ(y_0)μ(y_1)=−1, so they differ. Separately, for v=w=(0,2), σ(v,w)=1, μ(v)w_0−μ(v)μ(w)=−1, μ(v)w_1−μ(v)μ(w)=1, and the covariance differs from the index-0 expression. Finally R_{U,0}({0})=2/3.

## SAP.P020.T10

1. For every P, individual-outcome object I aggregating to P's totals, proof ∀j,i,Y_{0ji}=Y_{1ji}, subset s, and proof s admissible, all individual control and treatment outcomes equal their observed outcomes, and ∀j,y_{0j}=y_{1j}.
2. Under the same independently quantified data and hypotheses: ∀j, both potential totals equal o_j(s); σ²(y_0)=σ²(y_1)=σ²(o(s)); σ(y_0,y_1)=σ²(o(s)); V_{L_P}(H_P)=F_P; and F_P=Z_P(s). Thus the last observed-total expression equals the actual design variance for each admissible assignment under the individual sharp null.

## SAP.P020.T11

1. For every type Ω, finite law L, real functions u,v on Ω, and proof v(ω)>0 for every ω∈L.support, E_L(u/v)=[E_L u−C_L(u/v,v)]/E_L v.
2. For every P, define A_a(s)=S_a(y_a;s)/N_a(s). Then E_{L_P}D_P=d−(M/N){C(A_1,N_1)/t−C(A_0,N_0)/c}, and B_{L_P}(D_P,d)=−(M/N){C(A_1,N_1)/t−C(A_0,N_0)/c}. No additional P hypotheses beyond its structure fields occur.

## SAP.P020.T12

1. The affine individual-total summation identity from T7, for every n,Y,b0,b1 including n=0.
2. For every P, E H_{P0}=Σ_jy_{0j}, E H_{P1}=Σ_jy_{1j}, and E H_P=d.
3. For every P, real b0,b1, subset s and proof s admissible, H_{P^{b0,b1}}(s)=b0(M/N)[n̄_1(s)−n̄_0(s)]+b1H_P(s).
4. For every P,b0,b1,s, admissibility proof, proof b0≠0, and proof n̄_1(s)≠n̄_0(s), the transformed HT contrast differs from b1H_P(s).
5. There exist P, real b0,b1, and subset s, in that order, such that s is admissible and H_{P^{b0,b1}}(s)≠b1H_P(s).

## SAP.P020.T13

1. For every P and then every fixed real k, E R_{P0,k}=Σ_jy_{0j}, E R_{P1,k}=Σ_jy_{1j}, and E R_{P,k}=d.
2. For every P, natural A (implicit), real array X of A covariates on M clusters, real k_s, and real coefficient array k_q, the two covariate-adjusted arm-total expectations are Σ_jy_{0j},Σ_jy_{1j}, respectively, and E R^X_P=d. A=0 is allowed, but the assertion also covers every positive A; coefficients and X are fixed across assignments.

## SAP.P020.T14

The conjunction of seven independently quantified assertions:

1. For every P, arm a, hypothesis σ²(n)>0, and then real k, σ²(r_{a,k})=σ²(r_{a,k_a*})+σ²(n)(k−k_a*)².
2. For every P, hypothesis σ²(n)>0, arm a, and real k, σ²(r_{a,k_a*})≤σ²(r_{a,k}), with equality iff k=k_a*.
3. For every P and real k, without a size-variance hypothesis, V_{L_P}(R_{P,k})=M²/[N²(M−1)]·J_P(k).
4. For every P, real k, and hypothesis σ²(n)>0, V(R_k)=V(R_{k*})+K_P(k−k*)².
5. Under independently quantified P,k,σ²(n)>0, V(R_k)−V(H)=K_P k(k−2k*).
6. For every P, hypothesis σ²(n)>0, and real k: V(R_{k*})≤V(R_k), with equality iff k=k*; V(R_k)<V(H) iff k²<2kk*; and V(R_k)=V(H) iff k=0 or k=2k*.
7. For every real k and then real star, k²<2k·star iff [(star>0 and 0<k<2star) or (star<0 and 2star<k<0)].

The ratios defining k_a* and k* are the ones in the common dictionary; their uses in these optimum assertions require positive size variance. The unconditional moment formula contains no such ratios.

## SAP.P020.T15

1. For every P, V(H)=[V(H_0)+V(H_1)−2C(H_0,H_1)]/N²; V(H_0)=(M²/c)[(M−c)/(M−1)]σ²(y_0); V(H_1)=(M²/t)[(M−t)/(M−1)]σ²(y_1); and C(H_0,H_1)=−[M²/(M−1)]σ(y_0,y_1).
2. For separately quantified P, V(H)=F_P and V(H)≤A_P(y_0,y_1).
3. For every P, 2σ(y_0,y_1)−σ²(y_0)−σ²(y_1)≤0.
4. For every P, proofs t≥2 and c≥2, E W_P(y_0,y_1)=A_P(y_0,y_1) and V(H)≤E W_P(y_0,y_1).
5. For every P, fixed real k, proofs t≥2 and c≥2, E W_P(r_{0,k},r_{1,k})=A_P(r_{0,k},r_{1,k}) and V(R_k)≤E W_P(r_{0,k},r_{1,k}).
6. For every natural B (implicit), proof B>0, and array of populations P_b, E H_•=d_• and V(H_•)=Σ_b(N_b/N_•)²V_{L_{P_b}}(H_{P_b}).
7. For every B>0,P_b, then arbitrary real estimator functions Vhat_b on each block's subsets, if for every b, V_{L_{P_b}}(H_{P_b})≤E_{L_{P_b}}Vhat_b, then V(H_•)≤E_block[Σ_b(N_b/N_•)²Vhat_b(s_b)]. Vhat need not be pointwise nonnegative, but its expected conservativeness is an explicit hypothesis.

## SAP.P020.T16

For every P, if either (there exists a real τ such that for every cluster j, y_{1j}−y_{0j}=τ) or (c=t), then V_{L_P}(H_P)≤E_{L_P}Z_P. The common effect τ is a cluster-total difference, not an individual outcome difference. The conclusion is about HT only and is a bound in expectation, not for each assignment. There is no fixed-coefficient Des Raj clause.

## SAP.P020.T17

1. For every P, under the independent-copy laws with h+1 copies, all four copy averages converge in probability: A_{1,y_1,h+1}→(t/M)Σ_jy_{1j}, A_{0,y_0,h+1}→(c/M)Σ_jy_{0j}, A_{1,n,h+1}→(t/M)N, A_{0,n,h+1}→(c/M)N. Under those laws the pooled D_{P,h+1} converges in probability to d. Each convergence expands to ∀ε>0, error probability→0; no joint probability space across h is supplied.
2. For every P, [(Σ_jy_{1j})(t/M)]/[N(t/M)]−[(Σ_jy_{0j})(c/M)]/[N(c/M)]=d.
3. For every P, natural h, and proof h>0, N_{P[h]}=hN_P.
4. For every P,h,h>0,s,proof s admissible, and real k, d_{P[h]}=d_P, D_{P[h]}(s)=D_P(s), H_{P[h]}(s)=H_P(s), and R_{P[h],k}(s)=R_{P,k}(s).
5. For every P and proof B_{L_P}(D_P,d_P)≠0: for every h>0 that bias is preserved at P[h]; and the constant sequence (L_P,D_P,d_P) is not design consistent.
6. The constant sequence for E is not design consistent; 7h→∞; for every h>0,L_{E[h]}=L_E; `WithinReplicationConsistent E` is false; and for every h>0 the bias at E[h] is −1/315.

This statement contains no realized-arm-count growth theorem, no joint coupling across different population indices, and no general within-replication inconsistency clause for arbitrary P beyond the constant-sequence clause and the separate estimate-preservation identities. The within-replication inconsistency assertion itself is explicit for E.
