# Blind mathematical reading

This file was written from `SAP/P022/Defs*.lean` and `SAP/P022/Challenge*.lean` before opening `claims.json` or `record.json`. The Challenge contains 18 theorem stubs. Each asserts the entire proposition `TnStatement`; the following expands those propositions. No Solution or Comparator was inspected.

## Shared objects and definitions

All outcomes, thresholds, tolerances, and allocation limits below are real numbers unless a different type is specified. All limits of sequences are along the natural numbers tending to infinity.

* A **design** is three natural numbers `(N,m,k)` with `N >= 4`, `m >= 2`, `k >= 2`, and `m+k <= N`. An assignment is any permutation of `{0,...,N-1}`. Expectation `E_d` averages uniformly over all `N!` permutations, and `P_d(A)=E_d[1_A]`. The assignment type always contains the identity permutation. Its variance is `Var_d X=E_d[(X-E_d X)^2]`.
* For a nonempty vector `v` of length `s`, write `mu(v)=s^(-1) sum_i v_i`, `vpop(v)=s^(-1) sum_i (v_i-mu(v))^2`, `cov(v,w)=s^(-1) sum_i (v_i-mu(v))(w_i-mu(w))`, and `s2(v)=sum_i (v_i-mu(v))^2/(s-1)`. These expand `finiteMean`, `finiteVariance`, `finiteCovariance`, and `sampleVariance`. Mathlib's `Finset.expect` is the cardinality reciprocal times the sum; for an empty set it is zero. All substantive sample/population vectors here have length at least two.
* Given `d,y1,y0,pi`, `a=(y1(pi(0)),...,y1(pi(m-1)))` is the treatment sample and `b=(y0(pi(m)),...,y0(pi(m+k-1)))` the control sample. Write `tau=mu(y1)-mu(y0)`, `hat_tau=mu(a)-mu(b)`, and `V=Var_d(hat_tau)` for `averageEffect`, `estimatedEffect`, and `trueVariance`.
* Define `W(N,m,k,A,D,C)=(((N-m)/m)A+((N-k)/k)D+2C)/(N-1)`. Subtraction in this formula is in the reals, after casting natural parameters.
* `F_v(x)=s^(-1) sum_i 1_{v_i <= x}` and `F_v^-(x)=s^(-1) sum_i 1_{v_i < x}`. Sort a vector into nondecreasing order, with multiplicities. `ord_v(r)` is its one-based order statistic, implemented as list entry `r-1`, with natural subtraction and default value zero for an out-of-range entry. Thus `ord_v(0)` is the first entry for nonempty `v`. `Q_v(u)=ord_v(ceil_nat(s*u))`, where `ceil_nat` is the least nonnegative integer above its argument. On `0<u<=1` this is the usual empirical quantile. Values outside that interval use the foregoing total-function convention.
* A side `B` is either `H` (upper) or `L` (lower). Put `u_H=u` and `u_L=1-u`, and `C_B(a,b)=integral_0^1 Q_a(u)Q_b(u_B) du-mu(a)mu(b)`. This is `sharpCovariance`. `V_B(d,y1,y0)=W(N,m,k,vpop(y1),vpop(y0),C_B(y1,y0))` is `populationBound`.
* The marginal variance estimate is `A_N(v)=((N-1)/N)s2(v)`. The estimate from two observed vectors is `hat_V_B(N,a,b)=W(N,m,k,A_N(a),A_N(b),C_B(a,b))`; `estimatedVariance` applies this to the assigned samples. `conventionalEstimate=(N/(N-1))(A_N(a)/m+A_N(b)/k)`. Neyman's two estimates replace `C_B(a,b)` by `+sqrt(A_N(a)A_N(b))` or its negative in `W`.
* An **experiment sequence** consists of a design `d_q` for every natural `q`, with `N_q=q+4`, and two fixed infinite sequences `y1_i,y0_i`. Row `q` uses their first `N_q` entries. In particular these are nested populations, not arbitrary triangular arrays. Set `Y_{t,q}` equal to the treatment or control population vector. A joint law `H` is a Borel probability measure on `R^2`; its coordinate CDFs are `F_{H,t}(x)=H{p:p_t<=x}` and left CDFs `F^-_{H,t}(x)=H{p:p_t<x}`. The Lean values use `ENNReal.toReal`, which is ordinary conversion for these finite probabilities.
* `weakPopulationConvergence(S,H)` means: for every bounded continuous real function `f` on `R^2`, `mu_i f(y1_i,y0_i)` over row `q` tends to `integral f dH`.
* Write `C123(S,H,theta,rho)` for **all** of: `0<theta<=1`; `0<rho<1`; `m_q/N_q -> theta*rho`; `(m_q+k_q)/N_q -> theta`; weak population convergence to `H`; and, for each coordinate `t` and every discontinuity `x` of `F_{H,t}`, `F_{Y_{t,q}}(x) -> F_{H,t}(x)`.
* `Left(S,H)` additionally requires, at every such coordinate CDF discontinuity, `F^-_{Y_{t,q}}(x) -> F^-_{H,t}(x)`.
* `UI2(S)` means for each coordinate `t`, `sup_q mu_i[y_{t,i}^2 1_{y_{t,i}^2>=beta}] -> 0` as the real `beta -> infinity`, **and**, for every real `beta`, the set of the displayed row averages is bounded above. The second conjunct prevents an unbounded real supremum from taking a default value.
* `dist(A,B)=sup_{x in R}|A(x)-B(x)|` is a real supremum. In these statements its arguments are CDFs, hence the nonempty range is bounded by one. Write `hat_F_{t,q,pi}` for the empirical CDF of the assigned treatment or control sample. For any row-dependent event `E_q`, write `L_S(E)=limsup_q N_q P_{d_q}(E_q)` in the extended nonnegative reals `[0,infinity]`. This is `scaledProbabilityLimsup`; it is not a real-valued limsup. The underlying quantities are nonnegative, so `ENNReal.ofReal` does not alter them.
* `Lemma2Conclusions(S,H,theta,rho)` asserts (i) `dist(F_{H,t},F_{Y_{t,q}})->0` for both coordinates, and then (ii) existence of functions `K1,K0:R->N`, both positive on positive arguments and nonincreasing there, with, for every `eta>0`,
  `L_S{dist(F_{H,1},hat_F_1)>=eta} <= (1-theta*rho)K1(eta)/(theta*rho*eta^2)` and
  `L_S{dist(F_{H,0},hat_F_0)>=eta} <= (1-theta*(1-rho))K0(eta)/(theta*(1-rho)*eta^2)`.
  This definition chooses the functions after the entire sequence and allocation parameters.
* The reciprocal witness has `N_q=q+4`, `m_q=floor(N_q/2)`, `k_q=N_q-m_q`, and both potential outcomes `-1/(i+1)`. `originLaw` is point mass at `(0,0)`. The corner witness uses the same designs and the periodic outcome pairs `(0,0),(0,1),(1,0),(1,1)`. `cornerLaw` assigns mass `1/4` to each of those four pairs. `zeroWitness` uses these designs and all-zero outcomes. `fourUnitDesign` is `(4,2,2)`.
* `D_C(y,a)=integral_{-C}^C |F_a(x)-F_y(x)| dx` is `integratedCDFError`. `frechetCDF(G,F,H)(x,y)=min(G(x),F(y))`; for side `L` it is `max(0,G(x)+F(y)-1)`.
* For a bounded finite experiment put `J=(2N/(N-1)) integral_{-C}^C integral_{-C}^C [min(F_a(x),F_b(y))-min(F_y1(x),F_y0(y))] dy dx`. This is `lastIntegralTerm`. Put `beta1=N(m-1)/(m(N-1))`, `beta0=N(k-1)/(k(N-1))`. The seven terms `T_0,...,T_6` are
  `T0=((N-m)/(m-1))(mu(a^2)-beta1*mu(y1^2))`,
  `T1=((N-m)/(m-1))(mu(a)^2-beta1*mu(y1)^2)`,
  `T2=((N-k)/(k-1))(mu(b^2)-beta0*mu(y0^2))`,
  `T3=((N-k)/(k-1))(mu(b)^2-beta0*mu(y0)^2)`,
  `T4=(2N/(N-1))C(mu(a)-mu(y1)+mu(b)-mu(y0))`,
  `T5=(2N/(N-1))(mu(a)mu(b)-mu(y1)mu(y0))`, and `T6=J`.
  `sevenTotal(T)=T0-T1+T2-T3+T4-T5+T6`.
* For eight real numbers `nu_0,...,nu_7`, `correctedAllocation(nu,e)` is the seven-vector `(nu0,nu1,nu2,nu3,nu4+nu5,nu6+nu7,e/2)`. Write `r_i=termRateCoefficient(theta,rho,i)`. With `p=theta*rho` and `z=theta*(1-rho)`, the eight coefficients are `((1-p)^3/p^3,4(1-p)^3/p^3,(1-z)^3/z^3,4(1-z)^3/z^3,4(1-p)/p,4(1-z)/z,4(1-p)/p,4(1-z)/z)`.
* For positive `m,k`, sort the union `{i/m:0<=i<=m} union {j/k:0<=j<=k}` into `p_0<...<p_M`. This expands `partitionKnots`, `partitionPoint`, and `partitionCells`; out-of-range points are given default zero in Lean, and `M` is list length minus one using natural subtraction. `w_r=p_{r+1}-p_r`, `h_r=(p_r+p_{r+1})/2`. `midpointCovariance(a,b,B)=sum_{r=0}^{M-1} w_r(Q_a(h_r)-mu(a))(Q_b((h_r)_B)-mu(b))`.
* For zero-based ranks `i<m,j<k`, `omega_ij=max(0,min((i+1)k,(j+1)m)-max(ik,jm))/(mk)`. `codeEpsilon=e=1/67108864`; shifted code points are `c_0=e`, `c_r=p_r-e` for `r>0`. `printedCodeBound` is `W` using `A_N(a),A_N(b)` and covariance
  `sum_{r<M}(c_{r+1}-c_r) Q_a(c_{r+1}) ord_b(s_r)-mu(a)mu(b)`,
  where `s_r=ceil_nat(k*c_{r+1})` for `H` and `s_r=k+1-ceil_nat(k*c_{r+1})` for `L`.
* `sortedValues(v)` is the length-preserving sorted vector. `compatibleLaws(H)` is the set of probability laws with the same two coordinate CDFs as `H`. `empiricalCompatibleLaws(y1,y0)` instead fixes the two empirical marginal CDFs.
* `mu_{H,t}=integral p_t dH`, `v_{H,t}=integral(p_t-mu_{H,t})^2 dH`, and `c_H=integral(p_1-mu_{H,1})(p_0-mu_{H,0})dH`. Write `c_H^H=sup{c_J:J compatible with H}` and `c_H^L=inf` of that set. `ell_B(H,theta,rho)=((1-p)/p)v_{H,1}+((1-z)/z)v_{H,0}+2c_H^B` is `limitingBound`. `ell_true` uses `c_H` instead, and `gamma=ell_true/ell_H`.
* `boundConsistency(S)` means: for every `epsilon>0`, `P_{d_q}{max(N_q|hat_V_H-V_H|,N_q|hat_V_L-V_L|)>=epsilon}->0`.
* `BoundedThirdMoments(S)` means there exists one real `M` such that for every row and both coordinates, the row mean of `|y|^3` is at most `M`. `NonsingularLaw(H)` means for every real `a,b,c` with `a!=0 or b!=0`, the law is not almost surely supported on `a p_1+b p_0=c`.
* `Phi(x)=gaussianReal(0,1)((-infinity,x])` is the standard normal CDF (Mathlib's second Gaussian parameter is variance). `z_alpha=inf{x:1-alpha/2<=Phi(x)}`. `weakStandardNormal(S,Z)` requires, for every bounded continuous `f:R->R`, `E_{d_q}f(Z_q)->integral f dN(0,1)`.
* `DisplaysAs(v,p)` means `p-1/2000 <= v <= p+1/2000`, with both ties included. `halfWidth(L,U)=(U-L)/2`; `reductionPercent(A,H)=100(1-H/A)`.

Mathlib checks: averages are defined in `Algebra/BigOperators/Expect.lean`; natural ceilings in `Algebra/Order/Floor/Defs.lean`; interval integrals in `MeasureTheory/Integral/IntervalIntegral/Basic.lean`; Bochner integrals in `MeasureTheory/Integral/Bochner/Basic.lean`; limsups in `Order/LiminfLimsup.lean`; real square roots in `Analysis/Real/Sqrt.lean`; Gaussian measures in `Probability/Distributions/Gaussian/Real.lean`. Bochner integrals are zero for nonintegrable functions, real square roots are zero on negative inputs, and real division is total with division by zero equal to zero. Thus the hypotheses and the domains of each use matter. Finite empirical quantiles/CDFs here give bounded measurable step functions on the integration intervals; isolated quantile endpoint conventions do not affect those integrals. The limiting-law moment uses must be checked under their stated moment hypotheses.

## The 18 theorem readings

### SAP.P022.T1

An unconditional conjunction about the explicit reciprocal witness: it satisfies `C123` with origin law, `theta=1,rho=1/2`; for every natural row `q` and each coordinate `t`, the population CDF distance to that point mass is exactly one; for every `q,t` and **every assignment** the sampled CDF distance is also one; for each coordinate `L_S{distance>=1/2}=infinity`; and the entire proposition `Lemma2Conclusions` is false for this same witness and parameters.

### SAP.P022.T2

For **every** sequence `S`, joint law `H`, and real `theta,rho`, assuming `C123(S,H,theta,rho)` and `Left(S,H)`, define `K(eta)=2 ceil_nat(4/min(eta,1))`. Then: `K(eta)>0` for every positive `eta`; `K(b)<=K(a)` whenever `0<a<=b`; both population CDF distances tend to zero; and for every `eta>0` the treatment and control scaled tail limsups are bounded by the two formulas in `Lemma2Conclusions` with **this same explicit** `K` in both positions. There are no existential K choices.

### SAP.P022.T3

Two independent universally quantified parts.

1. For every design, outcomes, and reals `C,c`, assume `C>=0`, both outcomes have absolute value at most `C` at every unit, `c>0`, `cN<=m`, `cN<=k`, and `2/c<=N`. Put `D1(pi)=D_C(y1,a)` and `D0(pi)=D_C(y0,b)`. Then
   `E D1^2 <= C^2(N-m)/((N-1)m) <= C^2/(cN)`,
   `E D0^2 <= C^2(N-k)/((N-1)k) <= C^2/(cN)`, and
   `E(D1+D0)^2 <= 4C^2/(cN)`.
   For **both** sides and **every** assignment,
   `N|hat_V_B-V_B| <= (16/c+8)C(D1+D0)+8C^2/(c^2 N)`.
   For every `epsilon>0` with `16C^2/(c^2 epsilon)<=N` and both sides,
   `P_d{N|hat_V_B-V_B|>=epsilon} <= 16(16/c+8)^2 C^4/(cN epsilon^2)`.
2. For every sequence and real `theta,rho,C`, assume `0<theta<=1`, `0<rho<1`, the two allocation-ratio limits from `C123`, `C>=0`, and both infinite outcome sequences bounded in absolute value by `C`. No law or weak convergence assumption appears. For every `epsilon,c` with `epsilon>0` and `0<c<min(theta*rho,theta*(1-rho))`, and either side,
   `L_S{N_q|hat_V_B-V_B|>=epsilon} <= 16(16/c+8)^2 C^4/(c epsilon^2)`.

### SAP.P022.T4

For every design, every pair of outcome vectors, and every real threshold `x`, put `G=F_y1(x)`, `F=F_y0(x)`, and `hat_G=F_a(x)`, `hat_F=F_b(x)`. Then `E hat_G=G`, `E hat_F=F`,
`Var hat_G=(N-m)G(1-G)/((N-1)m)` and `Var hat_F=(N-k)F(1-F)/((N-1)k)`;
these variances are respectively at most `(N-m)/(4(N-1)m)` and `(N-k)/(4(N-1)k)`; and the population variances of the indicator vectors are exactly `G(1-G)` and `F(1-F)`.

### SAP.P022.T5

For four constant-one population entries at threshold zero: the population empirical CDF is zero, its indicator population variance is zero, every size-two treatment sample CDF is zero, and its assignment variance under `(4,2,2)` is zero. In addition `(4-2)/(4(4-1)2)=1/12`, and `0!=1/12`. This is an unconditional numerical counterexample, not a quantified hypothesis about some unspecified experiment.

### SAP.P022.T6

The conjunction has several independent parts, with the following exact quantifier order.

1. For every design, outcomes, and `C>=0` bounding both outcome vectors, for every assignment,
   `N(hat_V_H-V_H)=T0-T1+T2-T3+T4-T5+T6`.
   For every positive seven-vector `a` and real `epsilon` with `sum a<=epsilon`,
   `P{N|hat_V_H-V_H|>=epsilon} <= sum_j P{|Tj|>=a_j}`.
   For every assignment, `|J| <= (8NC^2/(N-1)) max(dist(F_a,F_y1),dist(F_b,F_y0))`.
   For every real `x>0` and assignment satisfying `x<=|J|`, at least one of those two distances is at least `(N-1)x/(8NC^2)`.
2. Separately, under the same bounded-design hypotheses, for each positive seven-vector `a`, real `epsilon` with `sum a<=epsilon`, and assignment satisfying `epsilon<=N|hat_V_H-V_H|`, there exists `j in {0,...,6}` with `a_j<=|Tj|`.
3. For every real eight-vector `nu` and real `epsilon1`, if `sum nu=epsilon1/2`, then `sum correctedAllocation(nu,epsilon1)=epsilon1`. No positivity is assumed in this identity.
4. For every real eight-vector `nu` and real `epsilon1`, if `sum nu=epsilon1`, then `nu0+nu1+nu2+nu3+(nu4+nu5)+(nu6+nu7)+(1-epsilon1)=1`.
5. For every sequence `S`, law `H`, and reals `theta,rho,C`, assume `C123`, `C>0`, a global absolute outcome bound `C`, and **as an additional explicit hypothesis** `Lemma2Conclusions(S,H,theta,rho)`. For every real `epsilon1,xi` with `epsilon1>0` and `0<xi<epsilon1/(16C^2)`, **there exist** natural-valued functions `K1,K0` and a real `kappa`. These are chosen after all the preceding data. They obey the two Lemma-2 tail bounds for every positive `eta` (but the selected functions are not asserted positive or monotone). At `eta0=epsilon1/(16C^2)-xi`,
   `C^4 kappa=(1-theta*rho)K1(eta0)/(theta*rho*eta0^2)+(1-theta*(1-rho))K0(eta0)/(theta*(1-rho)*eta0^2)`,
   and `L_S{|J|>=epsilon1/2}<=C^4 kappa`.
   For **every** positive eight-vector `nu` summing to `epsilon1/2`, **if** the six earlier term bounds hold, then for every real `epsilon>epsilon1`,
   `L_S{N|hat_V_H-V_H|>=epsilon} <= L_S{N|hat_V_H-V_H|>=epsilon1} <= C^4(sum_i r_i/nu_i^2+kappa)`.
   The six hypothesized bounds use thresholds `correctedAllocation(nu,epsilon1)_j` for `|Tj|`, `j=0,...,5`, with right sides `C^4 r_j/nu_j^2` for `j=0,...,3`, `C^4(r4/nu4^2+r5/nu5^2)` for `j=4`, and `C^4(r6/nu6^2+r7/nu7^2)` for `j=5`. There is no optimization conclusion and no assertion that the existential functions or constant depend only on the limiting law.

### SAP.P022.T7

An unconditional conjunction about the explicit corner witness: `C123` holds at `theta=1,rho=1/2` with corner law; `Left` holds; and both outcomes have absolute value at most one at every infinite-population index. Its scaled tail limsup for `0=1-1 <= |J|` is infinity. Furthermore, for **every** real `epsilon` with `0<epsilon<1/2`, along rows `q=4r`,
`limsup_r N_{4r} P{N_{4r}|hat_V_H-V|>=epsilon}=infinity`.
The second display compares with the **true** randomization variance `V`, not `V_H`.

### SAP.P022.T8

For every pair of natural sample sizes `m,k>=2` and all observed real vectors `a,b`, using the partition above: widths sum to one. For every natural cell `r<M` and real point `p_r<u<p_{r+1}`,
`ceil_nat(mu)=ceil_nat(m p_{r+1})`, `ceil_nat(ku)=ceil_nat(k p_{r+1})`, and
`k+1-ceil_nat(ku)=ceil_nat(k p_{M-r})`.
The weighted midpoint quantile means equal `mu(a)` and, for either side, `mu(b)`. For each side, the midpoint covariance equals `C_B(a,b)`. Consequently, for **every natural** `N` and either side, inserting this midpoint covariance in `W` gives `hat_V_B(N,a,b)` (no design feasibility condition on this auxiliary `N`). Each row sum of `omega` is `1/m`, each column sum `1/k`, and for either side,
`C_B(a,b)=sum_{i<m,j<k} omega_ij (ord_a(i+1)-mu(a))(ord_b(s_j)-mu(b))`,
where `s_j=j+1` for `H` and `s_j=k-j` for `L`.

### SAP.P022.T9

First, for `(4,2,2)` and constant-one outcomes the true variance is zero; for either side the correct estimate from the two constant-one samples is zero, whereas the shifted printed-code expression is `-1/50331648`.

Second, for **every** natural `N,m,k` with `m,k>=2` and `m+k<=N`, all real samples `a,b`, and assuming **every partition cell** has width strictly greater than `2e`,
`printedCodeBound_H-hat_V_H=-4e ord_a(1)ord_b(1)/(N-1)`, and
`printedCodeBound_L-hat_V_L=-4e ord_a(1)ord_b(k)/(N-1)`.
The width hypothesis controls the shifted point selections; the expression is exact real arithmetic.

### SAP.P022.T10

Three independent parts.

1. For every `N,m,k` with `m,k>=2,m+k<=N`, all fixed real observed vectors and either side,
   `hat_V_B(N,a,b)=(1/m-1/N)s2(a)+(1/k-1/N)s2(b)+2C_B(a,b)/(N-1)`.
2. For every fixed `m,k>=2`, samples `a,b`, and side, as natural `N->infinity`,
   `hat_V_B(N,a,b)->s2(a)/m+s2(b)/k`.
3. For every experiment sequence and natural `m,k`, if its arm sizes eventually equal `m,k` respectively and there exists a common real upper bound on both row population variances for **all** rows, then
   `V_q-[vpop(Y_{1,q})/m+vpop(Y_{0,q})/k]->0`.
   No allocation-fraction or law-convergence assumption is imposed in this part. It asserts no explicit finite-N true-variance remainder, special observed-data formula, or program execution claim.

### SAP.P022.T11

For **all**, in order, reals `Va,VH,z,L,U,LH,UH`, assume `Va,VH,z>0`; the four endpoints lie in the closed three-decimal bins centered at `-1.555,0.192,-1.528,0.165`; and their half widths `h=(U-L)/2`, `hH=(UH-LH)/2` equal `z sqrt(Va)`, `z sqrt(VH)` with a common `z`. Then
`0.873<=h<=0.874`, `0.846<=hH<=0.847`,
`100(1-VH/Va)<=100(1-(423/437)^2)=1204000/190969<6.5`.
Under the **further conditional hypotheses** that `Va` displays as `0.199` and `VH` as `0.186`,
`2400/397<=100(1-VH/Va)<=1204000/190969` and `5.5<100(1-VH/Va)<6.5`.
Separately, with the displayed variance inputs treated as exact, `100(1-0.186/0.199)=1300/199`.

### SAP.P022.T12

This universe-polymorphic theorem is a conjunction of six parts.

1. For every design with `m+k=N` and every real population vector `y`, the design expectation of Neyman's upper estimator with `y1=y0=y` is at most its true randomization variance.
2. For every type, nonempty finite subset `s`, real function `v` nonnegative on `s`, and real `c`, `(average_{i in s} c sqrt(v_i))^2<=c^2 average_{i in s} v_i`.
3. For all real `c,q,d` with `q>=391/2000`, `0<=d<=867/500`, and `d^2=c^2 q`, one has `c^2<=44217/2875`.
4. For all reals `c,meanWidth,meanVariance,trueVariance,bias`, the simultaneous assumptions `c^2<=44217/2875`, `meanVariance>=0`, `meanWidth>=3447/2000`, `meanWidth^2<=c^2 meanVariance`, `trueVariance<=399/2000`, `bias<=-13/2000`, and `meanVariance=trueVariance+bias` imply **False**. This part is an assertion that these numerical constraints are incompatible.
5. For every real `w,v` with `w>=3447/2000` and `w^2<=(98/25)^2 v`, `v>=11881809/61465600` and `v>193/1000`.
6. For all real `V,b`, if `V<=399/2000` and `b<=-13/2000`, then `V+b<=193/1000`.

### SAP.P022.T13

For every design and pair of real population vectors: the difference in means is design-unbiased for `tau`; the true variance equals `W(N,m,k,vpop(y1),vpop(y0),cov(y1,y0))`; for **every** pair `z1,z0` whose lists are respectively permutations of the two original lists, `C_L(y1,y0)<=cov(z1,z0)<=C_H(y1,y0)` and `V_L(y1,y0)<=V(d,z1,z0)<=V_H(y1,y0)`. Pairing both sorted vectors attains `V_H`; pairing sorted treatment with reverse-sorted control attains `V_L`.

For **every** joint probability law `J` with these empirical marginal CDFs, the product of coordinates is integrable and `C_L<=c_J<=C_H`. For **each** side `B` there **exists** such a law `J` with `c_J=C_B` and, for **every** bounded continuous real function `f` on `R^2`,
`integral f dJ=integral_0^1 f(Q_y1(u),Q_y0(u_B)) du`.
Thus both finite rearrangements and arbitrary probability couplings with these empirical marginals are included.

### SAP.P022.T14

For every design with the **additional equality** `m+k=N`, every pair of real population vectors, and every assignment,
`Neyman_L <= hat_V_L <= hat_V_H <= Neyman_H <= conventionalEstimate`.
There are no outcome moment or nondegeneracy assumptions.

### SAP.P022.T15

For every sequence, joint law, and `theta,rho`, assuming `C123` and `UI2`: for **every** compatible probability law `J`, **each** coordinate, and every natural power `j<=2`, `p_t^j` is integrable under `J`; for every such `J` the coordinate product is integrable; for either side `N_q V_{B,q}->ell_B(H,theta,rho)`; and `boundConsistency(S)` holds. The supremum/infimum defining `ell_B` ranges over **all** probability couplings with the limiting marginals.

### SAP.P022.T16

For every probability law `H` and reals `theta,rho,C` with `C>=0`, there **exist three functions** `kappa1,kappa2,kappa3:R->R`, all nonnegative on positive arguments, such that for **every** experiment sequence `S` satisfying `C123(S,H,theta,rho)` and both global absolute outcome bounds by `C`, and then for **all** real `epsilon,epsilon1,epsilon2,epsilon3` with `epsilon_i>0` and `epsilon1+epsilon2+epsilon3=epsilon`,
`L_S{N|hat_V_H-V_H|>=epsilon} <= C^4 kappa1(epsilon1)`, and
`L_S{N|hat_V_L-V_L|>=epsilon} <= C^4(1/epsilon1^2+kappa2(epsilon2)+kappa3(epsilon3))`.
The functions are chosen before `S` and before all tolerances, but after `H,theta,rho,C`. They are finite real-valued functions. No `Left` or `UI2` hypothesis is present.

### SAP.P022.T17

For every sequence, joint law, and real allocation limits satisfying `C123`, bounded third moments, and `NonsingularLaw(H)`: `0<gamma<=1`; `N_q V_q->ell_true`; the statistic
`Z_q=(hat_tau_q-tau_q)/sqrt(gamma*hat_V_{H,q})`
converges weakly to the standard normal in the bounded-continuous-test-function sense. Further, for **every** `0<alpha<1`, the literal event
`|hat_tau_q-tau_q|<=z_alpha sqrt(hat_V_{H,q})`
has probability tending to `2Phi(z_alpha/sqrt(gamma))-1`, and that limiting value is at least `1-alpha`. The square root and quotient are Lean's total real operations at each finite row; the conclusions do not assert pointwise positivity of every finite-row denominator. There is no statement of optimal or narrowest interval width.

### SAP.P022.T18

It is **false** that: for **every** joint law `H` there **exist** natural-valued functions `K1,K0`, positive and nonincreasing on positive arguments, such that for **every** experiment sequence `S` and real `theta,rho` satisfying `C123`, both population CDF distances tend to zero and for every positive threshold the two scaled sampled-CDF tail bounds in `Lemma2Conclusions` hold with those fixed functions. Equivalently, some law admits no such pair of functions that works for all sequences and allocation parameters. The negation scopes over this entire universal-law/existential-functions/universal-sequence assertion.
