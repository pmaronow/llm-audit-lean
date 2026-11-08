# Blind reading

Saved before opening `claims.json` or `record.json`. Source: the six Defs parts and the Challenge file, with the Mathlib meanings below. This is a reading of statements, not acceptance of their docstrings or proofs.

## Objects and conventions used throughout

* A design is a triple of natural numbers `(N,m,k)` with `N >= 4`, `m >= 2`, `k >= 2`, `m+k <= N`. An assignment is a permutation of `{0,...,N-1}`. `E_d` is the arithmetic average over all `N!` permutations, `P_d(A)=E_d 1_A`, and `Var_d(X)=E_d[(X-E_d X)^2]`. These are finite sums, not expectations under an unspecified probability law. Every unordered pair of disjoint treatment/control subsets of sizes `m,k` has the same induced weight.
* For `v:{0,...,s-1}->R`, write `bar(v)=(1/s) sum_i v_i`, `vpop(v)=bar((v-bar(v))^2)`, `covpop(v,w)=bar((v-bar(v))(w-bar(w)))`, and `s2(v)=sum_i (v_i-bar(v))^2/(s-1)`. The first variance uses denominator `s`; the sample variance uses `s-1`. `finiteMean` uses Mathlib `Finset.expect`: inverse of the cardinality (as a nonnegative rational) times the sum. An empty average is zero, but the design and sample-size hypotheses here exclude empty outcome arrays whenever their sizes matter.
* Under permutation `pi`, `a_i=y1_(pi(i))` for `0<=i<m` and `b_j=y0_(pi(m+j))` for `0<=j<k`. The estimand is `tau=bar(y1)-bar(y0)`, the estimator is `hat(tau)=bar(a)-bar(b)`, and `V_d(y1,y0)=Var_d(hat(tau))` is actual randomization variance.
* `R(N,m,k;v1,v0,cov) = [((N-m)/m)v1 + ((N-k)/k)v0 + 2 cov]/(N-1)`; all subtractions in this formula are in the reals, even though `N,m,k` are natural parameters.
* `F_v(x)=bar(1_(v_i<=x))` and `F_v^-(x)=bar(1_(v_i<x))`. Sort `v` in increasing order with multiplicities. `O_v(r)` is its entry at zero-based index `r-1`, with natural truncated subtraction and default zero for an out-of-range index. Thus `O_v(0)` is the smallest entry for a nonempty array. `Q_v(u)=O_v(ceil_nat(s u))`. For `0<u<=1`, this is the ordinary left quantile. At `u=0` it is the smallest entry; for arguments outside `[0,1]` the totalized definition may select a default. `sortedValues(v)_i=O_v(i+1)` and `i.rev=s-1-i`.
* The two sides are `H` (upper) and `L` (lower). Write `r_H(u)=u`, `r_L(u)=1-u`. `C_B(v,w)=integral_0^1 Q_v(u) Q_w(r_B(u)) du - bar(v)bar(w)`. `V_B=R(N,m,k;vpop(y1),vpop(y0),C_B(y1,y0))` is a population endpoint, not actual variance. `A_N(v)=((N-1)/N)s2(v)`. For observed arrays, `hat(V)_B=R(N,m,k;A_N(a),A_N(b),C_B(a,b))`. `estimateBound` is the same formula for arbitrary arrays and ambient `N`.
* Write `hat(V)_NB=R(N,m,k;A_N(a),A_N(b), +/- sqrt(A_N(a)A_N(b)))`, plus for `H`, minus for `L`; this is `neymanEstimate`. `hat(V)_conv=N/(N-1)[A_N(a)/m+A_N(b)/k]`. Mathlib `Real.sqrt` is zero on nonpositive inputs; the finite variance terms here are nonnegative.
* An experiment sequence has a design for each natural `q`, with `N_q=q+4`, and TWO FIXED infinite real sequences `y1_i,y0_i`. Row `q` uses their first `N_q` values. Thus the populations are nested prefixes, not arbitrary triangular arrays. `rowOutcomes S t q` uses `y1` when Boolean `t=true` and `y0` when false. Limits in `q` are ordinary limits as `q->infinity`.
* `H` is a Borel probability measure on `R^2` (Mathlib `ProbabilityMeasure`). `F_H,t(x)=H{p:p_t<=x}` and `F_H,t^-(x)=H{p:p_t<x}`, converted from extended nonnegative reals to reals. This conversion is exact since these masses are at most one. Weak population convergence means, for EVERY bounded continuous real `f` on `R^2`, `bar_i f(y1_i,y0_i) -> integral f dH`.
* Write `C123(S,H,theta,rho)` for the conjunction: `0<theta<=1`, `0<rho<1`; `m_q/N_q -> theta rho`; `(m_q+k_q)/N_q -> theta`; the preceding weak convergence; and, for EVERY Boolean `t` and real `x` at which `F_H,t` is not continuous, `F_(row q,t)(x) -> F_H,t(x)`. There is no left-limit convergence condition inside `C123`.
* `Left(S,H)` separately requires, for every such `t,x` of discontinuity, `F_(row q,t)^-(x) -> F_H,t^-(x)`.
* `UI2(S)` requires, for EACH `t`, that `sup_q bar_i[y_(t,i)^2 1_(beta<=y_(t,i)^2)] -> 0` as the real `beta->+infinity`, AND that the set in this supremum is bounded above for EVERY real `beta`. In particular its supremum is a genuine finite real supremum. The threshold is inclusive.
* `M3(S)` says there EXISTS a real `M` such that for ALL `q,t`, `bar_i |y_(t,i)|^3 <= M`.
* `d(A,B)=sup_(x in R)|A(x)-B(x)|` (`cdfDistance`) is a real supremum. In these statements the functions are CDFs and the range is nonempty and contained in `[0,1]`. `hat(F)_(q,t)` is the empirical CDF of the indicated observed treatment or control sample.
* For events `E_q` on assignments, write `L_S(E)=limsup_q ofReal(N_q P_(d_q)(E_q))` in `[0,+infinity]`. Mathlib `ofReal` truncates negatives to zero; the inputs here are nonnegative. This extended-real limsup has the usual meaning even when infinite, unlike an unbounded real supremum. A bound by `ofReal(r)` is finite.
* `Lemma2(S,H,theta,rho)` means: both distances `d(F_H,t,F_(row q,t))->0`; AND there EXIST functions `K1,K0:R->N`, positive at each positive argument, nonincreasing on positive arguments, such that for every `eta>0`,
  `L_S{d(F_H,1,hat(F)_1)>=eta} <= ofReal((1-theta rho) K1(eta)/(theta rho eta^2))`,
  `L_S{d(F_H,0,hat(F)_0)>=eta} <= ofReal((1-theta(1-rho)) K0(eta)/(theta(1-rho) eta^2))`.
  Its existential functions are chosen AFTER `S,H,theta,rho`.
* `D_C(v,a)=integral_(-C)^C |F_a(x)-F_v(x)| dx`.
* For a probability law `J`, `mu_t(J)=integral p_t dJ`, `var_t(J)=integral (p_t-mu_t(J))^2 dJ`, `cov(J)=integral (p_1-mu_1(J))(p_0-mu_0(J)) dJ`. `Comp(H)` is ALL probability laws with the same two marginal CDFs as `H`. `EmpComp(y1,y0)` is ALL laws whose marginal CDFs equal the two empirical CDFs. Define
  `B_B(H,theta,rho) = (1-theta rho)/(theta rho) var_1(H) + (1-theta(1-rho))/(theta(1-rho)) var_0(H) + 2 ext_B{cov(J):J in Comp(H)}`,
  where `ext_H=sup`, `ext_L=inf`, both taken in the reals. `T(H,theta,rho)` replaces this extremum by `cov(H)`, and `gamma=T/B_H`. Integrability and boundedness are not part of these definitions themselves; the hypotheses of T15 and T17 are intended to supply them.
* `Consistent(S)` says for EVERY `epsilon>0`, `P_(d_q){epsilon <= max(N_q |hat(V)_H-V_H|, N_q |hat(V)_L-V_L|)} -> 0`.
* `Nonsingular(H)` says for ALL real `a,b,c`, if `a!=0 OR b!=0`, it is NOT the case that `a p_1+b p_0=c` almost surely. This excludes support on any affine line, not just zero marginal variances.
* `Phi(x)` is the CDF at `x` of Mathlib `gaussianReal 0 1`, whose second parameter is variance. `z(alpha)=inf{x:1-alpha/2<=Phi(x)}` in the reals. `Normal(S,Z)` means for EVERY bounded continuous real `f` on `R`, `E_(d_q) f(Z_q)->integral f dN(0,1)`.
* Unspecified integrals on real intervals use Lebesgue measure; an interval integral is oriented. Mathlib Bochner integrals default to zero if not integrable. Empirical quantiles and CDF integrands here are bounded step functions on finite intervals, so this convention does not change their integrals. The law moments need the substantive moment hypotheses. Division in `R` is total (`x/0=0`); uses with design denominators and admissible allocation parameters have positive denominators. In T8's identity for arbitrary ambient `N`, degenerate real denominators are shared on both sides of an identity.

## Partition and decomposition definitions

For `m,k>=2`, let `0=p_0<...<p_R=1` be the increasing, duplicate-free union `{i/m:0<=i<=m} union {j/k:0<=j<=k}`. These are `partitionKnots`; `R=length-1`; `p_r` outside the list defaults to zero. `w_r=p_(r+1)-p_r`, `u_r=(p_r+p_(r+1))/2` for `0<=r<R`. Define

`M_B(a,b)=sum_(r<R) w_r [Q_a(u_r)-bar(a)] [Q_b(r_B(u_r))-bar(b)]`.

For zero-based ranks `i<m,j<k`,

`W_ij=max(0,min((i+1)k,(j+1)m)-max(ik,jm))/(mk)`.

Let `e=1/67108864`; `p'_0=e`, `p'_r=p_r-e` for `r>0`. `Code_B(N,a,b)` is `R(N,m,k;A_N(a),A_N(b),Ccode_B)`, with

`Ccode_B=sum_(r<R)(p'_(r+1)-p'_r) Q_a(p'_(r+1)) O_b(s_B(r)) - bar(a)bar(b)`,

where `s_H(r)=ceil_nat(k p'_(r+1))` and `s_L(r)=k+1-ceil_nat(k p'_(r+1))` (natural subtraction). This models the displayed shifted arithmetic, in exact real arithmetic.

`Frec_H(G,F;x,y)=min(G(x),F(y))` and `Frec_L=max(0,G(x)+F(y)-1)`.

For a design, outcomes bounded by `C`, and observed `a,b`, let `b1=N(m-1)/(m(N-1))`, `b0=N(k-1)/(k(N-1))`. The seven signed ingredients `T_j` are:

1. `T_0=(N-m)/(m-1) [bar(a^2)-b1 bar(y1^2)]`.
2. `T_1=(N-m)/(m-1) [bar(a)^2-b1 bar(y1)^2]`.
3. `T_2=(N-k)/(k-1) [bar(b^2)-b0 bar(y0^2)]`.
4. `T_3=(N-k)/(k-1) [bar(b)^2-b0 bar(y0)^2]`.
5. `T_4=2N C/(N-1) [bar(a)-bar(y1)+bar(b)-bar(y0)]`.
6. `T_5=2N/(N-1) [bar(a)bar(b)-bar(y1)bar(y0)]`.
7. `T_6=I=2N/(N-1) integral_(-C)^C integral_(-C)^C [min(F_a(x),F_b(y))-min(F_y1(x),F_y0(y))] dy dx`.

`sevenTotal=T_0-T_1+T_2-T_3+T_4-T_5+T_6`.

For `nu:{0,...,7}->R`, `A(nu,epsilon1)=(nu0,nu1,nu2,nu3,nu4+nu5,nu6+nu7,epsilon1/2)` (`correctedAllocation`). Put `p=theta rho`, `r=theta(1-rho)`. The eight `termRateCoefficient`s are

`c_i=((1-p)^3/p^3, 4(1-p)^3/p^3, (1-r)^3/r^3, 4(1-r)^3/r^3, 4(1-p)/p, 4(1-r)/r, 4(1-p)/p, 4(1-r)/r)`.

## Each theorem

### SAP.P022.T1

This is a closed conjunction, with no input hypotheses. Let `Sneg` have `N=q+4`, `m=floor(N/2)`, `k=N-m`, and BOTH outcomes `y_i=-1/(i+1)`. Let `H0=delta_(0,0)`. It asserts:

* `C123(Sneg,H0,1,1/2)`.
* For ALL `q` and Booleans `t`, `d(F_H0,t,F_(row q,t))=1`.
* For ALL `q,t` and assignments `pi` of row `q`, `d(F_H0,t,hat(F)_(q,t,pi))=1`.
* For EACH `t`, `L_Sneg{d(F_H0,t,hat(F)_t)>=1/2}=+infinity`.
* `NOT Lemma2(Sneg,H0,1,1/2)`.

### SAP.P022.T2

For EVERY sequence `S`, law `H`, and real `theta,rho`, assuming `C123(S,H,theta,rho)` and `Left(S,H)`, let `K(eta)=2 ceil_nat(4/min(eta,1))`. It asserts: `K(eta)>0` for EVERY positive `eta`; `K(b)<=K(a)` for ALL `0<a<=b`; both population CDF distances tend to zero; and for EVERY `eta>0`, both tail inequalities in `Lemma2` hold with THIS SAME explicit `K` in place of both `K1,K0`.

### SAP.P022.T3

There are two universally quantified conjuncts.

(i) For EVERY design `d`, outcomes `y1,y0`, and real `C,c`, assume `C>=0`, `|y1_i|<=C` and `|y0_i|<=C` for EVERY population index, `c>0`, `cN<=m`, `cN<=k`, and `2/c<=N`. Put `D1(pi)=D_C(y1,a)` and `D0(pi)=D_C(y0,b)`. Then

* `E D1^2 <= C^2(N-m)/((N-1)m) <= C^2/(cN)` and the corresponding inequality for `D0` with `k`.
* `E(D1+D0)^2<=4C^2/(cN)`.
* For EVERY side `B` and assignment `pi`, `N|hat(V)_B-V_B| <= (16/c+8) C(D1+D0)+8C^2/(c^2 N)`.
* For EVERY `epsilon>0` with `16C^2/(c^2 epsilon)<=N` and EVERY side `B`, `P{epsilon<=N|hat(V)_B-V_B|} <= 16(16/c+8)^2 C^4/(c N epsilon^2)`.

(ii) For EVERY `S,theta,rho,C`, assume `0<theta<=1`, `0<rho<1`, the TWO allocation limits from `C123`, `C>=0`, and the two uniform bounds `|y1_i|,|y0_i|<=C` for EVERY infinite-sequence index. No weak population convergence is assumed in this conjunct. Then for EVERY `epsilon>0`, EVERY `c>0` with `c<min(theta rho,theta(1-rho))`, and EVERY side `B`,

`L_S{epsilon<=N_q|hat(V)_B-V_B|} <= ofReal(16(16/c+8)^2 C^4/(c epsilon^2))`.

### SAP.P022.T4

For EVERY design `d`, pair `y1,y0`, and real threshold `x`, write `G=F_y1(x)`, `F=F_y0(x)`, `Gh(pi)=F_a(x)`, `Fh(pi)=F_b(x)`. The conclusion is the conjunction

`E Gh=G`, `E Fh=F`,

`Var Gh=(N-m)/((N-1)m) G(1-G)`, `Var Fh=(N-k)/((N-1)k) F(1-F)`,

`Var Gh<=(N-m)/(4(N-1)m)`, `Var Fh<=(N-k)/(4(N-1)k)`,

and `vpop(1_(y1_i<=x))=G(1-G)`, `vpop(1_(y0_i<=x))=F(1-F)`.

### SAP.P022.T5

Closed numerical conjunction: for four outcomes all equal to one and threshold zero, the population empirical CDF is zero; its indicator-array population variance is zero; for EVERY assignment in design `(4,2,2)` the treatment empirical CDF is zero; the design variance of that sampled CDF is zero; `(4-2)/(4(4-1)2)=1/12`; and `0!=1/12`.

### SAP.P022.T6

This is FIVE conjuncts; the long last one has a different quantifier order from a universal rate-function construction.

(i) For EVERY design, outcomes `y1,y0`, and real `C>=0` with both absolute outcome bounds for EVERY index:

* For EVERY assignment, `N(hat(V)_H-V_H)=sevenTotal(T)`.
* For EVERY positive vector `a` of seven real tolerances and EVERY real `epsilon` with `sum a_j<=epsilon`, `P{epsilon<=N|hat(V)_H-V_H|} <= sum_j P{a_j<=|T_j|}`.
* For EVERY assignment, `|I| <= [8N C^2/(N-1)] max(d(F_a,F_y1),d(F_b,F_y0))`.
* For EVERY real `x>0` and EVERY assignment with `x<=|I|`, at least one of the two CDF distances is at least `(N-1)x/(8N C^2)`.

(ii) For EVERY design, outcomes and real `C`, if `C>=0` and both absolute outcome bounds hold, then for EVERY positive seven-vector `a`, real `epsilon` with `sum a<=epsilon`, and assignment with `epsilon<=N|hat(V)_H-V_H|`, there EXISTS an index `j<7` with `a_j<=|T_j|`.

(iii) For EVERY real eight-vector `nu` and real `epsilon1` with `sum nu=epsilon1/2`, `sum_j A(nu,epsilon1)_j=epsilon1`. No positivity is assumed here.

(iv) For EVERY real eight-vector `nu` and real `epsilon1` with `sum nu=epsilon1`, `nu0+nu1+nu2+nu3+(nu4+nu5)+(nu6+nu7)+(1-epsilon1)=1`. Again there is no positivity hypothesis.

(v) For EVERY `S,H,theta,rho,C`, assuming `C123`, `C>0`, both uniform outcome bounds, and `Lemma2(S,H,theta,rho)`, and THEN for EVERY `epsilon1,xi` with `epsilon1>0` and `0<xi<epsilon1/(16C^2)`, there EXIST `K1,K0:R->N` and real `kappa` such that:

* For EVERY `eta>0`, both sampled-CDF tail inequalities displayed in `Lemma2` hold for these `K1,K0`. Positivity and monotonicity of these selected functions are NOT asserted.
* With `eta=epsilon1/(16C^2)-xi`, `C^4 kappa=(1-theta rho)K1(eta)/(theta rho eta^2)+(1-theta(1-rho))K0(eta)/(theta(1-rho)eta^2)`.
* `L_S{epsilon1/2<=|I_q|}<=ofReal(C^4 kappa)`.
* For EVERY positive eight-vector `nu` with `sum nu=epsilon1/2`, IF the following SIX additional tail-rate inequalities hold, THEN for EVERY real `epsilon>epsilon1`,
  `L_S{epsilon<=N|hat(V)_H-V_H|} <= L_S{epsilon1<=N|hat(V)_H-V_H|}` and
  `L_S{epsilon1<=N|hat(V)_H-V_H|} <= ofReal(C^4[sum_(i<8)c_i/nu_i^2+kappa])`.
  The six assumed inequalities bound `L_S{A_j<=|T_j|}` by `ofReal(C^4 c_j/nu_j^2)` for `j=0,1,2,3`; by `ofReal(C^4[c_4/nu4^2+c_5/nu5^2])` for `j=4`; and by `ofReal(C^4[c_6/nu6^2+c_7/nu7^2])` for `j=5`.

In (v), the witnesses may depend on the sequence and both tolerances. No minimization over allocations is asserted, and the earlier six rates are hypotheses, not conclusions.

### SAP.P022.T7

Closed conjunction for `Scorner`, whose design is the balanced full-sampling design of T1 and whose outcomes are periodic: `y1=(0,0,1,1,...)`, `y0=(0,1,0,1,...)`. `Hcorner` gives mass `1/4` to each of `(0,0),(0,1),(1,0),(1,1)`. It asserts `C123(Scorner,Hcorner,1,1/2)`, `Left(Scorner,Hcorner)`, and `|y1_i|,|y0_i|<=1` for EVERY `i`; then

`L_Scorner{(1-1)<=|I_q|}=+infinity`.

The threshold in this event is literally ZERO. Finally, for EVERY `0<epsilon<1/2`, the limsup along rows `q=4r` of

`ofReal(N_(4r) P{epsilon<=N_(4r)|hat(V)_H - V_d(y1,y0)|})`

is `+infinity`. The center in this LAST display is ACTUAL variance, not the sharp population upper endpoint.

### SAP.P022.T8

For EVERY natural `m,k>=2` and EVERY real arrays `a,b` of those lengths:

* `sum_(r<R) w_r=1`.
* For EVERY `r<R` and EVERY real `u` with `p_r<u<p_(r+1)`, `ceil_nat(mu)=ceil_nat(m p_(r+1))`, `ceil_nat(ku)=ceil_nat(k p_(r+1))`, and `k+1-ceil_nat(ku)=ceil_nat(k p_(R-r))`.
* `sum w_r Q_a(u_r)=bar(a)`; for EVERY `B`, `sum w_r Q_b(r_B(u_r))=bar(b)`.
* For EVERY `B`, `M_B(a,b)=C_B(a,b)`.
* For EVERY natural ambient `N` and EVERY `B`, `R(N,m,k;A_N(a),A_N(b),M_B(a,b))=estimateBound(N,a,b,B)`. This identity places no design lower bound on `N`.
* For EVERY rank `i<m`, `sum_j W_ij=1/m`; for EVERY rank `j<k`, `sum_i W_ij=1/k`.
* For EVERY `B`, `C_B(a,b)=sum_i sum_j W_ij [O_a(i+1)-bar(a)] [O_b(j+1)-bar(b)]` for `B=H`, with the last rank replaced by `k-j` for `B=L`.

All subtractions in rank expressions are natural, but the stated index ranges make them legitimate reflected indices.

### SAP.P022.T9

Two conjuncts. First, in design `(4,2,2)` with both outcomes constantly one, actual variance is zero, and for EVERY `B`, `estimateBound(4,(1,1),(1,1),B)=0`, while `Code_B(4,(1,1),(1,1))=-1/50331648`.

Second, for EVERY natural `N,m,k` with `m,k>=2`, `m+k<=N`, EVERY real observed arrays `a,b`, IF `2e<w_r` for EVERY partition cell `r<R`, THEN

`Code_H-estimateBound_H=-4e O_a(1)O_b(1)/(N-1)`,

`Code_L-estimateBound_L=-4e O_a(1)O_b(k)/(N-1)`.

### SAP.P022.T10

Three conjuncts:

(i) For EVERY `m,k,N` with `m,k>=2`, `m+k<=N`, EVERY `a,b,B`,

`estimateBound(N,a,b,B)=(1/m-1/N)s2(a)+(1/k-1/N)s2(b)+2C_B(a,b)/(N-1)`.

(ii) For EVERY fixed `m,k>=2` and arrays `a,b` and side `B`, as the natural ambient `N->infinity`, `estimateBound(N,a,b,B)->s2(a)/m+s2(b)/k`. No quantifier over changing arrays appears here.

(iii) For EVERY experiment sequence and EVERY natural `m,k`, IF eventually `m_q=m`, eventually `k_q=k`, and there EXISTS a real `M` bounding BOTH population marginal variances in EVERY row, THEN

`V_(d_q)(y1,y0)-[vpop(row y1)/m+vpop(row y0)/k] -> 0`.

### SAP.P022.T11

`DisplaysAs(x,p)` means the CLOSED interval `p-1/2000<=x<=p+1/2000`, so both ties count. Two conjuncts:

(i) For ALL real `Va,VH,z,L,U,LH,UH` in that order, assume `Va,VH,z>0`, `L` displays as `-1.555`, `U` as `0.192`, `LH` as `-1.528`, `UH` as `0.165`, and `(U-L)/2=z sqrt(Va)`, `(UH-LH)/2=z sqrt(VH)`. Then:

* `0.873<=(U-L)/2<=0.874` and `0.846<=(UH-LH)/2<=0.847`.
* `100(1-VH/Va)<=100(1-(423/437)^2)=1204000/190969<6.5`.
* IF ALSO `Va` displays as `0.199` and `VH` as `0.186`, THEN `2400/397<=100(1-VH/Va)<=1204000/190969` AND `5.5<100(1-VH/Va)<6.5`.

(ii) The exact displayed-input calculation is `100(1-(0.186)/(0.199))=1300/199`.

### SAP.P022.T12

Six conjuncts (the finite-set one is universe-polymorphic):

(i) For EVERY full-sampling design `m+k=N` and EVERY single outcome array `y` used in BOTH arms, `E_d hat(V)_NH <= V_d(y,y)`.

(ii) For EVERY type, finite NONEMPTY subset `s`, real function `v` nonnegative on `s`, and real `c`, `(average_(i in s) c sqrt(v_i))^2 <= c^2 average_(i in s) v_i`.

(iii) For ALL real `c,q,d` with `q>=391/2000`, `0<=d<=867/500`, and `d^2=c^2 q`, `c^2<=44217/2875`.

(iv) For ALL real `c,meanWidth,meanVariance,trueVariance,bias` satisfying `c^2<=44217/2875`, `meanVariance>=0`, `meanWidth>=3447/2000`, `meanWidth^2<=c^2 meanVariance`, `trueVariance<=399/2000`, `bias<=-13/2000`, and `meanVariance=trueVariance+bias`, conclude FALSE. This explicitly asserts incompatibility of these numerical constraints.

(v) For ALL reals `w,v` with `w>=3447/2000` and `w^2<=(98/25)^2 v`, `v>=11881809/61465600` and `v>193/1000`.

(vi) For ALL reals `V,b` with `V<=399/2000` and `b<=-13/2000`, `V+b<=193/1000`.

### SAP.P022.T13

For EVERY design and EVERY two population outcome arrays `y1,y0`:

* `E_d hat(tau)=tau` and `V_d(y1,y0)=R(N,m,k;vpop(y1),vpop(y0),covpop(y1,y0))`.
* For EVERY arrays `z1,z0`, IF their lists are respectively permutations (with multiplicities) of `y1,y0`, THEN `C_L(y1,y0)<=covpop(z1,z0)<=C_H(y1,y0)` and `V_L(y1,y0)<=V_d(z1,z0)<=V_H(y1,y0)`.
* For BOTH increasingly sorted arrays the actual variance equals `V_H`; for increasingly sorted `y1` and decreasingly sorted `y0` it equals `V_L`.
* For EVERY `J in EmpComp(y1,y0)`, the function `p_1 p_0` is integrable and `C_L<=cov(J)<=C_H`.
* For EACH `B` there EXISTS `J in EmpComp(y1,y0)` with `cov(J)=C_B` AND, for EVERY bounded continuous real `f` on `R^2`, `integral f dJ=integral_0^1 f(Q_y1(u),Q_y0(r_B(u))) du`. Thus attainment is asserted for probability couplings as well as finite rearrangements.

### SAP.P022.T14

For EVERY design with the ADDITIONAL hypothesis `m+k=N`, EVERY pair of population outcomes, and EVERY assignment,

`hat(V)_NL <= hat(V)_L <= hat(V)_H <= hat(V)_NH <= hat(V)_conv`.

There is no corresponding assertion here for a design with unsampled units.

### SAP.P022.T15

For EVERY `S,H,theta,rho`, assuming `C123` AND `UI2`:

* For EVERY `J in Comp(H)`, EVERY `t`, EVERY natural `j<=2`, `p_t^j` is integrable under `J`.
* For EVERY such `J`, `p_1 p_0` is integrable.
* For EACH side `B`, `N_q V_B(row q)->B_B(H,theta,rho)`.
* `Consistent(S)` holds, i.e. simultaneous convergence in probability to zero of BOTH scaled endpoint errors.

### SAP.P022.T16

For EVERY law `H` and real `theta,rho,C` with `C>=0`, there EXIST THREE real functions `kappa1,kappa2,kappa3:R->R`, all nonnegative at EVERY positive argument, such that for EVERY sequence `S` with `C123(S,H,theta,rho)` and `|y1_i|,|y0_i|<=C` for EVERY `i`, and for ALL real `epsilon,epsilon1,epsilon2,epsilon3` with `epsilon_j>0` and `epsilon1+epsilon2+epsilon3=epsilon`,

`L_S{epsilon<=N|hat(V)_H-V_H|} <= ofReal(C^4 kappa1(epsilon1))`,

`L_S{epsilon<=N|hat(V)_L-V_L|} <= ofReal(C^4[1/epsilon1^2+kappa2(epsilon2)+kappa3(epsilon3)])`.

The functions are chosen before `S` and tolerances but after `C,H,theta,rho`. No monotonicity is asserted. Invalid allocation parameters need not have any admissible sequence.

### SAP.P022.T17

For EVERY `S,H,theta,rho`, assuming `C123`, `M3(S)`, and `Nonsingular(H)`:

* `0<gamma(H,theta,rho)<=1`.
* `N_q V_(d_q)(row q)->T(H,theta,rho)`.
* `Normal(S,Z)` for `Z_q=(hat(tau)_q-tau_q)/sqrt(gamma hat(V)_H,q)`.
* For EVERY real `alpha` with `0<alpha<1`, the actual probability of the literal event `|hat(tau)_q-tau_q|<=z(alpha) sqrt(hat(V)_H,q)` tends to `2Phi(z(alpha)/sqrt(gamma))-1`, and this limit is at least `1-alpha`.

There is no assertion of minimal interval width or optimality. The interval event has no absolute value or positive-part operation on its estimated variance; Mathlib sqrt supplies its totalized value on negative samples.

### SAP.P022.T18

Negation of the following quantified proposition:

For EVERY law `H`, there EXIST `K1,K0:R->N`, positive at every positive argument and nonincreasing on positive arguments, such that for EVERY sequence `S` and EVERY real `theta,rho`, IF `C123(S,H,theta,rho)`, THEN both uniform population CDF limits AND BOTH sampled-CDF scaled tail bounds of `Lemma2` hold using those same functions.

Here `K1,K0` are chosen after `H` but BEFORE `S,theta,rho`. There is no `Left` hypothesis. The conclusion is that this uniform assertion is false; it does not merely negate a choice of functions made after the sequence.
