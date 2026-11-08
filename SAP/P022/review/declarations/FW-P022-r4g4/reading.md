# Blind statement reading

This file was saved before opening `claims.json` or `record.json`. The sources read were the three Challenge docstrings and statements, every named entry in `closure.json`, and the source definitions those entries expand. Generated closure entries (constructors, projections, decidable equality, matchers, numeral typeclass proofs and index-bound proofs) were also printed in `scratch/BlindPrint.lean`; the output is `scratch/BlindPrint.out`. They supply the displayed constructors, numeric constants and valid indices, not additional statistical assumptions.

## SAP.P022.T1

**Objects, definitions, and quantifiers.** This is a closed proposition, a conjunction about two fixed witnesses, rather than a universally quantified implication about arbitrary populations.

A design consists of natural numbers `(N,m,k)` with `N>=4`, `m>=2`, `k>=2`, and `m+k<=N`. Its assignment space is all permutations of `{0,...,N-1}`, with the uniform distribution. Expectation is the finite sum over the `N!` permutations divided by `N!`; probability is the expectation of the event's 0/1 indicator. For a vector `v` on `Fin s`, its finite mean is `sum_i v_i/s`. The observed treatment vector is `(y1[pi(i)])_{i<m}` and the observed control vector is `(y0[pi(m+j)])_{j<k}`. Thus this is sampling without replacement with disjoint arms.

An experiment sequence consists of one design for every natural `q`, with population size exactly `q+4`, and two fixed functions `y1,y0 : N -> R`. Row `q` uses their first `q+4` values. It is a nested fixed-outcome population, not a triangular array of independently changeable values. A joint law is a Borel probability measure on `R^2`. Write `G_t(x)=H{p:p_t<=x}` and `G_t^-(x)=H{p:p_t<x}`, with `t=true` selecting the first coordinate and `t=false` the second. The population CDF is `G_{q,t}(x)=#{i<N_q:y_t(i)<=x}/N_q`; its left CDF uses `<`. The sampled CDF is the corresponding empirical CDF of the treatment arm when `t=true` and control arm otherwise. Write `D(A,B)=sup_{x in R}|A(x)-B(x)|` and `L_S(E)=limsup_{q->infinity} ofReal(N_q P_q(E_q))` in the complete ordered set `[0,infinity]`.

The predicate called conditions 1–3 says, in this order: `0<theta<=1`, `0<rho<1`; `m_q/N_q -> theta*rho`; `(m_q+k_q)/N_q -> theta`; for EVERY bounded continuous `f:R^2->R`, the mean of `f(y1(i),y0(i))` over row `q` converges to its integral under `H`; and for EVERY Boolean `t` and real `x` at which `G_t` is not continuous, `G_{q,t}(x)->G_t(x)`. It does not require convergence of the LEFT CDF at atoms. Uniform square integrability says, for each Boolean `t`, that

`sup_q [N_q^{-1} sum_{i<N_q} y_t(i)^2 1_{beta<=y_t(i)^2}] -> 0` as real `beta->+infinity`, and that the set being supremized is bounded above for every real `beta`.

The predicate called Lemma 2 conclusions says: (i) for all `t`, `D(G_t,G_{q,t})->0`; and (ii) there exist functions `K1,K0:R->N`, chosen after `S,H,theta,rho`, such that for every positive `eta` both values are positive; for `0<a<=b` both values at `b` are no larger than at `a`; and for every positive `eta` the two scaled sampled-CDF tails are at most

`(1-theta*rho) K1(eta)/(theta*rho*eta^2)` and
`(1-theta*(1-rho)) K0(eta)/(theta*(1-rho)*eta^2)`.

The reciprocal witness has `N_q=q+4`, `m_q=floor((q+4)/2)`, `k_q=N_q-m_q`, and `y1(i)=y0(i)=-1/(i+1)`. Its limit law is the point mass at `(0,0)`. The statement asserts all of the following:

- Conditions 1–3 hold with `theta=1,rho=1/2`.
- For EVERY `q,t`, the population CDF distance from the limit is exactly 1; for EVERY `q,t,pi`, the sampled CDF distance is exactly 1.
- For EVERY `t`, the scaled tail at tolerance `1/2` is `infinity`, and the Lemma 2 conjunction is false.
- For EVERY unit `i`, both absolute outcomes are at most 1; uniform square integrability holds.
- For EVERY `q,t`, at zero both the population CDF and its left CDF are 1, whereas the limiting CDF is 1 and limiting left CDF is 0.
- At `x_q=-1/(2(q+4))`, for EVERY `q,t`, the population and EVERY sampled CDF equal 1 and the limiting CDF equals 0.
- For EVERY `t,q`, the sampled-CDF tail at `1/2` has probability exactly 1 and its scaled probability is exactly `N_q`.
- For EVERY natural `P`, map `s:Fin(P+1)->EReal`, and real `eta`, if `0<eta<=2`, `s` is strictly increasing, its first value is negative infinity and last is positive infinity, and for EVERY `i:Fin P`, `G^-(s_{i+1}) < G(s_i)+eta/2`, then SOME `j:Fin(P+1)` has `s_j=0`, and for EVERY `q,t` the population left-CDF discrepancy at zero is 1. Here the limiting extended CDF is `1_{0<=x}` and the extended left CDF is `1_{0<x}`.

The four-corner base witness uses the same designs, `y1(i)=0` if `i mod 4<2` and 1 otherwise, and `y0(i)=0` if `i mod 2=0` and 1 otherwise. The perturbed witness subtracts `1/(i+3)` from BOTH coordinates. Its limit law is the sum of four Dirac masses of weight `1/4` at `(0,0),(0,1),(1,0),(1,1)`. The remaining conjunction says:

- For EVERY `t,x`, the limiting marginal CDF is 0 for `x<0`, `1/2` for `0<=x<1`, and 1 for `1<=x`.
- Both limiting means are `1/2`, both limiting variances are `1/4`, covariance is zero. Mean is the coordinate integral, variance the integral of its squared centered value, and covariance the integral of the product of centered coordinates. For EVERY real `a,b,c` with `a!=0` or `b!=0`, the measure is NOT almost surely supported on the line `a p1+b p2=c`.
- The perturbed sequence satisfies conditions 1–3 at `theta=1,rho=1/2`. Both absolute outcomes are strictly less than 1 and are uniformly square integrable. Its CDFs at zero converge to `1/2`; its CDFs at one equal 1 for every row; its CDFs converge to the limiting CDF at every discontinuity.
- For EVERY `q,t`, `x_q=1-1/(2(q+6))` lies strictly between zero and one, the population CDF there is 1, and limiting CDF is `1/2`. The population uniform CDF distance is at least `1/2`. For EVERY assignment the sampled CDF there is 1 and its distance is at least `1/2`.
- For EVERY `t,q`, the sampled-CDF tail at tolerance `1/4` has probability 1 and scaled probability `N_q`. For EVERY `t`, its scaled limsup is infinity. The Lemma 2 conjunction is false.
- For EVERY natural `K`, the displayed treatment/control bound coefficient specializes to `4K` at tolerance `1/2`, and `16K` at tolerance `1/4` (with the fixed parameters above).

**Junk-value audit.** All finite vector means here have sizes at least 2 or 4; permutation spaces are nonempty. No empty average is used. The reciprocal denominators `i+1`, `i+3`, `2(q+4)`, `2(q+6)` are positive. Natural division by 2 genuinely gives the intended floor, and the natural subtraction defining `k_q` is not truncated because the subtrahend is at most `N_q`. Natural-to-real casts are exact. Probability measures have mass at most 1, so ENNReal `toReal` never encounters infinity in a CDF. Both arguments to every CDF distance take values in `[0,1]`, so its supremum is of a nonempty bounded set. The extra explicit boundedness clauses prevent unbounded-real-supremum artifacts in uniform square integrability. Infinite scaled tails are represented in ENNReal, not by a real limsup junk value; `ofReal` only sees nonnegative scaled probabilities. The law integrals are under finite-support probability measures and finite; bounded continuous test functions are integrable. Extended-real infinities are intentional partition endpoints, with no undefined arithmetic on them. `P=0` cannot satisfy the incompatible first/last endpoint requirements; this is only a conditional mesh assertion, not the witness's existence. No logarithm, square root, real power, real infimum, order-statistic default, or partial function occurs in this target's mathematical content.

**Docstring reading.** It calls this a refutation of the printed Lemma 2 under conditions 1–4, including a bounded nonsingular limiting-law witness. Whether those are the paper's actual conditions is reserved for the claim stage.

## SAP.P022.T6

**Objects and elementary definitions.** Again this is a closed conjunction, whose components have different universal quantifiers. A design is `(N,m,k)` in natural numbers with `N>=4`, `m,k>=2`, `m+k<=N`; a random assignment is a uniformly chosen permutation of `Fin N`, treatment observes the first `m` permuted units, and control observes the next `k`. Probability is the finite average of an indicator. Write `M(v)=sum_i v_i/s` for a vector of length `s`, `V(v)=M((v-M(v))^2)`, and `S2(v)=sum_i(v_i-M(v))^2/(s-1)`. The marginal variance estimate from a vector of length `s` is `(N-1)S2(v)/N`.

The quantile `Q_v(u)` sorts the vector nondecreasingly, takes natural rank `ceil(su)`, subtracts 1 in NATURAL arithmetic, and uses list element at that zero-based index or the default real value 0 when out of bounds. Write

`c_B(v,w)=integral_0^1 Q_v(u) Q_w(u) du - M(v)M(w)` for `B=H`,
and replace `Q_w(u)` by `Q_w(1-u)` for `B=L`.

For real `v1,v0,c`, put

`F(N,m,k;v1,v0,c)=[(N-m)v1/m+(N-k)v0/k+2c]/(N-1)`.

The population endpoint is `B_B=F(N,m,k;V(y1),V(y0),c_B(y1,y0))`; its estimate is `hat B_B=F(N,m,k;(N-1)S2(a)/N,(N-1)S2(b)/N,c_B(a,b))`, where `a,b` are the observed vectors. All integrals here are Mathlib oriented interval Lebesgue/Bochner integrals. Empirical CDFs are proportions `<=x`; their uniform distance is the real supremum over all real `x` of the absolute difference.

Define `U_H(G,F)(x,y)=min(G(x),F(y))` and `U_L(G,F)(x,y)=max(0,G(x)+F(y)-1)`. For nonnegative bound `C`, define

`I_B = [2N/(N-1)] integral_{-C}^C integral_{-C}^C [U_B(Ghat,Fhat)-U_B(G,F)] dy dx`.

Put `beta1=N(m-1)/(m(N-1))`, `beta0=N(k-1)/(k(N-1))`, and seven terms (zero-based):

`T0=(N-m)/(m-1) [M(a^2)-beta1 M(y1^2)]`,
`T1=(N-m)/(m-1) [M(a)^2-beta1 M(y1)^2]`,
`T2=(N-k)/(k-1) [M(b^2)-beta0 M(y0^2)]`,
`T3=(N-k)/(k-1) [M(b)^2-beta0 M(y0)^2]`,
`T4=[2N/(N-1)] C [M(a)-M(y1)+M(b)-M(y0)]`,
`T5=[2N/(N-1)] [M(a)M(b)-M(y1)M(y0)]`,
`T6=I_H`.

Their signed total is `T0-T1+T2-T3+T4-T5+T6`. Lower terms replace only `T6` with `I_L`. Given `nu:Fin 8->R`, the upper allocation is

`A(nu,e1)=(nu0,nu1,nu2,nu3,nu4+nu5,nu6+nu7,e1/2)`.

The lower allocation replaces its last entry with `e2+e3`.

**Finite conjunctions and exact quantifiers.** For EVERY design, population pair, and real `C>=0`, if all outcomes have absolute value at most `C`, then:

- For EVERY assignment, `N(hat B_H-B_H)` is the signed seven-term total.
- For EVERY `a:Fin 7->R` and real `epsilon`, if EVERY `a_j>0` and `sum a_j<=epsilon`, the event `epsilon<=N|hat B_H-B_H|` implies that SOME `j` has `a_j<=|T_j|`; its probability is at most the sum of those seven term-tail probabilities.
- For EVERY assignment, `|I_H| <= [8NC^2/(N-1)] max(D(Ghat,G),D(Fhat,F))`.
- IF `C>0`, then for EVERY real `x>0` and assignment, `x<=|I_H|` implies that at least one CDF distance is at least `(N-1)x/(8NC^2)`.

For EVERY `nu,e1` without positivity assumptions, `sum nu=e1/2` implies `sum A=e1`; and `sum nu=e1` implies `nu0+nu1+nu2+nu3+(nu4+nu5)+(nu6+nu7)+(1-e1)=1`.

The lower finite facts have the same universal population/bound hypotheses. They assert the exact decomposition `N(hat B_L-B_L)` with lower terms; event inclusion and the union bound for EVERY positive seven-vector with sum at most the event tolerance; `|I_L| <= [8NC^2/(N-1)] [D(Ghat,G)+D(Fhat,F)]`; and, IF `C>0`, for EVERY `e2,e3>0`, the event `e2+e3<=|I_L|` implies `D(Ghat,G)>=(N-1)e2/(8NC^2)` OR `D(Fhat,F)>=(N-1)e3/(8NC^2)`.

For EVERY real eight-vector and reals `e1,e2,e3`, `sum nu=e1` implies the lower allocation sums to `e1+e2+e3`. For EVERY design, outcomes and assignment, BOTH last integrals are zero when `C=0`, with no bounded-outcome hypothesis needed for this zero-interval identity.

**Asymptotic definitions.** A sequence consists of nested fixed real outcome functions on natural units and designs with `N_q=q+4`. Its conditions 1–3 are exactly: `0<theta<=1`, `0<rho<1`, `m/N->theta*rho`, `(m+k)/N->theta`, weak joint-law convergence against EVERY bounded continuous test function, and population CDF convergence at EVERY discontinuity of each limiting marginal CDF. A law is a Borel probability on `R^2`; its marginal CDF is its measure of a coordinate half-space. Write `L(E)=limsup_q ofReal(N_q P_q(E_q))` in ENNReal. Let `Z_q=N_q(hat B_H-B_H)`.

The additional predicate called Lemma 2 conclusions is an ASSUMPTION in these asymptotic implications. It asserts population uniform CDF convergence AND existence of positive-on-positive, nonincreasing-on-positive integer functions `K1,K0` with both scaled limiting-law sampled-CDF tail bounds `(1-p_t)K_t(eta)/(p_t eta^2)`, where `p_true=theta*rho` and `p_false=theta*(1-rho)`.

Define the fixed universal integer function `J(eta)=2 ceil_N(4/min(eta,1))`, the marginal rate `R_t(eta)=(1-p_t)J(eta)/(p_t eta^2)`, and `Rlast(theta,rho,C,e1,xi)=R_true(e1/(16C^2)-xi)+R_false(e1/(16C^2)-xi)`.

The eight positive rate coefficients, in order, are

`c0=(1-theta*rho)^3/(theta^3 rho^3)`, `c1=4c0`,
`c2=(1-theta(1-rho))^3/(theta^3(1-rho)^3)`, `c3=4c2`,
`c4=c6=4(1-theta*rho)/(theta*rho)`,
`c5=c7=4(1-theta(1-rho))/(theta*(1-rho))`.

Set `S(nu)=sum_{i<8} c_i/nu_i^2`. The six grouped coefficients are the first four summands separately, then the sum for indices 4,5, then the sum for 6,7. The predicate called earlier-six rates asserts for EVERY `j:Fin 6` that `L(A(nu,0)_j<=|T_j|)<=ofReal(C^4 times grouped_coefficient_j)`. The last allocation entry is unused by this predicate. It is an additional ASSUMPTION, not a theorem proving (17)–(22).

**Asymptotic conjunctions and quantifier order.**

1. For EVERY positive `eta`, `J(eta)>0`; for EVERY `0<a<=b`, `J(b)<=J(a)`. For EVERY `S,H,theta,rho`, conditions 1–3 PLUS Lemma 2 conclusions imply, for EVERY `t,eta>0`, `L(eta<=D(G_t,Ghat_t))<=ofReal(R_t(eta))`. The single function `J` is defined before and independently of all sequences and parameters.
2. For EVERY `S,H,theta,rho,C`, assume conditions 1–3, `C>0`, ALL fixed outcomes bounded by `C`, and Lemma 2 conclusions. For EVERY `e1>0` and `0<xi<e1/(16C^2)`, `L(e1/2<=|I_H|)<=ofReal(Rlast)`.
3. The preserved substatement also quantifies over these same inputs and THEN EXISTS `K1,K0:R->N` and `kappa:R`. These functions satisfy the two limiting-law tail inequalities for EVERY positive tolerance (this substatement does not separately require their positivity or monotonicity). At `eta=e1/(16C^2)-xi`, `C^4 kappa` equals the sum of their two displayed rate expressions; `L(e1/2<=|I_H|)<=ofReal(C^4 kappa)`. For EVERY positive `nu` summing to `e1/2`, IF its six grouped term inequalities hold, THEN for EVERY `epsilon>e1`, `L(epsilon<=|Z|)<=L(e1<=|Z|)<=ofReal(C^4(S(nu)+kappa))`. The existential witnesses precede this universal `nu`.
4. A further uniform formulation gives, for EVERY same set of sequence hypotheses and EVERY `e1>0,0<xi<e1/(16C^2),nu>0` with sum `e1/2`, IF earlier-six rates hold, THEN for EVERY `epsilon>e1`, `L(epsilon<=|Z|)<=L(e1<=|Z|)<=ofReal(C^4 S(nu)+Rlast)`.
5. For EVERY admissible `theta,rho` and EVERY `s>0`, put `r_i=c_i^(1/3)` using REAL exponentiation, `r=sum_i r_i`, and `nu_i^*=s r_i/r`. ALL `c_i` and `nu_i^*` are positive; `sum nu^*=s`; `S(nu^*)=r^3/s^2`; and for EVERY positive `nu` with sum `s`, `r^3/s^2<=S(nu)`.
6. Define `Ropt(theta,rho,C,e1)=4r^3/e1^2+Rlast(theta,rho,C,e1,e1/(32C^2))/C^4`. For EVERY admissible bounded sequence with Lemma 2 conclusions and EVERY `e1>0`, IF earlier-six rates hold for EVERY positive `nu` with sum `e1/2`, THEN `Ropt>0`, and for EVERY `epsilon>e1`, `L(epsilon<=|Z|)<=ofReal(C^4 Ropt)`. Thus this optimization conclusion has a universally quantified family of rate hypotheses. It optimizes the eight-vector allocation with the remaining tolerances fixed as displayed.
7. For EVERY admissible bounded sequence with `C>0` and Lemma 2 conclusions, and EVERY `e1,e2,e3>0`, `0<xi2<e2/(8C^2)`, `0<xi3<e3/(8C^2)`, and positive `nu` of sum `e1`, the lower last-term tail at `e2+e3` is at most `ofReal(R_true(e2/(8C^2)-xi2)+R_false(e3/(8C^2)-xi3))`. IF earlier-six rates also hold, the tail of `N|hat B_L-B_L|` at `e1+e2+e3` is at most the same sum plus `C^4 S(nu)`, all embedded using `ofReal`.

**Junk-value audit.** The design inequalities make all finite sample/population means and sample-variance denominators legitimate: `N,m,k,m-1,k-1,N-1` are positive, and all finite assignment spaces are inhabited. Real subtraction in `F` and beta factors is real subtraction, not truncated natural subtraction. The quantile rank subtraction IS natural subtraction: at `u=0` it returns the minimum order statistic; `u=1` returns the maximum, and on `(0,1)` ranks are in `[1,s]`. The reflected argument also lies in `[0,1]`. Out-of-range list defaults and natural ceilings of negative numbers therefore do not affect the integrals. The step-function quantile and CDF integrands are bounded, measurable and integrable on the finite intervals; no undefined Bochner integral is used. The negative orientation convention for interval integrals is not active under `C>=0`; `C=0` genuinely gives a zero interval. The reciprocal CDF thresholds and all asymptotic divisions by `C` are guarded by `C>0`. Admissible allocation parameters ensure `0<p_t<1`; tolerances, `nu_i`, `s`, and the cubic-root sum in every analytical rate/optimization assertion are positive. Therefore REAL `rpow` is evaluated only at positive bases and is the usual positive cube root, despite its arbitrary convention for negative bases. The purely algebraic budget equalities need no positivity and use no risky divisions. The explicit `J` is total at nonpositive inputs, but only positive inputs appear in tail assertions; there `min(eta,1)>0`, its ceiling is a genuine positive natural number. All CDF-distance suprema are nonempty bounded real suprema; law-CDF `toReal` is finite. The scaled limsups live in ENNReal and remain meaningful when unbounded. `ofReal` cannot silently erase a negative rate under the stated sign hypotheses. No square root, independent `Real.log`, real `sInf`, empty statistical index type, or partial function occurs.

**Docstring reading.** It expressly presents corrected budgets and centering, finite statements for both endpoints, limits conditional on Lemma 2 (and, for final conclusions, earlier six rates), and optimization independent of the sequence. It does not purport to prove the earlier six rates here.

## SAP.P022.T7

**Objects and definitions.** This is a closed proposition about a fixed nested population. Its design at row `q` has natural `N=q+4`, `m=floor(N/2)`, `k=N-m`, with `N>=4,m,k>=2,m+k=N`. Assignment is a uniform permutation of `Fin N`. Observations are `a_i=y1(pi(i))` for `i<m`, and `b_j=y0(pi(m+j))` for `j<k`. Expectation is the average over all `N!` assignments and probability is the indicator average. Population mean and variance are `sum v/N` and the mean of squared centered values; covariance is the mean product of centered values. Difference in observed means is `hat tau=M(a)-M(b)`; ACTUAL variance is the assignment average of `(hat tau-Ehat tau)^2`.

The two fixed potential-outcome functions are `y1(i)=1_{i mod 4>=2}` and `y0(i)=1_{i mod 2!=0}`. Thus the pairs cycle through the four corners `(0,0),(0,1),(1,0),(1,1)`. The joint law is the Borel probability measure giving each corner mass `1/4`.

For a vector of length `s`, quantiles use the sorted vector's natural rank `ceil(su)` with zero-based index `rank-1` (natural subtraction) and default value 0 for an out-of-range index. Its sharp upper covariance with another vector is `integral_0^1 Q_a(u)Q_b(u) du-M(a)M(b)`; the lower covariance reflects the second argument to `1-u`. The sharp population upper variance endpoint is

`B_H=[(N-m)V(y1)/m+(N-k)V(y0)/k+2c_H(y1,y0)]/(N-1)`.

The upper estimate replaces marginal population variances by `(N-1)/N` times unbiased sample variances `sum(a-M(a))^2/(m-1)` and `sum(b-M(b))^2/(k-1)`, and population sharp covariance by sample sharp covariance. Let `Z_q=N_q(hat B_H-B_H)`, `W_q=N_q|hat B_H-Vactual|`. The last integral is

`I_H=[2N/(N-1)] integral_{-1}^1 integral_{-1}^1 [min(Ghat(x),Fhat(y))-min(G(x),F(y))] dy dx`,

where the four CDFs count outcomes `<=` the argument, divided by their vector sizes. A limiting-law CDF is the corresponding coordinate-halfspace mass, and its left version counts `<`. Scaled tail limsup is `limsup_q ofReal(N_q P_q(E_q))` in ENNReal. Design convergence of real random variables `X_q` to `a` means: for EVERY real `eta>0`, `P_q(eta<=|X_q-a|)->0`.

**Conclusions and quantifiers.**

- Conditions 1–3 hold with `theta=1,rho=1/2`: both allocation limits, weak convergence against EVERY bounded continuous test function on `R^2`, and population CDF convergence at EVERY discontinuity of each limiting marginal. The limiting marginal CDF is 0 on `x<0`, `1/2` on `0<=x<1`, and 1 on `x>=1`, for EVERY Boolean marginal and real `x`.
- Left population CDFs ALSO converge to limiting left CDFs at EVERY discontinuity. For EVERY unit both outcomes have absolute value at most 1.
- For EVERY Boolean marginal, the population CDF at zero converges to `1/2`. For EVERY row it is 1 at one, its left CDF is zero at zero, and its left CDF at one equals its CDF at zero; the left CDF at one converges to `1/2`.
- The real inequalities `0<1` and identity `1+1+1=3` hold.
- For EVERY row the event `1-1<=|I_H|` has probability exactly 1, and its scaled probability equals `N_q`. Its scaled limsup is infinity; for EVERY real `R`, that limsup is NOT at most `ofReal(R)`.
- For EVERY natural `r`, consider row `q=4r`, whose size is `4(r+1)` (the docstring's `N=4r` describes the same divisible-by-four subsequence after shifting the integer parameter). Both arm sizes equal `2(r+1)`; both population means equal `1/2`, both variances equal `1/4`, mean product equals `1/4`, actual covariance is zero, the quantile-product integral equals `1/2`, and the sharp upper covariance equals `1/4`.
- On EVERY such row actual variance equals `1/[2(N-1)]` and the sharp upper endpoint equals `1/(N-1)`. For EVERY assignment, `N(hat B_H-Vactual)=Z+N/[2(N-1)]`.
- For EVERY natural `r` and real `delta>0`, IF `64/delta<=N_{4r}`, THEN `P_{4r}(delta<=|Z_{4r}|)<=51200/(N_{4r} delta^2)`.
- On the FULL sequence, `Z_q` converges in design probability to zero.
- On row subsequence `q=4r`, `W_{4r}` converges in design probability to `1/2`. For EVERY real `0<epsilon<1/2`, `P_{4r}(epsilon<=W_{4r})->1`, `N_{4r} P_{4r}(epsilon<=W_{4r})->+infinity` as a real sequence, and for EVERY real `R` this scaled probability is eventually greater than `R`. For EVERY such `epsilon`, the corresponding ENNReal limsup is infinity.

No independence of repeated assignments is used or postulated: every probability here is for one uniform design assignment in a row. The theorem provides a zero-threshold last-integral event and a distinct positive-threshold wrongly centered variance-estimator discrepancy.

**Junk-value audit.** All outcomes and assignment spaces are finite and nonempty. Sample sizes are at least 2 and denominators `m,k,m-1,k-1,N-1` are positive. The design uses floor division and untruncated natural subtraction as intended. Outcomes at natural indices use total modulo functions. The order-statistic convention at quantile argument zero returns the minimum; interior ranks and the other endpoint are valid. No out-of-range default affects the quantile integral; the finite step functions and CDF functions are integrable and measurable. Interval bounds are `[-1,1]`, with ordinary orientation. Limit-law probabilities are finite so `toReal(infinity)` is absent. All real CDF suprema (when introduced through conditions) are of nonempty bounded sets. The tail bound's `delta` is explicitly positive. ENNReal `limsup` records genuine infinity, and `ofReal` is applied to nonnegative scaled probabilities; the final comparison against every real `R` intentionally also allows negative `R` (whose image is zero). The threshold `1-1=0` is ordinary real subtraction; the probability-one event is an intentional zero threshold, not a junk-value consequence. No real power, logarithm, square root, empty extrema, nonintegrable mean, or undefined partial operation is used.

**Docstring reading.** It calls the split `(1,1,1)` admissible for the printed last-term bound and treats the estimator's gap from ACTUAL variance as a refutation of the printed concluding bound. Whether those really are the printed assertions and admissible tolerances is reserved for the claim stage.
