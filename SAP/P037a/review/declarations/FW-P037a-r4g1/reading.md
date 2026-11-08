# Blind reading

This file was written before opening `claims.json` or `record.json`. The reviewed statements are the declarations named in `closure.json`, including every listed dependency. Source declarations were read in `Defs/Part1` through `Defs/Part6`, `Defs/WholeW1`, `Defs/WholeW2`, and `Challenge/Part1` as applicable. All 114 distinct generated `_proof_` dependencies were also printed in `scratch/Closure.lean` (output `scratch/Closure.log`). These helpers supply numeral instances, nonempty finite-index instances, an ENNReal scalar-tower instance, measure outer-measure instances, or the bound on a predecessor index; they add no statistical assumptions. `Design`, its constructor, and its weight projection were printed as well.

Throughout, a `Fin n` index is an integer in `{0,...,n-1}`, all displayed fractions are real fractions unless stated otherwise, matrices and vectors have real entries, and sums/products over finite sets are ordinary finite sums/products. A Lean proposition introduced with `def ... : Prop` below is an abbreviation for its displayed conjunction or quantified assertion, not a hypothesis that the theorem assumes.

## SAP.P037a.T1

Location: `SAP/P037a/Challenge/Part1.lean:8` (theorem at line 18). No external parameters or hypotheses: this is a conjunction of assertions about specified data, followed by universally quantified extensions.

### The fixed design and responses, fully unfolded

There are four schools `i=0,1,2,3`. Write `q=(1/10,1/10,3/10,3/10)` and `r=(1,1,3,3)`. A treatment index `a=0,...,5` selects respectively the pairs `(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)`. Let `D_a(i)` equal one for the selected pair and zero otherwise.

For `r` a natural number and `c=0,...,3`, define

`h_r(c) = binom(r,c) binom(10-r,5-c) / binom(10,5)`.

Here the subtraction inside the binomial arguments is natural-number subtraction. For `k=0,...,12`, define

`m_r(k) = sum_{(c_0,...,c_3) in {0,...,3}^4, sum c_s=k} product_s h_r(c_s)`.

The sample space is the Cartesian product `{0,...,5} x {0,...,12} x {0,...,12}`. For `w=(a,k,l)` with selected pair `(u,v)`, its weight is `p(w)=(1/6)m_{r_u}(k)m_{r_v}(l)`. Define `Z_w(u)=k/20`, `Z_w(v)=l/20`, and `Z_w(i)=0` for the other two schools. Expectation `E F` means exactly `sum_w p(w)F(w)`.

Potential outcomes have domain `school x Bool x real composition`: `Y_i(false,c)=3/10`, `Y_i(true,c)=3/10-q_i`, independently of `c`. The observed response is `y_w(i)=3/10-D_a(i)q_i`. The three regressors are `x_w=(D_a,q,Z_w)`, in that order. For four-vectors define `S(x,y)=sum_i x_i y_i-(sum_i x_i)(sum_i y_i)/4`. The population matrix and response vector are `G_kl=E S(x_k,x_l)` and `v_k=E S(x_k,y)`.

### Conclusions and quantifiers

1. Every `p(w)>=0` and `sum_w p(w)=1`. For every school `i`, `E D_i=1/2`, `2 E Z_i=q_i`, and `2 E (Z_i-D_i q_i)^2=q_i(1-q_i)/36`. For every `i` and count `k<=4`, `m_{r_i}(k)>0`.
2. For every `i,c,c'`, `Y_i(true,c)-Y_i(true,c')=0`. For every real `c`, the average of `Y_i(true,c)-Y_i(false,c)` over four schools is `-1/5`.
3. For every three-vector `theta`, `G theta=v` if and only if `theta=(-3/31,-15/62,-16/31)`, and `-16/31 != 0`.
4. Exactly `G=[[1,0,1/5],[0,1/25,1/50],[1/5,1/50,151/2400]]`, `v=(-1/5,-1/50,-17/300)`, and `det G=31/60000 !=0`.
5. For every five real numbers `(a,tau,b1,b2,g)`, define potential responses
   `M_i(false,c)=a+g q_i` and `M_i(true,c)=a+g q_i+tau+b1(c-q_i)+b2(q_i-1/5)`.
   For every `i,c,c'`, their treated-composition difference is `b1(c-c')`. For every `c`, their mean treatment contrast is `tau+b1(c-1/5)`.
6. For every such five parameters, the observed response
   `m_w(i)=a+tau D_i+b1(Z_i-D_i q_i)+b2 D_i(q_i-1/5)+g q_i`
   has a unique population solution `theta` to `G theta=(E S(x_k,m))_k`. Its third coordinate is `(15 b1+16 b2)/31`; that coordinate equals `b1` if and only if `b1=b2`. Formally the order is `forall parameters, exists theta, equation and (forall theta', equation -> theta'=theta) and slope formula and equivalence`.
7. For all assignments and schools, parameters `(3/10,-1/5,0,-1,0)` recover `y`; for all schools, treatment Booleans, and real compositions, they recover `Y`.
8. For every `k in {0,...,12}`, `m_1(k)>0` iff `k<=4`, while `m_3(k)>0` for every such `k`. Exactly 454 assignments have positive weight.
9. For every `i`, writing `p_i=E D_i`, `p_i>0`, `E Z_i/p_i=q_i`, and `E (Z_i-D_i q_i)^2/p_i=q_i(1-q_i)/36`. The latter equals `1/400` for schools 0 and 1 and `7/1200` for schools 2 and 3. Since `Z_i` is zero off treatment, these are treated-school moments, not moments conditional on the entire assignment vector.
10. For each natural block count `B` and each vector of block assignments `w:{0,...,B-1}->sample space`, let
    `L_w(alpha,theta)=sum_b sum_i (y_{w_b}(i)-alpha_b-sum_{k=0}^2 x_{w_b,k}(i)theta_k)^2`.
    For every `B,w`, there exist real block intercepts `alpha` and three slopes `theta` such that `forall alpha',theta', L_w(alpha,theta)<=L_w(alpha',theta')`.
11. Give `w` the product weight `product_b p(w_b)`. Event probability is the finite sum of this weight times its zero-one indicator. The probability that `det(sum_b (S(x_{w_b,k},x_{w_b,l}))_kl)=0` tends to zero as `B` tends to infinity.
12. For every family `alpha_B(w),theta_B(w)` indexed by **all** natural `B` and **all** block samples, if each pair minimizes `L_w`, then for every real `eps>0`, the probability of `eps<|theta_B(w)_2-(-16/31)|` tends to zero. Quantifier order: choose the entire pair of minimizing families first; then choose `eps`; then take the limit. This is convergence in probability under independent block repetition and covers arbitrary minimizing selections at singular samples.

### Totalization and junk-value audit

The design uses natural casts and binomial coefficients. Binomial coefficients outside their combinatorial range are zero. `10-r` and `5-c` are truncated natural subtractions; here `r` is only 1 or 3 and `c<=3`, so no negative argument is being silently truncated. The divisor `binom(10,5)=252` is nonzero. Counts impossible for a school are explicitly retained in a padded sample space but have zero mass, so arbitrary response/regressor values there do not change any expectation. The low-low, four mixed, and high-high treatment pairs contribute `25+4*65+169=454` positive states.

All other divisors are nonzero integer constants except the conditional treatment probability, explicitly asserted positive (and equal to 1/2). All expectations are finite sums of finite real values, so there is no nonintegrable-mean convention. The population and pooled regression statements use equations and actual minimization rather than a singular matrix inverse. The pooled singularity event is an explicit event, not an inverse convention. For `B=0`, sums are empty, the product sample space has one point, every parameter minimizes the zero loss, and the pooled matrix is singular. This affects no limit at infinity and does not make the quantified assertion vacuous. There are no logarithms, square roots, real powers, extended-real casts, infima/suprema, or partial functions in this closure.

The docstring describes this same finite design, conditional moments, matrices, general response schedule, minimizing-estimator probability limit, minimizer existence, and disappearing singularity probability. It states that usual measure-theoretic conditions are assumed.

## SAP.P037a.T2

Location: `SAP/P037a/Challenge/Part1.lean:20` (theorem at line 23). Again no external hypotheses: it is a conjunction of thirteen facts, several universally quantified with their own hypotheses.

### Finite probability and block-regression notions

A finite design consists of a finite type `Omega`, a real weight function `d(w)>=0`, and `sum_w d(w)=1`. Its expectation is the finite sum `E_d F=sum_w d(w)F(w)`. The constructor carries exactly these conditions. For natural `B`, rows are pairs `(b,i)` with `b in {0,...,B-1}` and `i in {0,1,2,3}`. Define

`S_B(x,y)=sum_b sum_i sum_j (if i=j then 3/4 else -1/4) x_(b,i)y_(b,j)`.

This equals the sum of within-block centered cross products. Given finite coefficient indices `K`, columns `X_k(w)` and response `Y(w)`, population normal equations for `theta:K->R` mean

`forall k, E_d S_B(X_k,Y)=sum_l theta_l E_d S_B(X_k,X_l)`.

Extended normal equations for columns `W_k`, one additional column `R`, coefficients `(delta,beta)` and response `Y` mean these equations for each `W_k` with the extra term `beta E_d S_B(W_k,R)`, and also

`E_d S_B(R,Y)=sum_l delta_l E_d S_B(R,W_l)+beta E_d S_B(R,R)`.

For a random Boolean assignment vector `D(w)`, the condition called composition randomization is exactly

`forall f:(row->Bool)->R, forall row i, E_d[f(D(w)) R(w,i)]=0`.

All functions on these finite domains are allowed. Thus it expresses zero conditional first moment of `R_i` given the entire vector `D`, including constant `f`; it is not independence, a second-moment assumption, or a restriction to one particular regressor.

The concrete four-school design, `q,D,Z,y,S,E`, is exactly the finite definition given in the T1 section, not an additional premise. Let `R_w(i)=Z_w(i)-D_w(i)q_i`. Original columns are `(D,q,Z)`, centered columns `(D,q,R)`, and expanded columns `(D,q,Z,Dq)`. A concrete composition equation means, for each column `k`, `sum_l theta_l E S(X_k,X_l)=E S(X_k,Y)`.

### Thirteen conclusions and all local hypotheses

1. **Stratified sampling.** For every natural `H`, functions `N,n:Fin H->Nat`, and subsets `A_h` of `Fin(N_h)`, assume `N_h>0` for every stratum, `n_h<=N_h` for every stratum, and `sum_h n_h>0`. Write `K_h=|A_h|`, `T=sum_h n_h`, and `mu=sum_h n_h(K_h/N_h)/T`. The sample space consists of **one size-`n_h` subset of `Fin N_h` per stratum**, and each tuple has mass `1/product_h binom(N_h,n_h)`. Define `C(z)=sum_h |A_h intersect z_h|/T`. Then masses sum to one, `E C=mu`, and
   `E(C-mu)^2 = [sum_h v_h]/T^2`,
   where `v_h=0` if `N_h=1`, otherwise
   `v_h=n_h(K_h/N_h)(1-K_h/N_h)(N_h-n_h)/(N_h-1)`.
   This sample space has no school-treatment variable and these are unconditional product-law moments.
2. **Equal fractions.** For all natural `H`, natural-valued `N,K,n`, and real `f`, if every `N_h!=0`, `sum_h n_h!=0`, and `n_h=f N_h` for all `h` (real equality), then `sum_h n_h(K_h/N_h)/sum_h n_h = sum_h K_h/sum_h N_h`. No constraints `K_h<=N_h` or `n_h<=N_h` appear in this separate algebraic fact.
3. **Unequal example.** For `N=(13,14,14,14)`, `K=(2,1,0,0)`, `n=(7,7,7,7)`, eligible share is `3/55`, composition mean is `41/728`, their difference is `71/40040`, and they are unequal.
4. **Response identification.** For all finite types `Omega,K`, natural `B`, finite design `d`, columns `X_k(w)`, block intercepts `alpha_b`, coefficient vector `theta`, and real responses `err(w,i),Y(w,i)`, assume pointwise `Y=alpha_b+sum_k theta_k X_k+err` and `E_d S_B(X_k,err)=0` for every `k`. Then the population normal equations hold for `theta`. If additionally the linear map `v -> (sum_l v_l E_d S_B(X_k,X_l))_k` is injective, every solution `v` equals `theta`.
5. **Decomposition.** For every six reals `a,t,b,D,C,mu`, `a+D t+b D C=a+D(t+b mu)+b D(C-mu)`; `D` need not be binary for this algebraic identity.
6. **Centered orthogonality.** For all finite `Omega`, natural `B`, finite design `d`, random Boolean vector `D`, and real random row vector `R`, assume the composition randomization condition above. Then for every real row-vector-valued function `V` of the Boolean vector, `E_d S_B(R,V(D))=0`.
7. **Centered identification.** For all finite `Omega,K`, natural `B`, design `d`, random `D,C`, deterministic real row vectors `mu,a,t`, columns `W_k` that are functions of `D`, reals `b,beta`, and real vector `delta`, set `R_i=D_i(C_i-mu_i)` and `Y_i=a_i+D_i t_i+b D_i C_i`. Assume randomization for `R`, the extended population normal equations for `(W(D),R,Y,delta,beta)`, and `E_d S_B(R,R)>0`. Then `beta=b`. These three premises are independent conjuncts of the domain; there is no derivation of randomization from item 1.
8. **Augmentation equivalence.** For all finite `Omega,K` with decidable equality on `K`, natural `B`, design `d`, real random columns `W_k,R,Z,Y`, an index `e in K`, and pointwise relation `Z=R+W_e`, then for every `delta,beta`, extended equations using `Z` and coefficients `(delta,beta)` are equivalent to extended equations using `R` and coefficients `(delta+beta*1_{k=e},beta)`.
9. **Eligible centering.** For every real `D,C,mu,q`, `D(C-q)=D(C-mu)+D(mu-q)`; if `mu=q`, then `D(C-mu)=D(C-q)` and `D mu=D q`.
10. **Concrete regressions.** In the four-school law, `E S(R,R)=1/160`. For **every** candidate coefficient vector, the relevant population equations hold iff it equals the following vector: expanded columns and `y`: `(0,0,0,-1)`; centered columns and `y`: `(-1/5,-1/2,0)`; original columns and `y+Z/5`: `(-3/31,-15/62,-49/155)`; centered columns and `y+Z/5`: `(-4/25,-2/5,1/5)`; expanded columns and `y+Z/5`: `(0,0,1/5,-1)`; original columns and response `3/10-D/5-q/2+Z/5`: `(-1/5,-1/2,1/5)`.
11. **Uncentered orthogonality.** For all finite `Omega`, natural `B`, design `d`, and random `D,R`, randomization implies that for every row-vector-valued `V(D)`, `E_d sum_i V(D)_i R_i=0`.
12. **Slope moment, even without positive variation.** For all finite `Omega,K`, natural `B`, design `d`, random `D,R`, assume randomization. For every row vector `A(D)`, columns `W_k(D)`, reals `b,beta`, and vector `delta`, extended equations for `(W(D),R,A(D)+bR,delta,beta)` imply `beta E_d S_B(R,R)=b E_d S_B(R,R)`. No positivity is required here, so this also states the zero-variation identity without claiming identification in that case.
13. **Augmented slope identification.** For all finite `Omega,K` with decidable equality, natural `B`, design `d`, random `D,C`, deterministic row vectors `mu,a,t`, columns `W_k(D)`, an index `e`, and coefficients `b,beta,delta`, assume `W_e(D)=D mu` pointwise, randomization for `R=D(C-mu)`, the extended equations with extra column `Z=DC` and response `a+Dt+bDC`, and `E_d S_B(R,R)>0`. Then `beta=b`.

### Totalization and junk-value audit

All generic probability quantities are finite weighted sums, with a normalized nonnegative law, so no Bochner default values arise. An empty `Omega` cannot admit a `Design` because its mass sum would be zero. Empty coefficient types and zero blocks are permitted in the purely algebraic facts. They cause legitimate empty sums; the positive-variation hypotheses in items 7 and 13 exclude `B=0`. The augmentation statements have an explicit `e:K`, so that branch cannot have empty `K`.

Real division is totalized by `x/0=0`. In item 1, positive `N_h`, `n_h<=N_h`, and positive total seeds guarantee nonzero individual populations, positive binomial coefficients, positive product cardinality, and a positive total denominator. The `N_h=1` variance branch explicitly returns zero; sampling from a singleton is deterministic, so this is the correct degenerate variance rather than a spurious division by zero. In its other branch `N_h-1` is real subtraction and strictly positive. Item 2 separately requires every population and total seeds nonzero. A nonempty stratum set follows from the latter, so total population is also positive; no total-population division by zero occurs even without an explicit hypothesis for it. The unequal example has positive denominators and feasible population/reference/seed sizes.

The concrete regression pieces inherit the binomial padding, casts, and natural-subtraction audit from T1. No actual coefficient is defined using an inverse; all are solutions of equations. No infinity-to-real conversion, infimum, logarithm, square root, real power, or partial function occurs.

The docstring explicitly declares a restriction: unconditional product seed moments replace treated-school conditional moments, the joint school/seed construction and its conditional-zero-moment consequence are omitted, and randomization remains a premise. The listed retained algebraic and regression facts are present.

## SAP.P037a.T3

Location: `SAP/P037a/Challenge/Part1.lean:25` (theorem at line 35). There are no external hypotheses.

For real estimate `e` and standard error `s`, the table bin predicate is precisely

`e<0 and 11/200<|e|<13/200 and 1/40<s<7/200`.

The Wald statistic is `W(e,s)=|e|/s`. Let `Phi(z)` be Mathlib's CDF of `gaussianReal 0 1`, i.e. the real probability of `(-infinity,z]` under the Gaussian with mean zero and variance one. Define `P(z)=2(1-Phi(z))`. This is the two-sided normal tail for nonnegative `z`; every use as a Wald tail has nonnegative `z`. Define `c*=inf{z in R:39/40<=Phi(z)}` using the real conditional infimum. Define `round_2(x)=integer-round(100x)/100`, with nearest-integer ties toward positive infinity.

The conjunction asserts:

1. For every real `p`, not both `p<1/20` and `1/20<=p`.
2. For every real `c` satisfying `19/10<=c<=2`, both `(-57/1000,7/250)` and `(-57/1000,17/500)` satisfy the bin predicate, their Wald statistics are respectively `57/28` and `57/34`, and `57/34<c<57/28`.
3. For every real `e,s` satisfying the bin predicate, `11/7<W(e,s)<13/5`, together with the arithmetic equality `(6/100)/(3/100)=2`.
4. For every real `z` with `11/7<z<13/5`, there exist positive `a,s` with `11/200<a<13/200`, `1/40<s<7/200`, and `a/s=z`. Choosing estimate `-a` gives a table-bin witness for every interior ratio.
5. For every real `e,s`, `e<0` and the bin predicate imply `round_2(e)=-6/100` and `round_2(s)=3/100`.
6. `P(1.9)>.05`, `P(2)<.05`, `P(1.95996)>.05`, and `P(1.95997)<.05`. All six following absolute errors are **strictly** below `1/200000=.000005`:
   `P(57/28)` versus `.04178`; `P(57/34)` versus `.09365`; `P(2)` versus `.04550`; `P(1.9)` versus `.05743`; `P(11/7)` versus `.11608`; `P(13/5)` versus `.00932`.
7. `Phi(c*)=39/40`; for every real `z`, `Phi(z)=39/40` iff `z=c*`; and simultaneously `1.9<c*<2`, `1.95996<c*<1.95997`, and `11/7<c*<13/5`.
8. `P(W(-.057,.028))<.05` while `P(W(-.057,.034))>.05`. There also exist four reals `e,s,e',s'`, with both estimates negative and both pairs in the table bins, both estimates rounding to `-.06` and both standard errors rounding to `.03`, with the first normal Wald tail below `.05` and the second above `.05`.

The docstring describes incompatible significance descriptions and the normal, rounding, envelope, quantile, and numerical assertions above. No variable representing a printed text or a significance label is present: incompatibility is the elementary disjointness in item 1, applied to the intended descriptions.

### Totalization and junk-value audit

The Wald denominator is explicitly strictly positive in all bin-dependent clauses, and the two concrete errors are positive. Constant denominators are nonzero. Rounding uses the total integer floor/ceiling operations, but strict bins exclude all relevant half-way endpoints; its tie rule has no effect here. Casts from integers and naturals to reals are exact.

Real `sInf` gives a default value if its set is empty or unbounded below. Here the set is nonempty and bounded below: the genuine standard Gaussian CDF tends to one at positive infinity and zero at negative infinity, is continuous and strictly increasing. The theorem additionally certifies attainment and uniqueness and bounds the resulting number between two positive rational numbers. Thus the quantile does not exploit a junk infimum. The Gaussian variance is the positive number one, so its variance-zero Dirac branch is unused. Mathlib's CDF is only guaranteed to have its probability interpretation for probability measures; this Gaussian is a probability measure.

There are no arbitrary integrands, nonintegrable means, truncated subtractions, square roots, logarithms, real powers, empty statistical index sets, limit superior/inferior operations, or partial-function defaults in this closure. The generated helper shared with `compositionConditionalMoments` is just a numeral instance for seven.

## SAP.P037a.T4

Location: `SAP/P037a/Challenge/Part1.lean:37` (theorem at line 48). No external hypotheses. In every general weight-law assertion the natural parameter `k>=0` encodes the school count `n=k+2`, so there are at least two coordinates.

### Laws, events, and regression notions, fully unfolded

A single uniform draw has Lebesgue measure restricted to `(0,1)`. The product of `n` such measures is the law of independent uniforms. A single standard exponential draw is Mathlib's `expMeasure 1` (gamma shape one, rate one); its `n`-fold product is the independent exponential law. Normalize a real vector by `N(w)_i=w_i/sum_j w_j`.

For natural `m`, let `Delta_m={q in R^m: forall i,q_i>0 and sum_i q_i<1}`. Let `A_m(q)=(q_0,...,q_(m-1),1-sum_i q_i)`. The simplex measure is the pushforward under `A_m` of `m!` times `m`-dimensional Lebesgue measure restricted to `Delta_m`. Thus, for `n` weights, its argument is `m=n-1`. The uniform weight law is the pushforward of the product uniform law under `N`. The exponential weight law is defined identically using the product exponential law. The event under comparison is `p_0/(p_0+p_1)<1/4`.

For finite types `I,K`, weights `w:I->R`, matrix `X:I x K->R`, response `y:I->R`, and coefficient vector `b:K->R`, the predicate named WLS means exactly the normal equations

`forall k, sum_i w_i X_ik (y_i-sum_l X_il b_l)=0`.

The weighted Gram matrix is `G_kl=sum_i w_i X_ik X_il`, the weighted response vector is `v_k=sum_i w_i X_ik y_i`, and the defined coefficient is `G^{-1}v` using Mathlib's total matrix inverse. Full column rank is injectivity of the linear map `b -> Xb`.

### Conclusions and local quantifier order

1. For every natural `k`, the uniform-law event probability, converted from ENNReal to real, equals `1/6`; the simplex-law event probability equals `1/4`; the measures differ. Both ENNReal event masses are also explicitly not infinity.
2. For all reals `u,v,T` with `u>0,v>0,T>0`, `(u/T)/(u/T+v/T)=u/(u+v)`, and `u/(u+v)<1/4` iff `u<v/3`.
3. The iterated oriented interval integral `integral_(v=0)^1 integral_(u=0)^(v/3) 1 du dv` equals `1/6`.
4. The Lebesgue integrals on `(0,infinity)` of `exp(-v)` and `exp(-(4/3)v)` are respectively one and `3/4`. Also `1-3/4=1/4`, `1/6!=1/4`, and `1/6-1/4=-1/12`.
5. For all finite `I,K` (decidable equality on `K`), positive `w`, full-column-rank `X`, real `y`, candidate `b`, and real `c>0`, the defined coefficient for `cw` equals that for `w`, and the WLS equations for `cw,b` iff the WLS equations for `w,b`.
6. For every such coefficient type `K`, natural `k`, positive weights on `Fin(k+2)`, full-column-rank matrix `X`, and arbitrary real response `y`, normalizing the weights preserves the defined coefficient.
7. For every natural `k`, the normalized product-exponential measure equals the explicitly defined simplex measure. This simplex measure is a probability measure and almost every vector under it has all coordinates strictly positive and sum one.
8. For every natural `k`, measurable space `Omega:Type`, probability measure `mu`, and two families `U,E:Fin(k+2)->Omega->R`, assume each coordinate is measurable, the coordinates of `U` are jointly independent, the coordinates of `E` are jointly independent, each `U_i` has the uniform law, and each `E_i` has the standard exponential law. No independence between the families `U` and `E` is assumed or needed. Then:
   - almost surely, each family has positive coordinates, positive total, and positive sum of coordinates 0 and 1; its normalized ratio equals its raw ratio, and its raw ratio event is equivalent to `X_0<X_1/3`;
   - the normalized `U` law is the uniform weight law; the normalized `E` law is the simplex measure;
   - their event probabilities are respectively `1/6` and `1/4`, and `mu{E_0<E_1/3}` is `1/4`;
   - the two pushforward measures differ.
9. The function `exp(-v)(1-exp(-v/3))` is integrable on `(0,infinity)` and its integral there is `1/4`.
10. For all finite `I,K`, positive `w`, full-column-rank `X`, and real response `y`, `det G!=0`, the defined coefficient satisfies the WLS equations, and every solution `b` equals it. Together with positivity, these normal equations are also exactly the unique minimizer of the corresponding weighted quadratic loss, although the loss itself is not defined in this closure.

The docstring describes the same uniform-versus-exponential distinction, explicit simplex law, ratio probabilities, positive domains, combined exponential integral, and unique WLS scaling statement. It assumes usual measure-theoretic conditions.

### Totalization and junk-value audit

The normalization function and ratio event are globally defined using `x/0=0`. For the stated laws all input coordinates are positive almost surely, so total, two-coordinate sum, and normalized two-coordinate sum are positive almost surely. The pointwise cancellation assertion separately assumes all three positive inputs. No ratio probability is obtained by evaluating a zero denominator.

The simplex measure uses a factorial cast into ENNReal; factorial is positive and finite. All relevant measures are probabilities, and finite event masses are also expressly included, so `ENNReal.toReal(infinity)=0` cannot influence the probabilities. Every map used is Borel measurable: finite sums and total division, affine simplex completion, and the measurable input coordinates. Thus Mathlib's `Measure.map` fallback for a non-a.e.-measurable function is unused.

The Bochner and interval integrals return zero on nonintegrable functions in Mathlib. These particular functions are integrable (continuous on the bounded interval domains, or exponentially decaying on the positive half-line); integrability of the combined function is additionally a conclusion. All integral values have their ordinary meanings.

The matrix inverse would be zero at a singular real Gram matrix. Every asserted coefficient comparison assumes strictly positive weights and full column rank, and regularity explicitly establishes nonzero Gram determinant and unique normal-equation solution on this domain. Hence the inverse is genuine here. If `K` is empty, the coefficient vector is the unique empty vector, Gram determinant is one, and the conclusion is valid. If `I` is empty, injectivity of `X.mulVec` forces `K` empty; there is no spurious positive-dimensional fit on no data. There are no logarithms, square roots, real powers, truncated subtractions, infima/suprema, or limsup/liminf operations in this closure.

## SAP.P037a.T5

Location: `SAP/P037a/Challenge/Part1.lean:50` (theorem at line 68). This theorem uses `T5WholeStatement_W2`, **not** the separate definition `T5WholeStatement` in `WholeW1`. The latter is outside this theorem's closure. There are no external hypotheses.

### Definitions and geometry, fully unfolded

Use the uniform, exponential, normalization, simplex, ratio-event, Gram, WLS, and coefficient notions unfolded in the T4 section. In this section `m` free probability coordinates correspond to `m+1` multiplier coordinates, and every natural `m>=0` is allowed in the geometry and Jacobian clauses.

The positive orthant is `O_n={e in R^n: forall i,e_i>0}`. For `z in R^(m+1)`, its head is `q=(z_0,...,z_(m-1))` and its final coordinate is `t=z_m`. The chart domain is `D_m={z:q in Delta_m and t>0}`. Define

`F_m(e)=(e_0/T,...,e_(m-1)/T,T)`, where `T=sum_i e_i`,

`G_m(q,t)=(t q_0,...,t q_(m-1),t(1-sum_j q_j))`.

The exponential input measure on `R^n` is the product of `n` rate-one exponential laws. The uniform input measure is the product of `n` Lebesgue-restricted `(0,1)` laws. The chart density is the ENNReal-valued function

`rho_m(q,t)=ofReal(t^m exp(-t))` on `D_m`, and zero outside `D_m`.

The chart joint measure is Lebesgue measure with this density. Here a measure with density means integration of the nonnegative density against coordinate Lebesgue measure.

For real vector `x in R^m`, sort it increasingly using Mathlib's sorting permutation, giving `x_(0),...,x_(m-1)`. The first spacings are `s_0=x_(0)` and `s_i=x_(i)-x_(i-1)` for `i>0`. All spacings are the first `m` of these followed by `1-sum_i s_i`; on a sorted nonempty sample the final coordinate is `1-x_(m-1)`.

### Conclusions and quantifiers

1. For every natural `k`, the `(k+2)`-weight simplex measure (chart dimension `k+1`) is a probability and is concentrated on strictly positive unit-sum vectors.
2. For every natural `m`, for every `e in O_(m+1)`, `F_m(e) in D_m` and `G_m(F_m(e))=e`; for every `z in D_m`, `G_m(z) in O_(m+1)` and `F_m(G_m(z))=z`.
3. For every natural `m` and every `z=(q,t) in D_m`, `G_m` is differentiable at `z` and the absolute determinant of its Frechet derivative is `t^m`.
4. For every natural `m` and every `e in O_(m+1)`, `F_m` is differentiable at `e` and the absolute determinant of its Frechet derivative is `(T^m)^{-1}`. These are determinants of derivatives, not preassigned matrices called Jacobians.
5. For every natural `m`, pushing the `(m+1)`-fold product exponential measure through `F_m` yields the measure with density `rho_m`.
6. For every natural `k`, measurable space `Omega:Type`, probability `mu`, and family `E:Fin(k+2)->Omega->R`, assume all coordinates measurable, jointly independent, and each having law `expMeasure 1`. Then the normalized vector has the simplex measure, its forward-chart vector has joint measure `rho_(k+1)`, and almost surely its total is positive and its normalized coordinates are strictly positive and sum to one.
7. The pushforward of the one-dimensional uniform law through `v -> -log v` equals `expMeasure 1`.
8. For every natural `k`, measurable probability space `(Omega,mu)`, and measurable jointly independent `V_0,...,V_(k+1)` each uniform on `(0,1)`, the variables `-log V_i` are jointly independent, each has law `expMeasure 1`, their joint law is the product exponential measure, their normalized vector has the simplex measure, their forward-chart vector has joint measure `rho_(k+1)`, and almost surely their total is positive and their normalized coordinates are strictly positive and sum to one.
9. For every natural `m`, the Lebesgue integral on `t>0` of `t^m exp(-t)` is the real cast of `m!`.
10. For every natural `k`, the `(k+2)` spacings of `k+1` product-uniform draws have the simplex measure. Almost surely, the sorted sample is strictly increasing and each order statistic lies in `(0,1)`; the final spacing is one minus its largest order statistic; all spacings are positive and sum to one. The law clause is for the canonical product sample space, which is exactly a vector of independent uniforms.
11. For every natural `k`, normalized direct-uniform ratio probability is `1/6`, simplex ratio probability is `1/4`, and these laws differ (as in T4).
12. For every natural `k`, measurable probability space `(Omega,mu)`, and measurable jointly independent direct-uniform family `U` with `k+2` coordinates, its normalized law is the uniform weight law and differs from the simplex measure. Almost surely all raw weights are positive, and **for every** natural `d`, matrix `X` with `k+2` rows and `d` columns, and real response vector `y`, injectivity of `X.mulVec` implies equality of coefficients fitted with normalized and raw weights. This common full-measure set works for all such regression data.
13. For every finite row/coefficient type, positive weights, full-column-rank matrix, response, candidate coefficient, and positive common scale, scaling preserves the defined coefficient and equivalence of the WLS equations. For every `k>=0`, normalization preserves the coefficient under the same positive-weight/full-rank conditions.
14. For every finite row/coefficient type (decidable equality on coefficients), positive weights and full-column-rank matrix, the weighted Gram determinant is a unit in `R` (equivalently nonzero), the inverse-formula coefficient satisfies the WLS equations, and every solution equals it.

The docstring calls this the Bayesian bootstrap's constant-density simplex law; gives exponential, minus-log-uniform, and ordered-uniform-spacing constructions; describes the forward reciprocal and inverse positive Jacobian factors; gives the chart density, gamma integral, direct-uniform distinction, and WLS normalization fact. It states the resulting conditional relabel/recompute interpretation while expressly not claiming which procedure was actually used or replacement standard errors. Those historical/procedural statements have no separate formal variables or propositions in the theorem.

### Totalization and junk-value audit

The globally defined forward map divides by the total even off the positive orthant, where a zero total would use zero division. Both geometric and differential assertions restrict to a positive orthant, guaranteeing `T>0`; law assertions have positive inputs almost surely. The inverse is polynomial and its domain imposes positive `t` and strictly positive simplex coordinates. Natural exponents include `m=0`, where `t^0=1` and the chart has zero free probability coordinates; the construction reduces to the identity on a single positive multiplier. No truncated expression `n-1` is used to define these exponents.

Mathlib's `fderiv` is zero where no derivative exists. Both Jacobian assertions separately assert differentiability on their entire stated domains, so a default derivative cannot satisfy the claim in place of an actual derivative. Positivity also makes the reciprocal Jacobian nonzero.

`Real.log 0=0` and `Real.log x=log|x|` for negative `x`, but each uniform input lies strictly in `(0,1)` almost surely; hence every minus-log use agrees with the ordinary positive logarithm and is positive almost surely. The totalized function is Borel measurable. Sorting real finite vectors and taking spacings are Borel measurable; ties have product-uniform measure zero, and the theorem explicitly asserts strict ordering almost surely. The predecessor expression `i.val-1` is natural subtraction but is used only in the branch `i.val!=0`, so it is the true predecessor. The generated proof gives a valid index bound even in the unused zero branch. At `m=0` the first-spacing type is empty and the completion is the single weight one; the spacing law conclusions themselves use `m=k+1>=1`, so the largest order statistic is always available.

The joint density uses `ENNReal.ofReal`, which would truncate negative inputs to zero, but on its domain `t^m exp(-t)>0`; elsewhere the density is expressly zero. Factorials are finite positive integers. The gamma integrals are integrals of ordinary integrable functions on the positive half-line, so Bochner's nonintegrable-zero convention is unused. Pushforward maps are measurable (affine/polynomial maps, real division, logarithm, finite sorting), excluding arbitrary-Dirac fallback behavior. Probability law event masses are finite, so the two `toReal` probability equalities do not use `toReal(infinity)=0`.

As in T4, the matrix inverse is used on positive-weight/full-column-rank data; the conclusion certifies a unit Gram determinant and unique solution. Empty coefficient types give the unique empty fit, not a junk inverse. There are no square roots, noninteger real powers, limsup/liminf, unbounded suprema, or partial-function defaults in this closure.
