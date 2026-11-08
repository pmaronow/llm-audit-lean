# Blind reading

This file was written and saved after reading only the SAP Defs and Challenge sources and relevant Mathlib definitions, before opening `claims.json` or `record.json`. The theorem names are `SAP.P009a.T1` through `SAP.P009a.T17`. Each theorem asserts the proposition `TjStatement` without further outer parameters. The quantifiers below are the quantifiers inside those propositions. Challenge docstrings do not supply additional hypotheses.

## Expanded vocabulary

Units are numbered from 0 to n−1 (`Fin n`). An assignment is a function from these units to Bool, identified below with a vector z in {0,1}^n. An experiment E consists of a nonnegative mass function P on the entire assignment cube, summing to one, and arbitrary real outcome functions Y_i(z) on that entire cube. Expectations and probabilities are finite sums with these masses, with no measure-theoretic or integrability qualifications. A finite distribution cannot exist on an empty sample type because its masses must sum to one. The assignment cube itself is nonempty even when n=0.

Write p_i=P(Z_i=1), p_i(0)=P(Z_i=0)=1−p_i, and p_i(1)=p_i. The potential response Y_i(b;z) is Y_i with coordinate i overwritten by b. The assignment effect is tau_i(z)=Y_i(1;z)−Y_i(0;z), the assignment average is n^{-1} sum_i tau_i(z), and theta=E[n^{-1} sum_i tau_i(Z)]. The distributional effect is n^{-1} sum_i (E[Y_i|Z_i=1]−E[Y_i|Z_i=0]). No spillovers means that Y_i(z)=Y_i(z') whenever z_i=z'_i, for every i and every two full-cube assignments.

Conditional means are E[1_A X]/P(A). Conditional covariance is E[(X−E[X|A])(Y−E[Y|A])|A]. These are literal real divisions: if P(A)=0 the Lean value is zero. Covariance means E[(X−EX)(Y−EY)], and variance is covariance with itself.

The estimated arm mean is muhat_b(z)=n^{-1} sum_i 1_{z_i=b}Y_i(z)/p_i(b), the estimated arm count is nhat_b(z)=sum_i 1_{z_i=b}/p_i(b), and H(z)=muhat_1(z)−muhat_0(z). The Bernoulli variance estimate is V_B(z)=n^{-2} sum_i [1_{z_i=1}Y_i(z)^2/p_i^2+1_{z_i=0}Y_i(z)^2/(1−p_i)^2]. These are also literal real divisions at zero unless the surrounding hypotheses exclude that case.

The interference relation I_{ij}=1 holds if i=j, or if there exist two full-cube assignments differing only at coordinate i for which Y_j differs. It is therefore reflexive even for constant outcomes and uses the entire cube, including assignments of probability zero. Define d_{ij}=1 if some unit ell has I_{ell,i}=I_{ell,j}=1, and zero otherwise. Write d_i=sum_j d_{ij}, dbar=n^{-1}sum_i d_i, dmax=max_i d_i, drms=sqrt(n^{-1}sum_i d_i^2), C_i=sum_j I_{ij}, Cbar=n^{-1}sum_i C_i, and Cmax=max_i C_i. The incoming count is the number of j with I_{ji}=1, including self. When n>0 all these maxima have nonempty finite domains, 1≤dbar≤n, and 1≤Cbar≤n. Define lambda as the supremum of sum_{ij}v_i d_{ij}v_j over real v with sum_i v_i^2=1. This is the largest Rayleigh quotient; its SAP name is `spectralRadius`. The inflated variance estimates are V_A=dbar V_B, V_M=dmax V_B, and V_S=lambda V_B.

Product design means all p_i lie strictly between zero and one and P(z)=product_i p_i^{z_i}(1−p_i)^{1−z_i}. Fixed-size design with m treated means 0<m<n and P(z)=1/binomial(n,m) on assignments with exactly m treated coordinates, and zero elsewhere.

R(E;k,q,s), the regularity condition, is exactly: k,q,s are finite real numbers; k>0, q≥2, s≥1; for every i, 1/k≤p_i≤1−1/k; for every i, E|Y_i(Z)|^q≤k^q; and for every i and b, E|Y_i(b;Z)|^s≤k^s. No assertion that q,s are maximal moment orders is part of R. In every positive-size instance of R, k≥2 and both arms have positive probability. Under a product design all joint own-arm conditioning events for distinct units also have positive probability.

Let R_i(z) be the full assignment with all coordinates j for which I_{ji}=0 replaced by zero; let R_i^− also replace its own coordinate i by zero. For arbitrary finite-distribution random variables X,Y, alpha(X,Y) is the supremum, over all subsets A,B of their codomains, of |P(X in A,Y in B)−P(X in A)P(Y in B)|. This set of values contains zero and is bounded (in fact by 1/4), so the real supremum is meaningful. Set pow0(a,h)=0 when a=0 and a^h otherwise, explicitly giving 0^0 the value 0 here. Define e_h=n^{-1}sum_{ij}(1−d_{ij})pow0(alpha(R_i,R_j),h) and u_h=sum_i pow0(alpha(Z_i,R_i^−),h).

Write tauMS=n^{-1}sum_i (E tau_i)^2: this is the mean of the squared expected individual effects, not the mean of squared random effects. For any i,j,a, define xi_{ij}(a)=E[Y_i(z with i=a,j=1)−Y_i(z with i=a,j=0)]. Define xibar_{ij}=(1−p_i)xi_{ij}(1)+p_i xi_{ij}(0), and ybar_i=(1−p_i)E[Y_i|Z_i=1]+p_i E[Y_i|Z_i=0]. The direct bias B1 equals

    (n dbar)^{-1} sum_{i != j} [xibar_{ij} xibar_{ji} + 2 ybar_j (xi_{ij}(1)−xi_{ij}(0))].

The indirect bias B2 equals

    (n dbar)^{-1} sum_{i != j} sum_{a,b in {0,1}} (1−2a)(1−2b) Cov(Y_i,Y_j | Z_i=a,Z_j=b).

The contribution variance v_i is Var(1_{Z_i=1}Y_i/p_i−1_{Z_i=0}Y_i/(1−p_i)); its dispersion is Delta=sqrt(n^{-1}sum_i(v_i−n^{-1}sum_j v_j)^2). Finally A_{b,a,i}=1_{Z_i=b}Y_i^a for natural a.

A sequence S has a positive integer N_t at every natural t, N_t→infinity, and an experiment E_t of that size. N_t need not equal t+1 or be monotone. Sequence regularity uses the same k,q,s at every t. Sparse dependence means dbar_t/N_t→0. The statement f=o(g) below means literally f_t/g_t→0; O(g) means there is C>0 with |f_t|≤C|g_t| eventually. Probability convergence of X means P(|X_t|>epsilon)→0 for each epsilon>0. Law convergence to G means P(X_t≤x)→G(x) for each continuity point x of G.

Variance conservativeness VC(Vhat) means that there exists a function L:R→R such that, for every epsilon>0, P[(N_t/dbar_t)(Vhat_t−Var(H_t))≤−epsilon]→L(epsilon), and L(epsilon)→0 as epsilon decreases to zero through positive values. Existence of each inner limit is required. A positive eventual lower bound for a_t means there is c>0 such that a_t≥c eventually. The coverage predicate C(T,theta,Vhat,alpha) means |T−theta|≤sqrt(Vhat/alpha).

The underlying Mathlib notions used here have their ordinary meanings in these domains: `Function.update` overwrites one coordinate; `Real.rpow` on nonnegative bases is the usual real power with 0^0=1 before SAP's pow0 override; `Real.sqrt` is the nonnegative square root on nonnegative inputs and zero on negative inputs; `Nat.ceil` is the least natural integer above a real; `atTop` on naturals means eventually beyond some index; `Tendsto` and `nhds` are topological limits; `nhdsWithin 0 (Ioi 0)` is the limit at zero from above; and `Filter.liminf` is the supremum of eventual lower bounds. The only liminf here is of probabilities in [0,1], so it has no unboundedness problem. `standardNormalCDF` is the real value of `gaussianReal 0 1 (Iic x)`; Mathlib defines this as the Gaussian probability measure with mean zero and variance one, obtained from its usual Lebesgue density. Real supremums for degrees and Rayleigh quotients occur below only at positive sizes. `WithTop R` adds a greatest element infinity; `untopD 0` returns the underlying finite real order, using zero only on infinity, which is handled in a separate branch.

## T1

There are no hypotheses. At each t set n=t+1 and use the uniform distribution on {0,1}^n with Y_0=Z_0 and Y_i=0 for i>0. The sequence satisfies R(2,4,1). At every t it has product design, no spillovers, dbar=dmax=drms=lambda=1, and the sequence is sparse. At every t, theta=distributional effect=tauMS=1/n, Var(H)=1/n^2, E V_B=2/n^2, and Var(H)<E V_B. For every full-cube z, H(z)=2z_0/n, V_B(z)=4z_0/n^2, and V_A(z)=V_M(z)=V_S(z)=V_B(z). Also Delta^2=(n−1)/n^2. Each of V_B,V_A,V_M,V_S satisfies VC. The random quantity n(V_B−Var(H))−tauMS converges to zero in probability. For every t the coverage probability C(H,theta,V_B,1/20) is 1/2, and 1/2<1−1/20. Separately, at every t, E H=1/n.

## T2

Four assertions are conjoined.

1. For every family of measurable spaces Omega_t, every probability measure P_t on each space, every real random-variable families T_t,Vhat_t and deterministic real sequences theta_t,V_t,delta_t: assume T_t and T_t^2 are integrable at every t; both T_t and Vhat_t are measurable; E T_t=theta_t; V_t=E[(T_t−theta_t)^2]; V_t>0; Vhat_t(omega)≥0 for every t and omega; delta_t>0. For every real alpha with 0<alpha<1, all three following conclusions hold. For every t and every 0<eta<1,

       P(not C(T_t,theta_t,Vhat_t,alpha)) ≤ P(Vhat_t<(1−eta)V_t)+alpha/(1−eta).

   If P(Vhat_t<(1−eta)V_t)→0 for every 0<eta<1, then liminf_t P(C(T_t,theta_t,Vhat_t,alpha))≥1−alpha. If P[((t+1)/delta_t)(Vhat_t−V_t)≤−epsilon]→0 for every epsilon>0 and ((t+1)/delta_t)V_t has a positive eventual lower bound, then the preceding relative underestimation probabilities converge to zero for every 0<eta<1. All probabilities here are the `.toReal` values of the probability measures, hence finite.
2. For every real a,V,Vhat,eta,c, if a>0, eta>0, c≤aV, and Vhat<(1−eta)V, then a(Vhat−V)≤−eta c. Neither c nor V is separately required positive.
3. For every experiment sequence S, finite real k,q,s,alpha, and Vhat_t on its assignment cubes: assume sequence R(k,q,s), product designs at every t, pointwise Vhat≥0, 0<alpha<1, VC(Vhat), and a positive eventual lower bound for (N_t/dbar_t)Var(H_t). Then P(Vhat_t<(1−eta)Var(H_t))→0 for every 0<eta<1, and liminf_t P(C(H_t,theta_t,Vhat_t,alpha))≥1−alpha. There is no sparse-dependence assumption.
4. For every positive n, experiment E and real k,q,s, R(E;k,q,s) and product design imply E H=theta.

## T3

There exist three experiments E,F,G of size two with the following exact full-cube mass and outcome formulas and numerical conclusions. In E and G the coordinates are independent, with p_0=1/4 and p_1=3/4, so each mass is (z_0?1/4:3/4)(z_1?3/4:1/4). In E, Y_0=z_1 and Y_1=−z_0. In F, P(1,0)=1/4, P(0,1)=3/4, the other two masses are zero, and both outcome functions are constantly one. In G, Y_0=1 and Y_1=1−z_0. All three satisfy R(4,4,1), and E,G have product design. The conclusions are Var_E(muhat_1)=13/48, sum_{ij}Cov_E(A_{1,1,i},A_{1,1,j})=0; Var_F(nhat_1/2)=1/3, sum_{ij}Cov_F(Z_i,Z_j)=0; Var_G(sum_i A_{1,2,i}/p_i^2)=367/9, and 4^4 sum_{ij}Cov_G(A_{1,2,i},A_{1,2,j})=39. Finally 0<13/48, 0<1/3, and 39<367/9 are asserted.

## T4

Three universally quantified assertions are conjoined.

1. For every pair of finite types Omega,U, every finite probability distribution P on Omega, every real family X_i on Omega, all real weights w_i, and every real K, if 0<w_i≤K for every i, then

       Var(sum_i w_i X_i)=sum_{ij} w_i w_j Cov(X_i,X_j)
       Var(sum_i w_i X_i)≤K^2 sum_{ij}|Cov(X_i,X_j)|.

   U may be empty, in which case both expressions are zero. Omega is necessarily nonempty because P is normalized. There are no further independence or moment assumptions.
2. For every positive n, experiment E and finite real k,q,s satisfying R(E;k,q,s), each of the following holds. For every arm b,

       Var(muhat_b)≤(k^2/n^2)sum_{ij}|Cov(A_{b,1,i},A_{b,1,j})|.

   If E has product design, then for every b the absolute covariance sum equals sum_{ij}d_{ij}|Cov(A_{b,1,i},A_{b,1,j})|, and Var(muhat_b)≤k^4 dbar/n. Without a product-design assumption, for every b,

       Var(muhat_b)≤k^4 dbar/n+10k^4 e_{(q−2)/q}/n.
       Var(nhat_b/n)≤(k^2/n^2)sum_{ij}|Cov(1_{Z_i=b},1_{Z_j=b})|
       Var(nhat_b/n)≤k^2 dbar/n+k^2 e_{(q−2)/q}/n.

   If in addition q≥4 and E has product design, then for every b, writing W_b=sum_i A_{b,2,i}/p_i(b)^2,

       Var(W_b)≤k^4 sum_{ij}|Cov(A_{b,2,i},A_{b,2,j})|,
       sum_{ij}|Cov(A_{b,2,i},A_{b,2,j})|=sum_{ij}d_{ij}|Cov(A_{b,2,i},A_{b,2,j})|,
       Var(W_b)≤k^8 n dbar,

   and Var(n V_B)≤4k^8 dbar/n. These are separate inequalities; an unstated inequality between their right-hand sides is not part of the proposition.
3. For every positive n, E,k,q,s satisfying R, every natural a with a=1 or a=2 and 2a≤q, every i,j and arm b, |Cov(A_{b,a,i},A_{b,a,j})|≤k^{2a}.

## T5

There are no hypotheses. For every positive size n=t+1 use fair independent assignments and let M_n=max(1,floor(n/2)−1), with the subtraction performed in natural numbers. Set Y_i(z)=z_0 for i<M_n and zero otherwise. This sequence satisfies R(3,2,1), and for every t has product design and dbar/n=rho_n=(M_n^2+n−M_n)/n^2. Both this ratio and rho_{t+1} converge to 1/4. For every t, dbar/n≥1/4 iff t+1≤4; for every natural n>0, rho_n≥1/4 iff n≤4. For every natural m≥3, 1/4−rho_{2m}=(m−2)/(4m^2). For every natural m≥2, 1/4−rho_{2m+1}=(8m−11)/(4(2m+1)^2). All subtractions in these final real formulas are real subtractions.

## T6

Two assertions are conjoined. First, for every real sequence a_t and reals L,c, assume that for every epsilon>0 eventually a_t<L+epsilon and infinitely often a_t>L−epsilon, and that 0<c<L. Then {t:c≤a_t} is infinite. This uses an explicit finite-limsup predicate and no possibly unbounded Mathlib real limsup.

Second, for every positive n, experiment E and finite real k,q,s,L, assume R(E;k,q,s) and 0<L≤1. Let M=ceil(sqrt(L)n), a natural number, and let F keep E's design but have outcomes

    Y_i^F(z)=(n/M) z_0 [z_i p_i−(1−z_i)(1−p_i)] if i<M, and 0 otherwise.

Then dbar_F=M^2/n+(n−M)/n≥Ln; for all i,z, |Y_i^F(z)|≤1/sqrt(L); theta_F=p_0; and for every z, H_F(z)=z_0 and 1/k≤|H_F(z)−theta_F|. No product or fixed-size design is assumed in this second assertion. Its hypotheses ensure 1≤M≤n and positive arm probabilities.

## T7

There are no hypotheses. The same sparse fair sequence as in T1 satisfies R(2,4,1), sparse dependence, and, at every t, product design, no spillovers, dbar=dmax=1, and Var(H)>0. Also n Var(H)→0. For every t and every Boolean b, the probability that (H−theta)/sqrt(Var(H)) equals 1 if b=true, and −1 otherwise, is 1/2. The standardized sequence does not converge in law to the standard normal CDF. Only failure for this particular Gaussian limit is asserted.

## T8

For every experiment sequence S and finite real k,q,s, assume sequence R(k,q,s), product design at every t, an everywhere uniform real upper bound D on dmax_t, Var(H_t)>0 at every t, and a positive eventual lower bound for N_t Var(H_t). Then (H_t−theta_t)/sqrt(Var(H_t)) converges in law to the standard normal CDF. In particular q≥2, s≥1 are exactly the ranges from R, and no q>2 or additional sparsity hypothesis is present.

## T9

For every natural r≥1 there exists an experiment E of size n=4r+2, with exactly 2r+1 units treated uniformly. Let A={0} union {2,...,2r+1}; its complement contains 1. The entire outcome function equals: Y_0(z) is the average of z_j over A, Y_1(z) is the average over the complement, and Y_i(z)=z_i otherwise. The experiment satisfies R(2,4,1), d_{0,1}=0, dbar=3−4/n<3, Cbar=2−2/n, Cmax=2, and alpha(R_0,R_1)=1/4. The existential E is chosen separately for each r.

## T10

For every experiment sequence S, assume that for every t there exists an integer m with fixed-size design (hence 0<m<N_t); dbar_t is eventually bounded above by some real D; and for every t the finite set Q_t={(i,j):d_{ij}=0} has positive cardinality. Then there exists a family of finite exceptional sets F_t of ordered unit pairs such that F_t is a subset of Q_t at every t, |F_t|/|Q_t|→0, and for every epsilon>0, eventually for all i,j with d_{ij}=0 and (i,j) outside F_t, alpha(R_i,R_j)<epsilon. The exceptional sets are selected once for the whole sequence before epsilon is quantified. There is no regularity or arm-probability bound hypothesis.

## T11

For every natural m≥2, take n=m^2 fair independent coordinates. Partition indices into m consecutive blocks of m. For unit i, let h be the first unit in its block and ell the second; the displayed modulo operations give these same indices because m≥2. Define Y_i=z_i+z_ell if i=h, and Y_i=z_i+z_h otherwise. Then E has product design, R(2,4,1), Cbar=2, dbar=m, tauMS=1, B1=2/m^2, B2=0, and 0<B1≤tauMS/dbar. In addition, along m=t+2 the ratio dbar/Cbar tends to positive infinity. All of these are unconditional assertions about this particular family.

## T12

First, for every positive n, experiment E and finite real k,q,s, assume R(E;k,q,s), q≥4, and product design. Then

    |B1|≤12k^4(Cbar−1)/dbar,
    |B2|≤4k^4(dbar−1)/dbar,
    |B2|≤4k^4,
    0≤tauMS≤4k^4.

Second, for every experiment sequence S and finite real k,q,s, assume sequence R(k,q,s), q≥4, product designs at every t, and dbar_t/Cbar_t→infinity. Then tauMS_t/dbar_t→0, B1_t→0, and B2_t=O(1). If additionally Cbar_t/(dbar_t |B2_t|)→0 and B2_t is eventually nonzero, then tauMS_t/dbar_t=o(|B2_t|) and B1_t=o(|B2_t|). These extra two hypotheses apply only to the final two relative limits. No sparse-dependence hypothesis is present.

## T13

There are no hypotheses. In the fair independent three-unit experiment with Y_1(z)=z_0(2z_2−1) and Y_0=Y_2=0, product design and R(2,4,1) hold. Unit 0 affects unit 1. Nevertheless xi_{1,0}(0)=xi_{1,0}(1)=xibar_{1,0}=0.

## T14

Four assertions are conjoined. First, for every natural n, experiment E and distinct i,j, if i does not affect j, then for every arm a and every full-cube z the outcomes Y_j(z with j=a,i=1) and Y_j(z with j=a,i=0) are equal; xi_{j,i}(0)=xi_{j,i}(1)=xibar_{j,i}=0. Second, for every positive n and experiment E, no spillovers together with positive probabilities for both treatment arms of every unit imply that xi_{i,j}(0)=xi_{i,j}(1)=0 for all distinct i,j and B1=0. Third, the specific three-unit experiment in T13 has I_{0,1}=1 and xibar_{1,0}=0. Fourth, for every n,E and distinct i,j, xibar_{j,i}≠0 implies I_{ij}=1. The first and fourth assertions do not require positivity of arm probabilities, regularity, or a product design.

## T15

There are no hypotheses. At every t take n=t+1, fair independent assignments and Y_i(z)=z_i for all units. The sequence satisfies R(2,4,1); it has maximal observed and potential moment orders both infinity. Expanded, observed admissibility at real q≥2 means a single uniform positive k bounds E|Y_i|^q by k^q over all t,i; at infinity it means |Y_i(z)|≤k on every positive-mass assignment. Potential admissibility is the analogous condition for all t,i,b at orders s≥1. Maximality additionally says every admissible order is ≤infinity. At every t product design, no spillovers and dbar=1 hold. The sequence is sparse; e_1/n→0 and u_1/n→0. For every t,

    4 sum_{ij}Cov(Z_i,Z_j)=n,
    4 sum_{i != j}alpha(Z_i,Z_j)=0,
    n>0.

Both sums are over ordered pairs, with only the second sum removing the diagonal. No equality for either sum after normalization, or arm-count variance, is separately asserted.

## T16

For every positive natural n, arbitrary experiment E, Boolean arm b and positive real k, the following chain holds:

    (k^2/n^2)sum_{ij}Cov(1_{Z_i=b},1_{Z_j=b})
      ≤(k^2/n^2)sum_{ij}alpha(Z_i,Z_j)
      ≤k^2 dbar/n+(k^2/n^2)sum_{ij}(1−d_{ij})alpha(Z_i,Z_j).

All sums include the diagonal. There are no regularity, treatment positivity or design-independence hypotheses. k is simply a positive scaling constant here, not assumed to bound inverse arm probabilities.

## T17

There exists a four-unit experiment E whose mass is 1/6 on each assignment with exactly two treated units and zero otherwise. Its full-cube outcome schedule is Y_i(z)=z_i+1_{i=0}z_1. For every j, j affects 0 iff j=0 or j=1. It has fixed-size design with m=2, R(2,4,1), and incoming count for unit 0 equal to 2. Define T_0(z) as the number of treated incoming causes other than unit 0 itself. Then P(T_0=0)=1/2, and E[1_{T_0=0}|Z_0=1]=2/3.

The auxiliary numerical function h(N,M,K,t)=binomial(M,t)binomial(N−M,K−t)/binomial(N,K), with natural subtraction in its general definition, satisfies h(4,2,2,0)=1/6 and h(3,1,2,0)=1/3. All arguments used here are in the ordinary hypergeometric support, so subtraction truncation and division by zero have no effect. Finally 1/2≠1/6 and (2/3)/(1/2)≠(1/3)/(1/6). The last inequality compares 4/3 with 2, although those simplifications are not separately part of the statement.

## Blind domain observations

Every sequence fixes positive sizes tending to infinity. All uses of estimators with inverse arm probabilities have regularity or explicit positivity, or are explicit fair/fixed-size examples. All uses of B2 are under product designs with positive marginal probabilities, so its distinct-unit conditional covariances have positive conditioning probability. The first and last T14 implications use unconditional expectations of overwritten outcomes, not conditional means. T16 concerns bounded indicators and does not use an inverse marginal probability. T12 explicitly excludes eventual zero B2 in its relative comparison. Empty finite weight index types in T4 give the legitimate zero-sum special case without making its nonempty cases disappear. These observations do not yet compare any theorem with its intended claim.
