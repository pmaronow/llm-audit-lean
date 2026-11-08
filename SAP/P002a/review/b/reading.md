# Blind reading of the Challenge

This file was written from `SAP/P002a/Defs*.lean`, `SAP/P002a/Defs/*.lean`, the Challenge files, and the relevant Mathlib definitions, before opening `claims.json` or `record.json`. The Challenge contains 14 stubs: T1–T6 and T8–T15. Each asserts the proposition below, with no additional section hypotheses.

## Dictionary, including conventions

All unit indices are `Fin n`, i.e. integers 0 through n−1. Treatment and receipt indices are Booleans, identified below with 0 and 1. A population P consists of arbitrary real outcomes Y_i(b), Boolean receipts D_i(a), and a natural treated count n1. A covariate population also has arbitrary vectors x_i in R^k. Outcomes are indexed by *receipt*, so observed outcomes automatically obey exclusion: under assignment a they are Y_i(D_i(a)). There is no probability distribution on potential outcomes.

Write n0=n−n1 as a **real** difference, p=n1/n, C={i:D_i(0)=0 and D_i(1)=1}, and beta_P=|C|^−1 sum_C(Y_i(1)−Y_i(0)). Monotonicity means D_i(0)=1 implies D_i(1)=1 for every i. A valid design means n≥2 and 0<n1<n. No positive fraction of compliers is required, only C nonempty when Theta or Xi is used.

For a real vector q, bar(q)=sum_i q_i/n and bar(q)_S=sum_{i in S}q_i/|S|. Write V(q)=sum_i(q_i−bar(q))^2/(n−1) and Cov(q,t)=sum_i(q_i−bar(q))(t_i−bar(t))/(n−1). For a subgroup S, the analogous covariance uses denominator |S|−1 if |S|≥2, and is **defined to be zero** if |S|<2; subgroup variance is that covariance with equal arguments. These are the SAP definitions, not implicit statistical conventions. Real division is Mathlib field division, with q/0=0. Empty sums are zero. Under a valid design the population and assignment-arm denominators are positive; C is nonempty under Theta/Xi, but a singleton C still uses the zero-covariance convention.

W_ai(beta)=Y_i(D_i(a))−beta D_i(a), v_ai(beta)=W_ai(beta)−bar(W_a(beta)), and F4(q)=(n^−1 sum_i q_i^4)^(1/4), implemented by two nonnegative real square roots. Real.sqrt of a negative number is zero, but the displayed moment arguments are nonnegative in valid designs. S_a^2(P,beta)=p^2(1−p)^2 V(W_a(beta)). Sdiff2, though defined, does not occur in the asserted conclusions.

A(P) is the finite set of all n1-element subsets of the n units (`Finset.univ.powersetCard n1`). E_P and Pr_P are uniform average and counting probability on A(P). Var_P(f)=E_P[(f−E_P f)^2], with no Bessel correction on the assignment space. A valid design makes A(P) nonempty. If no assignment exists the definitions instead divide by zero, but no asserted statistical claim relies on that case.

For S an assignment, Q_i(P,beta,S)=W_{1_{i in S},i}(beta) is the observed adjusted outcome. Define

* R_P(q,S)=n^−1 sum_i q_i(1_{i in S}−p);
* tau_P(beta,S)=R_P(Q(P,beta,S),S);
* m_a(q,S)=bar(q)_S for a=1 and bar(q)_{S^c} for a=0;
* H_P(q,S)=p^2(1−p)^2[sum_{i in S}(q_i−m_1)^2/n1^2 + sum_{i in S^c}(q_i−m_0)^2/n0^2].

The absolute student statistic B(t,h) takes values in [0,infinity]: it is 0 if h=t=0, infinity if h=0 and t≠0, and otherwise `ENNReal.ofReal`(|t|/sqrt(h)). The latter converts a nonnegative real to the extended nonnegative reals, truncating a negative argument to zero. Raw AR is B(R,H). For a fixed extended-valued assignment function g, c_P(g,alpha) is the smallest attained value t with Pr_P(g≤t)≥1−alpha, or infinity if there is no such t. Raw acceptance of beta at S is

    B(R_P(Q_S,S),H_P(Q_S,S)) ≤ c_P(T ↦ B(R_P(Q_S,T),H_P(Q_S,T)),alpha).

Here **Q_S stays fixed** while T varies. Raw coverage cov_P(beta,alpha) is the probability over S of this event; the inequality includes ties. The zero-standard-error convention is explicit and is relevant to the degenerate examples.

For covariate calculations set u_i=(1,x_i), with coordinates `Option (Fin k)` (none is the intercept), ||b||²=sum_j b_j², G_x(S)=|S|^−1 sum_{i in S}u_i u_i', s_x(S,q)=|S|^−1 sum_{i in S}u_i q_i, and RSS_x(S,q,b)=sum_{i in S}(q_i−u_i'b)². OLS_x(S,q) is G_x(S)^−1 s_x(S,q) when det G_x(S)≠0. On a singular design it is a classical choice of a global RSS minimizer if one exists, and the zero vector otherwise. This is not a stipulated minimum-norm choice. Mathlib's nonsingular matrix inverse is the usual inverse on the branch where it is used; dot products and matrix-vector products are finite coordinate sums.

Population coefficients are psi_a(P,beta)=OLS_x(all,W_a(beta)); residuals are U_ai(P,beta)=W_ai(beta)−u_i'psi_a. Let b_a(S,q)=OLS_x(S_a,q), S_1=S, S_0=S^c. If l(x,c)=sum_{j=1}^k x_j c_j excludes the intercept, define

    J_P(q,S;c1,c0)=bar(q−l(x,c1))_S−bar(q−l(x,c0))_{S^c}.

Feasible adjusted tau is J_P(q,S;b_1(S,q),b_0(S,q)); oracle tau at beta is J_P(Q_S,S;psi_1(P,beta),psi_0(P,beta)). Its variance is over S, with observed Q_S changing with S. The feasible variance estimate H^x_P(q,S) is RSS_x(S,q,b_1)/n1² + RSS_x(S^c,q,b_0)/n0². Adjusted AR, acceptance, and coverage cov^x use B(J,H^x) and the same fixed-Q_S reassignment quantile as above. `oracleStar` and `xCirc` are defined but not used in these theorem conclusions.

Theta(P;delta,r,A) is exactly the conjunction of: valid design; monotone receipt; C nonempty; rn≤n1≤(1−r)n; Cov_C(W_1(beta_P),W_0(beta_P))≥−delta sqrt(V_C(W_1))sqrt(V_C(W_0)); and, for each a in {0,1}, F4(v_a(beta_P))≤A sqrt(V(W_a(beta_P))). Positivity of r,A and delta<1 are not built into Theta; when needed they are separate hypotheses.

Xi(P;delta,e,A,B,r) is exactly: valid design of P.pop; monotone receipt; C nonempty; rn≤n1≤(1−r)n; Cov(U_1(beta_P),U_0(beta_P))≥−delta sqrt(V(U_1))sqrt(V(U_0)); for each a, F4(U_a(beta_P))≤B sqrt(V(U_a(beta_P))); for every covariate coordinate j, sum_i x_ij=0 and n^−1 sum_i x_ij^4≤A; and for every b in R^k, e||b||²≤n^−1 sum_i(x_i'b)². The covariance here is over **all units**, not just compliers. Positivity of e,A,B,r and delta<1 is imposed only in the relevant outer hypotheses.

I_Theta(n;delta,r,A,alpha) is the extended-nonnegative infimum, first over every real beta and then over every population P with Theta and beta_P=beta, of `ofReal(cov_P(beta,alpha))`. I_Xi is the analogous adjusted quantity for fixed k and Xi. An empty inner infimum is infinity; the outer infimum selects actual populations whenever any exist. If the whole class is empty the result is infinity. thetaSizes and xiSizes are exactly the sets of n where the corresponding class is nonempty.

Limits at `atTop` mean ordinary limits as the natural index increases. The filter `atTop inf principal(classSizes)` means tending to infinity through the sizes with nonempty classes. Its `NeBot` hypothesis says that those sizes are unbounded. Mathlib liminf is the supremum of eventual lower bounds; its extended-real codomain is a complete lattice, so it has no unbounded-real fallback convention. Big-O means an eventual bound |f_j|≤C|g_j| for some fixed real C. `forall-a.e. omega` means outside a set of measure zero, and eventual means all sufficiently large natural indices.

`RandomizationSequence(P,mu,Z)` says that for every index j and **every** predicate E on subsets of the units at size j, {omega:E(Z_j(omega))} is measurable and has mu-measure `ofReal(Pr_{P_j}(E))`. Thus each Z_j has the complete-randomization marginal. It does not assert independence or pointwise membership in A(P_j); membership follows almost surely. In T9 the additional independence hypothesis says, for every finite I of indices and every family of subset predicates E_j, the measure of their simultaneous occurrence equals the product of their marginal measures. `IsProbabilityMeasure` means mu(Omega)=1, so the a.e. conclusion is not made true by a zero measure.

## Explicit populations

* N_m (`negativeDeltaModel`): n=12m, n1=2m, all units compliers, Y_i(0)=Y_i(1)=−1 for even i and +1 for odd i; k=1 and x_i=−1 if i mod 4<2, +1 otherwise.
* C4 (`centringModel`): n=4, n1=2, all compliers, z=(-1,-1,1,1), Y_i(a)=z_i+2a.
* B_m (`signModel`): n=2m, n1=m, all compliers, Y_i(a)=−1 for i<m and +1 for i≥m, independent of a.
* D(n,beta): n1=floor(n/2), all compliers, Y_i(0)=0, Y_i(1)=beta. Its covariate version has k=1 and x_i=(2(i+1)−n−1)/n.
* X2 (`interceptExampleX`): n=2,k=1,x=(2,−2).
* E_m (`nearSingularModel`): n=2m,n1=m, all compliers; t_i=(2(i mod m)−m+1)/(m−1), v_m=(m+1)/(3(m−1)), eta=2^{−(2m)^2}; Y_i(a)=t_i+(t_i²−v_m)/10 independent of a; x_i=1_{i<m}−1_{i≥m}+eta t_i.
* O_n (`oddNearModel`): n1=floor(n/2), all compliers, x_i=2i/(n−1)−1, Y_i(a)=(x_i²−bar(x²))/10 independent of a.

The index arithmetic in these formulas is natural-number modulo/division before casting where indicated; the displayed subtractions in t,x, moment denominators and controlSize are real subtractions.

## SAP.P002a.T1

A conjunction with no hypotheses:

1. For P=N_1, Theta(P.pop;−1/2,1/6,2), Xi(P;−1/2,1/2,2,2,1/6), beta_P=0, |A(P)|=66, S_1²(P,0)=S_0²(P,0)=25/1188, Var_P(tau_P(0))=5/396 and Var_P(oracleTau_P(0))=36/55. The first variance is strictly less than (3/2)[n0/(12·2) S_1²+2/(12n0) S_0²]; the second is strictly less than the same expression with the S_a² replaced by V(U_a(P,0)).
2. For every natural m, if m≥1, P=N_m satisfies the same Theta and Xi parameter conditions and beta_P=0. Its raw variance is 5/[36(12m−1)] and its oracle variance is 36/(60m−5). The respective expressions (3/2)[n0/(n n1) S_1²+n1/(n n0) S_0²] and (3/2)[n0/(n n1) V(U_1)+n1/(n n0) V(U_0)] equal 13/12 times the corresponding variance.
3. 12/11+12/11+2(−1/2)(12/11)=12/11, while 12/11+12/11+(−1/2)(10/2)(12/11)+(−1/2)(2/10)(12/11)=−36/55, and 12/11≤−36/55 is false.
4. For each Boolean arm a, psi_a(N_1,0)=the zero coefficient vector. This coefficient assertion is only for m=1.

## SAP.P002a.T2

Both universal assertions hold:

1. For every n, population P of size n, and real delta,r,A, if delta<1, 0<r≤1/2, A>0 and Theta(P;delta,r,A), then

       (1−max(delta,0))[n0/(n n1) S_1²(P,beta_P)+n1/(n n0) S_0²(P,beta_P)] ≤ Var_P(tau_P(beta_P)).

2. For every n,k, covariate population P, and real delta,e,A,B,r, if k>0, delta<1, e,A,B>0, 0<r≤1/2 and Xi(P;delta,e,A,B,r), then

       (1−max(delta,0))[n0/(n n1) V(U_1(P,beta_P))+n1/(n n0) V(U_0(P,beta_P))] ≤ Var_P(oracleTau_P(beta_P)).

## SAP.P002a.T3

The universal raw assertion in T2 with factor 1−delta instead of 1−max(delta,0) is false, **and** the universal adjusted assertion in T2 with that replacement is false. The domains and other hypotheses are exactly those in T2, including k>0 for the adjusted assertion. Logically these are two negated universally quantified propositions, hence need not have the same counterexample.

## SAP.P002a.T4

Four conjuncts:

1. For every n and real vector q, if n≥2 and F4(q)≤(1/2)sqrt(sum_i q_i²/(n−1)), then every coordinate of q is zero. No mean-zero hypothesis is imposed.
2. For every n and P with Theta(P;0,1/4,1/2), there exists a single real c such that W_ai(beta_P)=c for every arm a and unit i.
3. For every alpha with 0<alpha<1: for every n≥2 and every real beta, D(n,beta) satisfies Theta(0,1/4,1/2) and has beta_P=beta; for every n≥2 and **every** P in that Theta class, cov_P(beta_P,alpha)=1; for every n≥2, I_Theta(n;0,1/4,1/2,alpha)=1; this infimum sequence tends to 1 and does not tend to ofReal(1−alpha).
4. For every alpha with 0<alpha<1: for every n≥2 and every real beta, the covariate D(n,beta) satisfies Xi(0,1/4,4,1/2,1/4) and has beta_P=beta; for every n≥2 and **every** P in that size-n, k=1 Xi class, max(0,1−1548/(n−1))≤cov^x_P(beta_P,alpha); I_Xi(n;1,0,1/4,4,1/2,1/4,alpha) tends to 1 and does not tend to ofReal(1−alpha). No all-size equality to one is asserted in this adjusted part.

## SAP.P002a.T5

Three conjuncts:

1. For every real delta,r,A,alpha, if delta<1, 0<r≤1/2, A>0, 0<alpha<1 and thetaSizes(delta,r,A) is unbounded, then ofReal(1−alpha)≤liminf I_Theta(n;delta,r,A,alpha), taking n to infinity through thetaSizes.
2. For every natural k and real delta,e,A,B,r,alpha, if k>0, delta<1, e,A,B>0, 0<r≤1/2, 0<alpha<1 and xiSizes(k,delta,e,A,B,r) is unbounded, the corresponding adjusted lower bound holds along xiSizes.
3. For every strictly increasing natural size sequence sizes, every sequence P_j of populations of these sizes, and every real delta,r,A,alpha, assume delta<1, 0<r≤1/2, A>0, 0<alpha<1, Theta(P_j;delta,r,A) for every j, **for every j there exists a real effect c_j such that for every unit** Y_ij(1)=Y_ij(0)+c_j, and V(Y_j(0))>0 for every j. Then cov_{P_j}(beta_{P_j},alpha) tends to 1−alpha in the extended-nonnegative embedding, and the raw worst-class liminf through all nonempty sizes equals ofReal(1−alpha). It does not assert existence or necessity of such a sequence, or adjusted sharpness.

## SAP.P002a.T6

Three conjuncts with no outside hypotheses:

1. For every m≥4, P=E_m satisfies Xi(P;0,1/4,16,5,1/3), beta_P=0, and both G_x(S) and G_x(S^c) have nonzero determinant for every S in A(P). For **every such S**, fix q=Q(P,0,S). Then Var_P(T↦adjustedTau_P(q,T))≥8·2^{2(2m)^2}/2^{2m}; for every T in A(P), 0≤H^x_P(q,T)<5/(2m); and Pr_P(T:|H^x_P(q,T)/Var_P(adjustedTau_P(q,·))−1|≥1/2)=1.
2. For every n≥9, if n is odd, O_n satisfies Xi(0,1/4,16,5,1/3).
3. With P=E_{j+4} and fixed q_i=Y_i(0), the error probability in part 1 tends to 1 as j tends to infinity.

## SAP.P002a.T8

For X2=(2,−2), each covariate coordinate sums to zero and has fourth moment 16; for every b in R^1, 2||b||²≤bar((x_i'b)²). Let v=(1,0) be the intercept unit vector in R^{1+1}; then bar((u_i'v)²)=1, ||v||²=1, and bar((u_i'v)²)<2||v||². This is a single two-unit counterexample, not a quantified family.

## SAP.P002a.T9

For every type Omega with a measurable space, all three statements hold:

1. For every n,k,x, assume n>0; then for every real e, if each coordinate of x sums to zero and for every b in R^k, e||b||²≤bar((x_i'b)²), the population augmented Gram has intercept entry 1, both intercept/covariate cross entries 0 for every coordinate, covariate block entry bar(x_s x_t) for every pair s,t, and for every b in R^{1+k}, min(1,e)||b||²≤bar((u_i'b)²). Here k=0 and e≤0 are allowed.
2. For every n,k,x with n>0,k>0 and centered covariate coordinates, the infimum of bar((u_i'b)²) over ||b||²=1 in R^{1+k} equals min(1,lambda_x), where lambda_x is the infimum of bar((x_i'b)²) over ||b||²=1 in R^k. Both real infima have nonempty, nonnegative sets under these dimension hypotheses.
3. For every probability measure mu on Omega, strictly increasing sizes, natural k, covariate-population sequence P_j, assignment maps Z_j, and reals delta,e,A,B,r, assume k>0, delta<1, e,A,B>0, 0<r≤1/2, Xi(P_j;delta,e,A,B,r) for every j, RandomizationSequence(P.pop,mu,Z), and the full finite-event **independence across j** described above. Then, for every fixed strictly increasing sub:Nat→Nat, for mu-almost every omega there exists err:Nat→R such that err_j→0 and for all sufficiently large j, **for both arms a**, put N=sub(j), S=Z_N(omega), q=Q(P_N,beta_{P_N},S), and b=b_a(S,q)−OLS_{x_N}(all,q). One has

       (min(1,e)+err_j)||b||² ≤ b' G_{x_N}(S_a) b.

The null set and err may depend on sub; err may depend on omega. No sign condition on err is imposed, and it is chosen after omega, shared by both arms. The theorem asserts neither a uniform event over all subsequences nor a matrix-operator-norm convergence statement.

## SAP.P002a.T10

For P=C4 and S={0,1}, Theta(P;0,1/2,1), beta_P=2, and S in A(P). The treated within-arm mean squared deviation of Q(P,2,S) is 0. With M=bar(Y_i(D_i(1))) and dbar=bar(D_i(1)), the expression bar(v_1(2)²)_S−[bar(W_1(2))_S−M−2dbar]² is −24; E_P([bar(W_1(2))_T−M−2dbar]²)=49/3; and n0/[2·4·(4−1)] sum_i v_1i(2)²=1/3.

The following corrected evaluations also hold for this same P,S: S_1²(P,2)>0 and equals 1/12; M=2; dbar=1; bar(W_1(2))_S=−1; bar(v_1(2)²)_S=1; bar(W_1(2))_S−M−2dbar=−5; bar(W_1(2))_S−M+2dbar=−1; bar(v_1(2)²)_S−[bar(W_1(2))_S−M+2dbar]²=0; and E_P([bar(W_1(2))_T−M+2dbar]²)=1/3. These are explicit numerical assertions, not universal corrected identities (those occur in T11).

## SAP.P002a.T11

Three conjuncts:

1. For every n, population P, valid-design proof, real beta, subset S and proof S in A(P), let M=bar(Y_i(D_i(1))) and dbar=bar(D_i(1)). Then

       bar((Q(P,beta,S)−m_1(Q(P,beta,S),S))²)_S
       = bar(v_1(beta)²)_S − [bar(W_1(beta))_S−M+beta dbar]²,

   and E_P([bar(W_1(beta))_T−M+beta dbar]²)=n0/[n1 n(n−1)] sum_i v_1i(beta)². No monotonicity, LATE equality, or moment condition is assumed here.
2. For every n,P with valid design, every real beta, and S_1²(P,beta)>0, the expectation of [bar(W_1(beta))_T−M+beta dbar]²/S_1² equals n0/[n1 n(n−1)] times (sum_i v_1i(beta)²)/S_1².
3. For every strictly increasing sizes, population sequence P_j, and reals delta,r,A, assume delta<1, 0<r≤1/2, A>0, Theta(P_j;delta,r,A) and S_1²(P_j,beta_{P_j})>0 for every j. Define f_j to be the expectation in part 2 with beta=beta_{P_j}. Then f_j=O(n0_j/(n1_j sizes(j))) and f_j→0. The constant is allowed to depend on the supplied sequence and parameters.

## SAP.P002a.T12

For P=B_4 and S={0,1,2,3}: Theta(P;0,1/2,1), beta_P=0, S in A(P), |A(P)|=70, and the treated-minus-control mean of q=Q(P,0,S) is −2. Var_P(R_P(q,·))=1/28. The quantity [p²(1−p)²/(8−1)](n0 n1/8)[m_1(q,S)−m_0(q,S)]² equals 1/14 and is strictly greater than that variance. Dropping the factor n0 n1/8 gives exactly 1/28.

## SAP.P002a.T13

For every n, population P with valid design, arbitrary real vector q, subset S in A(P), real r with 0<r≤1/2, and balance bounds rn≤n1≤(1−r)n, both inequalities hold:

    [p²(1−p)²/(n−1)] [m_1(q,S)−m_0(q,S)]² ≤ Var_P(R_P(q,·)),
    [r²(1−r)²/n] [m_1(q,S)−m_0(q,S)]² ≤ Var_P(R_P(q,·)).

The same **fixed** q is used at every reassignment in the variance. No outcome or receipt hypotheses, or positivity of that variance, are imposed.

## SAP.P002a.T14

For every m≥2, P=B_m satisfies Theta(P;0,1/2,1) and beta_P=0. For every S in A(P), fix q=Q(P,0,S). Then Var_P(R_P(q,·))=1/[4(2m−1)], Pr_P(T:|sqrt(H_P(q,T))/Var_P(R_P(q,·))−1|≥1/2)=1, and **for every real kappa>0**,

    Pr_P(T:|H_P(q,T)/Var_P(R_P(q,·))−1|≥kappa) ≤ 2/(2m kappa).

In addition, for P=B_{j+2} and q_i=Y_i(0), the square-root-over-variance error probability just displayed tends to 1 as j tends to infinity. There is no separately asserted limit-zero conclusion for the variance-over-variance probabilities.

## SAP.P002a.T15

For every type Omega with measurable space, every probability measure mu, strictly increasing sizes, populations P_j, maps Z_j, and reals delta,r,A, assume delta<1, 0<r≤1/2, A>0, Theta(P_j;delta,r,A) at every j; V(W_a(P_j,beta_{P_j}))>0 for **every j and both arms**; and RandomizationSequence(P,mu,Z). Then for every fixed strictly increasing sub, additionally assume **for every j and every omega** (including any null exceptional vectors) that

    Var_{P_j}(T ↦ R_{P_j}(Q(P_j,beta_{P_j},Z_j(omega)),T)) > 0.

For mu-almost every omega, **for every real kappa>0**, the following tends to zero as j tends to infinity: put N=sub(j), q=Q(P_N,beta_{P_N},Z_N(omega)), and compute

    Pr_{P_N}(S: |H_{P_N}(q,S)/Var_{P_N}(R_{P_N}(q,·))−1|≥kappa).

The outer a.e. quantifier is inside the choice of the fixed subsequence and outside all positive tolerances. No independence of the Z_j is assumed. The strictly positive denominators are hypotheses, not conclusions or consequences asserted by this theorem.

## Mathlib trace

The finite-subset interpretation follows `Data/Finset/Powerset.lean` (`powersetCard`, `mem_powersetCard`). Ordinary finite sums, Bool membership decisions, finite dot products and nonsingular inverses are used; see `LinearAlgebra/Matrix/NonsingularInverse.lean` (`inv_def`). The real square-root definition is `Analysis/Real/Sqrt.lean` (including `sqrt_eq_zero_of_nonpos`). Extended nonnegative numbers and `ofReal` are imported by `Data/ENNReal/Basic.lean` from `Basic/ENNReal/Basic.lean`. The filter reading follows `Order/Filter/Defs.lean` (`Tendsto`) and `Order/LiminfLimsup.lean` (`limsSup`, `limsup`, and their generated order-dual liminf definitions). Big-O is expanded in `Analysis/Asymptotics/Defs.lean` (`isBigO_iff`). Almost-everywhere is the conull filter in `MeasureTheory/OuterMeasure/AE.lean`; probability-measure normalization is `MeasureTheory/Measure/Typeclasses/Probability.lean` (`IsProbabilityMeasure`). All statistical moments, parameter classes, randomization probabilities, quantiles, and regressions used above are the explicit SAP definitions expanded in this file, with no additional imported notion substituted for them.
