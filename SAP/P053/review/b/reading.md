# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. Sources at this stage are only
`SAP/P053/Defs*.lean`, `SAP/P053/Defs/*.lean`, `SAP/P053/Challenge*.lean`,
`SAP/P053/Challenge/*.lean`, and the relevant Mathlib definitions. There are eight
theorems, `SAP.P053.T1` through `SAP.P053.T8`; their bodies are `sorry` stubs.
The following records statements, not an inference from their names or comments.

## Common definitions and conventions

For a finite labelled population I, `support k` is the set Ω_k of all k-element
subsets of I. Mathlib `Finset.mem_powersetCard` says precisely that membership is
subsethood and cardinality k; its cardinality is binomial(|I|, k).
Complements are in the entire finite population, not another assignment space.
Every assignment in Ω_k has equal probability. For a Boolean outcome vector y,
a_y(z) is the number of true entries in z, and M_y is the number in I. Boolean
true and false represent 1 and 0. Define

* C(n1,n0,M,a) = (a, n1-a, M-a, n0-M+a), with all four entries integers.
* D_y(z) = a_y(z)/n1 - (M_y-a_y(z))/n0, a real number.
* R(n1,n0,M,t) = (n1 n0 t + n1 M)/(n1+n0).
* For h: Z^4 → S, G_h(t) = h(b,n1-b,M-b,n0-M+b), where
  b = floor(R(n1,n0,M,t)) is the greatest integer no larger than R.
* c(n,a): {0,...,n-1} → {false,true} is true exactly on labels less than a.
* The ordered sample on z, with a certificate |z|=n, lists its outcomes in
  increasing unit-label order. Mathlib `orderEmbOfFin` is the increasing bijection
  from {0,...,n-1} onto z. This is not sampling with replacement.
* For any real-valued assignment statistic T, U_k(T,z) is
  |{w in Ω_k : T(z) ≤ T(w)}|/|Ω_k|. Ties are included, and this is an upper tail.

The population structure P has natural-number arm sizes n1,n0, total N=n1+n0,
and two fixed real vectors Y1,Y0 on {0,...,N-1}. For any finite set A and vector y,

    mean_A(y) = sum_{i in A} y_i / |A|,
    SS_A(y) = sum_{i in A} (y_i-mean_A(y))^2,
    s_A^2(y) = SS_A(y)/(|A|-1).

Population mean and variance use the full set: bar(y), S_P^2(y). Set
tau_P=bar(Y1)-bar(Y0), d_i=Y1_i-Y0_i. `SharpNull P` is Y1_i=Y0_i
for every i. `ConstantEffects P` is d_i=tau_P for every i.
For an assignment z, Yobs_i(z)=Y1_i for i in z and Y0_i otherwise, and
hat(tau)_P(z)=mean_z(Yobs)-mean_{z^c}(Yobs).
For an assignment function X, E_P X is its uniform average over Ω_n1,
Var_P X=E_P[(X-E_P X)^2], and Pr_P(A) is the proportion of Ω_n1 in A.
The randomization variance uses this full-distribution divisor, not a sample
variance divisor |Ω_n1|-1.

The three variance estimators are

    V_O(P,z) = [SS_z(Yobs)+SS_{z^c}(Yobs)]/(N-2) * (1/n1+1/n0),
    V_N(P,z) = s_z^2(Yobs)/n1 + s_{z^c}^2(Yobs)/n0,
    V_F(P,z) = N*S_P^2(Yobs)/(n1*n0).

For a sequence E_k of such populations, write N_k, n1_k, n0_k, tau_k,
S1_k^2=S_{E_k}^2(Y1), S0_k^2=S_{E_k}^2(Y0), and
St_k^2=S_{E_k}^2(d). `Regularity E p v1 v0 vt tauInf` is the conjunction of
all the following hypotheses, with no stochastic conclusion among them:

1. N_k → infinity as k→infinity, in the natural-number order.
2. Eventually n1_k≥2 and n0_k≥2.
3. 0<p<1, and n1_k/N_k → p in R.
4. S1_k^2→v1, S0_k^2→v0, St_k^2→vt, and tau_k→tauInf in R.
5. There exists a real B≥0 such that for every k,
   (1/N_k) sum_i (Y1_{ki}^4+Y0_{ki}^4) ≤ B.

All limits along k are along the ordinary cofinite tail of the natural numbers.
For assignment functions X_k, `InProbability E X c` means: for every real
epsilon>0, Pr_{E_k}(|X_k-c|>epsilon)→0. Write X_k=o_p(1/N_k) for
`LittleOInvSize E X`, which is exactly N_k X_k→0 in this sense. Thus the
asymptotic probability spaces are the finite uniform assignment spaces for
each k, not a random model for potential outcomes.
Define

    L_N(p,v1,v0)=v1/p+v0/(1-p),
    L_O(p,v1,v0)=v1/(1-p)+v0/p.

Phi(t) is the real value of the measure of (-infinity,t] under Mathlib
`ProbabilityTheory.gaussianReal 0 1`, whose second argument is variance.
Mathlib defines this as the Gaussian density measure (Dirac only at variance
zero) and supplies `IsProbabilityMeasure`; consequently its `ENNReal.toReal`
conversion is a conversion of a finite probability. q_alpha is
inf{t in R : 1-alpha/2 ≤ Phi(t)}. It is used only for 0<alpha<1.
`Real.sqrt` is the nonnegative square root on nonnegative arguments and is
zero on negative arguments.

Lean real division is total, with x/0=0. All differences in the displayed
sample-variance divisors are real subtraction. The table uses integer
subtraction. Natural subtraction appears in the canonical control-success
count M_y-a_y(z); for assignments in this file a_y(z)≤M_y, so it is the actual
nonnegative difference. The generic support/probability functions are total
even at impossible sample sizes, but in every finite asserted example the
support is nonempty. The asymptotic hypotheses give ordinary positive arm and
residual divisors eventually. Early indices may have zero-size arms or total
size. The studentized conclusions of T6 separately impose eventual positivity
at every assignment, as detailed below.

## T1: `SAP.P053.T1`

For every type S (without any nonemptiness or other structure), for every pair
of natural numbers n1,n0 with n1>0 and n0>0, and then for every Boolean vector
y on n1+n0 labelled units, the following conjunction holds. The S parameter
is universally quantified outside the arm sizes and vector.

1. For every z in Ω_n1,

       D_y(z)=((n1+n0)*a_y(z)-n1*M_y)/(n1*n0),
       R(n1,n0,M_y,D_y(z))=a_y(z).

2. For every z,w in Ω_n1, both

       D_y(z)=D_y(w) iff a_y(z)=a_y(w),
       a_y(z)=a_y(w) iff C(n1,n0,M_y,a_y(z))=C(n1,n0,M_y,a_y(w)).

3. For every h:Z^4→S, there exists g:R→S, equal as a function to the explicit
   G_h above with M=M_y, such that for every Boolean vector yy on the same
   units with M_yy=M_y, and then every z in Ω_n1,

       h(C(n1,n0,M_y,a_yy(z)))=g(D_yy(z)).

   Thus one g is chosen before yy and works uniformly at the fixed total M.
4. For every F:({0,...,n1-1}→Bool)→({0,...,n0-1}→Bool)→S, if for every
   pair x1,x0 and every separate permutation pi1,pi0 of the respective index
   sets F(x1∘pi1,x0∘pi0)=F(x1,x0), then there exists g:R→S such that for
   every subset z and every proof of z in Ω_n1, there exist cardinality
   certificates |z|=n1 and |z^c|=n0 for which

       F(ordered_y(z),ordered_y(z^c))
         =F(c(n1,a_y(z)),c(n0,M_y-a_y(z)))
         =g(D_y(z)).

   This g may depend on y, F and the arm sizes, and is chosen before z.
5. For every h:Z^4→S, every Boolean sample pair x1,x0 and every separate
   permutation pi1,pi0, h evaluated on the four success/failure counts of
   (x1∘pi1,x0∘pi0) equals h evaluated on those of (x1,x0).
6. For every function T from the subtype of n1-element subsets to S,

       (there exists g:R→S such that for every z, T(z)=g(D_y(z)))
       iff
       (for every z,w, equality of their four-count tables implies T(z)=T(w)).

No outcomes under an alternative, fixed covariates, or labels are arguments
of a table function h. The original label-indexed y is fixed before the
factorization assertions, except for the explicit uniformity in item 3.

## T2: `SAP.P053.T2`

This is an unconditional conjunction of four components.

1. On units 0,1,2,3 take y=(1,1,0,0), x=(1,0,1,0), A={0,2}, B={1,2},
   arm sizes 2,2, and L(z)=1 if 0 is treated, 0 otherwise. Then |Ω_2|=6,
   A,B belong to Ω_2, D_y(A)=D_y(B)=0, both tables equal (1,1,1,1),
   L(A)=1, L(B)=0, D_{xy}(A)=1/2 and D_{xy}(B)=-1/2. Here xy is Boolean
   conjunction, the binary product of x and y.
2. There does not exist g:R→R with L(z)=g(D_y(z)) for every z in Ω_2;
   and there does not exist such a g with D_{xy}(z)=g(D_y(z)) for every z.
   These are two separate nonexistence statements.
3. For every natural m>0 (and every proof of m>0), repeat the four units on
   I_m={0,...,m-1}×{0,1,2,3}, with y_m(j,i)=y(i), x_m(j,i)=x(i),
   A_m={0,...,m-1}×A, B_m={0,...,m-1}×B, and
   L_m(z)=1 if (0,0) is treated, 0 otherwise. Then both assignments have
   size 2m, D_{y_m}(A_m)=D_{y_m}(B_m)=0, both tables are (m,m,m,m),
   L_m(A_m)=1, L_m(B_m)=0, D_{x_my_m}(A_m)=1/2,
   D_{x_my_m}(B_m)=-1/2, (2m)/(4m)=1/2, M_{y_m}/(4m)=1/2.
   Separately, neither L_m nor D_{x_my_m} is any real function of D_{y_m}
   on the entire support of assignments of size 2m.
4. With m=k+1, population size 4(k+1)→infinity, treatment fraction tends
   to 1/2, success fraction tends to 1/2, and for every k

       (1/(4(k+1))) sum_{i in I_{k+1}} (y_{k+1,i}^4+y_{k+1,i}^4) ≤ 2.

   The last formula uses the real binary coding, and repeats the same outcome
   twice. There is no `Regularity` predicate, population/effect-variance
   convergence or average-effect convergence in this component.

## T3: `SAP.P053.T3`

This is an unconditional conjunction of finite examples and one universally
quantified invariance statement.

1. On six units with y=(1,1,1,0,0,0) and arm sizes 3,3, the numbers of
   assignments with treated success count 0,1,2,3 are respectively 1,9,9,1.
   For every supported z, D_y(z)=(2a_y(z)-3)/3.
2. There are 20 assignments. At z={0,1,2}, which is supported,
   D_y(z)=1, U_3(D_y,z)=1/20 and U_3(|D_y|,z)=1/10.
   The first p-value is ≤1/20; the second is not ≤1/20.
3. On four units with y=(1,1,0,0) and arm sizes 2,2 there are six assignments.
   Top={0,1} and Bottom={2,3} are supported, D_y(Top)=1,
   D_y(Bottom)=-1. The signed and absolute upper-tail p-values at Top are
   1/6 and 1/3 respectively; at Bottom they are 1 and 1/3 respectively.
   At every supported z different from both, D_y(z)=0 and the corresponding
   signed and absolute p-values are 5/6 and 1 respectively.
4. For every natural n1,n0>0, every real outcome vector y on n1+n0 units,
   and every function g:R→R, let T(z)=mean_z(y)-mean_{z^c}(y). If g is
   strictly increasing on the attainable set {T(z):z in Ω_n1}, meaning
   a<b in that set implies g(a)<g(b), then for every z in Ω_n1,
   U_n1(g∘T,z)=U_n1(T,z). No monotonicity outside the attainable set is required.

## T4: `SAP.P053.T4`

For every real p,S1,S0, in that order, if 0<p<1 and S1,S0≥0, then

    (S0^2/p+S1^2/(1-p))-(S1^2/p+S0^2/(1-p))
      =((S1^2-S0^2)*(2p-1))/(p(1-p)),

and

    S1^2/p+S0^2/(1-p) < S0^2/p+S1^2/(1-p)
      iff (p>1/2 and S1>S0) or (p<1/2 and S1<S0).

These are deterministic algebraic statements, with no sequence or probability
hypotheses. S1 and S0 themselves, rather than their squares, are nonnegative.

## T5: `SAP.P053.T5`

For every sequence E:N→Population and then all real p,v1,v0,vt,tauInf,
if `Regularity E p v1 v0 vt tauInf`, all five statements below hold, under
the finite uniform randomization law at each k:

1. V_F(E_k,z) - [S1_k^2/n0_k + S0_k^2/n1_k + tau_k^2/N_k]
   =o_p(1/N_k).
2. V_O(E_k,z) - [S1_k^2/n0_k + S0_k^2/n1_k]=o_p(1/N_k).
3. N_k(V_F(E_k,z)-V_O(E_k,z))-tau_k^2→0 in probability.
4. N_k V_F(E_k,z)→L_O(p,v1,v0)+tauInf^2 in probability.
5. N_k V_O(E_k,z)→L_O(p,v1,v0) in probability.

No positivity of v1,v0,vt or the limiting estimator coefficient is an additional
hypothesis. vt is part of regularity but is not an argument used on the right
side of these five conclusions.

## T6: `SAP.P053.T6`

For every E and then every real p,v1,v0,vt,tauInf satisfying `Regularity`,
the following three implications all hold. Their additional antecedents are
local to the indicated component, not assumed for every component.

1. If tau_k→0, then V_F-V_O=o_p(1/N_k); and, if additionally
   L_O(p,v1,v0)>0 and `PositiveOLS E`, then V_F/V_O→1 in probability.
2. If `ConstantEffects (E_k)` for every k, then
   V_O(E_k,z)-Var_{E_k}(hat(tau)_{E_k})=o_p(1/N_k), and

       N_k(V_F(E_k,z)-Var_{E_k}(hat(tau)_{E_k}))-tau_k^2→0

   in probability.
3. If `SharpNull (E_k)` for every k, v0>0, and `PositiveOLS E`, then

       for every real t,
       Pr_{E_k}(hat(tau)(z)/sqrt(V_O(E_k,z)) ≤ t)→Phi(t);

   and for every real alpha with 0<alpha<1,

       Pr_{E_k}(q_alpha < |hat(tau)(z)|/sqrt(V_O(E_k,z)))→alpha.

Here `PositiveOLS E` means there exists an index K such that for every k≥K
and every z in Ω_{n1_k}, V_O(E_k,z)>0. This is uniform eventual positivity
over *all* supported assignments. It is stronger than positivity with
probability tending to one. No conditional permutation-distribution,
permutation-quantile, permutation-p-value or FRT-versus-Wald rejection-event
assertion occurs in this theorem.

## T7: `SAP.P053.T7`

For every E and then every real p,sigma1,sigma0,vt,tauInf, if sigma1≥0,
sigma0≥0 and `Regularity E p (sigma1^2) (sigma0^2) vt tauInf`, set
v1=sigma1^2 and v0=sigma0^2. The following conjunction holds:

1. V_N(E_k,z)-[S1_k^2/n1_k+S0_k^2/n0_k]=o_p(1/N_k).
2. V_O-V_N - [(S1_k^2/n0_k+S0_k^2/n1_k)
   -(S1_k^2/n1_k+S0_k^2/n0_k)]=o_p(1/N_k).
3. N_k V_O→L_O(p,v1,v0) and N_k V_N→L_N(p,v1,v0) in probability.
4. L_O-L_N=((v1-v0)*(2p-1))/(p(1-p)).
5. If L_O≠L_N, then v1≠v0 and p≠1/2.
6. If L_O≠L_N, then sigma1≠sigma0 and p≠1/2.
7. If tau_k→0, then

       V_F-V_N - [(S1_k^2/n0_k+S0_k^2/n1_k)
         -(S1_k^2/n1_k+S0_k^2/n0_k)]=o_p(1/N_k),
       N_k V_F→L_O(p,v1,v0),
       N_k V_N→L_N(p,v1,v0)

   in probability. There is no rate stronger than tau_k→0 in this antecedent.

## T8: `SAP.P053.T8`

The statement is a conjunction with a universally quantified regular-population
part, a finite formula for every natural k, an explicit asymptotic witness,
and a final scalar inequality.

A. For every E and all real p,v1,v0,vt,tauInf satisfying `Regularity`,

1. N_k Var_{E_k}(hat(tau))→L_N(p,v1,v0)-vt;
2. L_N(p,v1,v0)-vt≤L_N(p,v1,v0);
3. N_k V_N→L_N(p,v1,v0) in probability.

If, in addition, every E_k has constant effects, then all of the following hold:

4. For every k, S1_k^2=S0_k^2 and St_k^2=0;
5. v1=v0 and vt=0;
6. N_k Var_{E_k}(hat(tau))→L_N(p,v1,v0);
7. L_N(p,v1,v0)=L_O(p,v1,v0);
8. V_O-V_N=o_p(1/N_k);
9. For every k, sqrt(S1_k^2)=sqrt(S0_k^2) and sqrt(St_k^2)=0.

B. For every natural k, put r=k+1, N=10r, n1=2r, n0=8r, set Y0_i=1
for the first 5r labels and -1 for the remaining 5r, and Y1_i=2Y0_i.
For this specific population P_k all these exact finite statements hold:

    tau_k=0,
    S0_k^2=N/(N-1),
    S1_k^2=4N/(N-1),
    St_k^2=N/(N-1),
    Var_{P_k}(hat(tau))=81/(4(N-1)),
    S1_k^2/n0+S0_k^2/n1=10/(N-1),
    S1_k^2/n1+S0_k^2/n0=85/(4(N-1)),
    10/(N-1)<Var_{P_k}(hat(tau)).

C. This sequence satisfies `Regularity heterogeneousWitness (1/5) 4 1 1 0`;
tau_k=0 for every k; N_k Var_{P_k}(hat(tau))→81/4;
N_k V_O→10 in probability; L_O(1/5,4,1)=10;
L_N(1/5,4,1)=85/4; and 10<81/4.

D. Finally 81/4<85/4. This explicitly witnesses a zero-average-effect sequence
with heterogeneous unit effects and an OLS variance coefficient below the
actual coefficient, which is itself below the Neyman coefficient.

## Mathlib definition checks made during this stage

* `Data/Finset/Powerset.lean`: `powersetCard`, `mem_powersetCard`,
  `card_powersetCard` establish the exact finite assignment space.
* `Data/Finset/Sort.lean`: `orderIsoOfFin`, `orderEmbOfFin` establish that
  ordered samples enumerate each selected unit exactly once in increasing order.
* `Order/Monotone/Defs.lean`: `StrictMonoOn` has the pairwise meaning used in T3.
* `Algebra/Order/Floor/Defs.lean`: `Int.floor` is the usual greatest-integer floor.
* `Probability/Distributions/Gaussian/Real.lean`: `gaussianReal` uses a variance
  parameter, and its probability-measure instance makes CDF values finite.
* `Analysis/Real/Sqrt.lean`: `Real.sqrt` uses `Real.toNNReal`, with value zero
  on nonpositive inputs; the T6 positivity antecedent prevents that issue
  eventually on every assignment used in its studentized conclusions.
* `Order/Filter/Defs.lean` and `Order/Filter/AtTopBot/Defs.lean`: `Tendsto` is
  the filter limit, and `atTop` on N is the ordinary eventual-tail filter.
* `Algebra/GroupWithZero/Basic.lean`: `div_zero` confirms the total-division
  convention, whose possible uses have been identified above.
