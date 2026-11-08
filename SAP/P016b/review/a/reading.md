# Blind mathematical reading

This file was written from `SAP/P016b/Defs*.lean`, `SAP/P016b/Defs/Part*.lean`, and `SAP/P016b/Challenge*.lean` before opening `claims.json` or `record.json`. The ten Challenge theorems have no explicit arguments: each asserts the closed proposition named `T12Statement`, ..., `T21Statement`. All quantifiers below come from expanding those propositions and their auxiliary definitions.

## Common definitions and conventions

* An outcome on n units is an arbitrary vector in R^n, indexed by `Fin n` (indices 0,...,n-1). An assignment z is a vector of Booleans. Write z_i=1 for true (treated), z_i=0 for false (control); `bit` is the corresponding real 0 or 1.
* N_g(z) counts units in group g; S_g(u,z) sums their outcomes; M_g(u,z)=S_g(u,z)/N_g(z). The pooled mean is bar(u)=sum_i u_i/n. The mean contrast is D(u,z)=M_1(u,z)-M_0(u,z). TSS(u)=sum_i (u_i-bar(u))^2 and RSS(u,z)=sum_i (u_i-M_{z_i}(u,z))^2.
* F_g(u,z;x)=#{i:z_i=g and u_i<=x}/N_g(z). F(u;x)=#{i:u_i<=x}/n. KS(u,z)=max({0} union {|F_1(u,z;u_i)-F_0(u,z;u_i)|:i<n}); signedKS uses the differences without absolute values. These are finite maxima evaluated at the observed outcome coordinates.
* All divisions above are real divisions, with Lean's total convention x/0=0. Thus means and ECDFs of empty groups, and the pooled mean of an empty sample, are defined as zero. A statement below excludes these extensions only where its hypotheses explicitly do so.
* Additive generation and adjustment are G_t(y,z)_i=y_i+z_i*t and A_t(Y,z)_i=Y_i-z_i*t. Multiplicative generation and adjustment are H_a(y,z)_i=y_i*(1+z_i*(a-1)) and C_a(Y,z)_i=Y_i/(1+z_i*(a-1)); on treated units these are a*y_i and Y_i/a, and on controls they are y_i and Y_i. The discrepancy is d(y,z;t,a)_i=|H_a(y,z)_i-G_t(y,z)_i|.
* B(n,m) is the finite subtype of all Boolean assignments on n units with N_1=m. No probability distribution is part of this subtype itself. `complete4` lists assignments with treated pairs (0,1),(0,2),(0,3),(1,2),(1,3),(2,3), in that order; u4=(0,1,2,3).
* EIG(T) (`EffectIncreasingOnGroups`) means: for every assignment z with N_0(z)>0 and N_1(z)>0, and then every pair y,y', if y_i<=y'_i for all treated i and y'_i<=y_i for all controls, then T(y,z)<=T(y',z). The separately defined unrestricted `EffectIncreasing` does not occur in these theorem propositions.
* For v on 2m units, med(v) is obtained by listing v_0,...,v_(2m-1), sorting in nondecreasing real order, and averaging entries at zero-based positions m-1 and m. The underlying `List.getD` returns zero for a missing position; natural subtraction m-1 is truncated. Consequently med on m=0 is zero by defaults, but every use in these statements has m>0 or m=128, so both positions exist and are the ordinary two middle order statistics.
* A finite law P on a finite type Omega consists of real weights p_z>=0 with sum_z p_z=1. Zero-weight points are allowed by this structure. Its mass of E is sum_{z in E} p_z. These constraints themselves rule out an empty Omega. U_Omega is the uniform law p_z=1/|Omega|, defined only with an explicit nonempty-type instance. The separately defined uniform mass and expectation are #{z:E(z)}/|Omega| and sum_z f(z)/|Omega|, with total real division if the type is empty.
* For a real score s on Omega, U_P(s,z)=P{s(w)>=s(z)} and L_P(s,z)=P{s(w)<=s(z)} are inclusive exact tails. Write Q(L,U)=min(1,2*min(L,U)). `ExactValidity` (abbreviated V below) is the following closed proposition: for every finite type Omega, every finite law P on it, **if every p_z>0**, then for every score s and every real alpha with 0<=alpha<=1, each of the six masses P{U_P<=alpha}, P{L_P<=alpha}, P{Q(L_P,U_P)<=alpha}, P{U_P<alpha}, P{L_P<alpha}, P{Q(L_P,U_P)<alpha} is <=alpha. This assertion does not quantify over zero-weight finite laws in its conclusion.
* Given B references r_1,...,r_B and observation o, L_B=#{b:r_b<=o}, U_B=#{b:o<=r_b}, and p_raw=Q(L_B/B,U_B/B). `ReferenceVector B` is a vector t=(t_0,...,t_B) of B+1 real statistics. References are t_1,...,t_B and t_0 is observed. The corrected tails are L_plus=(1+#{b=1,...,B:t_b<=t_0})/(B+1) and U_plus=(1+#{b=1,...,B:t_0<=t_b})/(B+1).
* A probability measure mu on R^(B+1) is exchangeable here if for every permutation pi of the coordinate indices, the pushforward under t -> (t_(pi(i)))_i is mu. The function spaces use the ordinary product measurable structure on real coordinates; these coordinate permutations are measurable. `IsProbabilityMeasure` means mu(universe)=1. `mu.real(E)` is `(mu(E)).toReal`, the real value of its nonnegative-extended-real measure. Since mu is a probability, no infinite-measure-to-zero convention is used here. All comparison/count events in these statements are measurable finite combinations of real inequalities. Almost-everywhere injectivity of t means that, outside a null set, its B+1 coordinates are pairwise distinct.
* iidMass(P,m,E)=sum_{draw:Fin m -> Omega, E(draw)} product_i p_(draw_i); it is the probability of E under m independent P-draws. This is a finite sum, so no integrability or measurable-score hypothesis is needed. Uniform mass on a finite function type is likewise the uniform distribution over all draw vectors.
* Define

  K(M,B,c) = (2/M) sum_{r=0}^{M-1} sum_{k=0}^c choose(B,k) ((r+1)/M)^k ((M-(r+1))/M)^(B-k).

  This is `binomialMixture`. The exponent B-k is natural truncated subtraction. In the statements using this function, either c<B (or 2c<B), or c is explicitly 0,24,25,249,250 with the indicated B, so k<=c<B and this truncation never changes the intended exponent. The expression M-(r+1) is real subtraction, not natural subtraction. All relevant M are 6435.
* `Nat.floor x` and `Nat.ceil x` are the natural-number floor and ceiling (floor is zero on negative reals). Their arguments in these statements are nonnegative, so these agree with the ordinary integer floor and ceiling. Natural differences B-L_B and B/40-1 below are truncated; the counts are at most B and the specified B are 1000 and 10000, respectively. Natural B/40 is integer quotient.
* For a real matrix S on n units, h_i(S,z)=sum_j z_j*S_(j,i), a column-indexed treated-neighbor sum. Put

  f_i(S,beta,tau;z)=beta+(1-z_i)*(1-beta)*exp(-tau^2*h_i(S,z)).

  The model map is F_(z->w)(y)_i=f_i(w)/f_i(z)*y_i. No symmetry, diagonal, or sparsity condition belongs to this definition itself.

## Mathlib grounding

The SAP definitions reduce to finite sums (`Finset.univ`), finite types/subtypes, ordinary real field/order/absolute value/exponential operations, finite lists, finite products, and probability measures. I checked `Mathlib/Algebra/Order/Floor/Defs.lean` for the natural floor/ceiling and their order laws; `Mathlib/MeasureTheory/Measure/Real.lean` for real-valued measure; `Mathlib/MeasureTheory/Measure/Map.lean` for pushforwards; `Mathlib/MeasureTheory/OuterMeasure/AE.lean` for the null-complement interpretation of almost everywhere; and `Mathlib/Data/List/Sort.lean` and `OfFn.lean` for the sorted-list and enumeration semantics. Core list indexing, sorting, folds, and Boolean/Fin syntax retain their ordinary meanings. `sInf` in T19 is the real infimum of the explicitly specified set; that set is nonempty finite and bounded below under the stated m>0 and N_1=m hypotheses, hence this is an attained minimum, not an empty/unbounded infimum convention.

## SAP.P016b.T12

This is the conjunction of the following independent assertions, in order:

1. For every natural n, EIG(D on n units).
2. EIG(KS on 4 units) is false, and EIG(signedKS on 4 units) is false. Each negation requires a counterexample with both groups nonempty.
3. V, the exact validity proposition above, including its strictly-positive-weight hypothesis.
4. For every k=0,...,5, the inclusive upper exact tail of KS(u4,complete4(k)), using the uniform law on these six assignments, is respectively (1/3,1,1,1,1,1/3).
5. For every real alpha, if 0<=alpha<=1, the mass under that same uniform design of assignments whose upper KS tail is <=alpha is 0 when alpha<1/3, is 1/3 when 1/3<=alpha<1, and is 1 when alpha=1.

There is no displayed raw KS-value table in the proposition.

## SAP.P016b.T13

This is a conjunction of the following assertions.

1. (`NoTiesRawLaw`.) For every natural B>0, every probability measure mu on R^(B+1), if mu is exchangeable and its vectors are almost surely injective, then for every real alpha with 0<=alpha<1 and every natural c satisfying c=floor(alpha*B/2) and 2c<B:
   * for every k in {0,...,B}, the probability that #{b=1,...,B:t_b<t_0}=k is 1/(B+1);
   * almost surely L_B=#{b:t_b<t_0} and U_B=B-L_B;
   * P_mu{p_raw<=alpha}=2(c+1)/(B+1).
   The rank and count assertions are syntactically inside the alpha,c hypotheses, even though their conclusions do not depend on alpha,c.
2. For every probability mu on R^1001, exchangeability and almost-sure injectivity imply P{p_raw<=1/20}=4/77 and 1/20<P{p_raw<=1/20}.
3. For every probability mu on R^10001, the same two hypotheses imply P{p_raw<=1/20}=502/10001 and 1/20<P{p_raw<=1/20}.
4. (`PowerTwoDesign`.) Set y_i=2^i for i=0,...,15. Then |B(16,8)|=12870, sum y_i=65535, sum y_i^2=1431655765; for every z in B(16,8),

   RSS(y,z)=1431655765-[S_1(y,z)^2+(65535-S_1(y,z))^2]/8.

   The image set of RSS over this design has cardinality 6435. For every ordered pair z,w in B(16,8), RSS(y,z)=RSS(y,w) if and only if z=w or z is the coordinatewise Boolean complement of w.
5. (`PowerTwoSampled`.) Retain that y and design. All draw vectors below are uniformly distributed in the indicated finite function type, so the observed assignment and every reference are fresh independent uniform draws with replacement.
   * For every natural B>0 and natural c with 2c<B, the probability, over B+1 assignments, of L_B<=c or U_B<=c for the score RSS(y,draw_i) is K(6435,B,c).
   * For every natural B,c with B>0 and c<B, 2(c+1)/(B+1)-2/6435 <= K(6435,B,c) <= 2(c+1)/(B+1). This bound does not additionally require 2c<B.
   * For each B in {1000,10000}, P{p_raw<=1/20}=K(6435,B,B/40) and P{p_raw<1/20}=K(6435,B,B/40-1).
   * Both K(6435,1000,25) and K(6435,10000,250) are >1/20. Both K(6435,1000,24) and K(6435,10000,249) are <1/20.
   * For every natural B>0, P{p_raw=0}=K(6435,B,0), and this equals

     2 sum_{r=0}^{6433}(6434-r)^B / 6435^(B+1),

     and is strictly positive.
6. The numerical identities (4/77)-2/6435=2326/45045 and 1/20<2326/45045.

## SAP.P016b.T14

The conjunction asserts:

1. For every natural B>0 and every probability mu on R^(B+1), exchangeability alone implies all of:
   * for every natural c<=B, P{L_B<=c}<=(c+1)/(B+1) and P{U_B<=c}<=(c+1)/(B+1);
   * for every real alpha with 0<alpha<1, P{p_raw<alpha}<=2*ceil(alpha*B/2)/(B+1);
   * for every real alpha with 0<=alpha<=1, P{L_plus<=alpha}<=floor(alpha*(B+1))/(B+1), the same bound holds for U_plus, this right-hand side is <=alpha, and P{Q(L_plus,U_plus)<=alpha}<=alpha.
   There is no no-ties hypothesis in any of these implications.
2. For every exchangeable probability on R^1001, P{p_raw<1/20}<=50/1001. For every exchangeable probability on R^10001 the bound is 500/10001. Both bounds are strictly less than 1/20.
3. For every finite type Omega, every finite law P, every natural B (including zero), every real score s on Omega, every permutation pi of {0,...,B}, and every predicate E on R^(B+1), the iid mass of E((s(draw_(pi(i))))_i) equals the iid mass of E((s(draw_i))_i). This is an equality of finite sums for arbitrary predicates, with zero-weight points allowed.
4. V, including its requirement that all represented points have strictly positive weight.

## SAP.P016b.T15

This is a conjunction of explicit local identities and a parameter-diagonal assertion:

1. For Y=(9,11,10,12) and z=(0,0,1,1), A_(1/2)(Y,z)=(9,11,19/2,23/2), C_2(Y,z)=(9,11,5,6), F_1(A_(1/2)(Y,z),z;6)=0, and F_1(C_2(Y,z),z;6)=1.
2. F((1,3);2)=1/2 and F((1,3);3)=1.
3. For every real t and then every real b, (there exists real t0 with t=t0 and b=t0) if and only if b=t.
4. There does not exist a real t0 with 1/2=t0 and 2=t0.

## SAP.P016b.T16

This conjunction says:

1. For every n, every outcome Y, every assignment z, every index i, and every real t,t',a,a', if a!=0 and a'!=0, then:
   * if z_i=0, A_t(Y,z)_i=Y_i and C_a(Y,z)_i=Y_i;
   * if z_i=1, A_t(Y,z)_i=Y_i-t and C_a(Y,z)_i=Y_i/a; additionally, t!=t' implies A_t(Y,z)_i!=A_t'(Y,z)_i, and a!=a' together with Y_i!=0 implies C_a(Y,z)_i!=C_a'(Y,z)_i.
   The two nonzero-multiplier premises scope over even the control and additive conclusions in this clause.
2. For every n,Y,z and real t,a,x, if N_0(z)>0 and a!=0, then both control ECDFs F_0(A_t(Y,z),z;x) and F_0(C_a(Y,z),z;x) equal F_0(Y,z;x).
3. For every natural n>0, every outcome u on n units and real x, F(u;x)=#{i:u_i<=x}/n (the numerator is the cardinality of a filtered finite set).
4. There exist separate real t0,b0 with 1/2=t0 and 2=b0; there is no single real t0 with both equalities.

## SAP.P016b.T17

For every n,Y,z, if N_0(z)>0 and N_1(z)>0, then for every real t, put u=A_t(Y,z). All of the following hold:

* for every i, z_i=1 implies u_i+t=Y_i;
* M_1((u_i+t)_i,z)-M_0(u,z)=D(u,z)+t;
* that same left-hand side equals D(Y,z).

Independently, D(u4,(0,0,1,1))=2, while M_1((u4_i+10)_i,(0,0,1,1))-M_0(u4,(0,0,1,1))=12. Thus the generic algebra compares an imputed-treated group to adjusted controls, and the explicit two-versus-twelve example uses the same underlying vector u4 with and without a treated shift.

## The calibration witness used by T18 and T19

The fixed assignment has indices 0,...,127 in control and 128,...,255 treated. Its fixed vector y is 9 at indices 0,...,63; 11 at 64,...,127; 8 at 128; 9 at 129,...,191; 11 at 192,...,254; and 12 at 255. Set t=34/99, a=413/396, d=d(y,z;t,a).

`CalibrationWitness` (W below) asserts every one of these facts:

* N_0=N_1=128, M_0(y,z)=M_1(y,z)=10, and TSS(y)/256=131/128.
* a=1+t/8.
* For every coordinate i, d_i=0 when i<129; d_i=t/8 when 129<=i<192; d_i=3t/8 when 192<=i<255; and d_255=t/2.
* Exactly 127 treated units have nonzero discrepancy, and med(d)=0.
* M_1(H_a(y,z),z)-10=85/198, M_1(G_t(y,z),z)-10=t, and 85/198=(5/4)t.
* 10-M_1(C_a(y,z),z)=170/413, 10-M_1(A_t(y,z),z)=t, (170/413)/t=495/413, and 1<495/413.

## SAP.P016b.T18

W holds. In addition, for every real a (with no positivity or nonzero restriction), med(d(calibrationY,calibrationZ;34/99,a))>=0. Combined with W's zero at a=413/396, this says that the exhibited zero is a global minimum over all real a of this median-discrepancy criterion.

## SAP.P016b.T19

This is the following conjunction, in the stated order:

1. For every natural m>0, every outcome y on 2m units, and every assignment z with N_1(z)=m, then every pair of reals t,a and every coordinate i satisfies d(y,z;t,a)_i=|(a-1)y_i-t| if z_i=1 and zero otherwise. There is no restriction on a in this clause.
2. For every m>0,y,z with N_1=m and every real t,a,

   med(d(y,z;t,a))=(1/2)*inf{v in R: there exists treated i with v=|(a-1)y_i-t|}.

   This is one half of the least treated discrepancy, including when some treated discrepancies are zero.
3. For every m>0,y,z with N_1=m, every real t and every treated index j with y_j!=0, put a_j=1+t/y_j. Then d_j(t,a_j)=0, med(d(t,a_j))=0, for every real a the criterion med(d(t,a)) is nonnegative, and for every treated i,

   d_i(t,a_j)=|t|*|y_i/y_j-1|;

   if additionally t!=0 and y_i!=y_j then this discrepancy is nonzero. Neither a_j!=0 nor a_j>0 is assumed.
4. For every n,Y,z with N_1(z)>0 and then every real t,a with a!=0,

   M_1(Y,z)-M_1(A_t(Y,z),z)=t,

   M_1(Y,z)-M_1(C_a(Y,z),z)=(1-1/a)*M_1(Y,z).

5. For every m>0, every y on 2m units, every real t,a with a!=0, uniform expectation over B(2m,m) of M_1(y,z) is bar(y); expectation of M_1(y,z)-M_1(A_t(y,z),z) is t; expectation of M_1(y,z)-M_1(C_a(y,z),z) is (1-1/a)*bar(y).
6. For every real mu,t,a, if mu!=0, mu!=t, and a!=0, then ((1-1/a)*mu=t) if and only if a=mu/(mu-t).
7. W holds, and 10/(10-34/99)=495/478, 413/396!=495/478, 10*(1-1/(413/396))=170/413, and 170/413!=34/99.

## SAP.P016b.T20

This conjunction asserts:

1. For every real y0,y1,Y,tau and Boolean z, if Y=z*y1+(1-z)*y0 and y1=y0+tau, then y0=Y-z*tau.
2. For every n,y,z and real t,t0, A_t0(G_t(y,z),z)=G_(t-t0)(y,z), and A_t(G_t(y,z),z)=y.
3. For every n and real n-by-n matrix S, if every entry of S is nonnegative, then for every real beta,tau with beta>0, all four clauses hold:
   * for every assignment v and every coordinate i, f_i(S,beta,tau;v)>0;
   * for every outcome y and assignment z, for every i the all-control multiplier f_i(0)=1, and F_(z->0)(y)_i=y_i/f_i(z) as an equality of outcome vectors;
   * for every outcome y and assignments z,w,w', F_(z->z)(y)=y and F_(w->w')(F_(z->w)(y))=F_(z->w')(y);
   * for every outcome y0 and function y assigning an outcome vector to every assignment, if for every z,i one has y(z)_i=f_i(z)*y0_i, then for every z the vector (y(z)_i/f_i(z))_i equals y0.

There is no symmetry or binary-entry hypothesis here, no bound beta<=1 or beta>=1, and no restriction on the real tau beyond its occurrence as tau^2. n=0 is included in the universal algebraic claims.

## SAP.P016b.T21

For every finite law P on B(256,128), **if for every assignment z its weight equals 1/choose(256,128)**, then for every real matrix S on 256 units, **if S is symmetric and every entry is either 0 or 1**, then for every real outcome vector y0 and every real-valued statistic T(outcome,assignment), define, for each z in B(256,128),

Y(z)_i=f_i(S,2,1/2;z)*y0_i,

u(z)_i=Y(z)_i/f_i(S,2,1/2;z),

s(z)=T(u(z),z).

Then all of the following hold:

1. For every z, u(z)=y0.
2. For each of the three functions p(z)=U_P(s,z), p(z)=L_P(s,z), and p(z)=Q(L_P(s,z),U_P(s,z)), both P{p(z)<=1/20}<=1/20 and P{p(z)<1/20}<=1/20. The finite set of three functions may identify functions that happen to coincide, without removing any asserted bound.
3. Under 1001 independent P assignments (one observed and 1000 references), the mass of {p_raw<1/20} is <=50/1001, and 50/1001<1/20.
4. Under 10001 independent P assignments (one observed and 10000 references), the analogous mass is <=500/10001, and 500/10001<1/20.

The statistic T is arbitrary, with no effect-increasing requirement. These are unconditional probabilities over observation and fresh independent references. There is no numerical p-value-curve, fixed-simulation-data, or shared-reference-sample assertion in this proposition.
