# Blind reading of the Challenge statements

This file was written after reading all eight Defs parts and the Challenge files,
and before opening either `claims.json` or `record.json`. The readings below are
of the propositions, not of their docstrings. Every theorem is a closed
proposition, namely the corresponding `TnStatement`; its separate conjuncts have
independent quantifiers.

## Definitions and Mathlib semantics used throughout

* `Fin N` means the integers from 0 through N−1. An assignment is a function
  z : Fin N → Bool, with b(z_i)=1 for true and 0 for false. All unspecified
  sums over a finite type include every element. `treatedCount` is the natural
  number of true coordinates; t(z)=`nTreated` is that count as a real number,
  and u(z)=`nControl`=N−t(z) is **real** subtraction.
* A `FiniteLaw Q` on a finite type Ω consists of real masses Q(z)≥0 with
  Σ_z Q(z)=1. E_Q f=Σ_z Q(z)f(z), P_Q(A)=Σ_{z∈A}Q(z),
  Cov_Q(f,g)=E_Q[(f−E_Q f)(g−E_Q g)], and Var_Q f=Cov_Q(f,f).
  A finite type admitting such a law cannot be empty. `uniformLaw` requires a
  nonempty finite type and assigns mass 1/|Ω|. Conditioning on A requires
  P_Q(A)>0 and assigns Q(z)/P_Q(A) on A and zero elsewhere.
* `commonBernoulli Q p` means, for **every** assignment z,
  Q(z)=∏_i (p if z_i=true, 1−p otherwise). A marginal is an override
  expectation, not conditioning: m_Q(F,i,b)=E_Q[F(z with coordinate i set to b)].
* `Plane` is Mathlib's `EuclideanSpace ℝ (Fin 2)` (PiLp with exponent 2), with
  Euclidean distance. `lineEmbedding x` is the point (x,0), for rational x.
  A spatial model P has a set F⊆ℝ², N labelled nodes s_i∈F, an arbitrary
  Mathlib Borel measure ζ on ℝ², and real outcomes Y(x,z). There is no implicit
  measurability, boundedness, integrability, or distinctness assumption.
  C_i(d)={x∈F : dist(s_i,x)=d}, μ_i,d=ζ restricted to C_i(d),
  c_i(d)=(μ_i,d(ℝ²)).toReal, and
  A_i,d(f)=c_i(d)⁻¹ ∫ f dμ_i,d. Write M_i(d,z)=A_i,d(Y(·,z)).
  The node marginal m_i(b,d)=E_Q M_i(d,z with i set to b), the node effect
  τ_i(d)=m_i(true,d)−m_i(false,d), AMR(d)=N⁻¹Σ_i τ_i(d), and
  risk_b(d)=N⁻¹Σ_i m_i(b,d). `marginalY` and `pointEffect` apply the same
  override expectation and difference pointwise before averaging.
* These are genuine Mathlib restricted measures and Bochner integrals, not
  surface measure supplied automatically by the word “circle.” Mathlib's
  restriction is defined on all sets; for measurable evaluation sets its value
  is ζ of the intersection (`Measure/Restrict.lean`, `restrict_apply`).
  `ENNReal.toReal` sends infinity to zero; real inverse at zero is zero; a
  nonintegrable Bochner integral is zero (`Integral/Bochner/Basic.lean`,
  `integral_undef`). Hence positivity, finiteness, and integrability clauses
  below matter. In T6's last clause the integrand vanishes on the circle,
  which itself supplies integrability there. The sharp null is
  ∀x∈F ∀z, Y(x,z)=Y(x,all-false).
* The Hájek contrast is
  H(M,z)=Σ_i b(z_i)M_i(z)/t(z) − Σ_i(1−b(z_i))M_i(z)/u(z).
  For fixed four-node data y, C(y,z)=Σ_i b(z_i)y_i/2−Σ_i(1−b(z_i))y_i/2.
  `finiteAMR Q M` is N⁻¹Σ_i[m_Q(M_i,i,true)−m_Q(M_i,i,false)].
  The linearization score is
  φ_i(z)=2b(z_i)(M_i(z)−m₁)−2(1−b(z_i))(M_i(z)−m₀).
* The inclusive two-sided tail p_Q(T,z) is P_Q{|T(w)|≥|T(z)|}.
  `outside(lo,hi,t)` means strictly t<lo or hi<t.
  For a list s_0,…,s_n and q, `quantile7` sets h=nq,
  j=min(toNat(floor h),n), g=h−j, and returns
  (1−g)s_j+g s_min(j+1,n). On q∈[0,1] and a sorted sample this is the
  usual type-7 interpolated quantile. The definition does not sort its input.
* `countMean C f` is Σ_{x∈C}f(x)/|C| with real division.
  For a finite rational field F and rational nodes s_i, `lineCircle` filters F
  by |x−s_i|=d, and `lineM` is the counting mean of outcomes on that set.
* For fixed data M_i and assignment z, the group mean is the mean in the arm
  indicated by b; e_i=M_i−mean of i's arm;
  v_i=b(z_i)/t−(1−b(z_i))/u; g_i=v_i e_i is the regression score.
  K_c(D)_{ij}=1 if D_ij≤c, 0 otherwise, and
  HAC(g,D,c)=Σ_iΣ_j g_i g_j K_c(D)_ij. D need not be a metric.
  X has rows (1,b(z_i)), H=(XᵀX)⁻¹,
  OLS residuals are M−XH XᵀM, and the meat matrix has entries
  Σ_iΣ_j K_c(D)_ij e_i^OLS e_j^OLS X_ia X_jb.
  Mathlib matrix inverse is the determinant/adjugate inverse, zero for a
  singular real matrix (`Matrix/NonsingularInverse.lean`, `inv_def` and
  `nonsing_inv_apply_not_isUnit`). The two-arm hypotheses below make this
  inverse nonsingular when it is used.
  Archived variance at cutoff c and natural position k is HAC at c+k if c>0,
  and at c otherwise. Physical variance is HAC at c, ignoring position.

## Fixed data used by the propositions

* The six assignments z^k, k=0,…,5, in order are
  1100, 1010, 1001, 0110, 0101, 0011. The blocked four assignments are
  z¹,z²,z³,z⁴. Complement indices are (5,4,3,2,1,0).
* U is all 60-element subsets of {0,…,120}; B consists of unions of a
  5-element subset of {0,…,9} and a 55-element subset of {10,…,120}.
  o={0,…,4}∪{10,…,64}; a=(o\{10})∪{5}. For a finite support S,
  q_S(z)=1/|S| on S and zero elsewhere.
* The rectangle model has field [−1,31]×[−1,1], nodes (10i,0), i=0,…,3,
  assignment-independent outcome Σ_i i·1{dist(x,(10i,0))≤1}, and measure
  Σ_{i=0}³Σ_{r=0}⁵ δ_(10i+r/10,0). Its five evaluated radii are
  d_j=(j+1)/10, j=0,…,4. T_j(k)=H(M(·,d_j,·),z^k).
* The two-node field is {−1,0,1,2,3}⊆ℚ, nodes 0,2, and
  Y(x,z)=b(z_0)1{|x|≤1}+b(z_1)1{|x−2|≤1}. Pair assignments enumerate
  00,01,10,11. For replication number L, nodes have labels (h,a)∈Fin L×Fin 2
  and positions 6h+2a; field={6h+r−1 : h<L, r<5};
  Y(x,z)=Σ_i b(z_i)1{|x−s_i|≤1}. Circles use counting measure at radius 1.
  The replicated spatial score uses m₁=5/4,m₀=1/4. The algebraic pair score
  is (1/2)(2b(z_(h,0))−1)(2b(z_(h,1))−1), the same for both labels in a pair.
* Risk cells are k=0,…,39999, with baseline vector β=(400,1000,400,1000).
  For each node i and radius label j∈Fin 4,
  Y_ij(k,z)=1{k<β_i−321·1{z_i=true}} and M_ij is its mean on all 40000 cells.
  The subtraction in this particular indicator is natural subtraction.
  The companion outcome is 1−b(z_i), independent of j,k, with counting mean
  M'_ij. `riskSamplingProbability Q b`=(1/16)Σ_iΣ_j m_Q(M_ij,i,b).
* The bandwidth spatial model has field ℝ², nodes (2i,0),
  Y(x,z)=Σ_i 2i·1{dist(x,(2i,0))≤3/10}, and measure
  Σ_{i=0}³Σ_{r=0}³ δ_(2i+r/10,0). Its radii are (j+1)/10 for j<3.
  The short grid is (1/5,3/10), the long grid (1/10,1/5,3/10).
  The distance array D^b_ij=|2i−2j|.
* The four toy nodes are the Euclidean points with coordinates
  (2028297641/2147483648,4318520789/2147483648),
  (7976664621/2147483648,1029755657/268435456),
  (1053580245/536870912,2017196647/2147483648), and
  (7110225301/2147483648,499145583/1073741824).
* The printed grid is d_k=5k/111, k∈Fin 5. The corrected grid is
  d'_k=k/222, k∈Fin 41. The selected range is the inclusive interval
  [1/111,5/222].

## SAP.P008a.T1

There are no hypotheses. The theorem asserts the conjunction:

1. |U|=choose(121,60), |B|=choose(10,5)choose(111,55), B is a strict subset
   of U, o belongs to both, and a belongs to U but not B. Both support laws
   give o positive mass; q_U(a)>0, q_B(a)=0; each law sums to one on its
   support; and q_U≠q_B as functions on all finite subsets of ℕ.
2. k↦z^k is injective, and for every four-node assignment z, it has two
   treated coordinates iff ∃k∈Fin 6, z^k=z; z¹=1010. The blocked enumeration
   is injective and, for every z, belongs to it iff z_0≠z_1 and z_2≠z_3.
3. For every k∈Fin 6, contrasts for y=(0,1,0,1) are
   (0,−1,0,0,1,0)_k and for y=(0,1/3,2/3,1) are
   (−2/3,−1/3,0,0,1/3,2/3)_k.
4. At observation z¹ (blocked index 0), the first data vector has inclusive
   tails 1/3 under uniform six and 1/2 under uniform blocked four. The second
   has tails 2/3 and 1/2 respectively; 1/3<1/2<2/3.

## SAP.P008a.T2

Five independently quantified conjuncts:

1. For every finite type Ω, law Q, real statistic T:Ω→ℝ, and δ∈[0,1],
   P_Q{z:p_Q(T,z)≤δ}≤δ.
2. For every such Ω,Q, event A with P_Q(A)>0, statistic T, and δ∈[0,1],
   the same inequality holds with Q conditioned on A throughout.
3. For every N, law Q on assignments, p with 0<p<1 and commonBernoulli Q p,
   then every natural M≤N: the count-M event has positive probability; for
   every z with count M, Q(z)/P_Q(count=M)=1/choose(N,M).
4. For every N, spatial model P, law Q, event A with positive Q probability,
   finite real radius set D, measurable field, sharp null, N>0, positive
   c_i(d) and μ_i,d(ℝ²)≠∞ for every i,d∈D, integrability of Y(·,z) for
   every i,d∈D and **every assignment z**, and nonzero treated and control
   counts for every z satisfying A with Q(z)>0, then every δ∈[0,1]: let
   S(z)=Σ_{d∈D}H(M(·,d,·),z). Its inclusive conditional tail satisfies
   P_{Q|A}{p_{Q|A}(S,z)≤δ}≤δ. Moreover for every z with A(z), Q(z)>0,
   S(z)=Σ_{d∈D}H((i,w)↦M_i(d,all-false),z).
5. The four numerical tail values and their strict ordering in T1 hold.

D may be empty, but is not required to be; support-arm conditions apply only
to assignments of positive conditional probability.

## SAP.P008a.T3

No hypotheses. The six assignments injectively enumerate precisely the
two-treated assignments and z¹=1010. Each closed unit disk about a rectangle
node lies in the field, and disks about distinct nodes are disjoint. For every
i<4,j<5, its evaluated circle has positive finite mass and every assignment's
outcome is integrable there. For every x,z, outcomes equal the all-false
outcomes. For every i,j,z, M_i(d_j,z)=i, and for every j,k,
T_j(k)=(−2,−1,0,0,1,2)_k.

For every j, type-7 quantiles at 1/40 and 39/40 are −15/8 and 15/8;
under uniform k∈Fin 6 the chance of strictly falling outside these is 1/3.
For Σ_{j<5}T_j, the corresponding quantiles are −75/8 and 75/8, and the
outside probability is also 1/3>1/20. For every law Q on four-node assignments
satisfying commonBernoulli Q (1/2), the two-treated event has positive
probability and every assignment in that event has conditional mass 1/6.
Finally, for every j,k the single-radius outside event is equivalent to
k=0 or k=5; the summed statistics are (−10,−5,0,0,5,10)_k and their outside
event is likewise equivalent to k=0 or k=5.

## SAP.P008a.T4

1. For every real y on four nodes and k<6, its complement index is distinct,
   its assignment is the coordinatewise Boolean complement, both arm counts
   are two, and H(y,z^k)=C(y,z^k).
2. For every natural J, real weights a_j and real data m_ji, let
   S(k)=Σ_{j<J}a_j C(m_j,z^k). For every k, S(complement k)=−S(k),
   p_uniform6(S,k)≥1/3, and p_uniform6(S,k)≤1/20 is false.
3. For every nonempty finite R⊆Fin 6, P_uniform6(R)=|R|/6≥1/6>1/20.
4. For every finite Ω, law Q, real T and δ∈[0,1], the inclusive-tail
   calibration inequality of T2 holds.
5. For every finite Ω, law Q, natural B (including zero), finite law R on
   tuples z:Fin(B+1)→Ω whose mass at **every tuple** is ∏_k Q(z_k), real
   statistic S, and δ∈[0,1],
   P_R{[1+# {b< B: |S(z_0)|≤|S(z_(b+1))|}]/(B+1)≤δ}≤δ.
6. The five rational displayed numbers 1.491+1.550+1.550+1.691+1.714
   sum to 1999/250=7.996.

## SAP.P008a.T5

The pair assignment enumeration is bijective. Both nodes lie in the field,
their radius-one circles are {−1,1} and {1,3}; for every assignment z,
M_0(z)=b(z_0)+b(z_1)/2 and M_1(z)=b(z_1)+b(z_0)/2.

Under uniform pair assignments, for every node its override means at true
and false are 5/4 and 1/4. For every node and assignment index its score
equals (1/2)(2b(z_0)−1)(2b(z_1)−1). Node 0's score variance, the covariance
of the two scores, and the variance of their average all equal 1/4. The
diagonal-only normalized variance is (1/4+1/4)/4=1/8<1/4. The normalized
covariance sum retaining only node distances ≤1 is also 1/8, whereas the
full average-score variance is 1/4. For each node the score has mean zero
and variance 1/4; the average override effect is one.

For every natural L>0: each replicated node belongs to the replicated field;
for every x in that field and every assignment, 0≤Y(x,z)≤2; for every node
its radius-one circle is {s_i−1,s_i+1}; for every pair h and assignment,
its two circle means are b(z_(h,0))+b(z_(h,1))/2 and the reverse. For every
node and assignment its spatial score equals the algebraic pair score.
Under the uniform law on **all** 2L-node assignments, the variance of
(2L)⁻¹Σ_i φ_i is 1/[2(2L)], while (2L)⁻²Σ_i Var φ_i is 1/[4(2L)].

Further independent clauses state: for every L>0, node i and Boolean b,
the override mean is b(b)+1/4; for every natural L, node i and rational x,
x is in its replicated circle iff it is in the field and the embedded
Euclidean distance to the node is one; for every L and distinct nodes i,j,
their embedded distance is at least two. For every L>0, node i and assignments
z,z' agreeing on **both** coordinates of i's pair, their circle means at i
agree. For every L>0, the normalized covariance sum with actual embedded
distance cutoff one is 1/[4(2L)].

## SAP.P008a.T6

1. For every N, assignment z, real node data M, real array D, and c≥0,
   assume t(z)≥1, u(z)≥1, D_ii=0 for all i, and c<D_ij for all i≠j.
   With X,H and OLS meat as defined above: H(M,z)=Σ_i v_iM_i;
   (H Xᵀ)_(1,i)=v_i for every i; OLS residuals equal group residuals;
   (H meat H)_(1,1)=HAC(g,D,c)=Σ_i g_i²
   =Σ_{z_i=true}e_i²/t²+Σ_{z_i=false}e_i²/u²
   =HAC(g,D,0).
2. For every real g on four nodes, distinct toy nodes have distance >2/5;
   HAC at that cutoff is Σ_i g_i² and equals HAC at zero. For every real
   t and critical, both t−critical·sqrt(HAC) and t+critical·sqrt(HAC)
   agree at the two cutoffs.
3. For every N, real base_i, real coefficients a_ik, real m₁,m₀, and
   distinct i,j, under the uniform law on assignments, scores formed from
   M_i(z)=base_i+Σ_k a_ik b(z_k) have Cov(φ_i,φ_j)=a_ij a_ji.
4. For every N>0 and the same arbitrary base,a,m₁,m₀,
   Var(N⁻¹Σ_iφ_i)=N⁻²[Σ_i Var φ_i+Σ_iΣ_{j≠i}a_ij a_ji].
   Then for every real D,c with c≥0, D_ii=0, and
   ∀i,j, c<D_ij ⇒ a_ij a_ji=0, the N⁻² normalized covariance sum
   retaining D_ij≤c equals that full variance.
5. For every N, spatial model P, real d,r,c, and real functions
   g_ik:ℝ²→ℝ, assume the field is measurable, every c_i(d)>0,
   μ_i,d(ℝ²)≠∞, g_ik(x)=0 whenever r<dist(s_k,x) for **all** i,k,x
   on the whole plane, and d+r≤c. Then for every i,k with
   c<dist(s_i,s_k), A_i,d(g_ik)=0. There is no separate integrability
   hypothesis in this last clause.

## SAP.P008a.T7

No hypotheses on the fixed examples. For every i,j,k,z, the risk outcome is
zero or one; for every i,j,z its mean is (β_i−321b(z_i))/40000 (now real
subtraction). Under uniform four-node assignments, for every i,j,b its
override mean is (β_i−321b(b))/40000. At every j its average node effect
is −321/40000, and the observed Hájek contrast at 1100 is also −321/40000.
The four-radius sum is −321/10000. Further numerical identities are
379/40000−7/400=−321/40000 and
7/400−321/10000=−73/5000<0. Four copies of −1 sum to −4; for every
a,b∈[0,1], a−b≠−4.

The defined sampling probabilities under uniform assignments are 7/400 for
false and 379/40000 for true, with difference −321/40000.
For every i,j,k,z the companion outcome is binary, and for every i,j,z
M'_ij(z)=1−b(z_i). For every j its finite AMR is −1, the four finite AMRs
sum to −4, and no a,b∈[0,1] have difference equal to that sum.
Uniform assignments satisfy commonBernoulli at 1/2 and give observation
1100 mass 1/16. Every companion observed contrast at 1100 is −1, and their
sum is −4. Finally, for every real radius weighting w_j≥0 with Σ_jw_j=1,
the weighted sum of the first example's finite AMRs is −321/40000.

## SAP.P008a.T8

1. For every N, spatial model P, assignment law Q and real d, assume N>0,
   measurable field, c_i(d)>0 and μ_i,d(ℝ²)≠∞ for every node, integrability
   of Y(·,z with i set to b) for **every i,b,z with Q(z)≠0**, and binary
   outcomes for every field point and every assignment. Then for each b,
   0≤risk_b(d)≤1, and AMR(d)=risk_true(d)−risk_false(d).
2. For every natural J, real vectors w,q₀,q₁ with w_j≥0, Σ_jw_j=1,
   q₀j,q₁j∈[0,1], then every real L,U bounding each effect
   L≤q₁j−q₀j≤U: both weighted risks lie in [0,1]; their difference is
   Σ_jw_j(q₁j−q₀j), this is between L and U, and its absolute value is ≤1.
3. For every J>0 and arbitrary real q₀,q₁, the difference of their means
   is the mean of differences and Σ_j(q₁j−q₀j)=J times that mean.
4. For every natural J, nonnegative normalized w and real t,
   Σ_{j<J}t=Jt and Σ_jw_jt=t.
5. For every n, monotone sample s:Fin(n+1)→ℝ, real q,m,x,y with
   0≤q≤1 and m>0: x≤y iff x/m≤y/m; |x|≤|y| iff |x/m|≤|y/m|;
   quantile7(s/m,q)=quantile7(s,q)/m.
6. The exact rescalings (−19/625)/4=−19/2500,
   (−321/10000)/4=−321/40000, (21/625)/4=21/2500 hold,
   with −321/40000<−19/2500. The companion four-radius finite AMR sum is
   −4, unequal to a−b for every a,b∈[0,1].

## SAP.P008a.T9

For every pair of bandwidth-model nodes their distance is |2i−2j|. For every
i<4,j<3 the circle mass at (j+1)/10 is exactly one and finite, and for every
assignment the outcome is integrable there. Every corresponding circle mean
is 2i for every assignment.

Short-grid index 0 equals long-grid index 1 and is 1/5; assignment 0011 has
two treated and two controls. The circle-mean and distance identities hold,
and the Hájek contrast at radius 1/5 is four. With that fixed observation,
those spatial data, and physical input cutoff 2/5, archived variance at
natural position 1 is one and at position 2 is 1/2. For every i, the regression
score from data (0,2,4,6), assignment 0011, is (1/2,−1/2,−1/2,1/2)_i.

Finally, for every four-node assignment z and arbitrary real data M with both
arm counts nonzero: every squared toy-node distance is ≤32, its archived
regression-score variance at input cutoff 2/5 and position 6 is zero, and
for **every real a**, 2a times its square root differs from 869/250.

## SAP.P008a.T10

For every N, assignment z, real data M, real array D and real c, assume both
arm counts are nonzero; then for every natural j,k: physical variance at j
is HAC(g,D,c), physical variances at j,k agree, and Σ_i g_i=0. For every
additional hypothesis ∀i,l D_il≤c, HAC(g,D,c)=(Σ_i g_i)²=0.

For g=(1/2,−1/2,−1/2,1/2), D_ij=|2i−2j| and c=2/5, physical variance at
positions 1 and 2 is one. For every four-node z,M with both arms nonzero,
toy-node HAC at 2/5 is Σ_i g_i², equals HAC at zero, and archived variance
at input cutoff 2/5 and position 6 is zero.

## SAP.P008a.T11

No hypotheses for the numerical conjuncts:
1.491+1.550+1.550+1.691+1.714=1999/250=7.996, and adding
1.700+1.678+1.002 gives 1547/125=12.376.
For **every** five real a,b,c,e,f whose individual distances from those first
five displayed values are at most 1/2000, their sum S satisfies
15987/2000≤S≤15997/2000, |S−619/50|>1/200, and S>1595/200.
Thus this interval is [7.9935,7.9985], the excluded value is 12.38 with
half-cent tolerance, and the final strict lower bound is 7.975.
Finally |12.376−12.38|<0.005. No rounding function is defined or used.

## SAP.P008a.T12

For every k<5 the printed grid value 5k/111 is outside the selected inclusive
range. For every real f on Fin 5 the sum over selected indices is zero.
The three numbers −321/10000, −19/625 and 21/625 are nonzero, and
25/111>20/111. For every n, every real array M on Fin(n+1)×Fin 5, and
every q∈[0,1], each sample's selected sum is zero and the type-7 quantile
of these sums is zero. No nonempty selected set is assumed: its emptiness
is precisely the first conclusion.

## SAP.P008a.T13

The corrected grid has 41 indices and endpoint d'_40=20/111. For every
k<41, its radius is in the selected range iff 2≤k≤5. For every real f on
Fin 41 the selected sum is f_2+f_3+f_4+f_5. For every k<40 the increment
from k to k+1 is 1/222. Multiplying the four selected radii by 111 gives
1,3/2,2,5/2 respectively; 1/222=(1/2)/111.

## SAP.P008a.T14

For every N>0, real vectors μ₁,μ₀,τ on Fin N satisfying
∀i τ_i=μ₁i−μ₀i, the mean of τ equals the mean of μ₁−μ₀.
Independently, for every real A, A²=A iff A=0 or A=1.
Finally (3−0+(7−2))/2=4, 4·4=16, and 16≠4.

Post-blind proofreading note: in the T3 paragraph, “law Q on four assignments”
was corrected to “law Q on four-node assignments” (all 16 Boolean vectors).
The source is `Assignment 4 = Fin 4 → Bool` and Defs/Part5.lean:118–120.
This wording correction did not change any claim-stage classification.
