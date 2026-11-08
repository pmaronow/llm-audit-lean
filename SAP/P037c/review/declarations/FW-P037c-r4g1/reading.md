# Blind reading

This file was written before opening `claims.json` or `record.json`. Sources read:
`Challenge/Part1.lean`, `Defs/Part1.lean`, `Defs/Part2.lean`,
`Defs/Part3.lean`, `Defs/Part4.lean`, and the relevant definitions in
`Defs/WholeW1.lean`. All 96 distinct compiler-generated declarations listed in
the five closures were printed and read in `scratch/closure-checks.out`.
They prove numeral typeclass facts or bounds on finite indices; none adds a
substantive statistical assumption. The imported aggregate files contain imports
and options, not additional hypotheses.

Throughout, `Fin n` is the natural numbers below n, `Bool` is a two-element type,
`Finset` is a finite set, and all displayed sums/products are finite ordinary
real sums/products unless explicitly described as natural-number arithmetic.
There are no ambient probability spaces or implicit independence assumptions:
where probability is asserted, it is expressed by a specified finite mass law.

## SAP.P037c.T35

The theorem has no inputs or hypotheses. It asserts the following conjunction
of explicit arithmetic/combinatorial facts (including the entire one-block
statement).

**One block.** Let U = {0,...,4} × {false,true}. For i=(b,s), put
P(i)=(b,not s). Let S consist of all five-element subsets of U, let
O={(b,false): b=0,...,4}, and define the potential-outcome schedule
y_z(i)=1 if i belongs to z and 0 otherwise, for every subset z of U.
For any subset z and vector Y:U→R define

    t(z,Y) = (sum_{i in z} Y(P(i)))/5
             - (sum_{i in U\z} Y(P(i)))/5,
    q(z) = #{z' in S: |t(z',y_z)| >= |t(z,y_z)|}/252.

Thus q recomputes outcomes from its observed assignment z and holds that vector
fixed as it enumerates z'. A split means, for every pair b,
(b,false) belongs to z iff (b,true) does not belong to z. It is a predicate on
all subsets, with no random sampling inside its definition.

The one-block assertions are:

1. |S|=252, O belongs to S, and t(O,y_O)=-1.
2. For every integer k with 0<=k<6, exactly binomial(5,k)^2 members z of S
   have t(z,y_O)=(2k-5)/5. The six binomial squares are exactly
   [1,25,100,100,25,1].
3. q(O)=1/126=2/252 and 1/126<1/100. For every z in S, if z splits all
   pairs, q(z)=1/126; if it does not, q(z)>=13/63.
4. Exactly 32 members of S split all pairs; 2^5=32; and
   #{z in S:q(z)<1/100}/252=8/63.
5. For all subsets z,z' and all i, if i belongs to z iff i belongs to z',
   then y_z(i)=y_z'(i). This is an own-treatment-only outcome schedule.
6. For every z in S,
   t(z,y_O)=(2|z intersect P(O)|-5)/5.
7. For every b, y_O(b,false)=1 and y_O(b,true)=0;
   sum_{i in O} y_O(P(i))/5=0 and
   sum_{i in U\O} y_O(P(i))/5=1.
   P(O)=U\O and P(U\O)=O.

**Four blocks.** Let V={0,...,3}×U, let P_V(h,i)=(h,P(i)), and let S4
consist of all subsets z of V containing exactly five students with each first
coordinate h. Define O4={(h,b,false):h<4,b<5},
y4_z(i)=1_{i in z},

    t4(z,Y) = sum_{i in z}Y(P_V(i))/20
              -sum_{i in V\z}Y(P_V(i))/20,
    m(z)=1/|S4|.

The mass formula is defined for every subset, but only summed over S4. The
remaining assertions are:

1. |S4|=252^4, sum_{z in S4}m(z)=1, and every z in S4 has positive mass
   and cardinality 20. O4 belongs to S4.
2. For all subsets z,z' and all i, identical own membership implies identical
   y4 outcomes.
3. For every z in S4 and every vector Y:V→R, the nomination statistic equals
   t4(z,Y). Here the nomination statistic is the difference

       [sum_{i in E,j} A(i,j) M(j) Z(i) Y(j)]
         /[sum_{i in E,j} A(i,j) M(j) Z(i)]
       -[sum_{i in E,j} A(i,j) M(j) (1-Z(i)) Y(j)]
         /[sum_{i in E,j} A(i,j) M(j) (1-Z(i))],

   with E=V, A(i,j)=1_{j=P_V(i)}, M(j)=1, and Z=y4_z. These denominators
   count 20 nomination recipients with multiplicity in each arm.
4. t4(O4,y4_O4)=-1. For every z in S4, |t4(z,y4_O4)|<=1;
   exactly two members attain absolute value 1.
5. The sum over z in S4 of m(z) times
   1_{|t4(z,y4_O4)| >= |t4(O4,y4_O4)|} equals 2/252^4.

The docstring describes exactly these one-block and copied-observation facts.
It does not assert a four-block repeated-experiment rejection rate.

**Junk-value audit.** All fixed divisors (5,20,126,252,100,63) are nonzero.
The cardinal divisor in m could in isolation be zero for an empty support;
the statement explicitly proves |S4|=252^4>0. The generic nomination statistic
is totalized by real division with inverse(0)=0, but its use here has exactly
20 nominations in each arm. Unsupported subsets can have other sizes, but
the theorem's statistic/probability conclusions are support-restricted.
Natural binomial coefficients and cardinalities are cast exactly to R;
there is no integer truncation or modular arithmetic in (2k-5)/5, which is a
real expression. All index types are nonempty. No log, square root, real power,
integral, extended-real conversion, infimum, supremum, limsup, liminf, or partial
function default is used.

## SAP.P037c.T36

For every two types Omega and I equipped with finite enumerations, the theorem
asserts three conjuncts. The first two are universal implications; the third
is a fixed ten-student witness independent of those input types.

**Exact sharp-null validity.** For every E subset of I, A:I×I→R,
M:I→R, Z:Omega→I→R, p:Omega→R, Y:Omega→I→R, z0 in Omega, and alpha in R,
assume, in this order:

1. A(i,j)>=0 for every i,j.
2. M(i) is either 0 or 1 for every i.
3. Z(z,i) is either 0 or 1 for every z,i.
4. Z(z,i)=0 whenever i is outside E.
5. For every z, both nomination denominators
   sum_{i in E,j}A(i,j)M(j)Z(z,i) and
   sum_{i in E,j}A(i,j)M(j)(1-Z(z,i)) are strictly positive.
6. Every p(z)>0 and sum_z p(z)=1.
7. For all z,z',i, Y(z,i)=Y(z',i) (the global sharp null).
8. 0<=alpha<=1.

Use exactly the displayed nomination-statistic formula in the preceding
section, with the relevant E,A,M,Z and outcome vector. Define

    q(z)=sum_{z'}p(z')
          1_{|T(Z(z'),Y(z0))| >= |T(Z(z),Y(z0))|}.

The conclusion is sum_z p(z)1_{q(z)<=alpha}<=alpha. There is no distinctness
assumption on assignment representations Z(z), and no further graph restriction
such as binary edges, no self-loops, or fixed outdegree. Ties enter the upper
tail through >=. This is a weighted exact two-sided test, not a Monte Carlo
approximation.

**Direct-effect decomposition.** For every E,A,M,z,baseline and real delta,
assume A is nonnegative, M and z are binary, z vanishes outside E, and both
nomination denominators are positive. Then

    T(z, baseline + delta*z)
      = T(z, baseline) + delta*T(z,z).

All multiplication/addition in the outcome argument is pointwise. No
randomization law occurs in this conjunct.

**Concrete witness.** On U, S, O, P, y_z, t and q from T35, put
A(i,j)=1_{j=P(i)}, E=U, M=1. The assertions are:

1. For every z in S and every outcome vector Y, T(y_z,Y)=t(z,Y).
2. For all subsets z,z' and all i, equal own membership implies y_z(i)=y_z'(i).
3. It is false that y_z(i)=y_z'(i) for all z,z' in S and all i. Thus the
   global sharp null fails, even though the own-treatment-only condition holds.
4. T(y_O,y_O)=-1, q(O)=1/126, and
   #{z in S:q(z)<1/100}/252=8/63.

The docstring calls the last item rejection without social influence and
correctly separates this from sharp-null validity. This is not a claim that
the witness refutes the global sharp-null test.

**Junk-value audit.** Both denominators are expressly positive whenever the
general statistic is used as a mean. With this witness they are both 5.
All other divisors are fixed positive numbers. Omega or I may be empty as
input types; the sharp-null implication then has no z0 or fails its positive
denominator requirements. This does not eliminate nonempty models, and the
fixed witness remains a substantive conjunct. Strict positivity of every
p(z), rather than just nonnegativity, selects a support representation with
no zero-mass states. No integrals, roots, logs, real powers, truncated
subtraction, extended-real conversions, order extrema, limits, or defaults
are involved.

## SAP.P037c.T27

This is another closed assertion with no hypotheses. Its finitely many
universal quantifiers range over explicitly constructed data and the two stated
weight vectors; it does not quantify over general experiments or outcomes.

**Data and WLS.** The analysis population is U={0,...,3}×{0,1,2}. For i=(k,j),
x_i=k+j (both coordinates cast from natural numbers to R),
Y_i(a)=(2 if a=3 else 1)*x_i, and observed y_i=Y_i(k). The observed category
is D_i=k. A regression coefficient b minimizes WLS precisely if, for every
competing coefficient vector c,

    sum_i w_i (y_i-sum_j X_ij b_j)^2
      <= sum_i w_i (y_i-sum_j X_ij c_j)^2.

The pooled design is [1_{D=0},1_{D=1},1_{D=2},1_{D=3},x]. Separate designs
are [1,x], with weight zero outside the chosen category. For any real
four-vector w define

    B=(w0+w1+w2+2*w3)/(w0+w1+w2+w3),
    b(w)=[1-B,2-2B,3-3B,8-4B,B],
    m_k(b)=b_k+(5/2)b_4.

All fit claims below restrict w to [4,4,4,4] or [2,8,8,4]. They assert:

1. sum_i x_i/12=5/2.
2. For each of the two weights and each category k, [0,(2 if k=3 else 1)]
   is a separate WLS minimizer. A vector b is a pooled WLS minimizer iff
   b=b(w). The pooled normal equations have zero weighted residual sum
   within every category and zero weighted x-times-residual sum overall.
3. b([4,4,4,4])=[-1/4,-1/2,-3/4,3,5/4];
   b([2,8,8,4])=[-2/11,-4/11,-6/11,36/11,13/11].
4. Their standardized means m_k are respectively
   [23/8,21/8,19/8,49/8] and [61/22,57/22,53/22,137/22].
5. Define a separate augmented mean for category a by

       (1/12)sum_i [1_{D_i=a}w_{D_i}(y_i-f_a(i))+f_a(i)],
       f_a(i)=(2 if a=3 else 1)x_i.

   For both weights this equals 5 for a=3 and 5/2 otherwise. These are also
   exactly sum_i Y_i(a)/12. Each observed separate residual is zero.
6. The separate contrast a=3 minus a=2 is 5/2. The pooled contrasts are
   15/4 and 42/11, respectively, both unequal to 5/2; their differences
   from the separate contrast are 5/4 and 29/22.

**E1 law.** Let Omega1 be all functions d:U→{0,1,2,3}; assign each the mass
(1/4)^12. The theorem asserts that these masses sum to one and are positive.
For every subset s of U and every function a:U→{0,1,2,3},

    sum_d (1/4)^12 * 1_{for all i in s, d_i=a_i}=(1/4)^|s|.

Consequently the statement also explicitly asserts every marginal is 1/4,
its inverse is 4, and the event d_i=i.first for all i has probability
(1/4)^12>0. It restates consistency Y_i(i.first)=y_i. This is genuinely a
product exposure law on all assignments, rather than one repeated draw.

**E2 school and seed construction.** There are six schools s=0,...,5;
n_s=7 for s<3 and n_s=9 otherwise. The student type is the dependent union
of {(s,j):0<=j<n_s}. Directed nomination A_s(i,j) is true exactly when

    (i>=6 and (j=0 or j=2)) or ((i=4 or i=5) and j=0).

The indegree d_s(j) counts nominators. The 90th-percentile definition sorts
all n_s indegrees increasingly, sets h=9(n_s-1), q=floor(h/10), r=h mod 10,
and uses (10-r)/10 times entry q plus r/10 times entry q+1 (zero default
if an entry is absent).

Each assignment consists of a set H of exactly three schools and independent
two-bit choices b_s=(b_s1,b_s2) in every school. Every (H,b) has mass
1/(20*4^6). The within-school seed set is
{0 if b_s1 else 1, 2 if b_s2 else 3}. There are exactly two seeds, one in
each of the two cells {0,1} and {2,3}.

A student's five-category exposure is: 0 if the school is not in H; otherwise
4 if the student is a seed; otherwise 3 if an adjacent seed (nomination in
either direction) has indegree strictly above the within-school 90th percentile;
otherwise 2 if there is any adjacent seed; otherwise 1. The marginal
probability of a category is the sum of the assignment masses giving it.

The focal map sends (0,j) to student 6 in school j, and (k,j) for k=1,2,3
to student 6+j in school k+2. Its simpler four-category exposure is 0 outside
H; inside H it is 3 if b_s1, else 2 if b_s2, else 1. The detailed design
assertions are:

1. d_s(0)=n_s-4, d_s(2)=n_s-6, all other indegrees are zero.
2. The percentile is 9/5 for s<3 and 17/5 otherwise. A student is strictly
   above it iff the student number is zero.
3. Each seed set has the stated size and one seed in each stated cell.
4. The focal map is injective. Every focal detailed exposure is the simpler
   exposure embedded into categories 0,...,3 of the five-category type.
5. Each focal student's four marginal probabilities are
   [1/2,1/8,1/8,1/4]. A student has all four probabilities strictly between
   zero and one iff it lies in the image of the focal map. Thus the analysis
   population is exactly these twelve students, not an unspecified subset.
6. The joint event H={3,4,5} and every focal exposure equals its first
   coordinate has mass 1/640 (the sum over seed choices includes the mass
   for that one school set).
7. Inverses of the observed focal marginal probabilities are [2,8,8,4].
8. There are 20 choices of H, the full school/seed mass sums to one, and
   1/(20*4^6)>0.

**Junk-value audit.** b(w) is defined even if sum w=0, but only the two
positive vectors occur in fit/mean conclusions, with sums 16 and 22.
All marginal inverses used are explicitly positive numbers. All mean divisors
are 12. The generic augmented mean divides by the population size, which
here is 12. Natural subtractions n_s-1, n_s-4, n_s-6 and 10-r have no
truncation on n_s=7 or 9 and 0<=r<10. Sorted indices are (5,6) for n=7
and (7,8) for n=9, so `List.getD` never uses its zero default. Vector
indices and finite-index embeddings are within bounds, not modular casts.
The empty cylinder s is allowed and states normalization, rather than an
empty-population assertion. There are no matrix inverses in this closure:
fits are defined by actual minimization, not a singular-inverse convention.
There are no analytic partial-domain operations or infinite sums.

## SAP.P037c.T28

For every finitely enumerated type I the theorem asserts the following
conjunction. Different conjuncts have their own independent universal inputs.
There is no existential choice of fitted coefficients in this theorem; whenever
the first conjunct speaks of b,s it assumes they are WLS minimizers.

**General WLS identities.** For every natural p, positive population size
N=|I|, category map D:I→{0,1,2,3}, positive weights w_i, outcomes y_i,
fixed covariates x_i in R^p, pooled coefficient b in R^(4+p), and separate
coefficients s_k in R^(1+p), assume:

1. The linear map with row [four category indicators,x_i] is injective
   (full column rank).
2. For every category k the [1,x_i] linear map restricted to {i:D_i=k}
   is injective.
3. b globally minimizes the pooled weighted residual sum of squares.
4. Every s_k globally minimizes the [1,x] sum with weight w_i inside
   category k and zero outside it.

Put fP_k(i)=b_k+sum_j x_ij b_(4+j) and
fS_k(i)=s_k0+sum_j x_ij s_k(1+j). Then, for every k, both within-category
weighted residual sums vanish. Define the augmented mean of any prediction f
at category k as

    A_k(f)=(1/N)sum_i [1_{D_i=k}w_i(y_i-f(i))+f(i)].

For every k, A_k(fP_k)=sum_i fP_k(i)/N and
A_k(fS_k)=sum_i fS_k(i)/N. For every k,l,
sum_i fP_k(i)/N-sum_i fP_l(i)/N=b_k-b_l.

**One real covariate.** Independently, for every N>0, D, strictly positive
w_i, real x_i and y_i, let

    W_k=sum_{D_i=k}w_i,
    xb_k=sum_{D_i=k}w_i x_i/W_k,
    yb_k=sum_{D_i=k}w_i y_i/W_k,
    Sxx_k=sum_{D_i=k}w_i(x_i-xb_k)^2,
    Sxy_k=sum_{D_i=k}w_i(x_i-xb_k)(y_i-yb_k),
    b_k=Sxy_k/Sxx_k,
    beta=(sum_k Sxy_k)/(sum_k Sxx_k),
    xbar=sum_i x_i/N.

Assume Sxx_k>0 for every k. For every k and coefficient vector c in R^2,
c is a separate WLS minimizer iff c=[yb_k-b_k xb_k,b_k]. For every
c in R^5, it is a pooled WLS minimizer iff
c=[yb_0-beta xb_0,...,yb_3-beta xb_3,beta]. For every k the separate
minus pooled standardized mean equals (b_k-beta)(xbar-xb_k).

**Other conjuncts.** For every five real numbers yb,bk,beta,xb,xbar, the
difference of the expressions yb-bk*xb+bk*xbar and
yb-beta*xb+beta*xbar is (bk-beta)(xbar-xb). Independently, for every p,
N>0, alpha:{0,1,2,3}→R, beta in R^p, x:I→R^p and category k,

    sum_i (alpha_k+sum_j x_ij beta_j)/N
      =alpha_k+sum_j (sum_i x_ij/N) beta_j.

For all five real scalars above, the two standardized expressions are equal
iff bk=beta or xbar=xb. Finally (2-5/4)(5/2-4)=-9/8 and 5-49/8=-9/8.
These last equality tests are scalar one-covariate tests; no general
multi-covariate equality iff statement is present.

**Junk-value audit.** The mean definitions are total for N=0 but every
nontrivial mean assertion requires N>0. Positive Sxx_k with positive
weights forces each category nonempty and hence W_k>0; it also forces
sum Sxx_k>0. Thus the locally introduced divisions never rely on zero
values in a concluded coefficient formula. General full-rank separate
designs also exclude empty categories. p=0 is allowed and corresponds to
intercept-only fits with a genuine empty covariate sum. The natural
subtractions j-4 and j-1 in the row definitions occur only after branches
proving j>=4 and j>=1, respectively; the generated proofs establish the
remaining index is below p. There is no truncated-subtraction effect.
No matrix inverse, default coefficient selection, integrals, extended-real
arithmetic, limits, roots or logs occur.

## SAP.P037c.T33

This theorem has no inputs or hypotheses. It describes a specific abstract
exposure design and regression calculations.

**Population and law.** The population is U={0,1,2,3}×{0,1}. States are
z=(h,b), where h indexes the six pairs
[{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}] and b is a four-vector of Booleans.
Write H_h for that pair and a=[1/10,1/5,3/10,2/5]. For unit (j,e),
the exposure D_z(j,e) is 3 if j belongs to H_h and b_j equals (e=0),
2 if j belongs to H_h and those Booleans differ, 0 if j is outside H_h
and they agree, and 1 if j is outside H_h and they differ. Put

    m(h,b)=(1/6) product_j
       (a_j if b_j else 1-a_j) for j in H_h,
       (1/2) for j outside H_h,
    c_(j,e)=(1/2)*(a_j if e=0 else 1-a_j),
    pi_i(0)=pi_i(1)=1/4,
    pi_i(2)=1/2-c_i, pi_i(3)=c_i.

The observed exposure D0(j,e) is 3 for j<2,e=0, 2 for j<2,e=1,
0 for j>=2,e=0 and 1 for j>=2,e=1. Observed outcomes, by pair, are
[[0,2],[1,0],[3,1],[2,4]].

For any exposure map D, set w_D(i)=1/pi_i(D_i), and let H_D be the
8-by-5 matrix [1_{D=0},1_{D=1},1_{D=2},1_{D=3},c]. The WLS map is

    L_D=(H_D' diag(w_D) H_D)^(-1) H_D' diag(w_D).

The inverse here is Mathlib's nonsingular matrix inverse. Define point
coefficients b0=L_D0 y, point means M_k=b0_k+b0_4/4, and point residual
r=y-H_D0 b0. For state z and any real outcome vector v, the full-control
contrast is (L_Dz v)_3-(L_Dz v)_2. The collapsed contrast uses the same
formula with only the four indicator columns (no fifth column).
Define V(f)=sum_z m(z)f(z)^2-(sum_z m(z)f(z))^2.

The fixed variance constants are

    Vfull =
    1574066925743604937750798623088231315086040632174801225920729815316988109390788379330079414475192929
    /171796363313262196427951740421954806512514436622177625713808591915692887084446808987770465290240000,
    Vcol=1453114769225810453/621302156766720000.

These constants are compared to actual refit variances, rather than serving
as the definitions of those variances.

**Assertions, all conjunctive.**

1. There are 96 states, sum_z m(z)=1 and m(z)>0 for every state.
2. For every state z and every category k, exactly two students have
   D_z=k. For every i,k, sum_z m(z)1_{D_z(i)=k}=pi_i(k).
3. H_Dz has injective multiplication map for every z; the indicator-only
   multiplication map is also injective for every z. H_D0 has an injective
   multiplication map as well. For every exposure map D and every unit i,
   w_D(i)>0.
4. b0=[1/13,-2,-14/3,-23/39,180/13], and M is
   [46/13,19/13,-47/39,112/39]. The residuals by pair are
   [[-4/39,17/39],[8/39,-34/39],[11/13,-24/13],[-11/13,24/13]].
5. For every i, pi_i(2)+pi_i(3)=1/2, and sum_i c_i/8=1/4.
6. Define imputed data y_z(i)=y_i+M_(D_z(i))-M_(D0(i)). For every z,
   its full refit contrast equals the full refit residual contrast plus
   M_3-M_2.
7. V(full residual contrast)=Vfull,
   V(collapsed residual contrast)=Vcol,
   and these two variances differ. Also
   V(full imputed-data contrast)=Vfull.
8. 9<Vfull<37/4 and 2<Vcol<5/2.
9. For every state z, data vector v and category k define the full
   standardized refit mean m_z(v,k)=(L_Dz v)_k+(L_Dz v)_4/4.
   (The statement defines this for arbitrary v but the identity uses r,y_z.)
   For every z,k, m_z(y_z,k)=m_z(r,k)+M_k.
10. 305/200<sqrt(Vcol)<307/200 and
    605/200<sqrt(Vfull)<607/200. These open intervals give ordinary
    two-decimal rounding to 1.53 and 3.03, respectively.

The docstring expressly calls this an abstract exposure design, not a
school-and-seed construction.

**Junk-value audit.** Matrix inversion is totalized: a singular square
matrix over R has inverse zero (Mathlib `Matrix.nonsing_inv_apply_not_isUnit`).
The stated positive weights and injective full and collapsed design maps
exclude singular Gram matrices in all refits used here, including the point
fit; thus the inverse is the actual WLS map. Although H_D can be singular
for arbitrary unsupported maps D, the only assertion quantified over all D
is weight positivity and does not invert that matrix. Every pi_i(k) is
strictly positive (the c_i values lie between 1/20 and 9/20), so all inverse
probability weights are genuine. Constants and mean denominators are
positive. Mathlib real square root is zero for negative inputs, but both
inputs here are expressly strictly positive. Variance is a raw-moment
finite formula, meaningful because normalization and positive masses are
conclusions checked separately. Finite embeddings and vector indices stay
within bounds. No truncated subtraction, logarithm, real exponentiation,
integral, extended-real conversion, extrema, sequence limits, empty index
type or partial-function default enters this statement.
