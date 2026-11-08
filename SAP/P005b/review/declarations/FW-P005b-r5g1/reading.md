# Blind reading of T15–T19

This file was written before opening `claims.json` or `record.json`. I read every
entry of `closure.json`, the source of every listed declaration, the five target
docstrings, and the generated declarations with no source line by `#print` in
`scratch/BlindCheck.lean` (successful compilation, output in
`scratch/BlindCheck.out`). No Solution or proof from another review was read.

## Common fully expanded notation

The following is mathematical abbreviation for the actual Mathlib operations,
not additional assumptions. A population of size n and dimension d is an
arbitrary triple of functions x: Fin n -> (Fin d -> R), yT,yC: Fin n -> R.
Its constructor and projections impose no equations. Put I_n = {0,...,n-1}.
All sums below are finite Finset sums in R. Natural-number sizes in real
expressions are coerced to R.

For S a subset of I_n, C(S)=I_n\\S, and

* M_S(a) = (sum over i in S of a_i)/|S|;
* M(a) = (sum over i in I_n of a_i)/n;
* D(n,m) = the Finset of every m-element subset of I_n;
* E_m(f) = (sum over S in D(n,m) of f(S))/|D(n,m)|;
* V_m(f) = E_m((f-E_m(f))^2);
* Pr_m(A) = |{S in D(n,m): A(S)}|/|D(n,m)|;
* cov_S(a,b) = M_S(ab)-M_S(a)M_S(b), and cov(a,b)=cov_{I_n}(a,b).

Thus cov_S uses divisor |S|, not |S|-1. There is no general measure,
integral, hidden distribution, random seed, or independence premise: the
probability is explicitly uniform complete randomization.

Write x_i dot v = sum over k in Fin d of x_{ik}v_k; xbar_S has coordinates
M_S(x_k). Write G_{kl}=M(x_k x_l), h_i=sum_k x_{ik}^2, and
kappa = sSup {h_i/n: i in Fin n} in R. Standardization means xbar_{I_n}=0
as a function and G=the d by d identity matrix. For n>0, kappa is the maximum
of this nonempty finite set. Put p=m/n, q=(n-m)/n,
b(y)_k=M(y x_k), and b=p b(yT)+q b(yC). The common residuals are
eT_i=yT_i-M(yT)-x_i dot b and eC_i=yC_i-M(yC)-x_i dot b.
For arbitrary eT,eC, eobs(S)_i=eT_i if i in S and eC_i otherwise, and
star(P,S,eT,eC)=(xbar_S-xbar_C(S)) dot b(eobs(S)).

These expand all the population, vector, residual, randomization, expectation,
variance and probability definitions that occur below into functions, finite
sums, arithmetic, identity matrices and real suprema. Matrix-vector products
are the usual coordinate finite sums. No inverse matrix occurs in the five
statement closures.

## SAP.P005b.T15

Source: `Challenge/Part1.lean:7–10`, `Defs/Part3.lean:13–46` and the
Part1/Part2 closure entries. Its docstring describes corrected control and
treatment covariance coefficients, the intermediate treatment fraction, and
their combination. It does not mention expectations or OLS in the statement.

Quantification is first all natural t,c, then hypotheses t>=2 and c>=2. Set
n=t+c and define the real rational coefficients

* T=(n-t)(n-2t)/((n-1)(n-2)t^2);
* U=-(n-2t)/((n-1)(n-2)t);
* Hc=c(n-1)/((c-1)n), Ht=t(n-1)/((t-1)n),
  J=t^2(n-1)/(c(t-1)n).

The first three conclusions are

1. Hc/(n-1)-U*t(n-1)/((c-1)n)=1/(n-2);
2. -Ht/(n-1)+T*J=(n-tn)/((n-2)(t-1)n);
3. (n-tn)/((n-2)(t-1)n)=-1/(n-2).

Then, independently for every natural d, arbitrary functions x,yT,yC with
the indicated sizes, and S subset I_n, if |S|=t, let
A=cov_S(h,yT), B=cov_C(S)(h,yC). The fourth conclusion is

  (Hc*B-Ht*A)/(n-1)+T*J*A-U*t(n-1)/((c-1)n)*B
    = B/(n-2)-A/(n-2).

The definitions `controlCoefficient`, `treatedCoefficient` and
`covarianceCombination` are exactly the left sides just written, with T and U
being `NTTT n t` and `NTTC n t`. Population data are unrestricted; in
particular this is an algebraic identity for covariances, not an expectation
identity for regression bias. There is no standardization assumption.

Junk-value audit: R division sets a/0=0, but t,c>=2 makes n,n-1,n-2,t,t-1,c,c-1
strictly positive, S and C(S) nonempty, and D(n,t) nonempty. `(n-2 : R)` and
`(n-2t : R)` are real subtraction after casting n,t, as confirmed by pp.all;
there is no truncated subtraction in these coefficients. t+c is natural
addition. Empty dimension d=0 is allowed: all dot sums and h_i are zero,
and the covariance combination specializes consistently to zero. No log,
sqrt, rpow, integral, limsup, sInf, sSup or partial function is used.

## SAP.P005b.T16

Source: `Challenge/Part1.lean:12–15`, `Defs/Part3.lean:48–90`, and its
Part1/Part2 closure entries. The docstring describes corrected finite indicator
calculations, coefficient simplification and the complement relation.

For every n,m in N, assume n>=3, 0<m<n; then for every a,b,c:Fin n->R assume
sum_i a_i=sum_i b_i=sum_i c_i=0. These premises precede a conjunction of all
the following assertions. Let Z_i(S)=1 if i in S and 0 otherwise, and put

  L=sum_i a_i b_i c_i,
  u2=m(m-1)/(n(n-1)), u3=m(m-1)(m-2)/(n(n-1)(n-2)),
  R(S)=sum_i sum_{j!=i} Z_i Z_j a_i b_i c_j,
  H(S)=sum_i sum_{j!=i} sum_{k!=i,k!=j} Z_i Z_j Z_k a_i b_j c_k,
  T=(n-m)(n-2m)/((n-1)(n-2)m^2),
  U=-(n-2m)/((n-1)(n-2)m).

1. For every i!=j, E_m(Z_i Z_j)=u2.
2. For every pairwise distinct i,j,k, E_m(Z_i Z_j Z_k)=u3.
3. E_m(R)=sum_i sum_{j!=i} E_m(Z_i Z_j) a_i b_i c_j.
4. E_m(R)=-u2*L.
5. E_m(H)=2*u3*L.
6. E_m(M_S(a)M_S(b)M_S(c)) is m^(-3) times the sum of
   E_m(sum_i Z_i a_i b_i c_i),
   E_m(sum_i sum_{j!=i} Z_i Z_j (a_i b_i c_j+a_i b_j c_i+a_j b_i c_i)),
   and E_m(H).
7. The same treated third moment equals m^(-3)*(m/n-3*u2+2*u3)*L.
8. It also equals T*M(abc).
9. E_m(M_S(a)M_S(b)M_C(S)(c))=U*M(abc).
10. m^(-3)*(m/n-3*u2+2*u3)=T/n.
11. E_m(R)=u2*(sum_i sum_{j!=i} a_i b_i c_j).
12. The last expression equals
    u2*((sum_i sum_j a_i b_i c_j)-sum_i a_i b_i c_i).
13. T/n=(n-m)(n-2m)/(n*m^2*(n-1)*(n-2)).
14. For every S in D(n,m), M_C(S)(c)=-(m/(n-m))*M_S(c).
15. U=-(m/(n-m))*T.

The erased Finsets in the source implement exactly the unequal-index sums
above, with ordered pairs/triples, not unordered pairs/triples. No SAP notion
remains beyond those expanded here and in the common notation.

Junk-value audit: n>=3 and 0<m<n guard every denominator and ensure both
arms and the design are nonempty. In u2 and u3, m-1 and m-2 are REAL
subtractions; m=1 and m=2 are allowed, and the falling products give zero
where appropriate, without division by those factors. The n-2m numerator may
be negative and is a real difference. All index sums are finite and defined,
including the zero sums over erased sets. There are enough population indices
for the distinct-index clauses. No unmeasurable functions, integrals, extrema,
logarithms, square roots, rpow, limsup/liminf, or partial-function defaults occur.

## SAP.P005b.T17

Source: `Challenge/Part1.lean:17–22`, `Defs/WholeW1.lean:13–60`,
`Defs/Part4.lean:14–57`, and all other closure entries. The actual theorem
uses T17WholeStatement, which contains all of T17Statement plus two more
groups. Its docstring states a variance bound for the actual common-residual
term, deterministic contraction and order, and its stochastic order, allowing
dimension zero.

Use the common expanded notation. For arbitrary delta:Fin n->R, let

  mu_k=(1/n)*sum_j x_{jk} delta_j,
  K_ij=sum_k x_{ik}(x_{jk}delta_j-mu_k),
  Q_ij=(sum_k x_{ik}x_{jk})delta_j,
  C_nm=(1/(q*m*n))^2*m(n-m)/(n(n-1)),
  F(delta)=M(h*delta^2)/(p*q*n*(n-1)).

The conjunction has the following independently universally quantified groups.

1. For every n,d,m and P, if n>=2, 0<m<n and G=I, then for every delta:
   for each i, sum_j K_ij^2 <= sum_j Q_ij^2;
   C_nm*sum_i sum_j Q_ij^2
   = (1/(q*m*n))^2*n^2*m(n-m)/(n(n-1))*sum_j (1/n)*h_j*delta_j^2;
   C_nm*sum_i sum_j Q_ij^2=F(delta);
   and F(delta)<=kappa/(p*q*(n-1))*M(delta^2).
   Here x need not have zero mean; G=I is the only covariate premise.

2. For every n,d,P with n>0 and G=I and every a:Fin n->R,

     sum_i sum_j ((x_i dot x_j)*a_j)^2
       =sum_j a_j^2*x_j dot ((sum_i x_i x_i^T)*x_j)
       =n*sum_j a_j^2*h_j.

   The middle expression is literal finite matrix-vector multiplication; its
   l-th coordinate is sum_k (sum_i x_{il}x_{ik})x_{jk}.

3. For every n,d,m,P with n>0 and every real K, if M(yT^2)<=K and
   M(yC^2)<=K, then M((eT-eC)^2)<=4K. There is no Gram, centering,
   arm-size or sign premise on K here. The same common slope occurs in both
   residuals and cancels, so delta_i=eT_i-eC_i is
   (yT_i-yC_i)-M(yT-yC), even without standardization.

4. For every pair of natural sequences d_n,m_n and every population sequence
   P_n:Population n (d_n), assume exactly:

   * for every n>=3, d_n<=n and 0<m_n<n;
   * there exists K>=0, uniform in n, such that for every n>=3,
     M(yT_n^2)<=K, M(yC_n^2)<=K, and for every k in Fin d_n,
     M(x_{n,k}^2)<=K;
   * eventually (as n tends to infinity) xbar_n=0 and G_n=I;
   * there exist real lo,hi with 0<lo<hi<1 such that for every n>=3,
     lo<m_n/n<hi.

   With delta_n=eT_n-eC_n, conclude F_n(delta_n)=O(kappa_n/n) and
   M(delta_n^2)=O(1). IsBigO here means an eventual inequality of real
   absolute values |f_n|<=C|g_n| for a fixed nonnegative C. There is no
   positive lower bound on d_n and no leverage-decay condition.

5. For every n,d,m,P with n>=2, 0<m<n and xbar=0, G=I, use the actual
   common residuals defined from P and m, and delta=eT-eC. Put
   star(S)=(xbar_S-xbar_C(S)) dot [(1/n)sum_i x_i eobs(S)_i]. Then

     V_m(star) <= C_nm*sum_i sum_j K_ij^2
               <= C_nm*sum_i sum_j Q_ij^2.

6. For every d_n,m_n,P_n satisfying precisely the four sequence premises in
   group 4 (the separate name wholeW1Standing repeats those premises),

     star_n=O_p(sqrt(kappa_n*d_n/n)).

   Expanded: for every real epsilon>0 there exist M>0 and natural n0 such
   that for every n>=n0,
   |{S in D(n,m_n): |star_n(S)|>M*sqrt(kappa_n*d_n/n)}|
     /|D(n,m_n)| < epsilon.

All quantification of populations is independent in the six groups; no later
group silently acquires the premises of an earlier one. `centered`,
`commonResidual`, `observedResidual`, `populationSlope`, `N`, `wholeW1Delta`,
`wholeW1Kernel` and `wholeW1Star` are exactly the finite coordinate expressions
given above, with `leverage` h_i and `kappa` the normalized maximum. In
particular star is defined from residuals, not defined to equal a bound or
remainder conclusion.

Junk-value audit: finite assertions guard n and, wherever required, m and n-m,
so their uniform probability, means and rational bounds have nonzero
denominators. Group 3 has unrestricted m, but m enters only the common slope
that cancels in delta; it causes no zero division by m or n-m. All subtractions
in rational formulas are in R. Sequences have no premises at n=0,1,2:
means/design averages there can evaluate to zero by division by zero, and the
supremum of an empty real set at n=0 is zero. These finitely many terms do not
affect an atTop order or probability assertion. For all relevant n>=3,
D(n,m_n) is nonempty and kappa is the maximum of a nonempty finite bounded
set. Thus neither unbounded-set nor empty-set sSup junk drives a conclusion.
At eventual standardized sizes, kappa>=0, so sqrt has its ordinary
nonnegative argument; Real.sqrt of negative inputs is zero in general, but
this default cannot affect the eventual assertion. For d_n=0, all x vectors,
matrix sums, h_i, kappa and star are genuinely zero for n>0; the d=0 identity
matrix is the empty matrix. The zero rate requires star=0 with high
probability, which is actually satisfied, not excused by division by zero.
All random variables are finite functions. No integrability issue, infinite
toReal, log, rpow, sInf, limsup/liminf, or partial-function default is involved.

## SAP.P005b.T18

Source: `Challenge/Part1.lean:24–27`, `Defs/Part4.lean:59–82`, and its
Part1/Part2 closure entries. The docstring describes a weighted normal equation,
three bracketed vector expressions, and identification with the common-residual
term.

The assertion is a conjunction of two independently quantified groups.

1. For every n,d,m,P with n>0 and 0<m<n, every S subset I_n with |S|=m,
   and every eT,eC:Fin n->R, assume the vector normal equation

     p*(1/n)sum_i eT_i*x_i+q*(1/n)sum_i eC_i*x_i=0.

   No standardization or mean-zero residual hypothesis occurs in this group.
   Set A=(1/n)sum_i x_i(eT_i-eC_i), B=(1/n)sum_i x_i eC_i, and
   U=(1/n)sum_{i in S} x_i(eT_i-eC_i). The four conclusions are

     B=-p*A;
     U+B=(1/n)sum_{i in S} [x_i(eT_i-eC_i)+(1/p)B];
     U+B=(1/n)sum_{i in S} [x_i(eT_i-eC_i)-A];
     (1/q)*xbar_S dot (U+B)
       =(1/q)*xbar_S dot ((1/n)sum_{i in S}[x_i(eT_i-eC_i)-A]).

   Each vector equality means equality at every k in Fin d.

2. For every n,d,m,P with n>0, 0<m<n, xbar=0 and G=I, and every
   S in D(n,m), let eT,eC be the common residuals from the common notation,
   and U,B the preceding vector formulas. Conclude

     xbar_S-xbar_C(S)=(1/q)*xbar_S;
     p*(1/n)sum_i x_i eT_i+q*(1/n)sum_i x_i eC_i=0;
     star(P,S,eT,eC)=(1/q)*xbar_S dot (U+B).

There is no inverse, fitted-sample rank condition, probability bound, or
asymptotic assertion. The general normal equation is assumed for arbitrary
residuals in group 1 and established for the specific common residuals in
group 2, so it is not assumed in place of the population calculation.

Junk-value audit: n>0 and 0<m<n imply p,q,n,m,n-m and both arm sizes are
strictly positive, and the design is nonempty. Thus all displayed fractions
and means have their ordinary meanings. Real subtractions are ordinary
subtractions. At d=0, vector equalities concern the unique function from the
empty type, dot sums are zero and the assertions consistently specialize.
This dimension does not make the universally quantified positive-dimensional
assertions vacuous. No sSup/kappa, sInf, log, sqrt, rpow, integral, infinite
toReal, limsup/liminf, or partial-function default occurs.

## SAP.P005b.T19

Source: `Challenge/Part1.lean:29–32`, `Defs/Part5.lean:13–19`, and the
Part1 closure entries. The docstring explicitly calls the printed universal
conjunction false, referring to an uncentered covariance variance bound.

The statement is NOT a positive assertion of a covariance formula: it is the
negation of a universally quantified conjunction. The quantified positive
assertion being negated says: for every natural n,m with n>=4 and 0<m<n,
every arm t in the two-element type {treated,control}, and arbitrary
a,b:Fin n->R, if A_t(S)=S for treated and C(S) for control and r=m for
treated and the natural n-m for control, then BOTH

  E_m(cov_A_t(S)(a,b))=((r-1)*n)/(r*(n-1))*cov(a,b)

and

  V_m(cov_A_t(S)(a,b))
    <= 2*(n-r)/(r*(n-1))*M((ab-M(ab))^2)
       +2*(n-r)*n/(r^3*(n-1))*M(a^2)*M(b^2).

Here cov_A uses divisor r; all the M's on the right are full-population
means, and the first right-hand variance is of RAW a_i*b_i, not of a product
of centered a and b. No zero-mean assumption on a,b occurs. `Arm`, its
constructors/recursor/case eliminator, the generated match function,
`armSet` and `armSize` implement precisely the two alternatives just stated.
`covarianceBound` is exactly the displayed right side, not a free hypothesis.

Classically the actual theorem therefore asserts the existence of some
n>=4, 0<m<n, t,a,b for which at least one of these two conclusions fails.
It does not itself identify that witness, assert both conclusions fail, or
state a corrected positive lemma. Whether this negation refutes the canonical
claim must await step 2.

Junk-value audit: the positive assertion's guards imply n>=4, 1<=r<n,
so r,n,n-1 and |D(n,m)| are positive. The natural subtraction n-m in
armSize is nontruncated in this range. r-1, n-1 and n-r inside real formulas
are real differences (pp.all confirms the covarianceBound casts). For r=1,
sample covariance is genuinely zero; no factor r-1 occurs in a denominator.
All finite population arrays are measurable with finite moments. No empty
arm/design average, integral convention, sSup/sInf, log, sqrt, rpow, infinite
toReal, limsup/liminf or partial-function default can manufacture a refutation.

## Remaining closure bookkeeping

The generated `_proof_1` declarations in the closure were printed and read:
`T15Statement._proof_1`, `T16Statement._proof_1`, `T17Statement._proof_1`,
`biasEstimate._proof_1` and `covarianceBound._proof_1` merely construct
`Nat.AtLeastTwo` evidence for the numerals 2, 3 or 4 used by real casts and
powers. They supply no extra premise, mathematical restriction, or assertion
about data. `Population.mk` and its three projections, `Arm.rec`,
`Arm.casesOn` and `armSet.match_1` were also printed and read. They have
exactly the ordinary constructor/projection/elimination meanings recorded
above. No closure entry was excluded as a proof-detail shortcut.
