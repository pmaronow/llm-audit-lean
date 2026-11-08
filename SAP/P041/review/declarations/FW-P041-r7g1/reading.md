# Blind reading (saved before opening claims.json or record.json)

This reading uses only closure.json, the Challenge and Defs sources, Lean's
printed elaborations, and the relevant Mathlib definitions. All 139 distinct
declarations in the five closures were read. The generated `_proof_*`
declarations are ordinary numeral-instance proofs (`Nat.AtLeastTwo` and, in T5,
`NeZero`); they impose no mathematical hypothesis. Their printed bodies are in
scratch/ClosurePrint.log. Fractions and terminating decimals below denote exact
real numbers unless a natural-number operation is expressly indicated.

## SAP.P041.T1

Source: Challenge/Part1.lean:10–13; Defs/Part3.lean:11–47;
Defs/Part1.lean:11–22. The docstring describes a stipulated exponential
countermodel, equal non-null hazard ratios, unequal twelve-hour contrasts, and
positive binomial expressions at four counts.

Unfold all its SAP functions as follows, for real q and t:

- A(q) = -2 log(q)/12 and N(q) = -3 log(q)/12, with Mathlib Real.log.
- S(h,t) = exp(-h t), with Mathlib Real.exp.
- D(q) = exp(-A(q)12) - exp(-N(q)12).
- B(n,k,p) = (Nat.choose n k cast to R) p^k (1-p)^(n-k), where n,k
  are natural numbers, both powers have natural exponents, and n-k is natural
  subtraction.

The statement is the conjunction of:

1. For every real q, if 0<q, then if q<1, all of the following hold:
   A(q)>0, N(q)>0, A(q)/N(q)=2/3, N(q)/A(q)=3/2, 2/3≠1,
   S(A(q),12)=q², S(N(q),12)=q³, and D(q)=q²(1-q).
2. For every pair of reals q,t, if 0<q, then q<1, then 0≤t, the
   two equalities S(A(q),t)=q^(t/6) and S(N(q),t)=q^(t/4) hold.
   These last two powers are Mathlib real powers (Real.rpow), not natural powers.
3. A closed conjunction with no hypotheses:
   S(A(4/5),12)=16/25, S(N(4/5),12)=64/125, D(4/5)=16/125;
   S(A(99/100),12)=9801/10000,
   S(N(99/100),12)=970299/1000000, D(99/100)=9801/1000000;
   D(4/5)-D(99/100)=118199/1000000>0;
   D(4/5)/D(99/100)=128000/9801>13;
   A(4/5)/N(4/5)=A(99/100)/N(99/100)=2/3≠1;
   1-S(N(4/5),12)=61/125, 1-S(A(4/5),12)=9/25,
   1-S(N(99/100),12)=29701/1000000,
   1-S(A(99/100),12)=199/10000;
   each of these four removal probabilities is strictly between zero and one;
   B(150,75,61/125)>0, B(150,52,9/25)>0,
   B(76,1,29701/1000000)>0, B(75,3,199/10000)>0.

There is no quantified observed dataset, random variable, independence assumption,
or probability law in this proposition. B is an explicit binomial mass formula.

Junk conventions: Real.log(0)=0 and Real.log(x)=log(|x|) for negative x;
division by zero is zero. Neither can affect the asserted hazard identities,
because 0<q<1 implies log(q)<0 and A(q),N(q)>0; both supplied q's are interior.
All constant denominators and D(99/100) are nonzero. Real.rpow is the real part
of complex exponentiation; at base zero it uses 0^0=1 and 0^y=0 for y≠0,
and negative bases have a cosine extension. Its bases here are positive.
Nat.choose n k=0 for k>n, while n-k truncates to zero; all four k's satisfy
k≤n, so no such boundary is used. Ordinary natural powers use x^0=1.
No integrals, extrema, limits, empty types, or partial-function defaults occur.

## SAP.P041.T2

Source: Challenge/Part1.lean:15–19; Defs/Part4.lean:11–52;
Defs/Part1.lean:11–19,24–25,33–48. The docstring explicitly restricts this
to numerical Wald and pooled-contrast calculations plus existence of an
exponential countermodel; it lists omitted interpretations and finer numbers.

Definitions, fully unfolded into real arithmetic and Mathlib notions:

- R(v,x) means v-0.0005≤x≤v+0.0005 (both endpoints included).
- L(h,s)=s/h; Z(h,s)=h log(h)/s.
- I(h,s) is the closed real interval
  [exp(log(h)-(49/25)s/h), exp(log(h)+(49/25)s/h)].
- W(hF,sF,hA,sA) = (log(hF)-log(hA)) /
  sqrt((sF/hF)²+(sA/hA)²), using Mathlib Real.sqrt.
- P(z)=2 Phi(-|z|), where Phi is Mathlib's cdf of gaussianReal 0 1,
  the normal probability measure with mean zero and variance one. Thus Phi(x)
  is the real-valued probability of (-infinity,x]. This is a reference p-value
  formula, without a sampling-law assertion.
- C(nP,nN,rP,rN)=(1-rP/nP)-(1-rN/nN), all four arguments real.
- A(q)=-2 log(q)/12, N(q)=-3 log(q)/12, and
  D(q)=exp(-A(q)12)-exp(-N(q)12).

The seven conjuncts, with separate quantifiers in each, are:

1. For all real h,s, R(0.691,h) then R(0.318,s) imply
   0.80<|Z(h,s)|<0.81 and |Z(h,s)|<1.
2. For all real hF,sF,hA,sA, in that order, the four hypotheses
   R(0.691,hF), R(0.318,sF), R(0.629,hA), R(0.091,sA), in that order,
   imply |log(hF)-log(hA)|<0.21 L(hF,sF),
   0.21 L(hF,sF)<(49/25)L(hF,sF),
   |log(hF)|<(49/25)L(hF,sF), and both 1 and hA belong to I(hF,sF).
3. For all real h,s with R(0.691,h) and R(0.318,s), the lower endpoint
   of I(h,s) lies strictly in (0.279,0.282), and the upper endpoint strictly
   in (1.700,1.706).
4. For all real hF,sF,hA,sA with the four hypotheses from (2),
   0.18<W(hF,sF,hA,sA)<0.21.
5. The closed bounds |P(Z(0.691,0.318))-0.42|≤0.005 and
   |P(W(0.691,0.318,0.629,0.091))-0.845|≤0.0005.
6. The closed arithmetic statements
   C(150,150,52,75)=23/150,
   C(75,76,3,1)=-51/1900, and their difference is 1027/5700>0;
   C(150,150,82,101)=19/150,
   C(75,76,7,3)=-307/5700, and their difference is 343/1900>0.
7. There exist real qA and then real qF such that
   0<qA<1, 0<qF<1, A(qA)/N(qA)=2/3,
   A(qF)/N(qF)=2/3≠1, D(qF)>0, and 13 D(qF)<D(qA).

There are no other hypotheses. In particular sA is bound even in conjunct (2),
where its value does not enter the conclusion. The existential does not specify
the two q values or the exact two contrasts.

Junk conventions: log and division have the totalizations described in T1,
but all rectangle values h,s,hA,sA are strictly positive. The squared terms in
W are strictly positive, so the square root and its denominator are positive.
Real.sqrt returns zero on negative inputs; that extension is unused. The C
denominators are positive constants. The existential explicitly excludes the
logarithm and zero-rate boundaries. gaussianReal uses a Dirac measure at zero
variance, but the variance is exactly one here. Mathlib's cdf is total even for
nonprobability measures, but gaussianReal 0 1 is a genuine probability measure;
its interval measures are finite, so ENNReal.toReal(infinity)=0 is never used.
The interval is an ordinary Set.Icc, not an infimum, supremum or partial choice.
No nonintegrable means, natural subtractions, empty index types, or limit
conventions enter this theorem. All approximation tolerances are explicit.

## SAP.P041.T3

Source: Challenge/Part1.lean:21–24; Defs/Part5.lean:11–37;
Defs/Part1.lean:27–31. The docstring says that the three directional
percentages fail separately, the symmetric percentages round to the printed
numbers, and the latter understate the directional increases.

Write R(a,b)=100(a/b-1), S(a,b)=100|a-b|/((a+b)/2), and
H(x,k) for (k cast from Z to R)-1/2≤x<(k cast to R)+1/2.
These are all the substantive SAP definitions, using real arithmetic and
absolute value, and the usual integer cast. The three conjuncts are:

1. A closed list of exact equalities and rounding assertions:
   R(75/150,52/150)=575/13,
   R(92/150,69/150)=100/3,
   R(62/100,32/100)=375/4;
   575/13-36=107/13>1/2,
   100/3-29=13/3>1/2,
   375/4-64=119/4>1/2;
   not H(R(75/150,52/150),36),
   not H(R(92/150,69/150),29),
   not H(R(62/100,32/100),64);
   H(R(75/150,52/150),44),
   H(R(92/150,69/150),33),
   H(R(62/100,32/100),94);
   S(75,52)=4600/127, S(92,69)=200/7, S(62,32)=3000/47;
   H(S(75,52),36), H(S(92,69),29), H(S(62,32),64).
2. For every real a and then real b, if 0<b, then b<a,
   R(a,b)-S(a,b)=100(a-b)²/(b(a+b)) and R(a,b)-S(a,b)>0.
   No upper bound of one is imposed; this is a homogeneous count or
   probability comparison formula.
3. The closed differences
   R(75,52)-S(75,52)=13225/1651,
   R(92,69)-S(92,69)=100/21,
   R(62,32)-S(62,32)=5625/188.

Junk conventions: real division by zero would give zero, making R(a,0)=-100
and S(a,-a)=0; these inputs are excluded by the positive supplied constants
and 0<b<a in the universal formula. All literal denominators are nonzero.
H specifies a half-open rounding cell, including the lower half tie and
excluding the upper; none of these numerical values lies on a tie.
Integer casts are exact, with no clipping. All squares are natural powers.
There are no logs, roots, real powers, expectations, empty types, extrema,
limits, or partial defaults.

## SAP.P041.T4

Source: Challenge/Part1.lean:26–29; Defs/Part6.lean:11–30;
Defs/Part1.lean:27–31. The docstring calls these corrected directional
percentages, a conditional 76-removal calculation, and a symmetric repair.

Use R(a,b)=100(a/b-1), S(a,b)=100|a-b|/((a+b)/2), and
H(x,k) meaning (k:real)-1/2≤x<(k:real)+1/2, with k an integer.
There are no variables, hypotheses, or quantifiers. The entire proposition is
the conjunction of these closed real assertions:

- R(75/150,52/150)=575/13; it satisfies H(-,44), and its distance from
  44.23 is at most 0.005.
- R(92/150,69/150)=100/3; it satisfies H(-,33), and its distance from
  33.33 is at most 0.005.
- R(62/100,32/100)=375/4=93.75, and satisfies H(-,94).
- R(76/150,52/150)=600/13; it satisfies H(-,46), and its distance from
  46.15 is at most 0.005.
- S(75,52)=4600/127, S(92,69)=200/7, S(62,32)=3000/47,
  satisfying H(-,36), H(-,29), H(-,64), respectively.

The formula with numerator 76 is arithmetic on a supplied hypothetical input;
the proposition does not assert an empirical count of 76 or bind a variable
that represents one. It contains no inference from data collection to counts.

Junk conventions: real division is total with 1/0=0, but every denominator
here, including the directional comparison baselines and symmetric averages,
is strictly positive. The integer rounding cells are half-open as in T3;
no supplied value is a tie. Integer casts are exact and all decimals denote
exact rationals. No other listed junk-value mechanisms occur.

## SAP.P041.T5

Source: Challenge/Part1.lean:31–34; Defs/Part7.lean:11–65;
Defs/Part2.lean:11–33. The docstring describes a uniformly balanced order
with scrutiny, no own-treatment direct effect, a zero slow contrast, and a
positive accelerated expectation; it includes all six orders, a general
formula, m=50, arbitrary treatment-independent patterns, and an independent
assignment boundary.

All SAP definitions unfolded:

- For natural m let U_m=Fin(2m), the ordered set of natural ranks 0,...,2m-1,
  and B_m=Finset.univ.powersetCard m, the finite set of all m-element subsets
  of U_m. A subset z records cited ranks.
- For any natural n, subset z of Fin(n), and r:Fin(n),
  Y_z(r)=1 if there exists s:Fin(n) with s<r and s not in z, and 0 otherwise.
  This is an ordinary decidable existential, not a choice of a witness.
- C_m(z,Y)=(sum over r in z of Y(r))/m minus
  (sum over r in Finset.univ \\ z of Y(r))/m, with m cast to real.
- E_m(f)=(sum over z in B_m of f(z))/(card B_m cast to real).
  This is an explicit finite arithmetic average, not a Bochner integral.
- K(z)=card {r in Fin(n): every s:Fin(n) with s≤r belongs to z}, a natural
  number counting the initial uninterrupted cited ranks.
- Q_m(k)=card {z in B_m: K(z)=k}/card B_m, both cardinalities cast to real.
- The row predicate Row(z,y,c,u,d), on a subset of Fin(4), a real-valued
  vector y:Fin(4)->R, and reals c,u,d, is the conjunction Y_z=y,
  (sum over z of Y_z)/2=c, (sum over Finset.univ \\ z of Y_z)/2=u,
  and C_2(z,Y_z)=d. This checks the whole vector as well as its means.
- The independent boundary J is (1/16) times the sum over every subset z of
  Fin(4) of (1/4) times sum over r:Fin(4) of
  (2 if r in z, else -2)Y_z(r). Thus it is the mean of a
  Horvitz–Thompson contrast under four independent fair binary assignments;
  it is not a difference using random realized arm sizes.

The ten conjuncts, retaining the order and scope of quantifiers, are:

1. For every natural n (implicit), every z,z' subset of Fin(n), then every
   r:Fin(n), if for every s:Fin(n), s<r implies (s in z iff s in z'),
   then Y_z(r)=Y_z'(r). Thus arbitrary changes at r and later ranks have
   no effect on r's outcome when its past is fixed; balance is not imposed
   on these potential assignments.
2. For every natural m with 1≤m, for every subset z of U_m, C_m(z,0)=0.
3. For every natural m with 1≤m, E_m(z -> C_m(z,0))=0.
4. B_2 consists of exactly the six subsets below, and the six Row predicates
   have the following vectors and means (all ranks zero based):

   | z | Y_z | cited mean | uncited mean | contrast |
   |---|---|---|---|---|
   | {2,3} | (0,1,1,1) | 1 | 1/2 | 1/2 |
   | {1,3} | (0,1,1,1) | 1 | 1/2 | 1/2 |
   | {1,2} | (0,1,1,1) | 1 | 1/2 | 1/2 |
   | {0,3} | (0,0,1,1) | 1/2 | 1/2 | 0 |
   | {0,2} | (0,0,1,1) | 1/2 | 1/2 | 0 |
   | {0,1} | (0,0,0,1) | 0 | 1/2 | -1/2 |

5. Separately repeats the six contrasts above; their E_2 average is 1/6,
   is not zero, and E_2 of the zero-outcome contrast is zero.
6. For every natural m, if 1≤m, the following all hold:
   for every natural k≤m,
   Q_m(k)=choose(2m-k-1,m-1)/choose(2m,m), with both choose values
   cast to real and all subtractions in their arguments natural;
   E_m(K cast to real)=m/(m+1);
   for every z in B_m, sum over cited ranks of Y_z = m-K(z) and
   sum over uncited ranks of Y_z = m-1 (these two subtractions are real);
   E_m((sum over cited ranks of Y_z)/m)=m/(m+1);
   E_m(C_m(z,Y_z))=1/(m(m+1)), and this average is strictly positive.
7. For every natural m with 1≤m, for every z in B_m, the uncited mean is
   (m-1)/m (real subtraction).
8. The closed m=50 instance:
   E_50(K)=50/51, E_50(cited mean)=50/51;
   every z in B_50 has uncited mean 49/50;
   E_50(C_50(z,Y_z))=1/2550 and is nonzero.
9. For every natural m with 1≤m, and then for every real-valued vector
   Y:Fin(2m)->R, E_m(z -> C_m(z,Y))=0. The Y is chosen outside
   the averaging over z, so it cannot depend on z.
10. The particular fixed vector (0,0,1,1) has expected contrast zero for
    m=2, and J=0.

Junk conventions: the contrast is defined even at m=0 using division by
zero, but every assertion about this contrast has m≥1 or m=2 or 50.
B_m is nonempty for every m (including B_0={empty set}), with size
choose(2m,m)>0; neither E_m nor Q_m averages over an empty family.
For m≥1 both realized arms in B_m have m elements. C_m is also used
off the balanced support in the zero-vector assertion; both sums are zero,
so its use of the fixed denominator m is harmless there. Empty finite sums
use zero; the first rank's outcome is zero because it has no predecessor,
which is substantive intended behavior. In (6), 0≤k≤m and m≥1 ensure
2m-k≥1 and m≥1, so neither natural subtraction truncates in the displayed
choose formula; the choose denominators are nonzero. Real subtractions
m-K and m-1 do not truncate. Fin(n) is empty at n=0; (1) is then vacuous
in r, but its positive-size instances are not, and all design clauses
have positive size. The Fin(4) literals 0,1,2,3 are in range; their modular
numeral convention does not change a rank. Natural cardinality and rank
casts to reals are exact. J sums over 16 subsets and divides by 4 and 16,
so it has no empty-arm division even on all-cited or all-uncited orders.
There are no logs, square roots, real powers, nonintegrable means, extended
real casts, infima/suprema, limits, or partial-function defaults in T5.
