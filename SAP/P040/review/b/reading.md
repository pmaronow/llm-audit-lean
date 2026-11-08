# Blind reading of the Challenge statements

This file was written after reading only the Defs and Challenge Lean files and the relevant Mathlib definitions, before opening `claims.json` or `record.json`. Challenge docstrings are descriptions, not additional hypotheses. All five theorems have no parameters or external hypotheses: each asserts the entire closed proposition described below. Implications inside those propositions are identified explicitly.

## Shared finite probability and interval definitions

The count space is the nonempty finite set D = {0,1,...,15} (`Fin 16`). For every real p and k in D define

* b_p(k) = choose(15,k) p^k (1-p)^(15-k), where choose is the ordinary natural binomial coefficient, coerced to the reals.
* P_p(E) = sum over all k in D of b_p(k) if E(k), and zero otherwise. This is a finite sum, with no measure-theoretic probability hypotheses. On 0 <= p <= 1 it is the Binomial(15,p) probability of E. Outside that range it is just the specified polynomial sum.
* C_p(I) = P_p({k : p belongs to I(k)}) for every function I : D -> subsets of R. No measurability, interval shape, or nonemptiness requirement is imposed on I(k).
* h(k) = k/15, v(k) = h(k)(1-h(k))/15, r_z(k) = z sqrt(v(k)), and W_z(k) = [h(k)-r_z(k), h(k)+r_z(k)]. These are closed real intervals, with no clipping to [0,1].
* A_p(k) = P_p({j : k <= j}); B_p(k) = P_p({j : j <= k}). Both tails include k.
* E(k) = {p in [0,1] : A_p(k) >= 1/40 and B_p(k) >= 1/40}.
* J(k) = {p in [0,1] : A_p(k) >= 1/20}.
* g(p) = p^14(15-14p), for every real p.

Write R2(x,w) for w-1/200 <= x < w+1/200; R6(x,w) for w-1/2000000 <= x < w+1/2000000; and R1(x,w) for w-1/20 <= x < w+1/20. These are explicit half-open neighborhoods, not an invocation of a rounding function.

Here and below [a,b] means a <= x <= b and (a,b) means a < x < b. Mathlib's real square root is the nonnegative square root on nonnegative arguments and zero on negative arguments. Here v(k) >= 0 since 0 <= k <= 15. The exponent 15-k is natural subtraction, but it does not truncate because k <= 15.

Define H to be the following complete conjunction (the shared `printedWaldArithmetic`):

1. h(14) = 14/15 and v(14) = 14/3375.
2. r_(49/25)(14)^2 = 33614/2109375.
3. 8070/10000 < h(14)-r_(49/25)(14) < 8071/10000.
4. 10595/10000 < h(14)+r_(49/25)(14) < 10596/10000.
5. R2(h(14)-r_(49/25)(14),81/100) and R2(h(14)+r_(49/25)(14),106/100).
6. 1 < h(14)+r_(49/25)(14), and 4/5 does not belong to W_(49/25)(14).

Define M to be the following complete conjunction (the shared `methodFreeObstruction`):

1. For every I : D -> subsets of R, if 4/5 does not belong to I(14), then C_(4/5)(I) <= 5298209257/6103515625 and C_(4/5)(I) < 19/20.
2. For every ell : D -> R, if 4/5 < ell(14), then P_(4/5)({k : ell(k) <= 4/5}) <= 5298209257/6103515625 and this same probability is < 19/20.

The universal functions I and ell are chosen before their respective implication hypotheses. No purported coverage hypothesis is assumed.

## SAP.P040.T1

This theorem asserts all of the following, simultaneously:

1. b_(4/5)(14) = 805306368/6103515625 and 1/20 < b_(4/5)(14).
2. M.
3. 4/5 does not belong to (81/100,106/100).
4. For every real l, if R2(l,81/100), then 4/5 < l.
5. H.
6. For every real z, first assuming 19599/10000 <= z and then z <= 19601/10000, all of the following hold:
   * For every k in D, all three equivalences hold: 4/5 belongs to W_z(k) iff 9 <= k <= 13; 4/5 belongs to W_z(k) iff (4/5-h(k))^2 <= z^2 v(k); and h(k)-r_z(k) <= 4/5 iff k <= 13.
   * C_(4/5)(W_z) = 24866193408/30517578125 and C_(4/5)(W_z) < 19/20.
   * P_(4/5)({k : h(k)-r_z(k) <= 4/5}) = 25417304461/30517578125 and this probability is < 19/20.
   * P_(4/5)({k : 4/5 < h(k)-r_z(k)}) = 5100273664/30517578125 and this probability is > 1/20 and > 1/40.

There is no normal distribution, quantile, or inverse distribution function in this statement. Its multiplier conclusion is universally quantified over the explicit closed real interval.

## SAP.P040.T2

This theorem asserts the following conjunction:

1. R2(h(14),93/100).
2. For every real p, A_p(14) = g(p) and B_p(14) = 1-p^15. This quantifier is over all reals, not only probability parameters.
3. g is continuous on R, is strictly increasing on [0,1], and p -> 1-p^15 is strictly decreasing on [0,1]. The two strict monotonicity assertions quantify, respectively, over every a in [0,1], then every b in [0,1], and assume a < b.
4. For every real p, g has derivative 210 p^13(1-p) at p. For every p in (0,1), that derivative expression is positive. Also g(0)=0 and g(1)=1.
5. There exist real numbers L, U, L_one, in that order, such that all of the following hold jointly:
   * 680515/1000000 < L < 680516/1000000; 998313/1000000 < U < 998314/1000000; and 720603/1000000 < L_one < 720604/1000000.
   * g(L)=1/40, g(L_one)=1/20, U^15=39/40, and U=(39/40)^(1/15), where the last power is a real power.
   * For every p in [0,1], g(p)=1/40 implies p=L. Separately, for every p in [0,1], g(p)=1/20 implies p=L_one. Separately, for every p in [0,1], 1-p^15=1/40 implies p=U.
   * E(14)=[L,U] and J(14)=[L_one,1].
   * L < L_one < 4/5; R2(L,68/100); and R2(U,1).
6. For every real L, then every real U, assuming in order L in [0,1], U in [0,1], g(L)=1/40, and U^15=39/40, one has R6(L,680515/1000000) and R6(U,998314/1000000). These L,U are universally bound independently of the existential witnesses in item 5.
7. A_(4/5)(14)=5100273664/30517578125, B_(4/5)(14)=29443836301/30517578125, A_(4/5)(14)>1/20, and B_(4/5)(14)>=1/40.
8. 4/5 belongs to E(14) and to J(14).
9. For every real p, assuming p in [0,1], both C_p(E)>=19/20 and C_p(J)>=19/20.
10. M.

The endpoint assertions identify actual roots and entire sets; the reported decimal centers are not substituted for those roots as interval endpoints.

## SAP.P040.T3

This theorem asserts exactly R2(h(14),93/100) and H. It has no probability-coverage conclusion, no assertions about sampling or treatment counts, and no quantification over a population parameter.

## Shared regression and reference definitions for T4 and T5

There are 30 row indices i in {0,...,29}. The day, treatment, book-sales, cafe-sales, and bulk-sales functions are fixed, explicit vectors; their complete entries are given in the data table at the end of this file. Total sales are book+cafe+bulk at the same row. Outcome indices o=0,1,2,3 mean total, bulk, cafe, book, respectively. Boolean a=false means unadjusted and a=true means adjusted.

Let d_i be the recorded day, t_i the recorded treatment, dbar=(sum_i d_i)/30, and f_c=(sum_i 1_{d_i mod 7=c})/30 for c=0,...,6. Put w_ci=1_{d_i mod 7=c}-f_c. Define three real matrices:

* X0, with 30 rows and 2 columns, whose row i is (1,t_i).
* X1, with 30 rows and 9 columns, whose row i is (1,t_i,d_i-dbar,w_0i,w_1i,w_2i,w_3i,w_4i,w_5i).
* Xfull, with 30 rows and 10 columns, whose row i is (1,t_i,d_i-dbar,w_0i,w_1i,w_2i,w_3i,w_4i,w_5i,w_6i).

For any real 30-by-K matrix X define O(X)=(X^T X)^(-1) X^T, beta(X,y)=O(X)y, e_i(X,y)=y_i-(X beta(X,y))_i, and

V(X,y,j) = [30/(30-K)] sum_i [O(X)_(j,i) e_i(X,y)]^2;
Q(X,y,j) = beta(X,y)_j^2 / V(X,y,j).

All arithmetic in this display, including 30-K, is real. Matrix multiplication and matrix-vector multiplication are the usual finite sums. Mathlib's matrix inverse is det(X^T X)^(-1) times its adjugate over R; on a singular matrix it is zero, not a generalized inverse. Real division by zero is totalized to zero. The concrete theorems assert injectivity/rank and positive statistics or variances, rather than assuming those properties.

Let q_(a,o)=Q(X1,y_o,1) when a=true, and Q(X0,y_o,1) when a=false. Column 1 is the treatment coefficient, with zero-based indexing. Let df_true=30-rank(Xfull) and df_false=30-rank(X0); these subtractions take place in the natural numbers before coercion to R. Matrix rank is the real dimension of the image of v -> Xv; all these images are finite dimensional. Equality of `LinearMap.range` means equality of column spaces. Injectivity of X.mulVecLin means that for every pair of coefficient vectors u,v, Xu=Xv implies u=v.

The exact squared-statistic table s_(a,o) is:

| a | o=0: total | o=1: bulk | o=2: cafe | o=3: book |
|---|---|---|---|---|
| false | 263679812816672/522999591200175 | 23273498735648/15141092298015 | 1492978176032/21949506186495 | 9067019347232/22381571766655 |
| true | 1200277903320876335774/280628848000463708694463 | 12396039010057804992800/10415886991743115636339 | 12767624825803755635000/42131842162249950707521 | 3084161273413343448962/24391999904970062376441 |

Use the following constants:

* b_c=-146561/16484; V_c=42131842162249950707521/161509653387533360000; Q_c=12767624825803755635000/42131842162249950707521.
* b_b=955199/41210; V_b=10415886991743115636339/23072807626790480000; Q_b=12396039010057804992800/10415886991743115636339.

For real q,nu define the literal integral expressions

N(q)=1-sqrt(2/pi) integral from 0 to sqrt(q) of exp(-u^2/2) du;

f_nu(t)=Gamma((nu+1)/2)/[sqrt(nu*pi) Gamma(nu/2)] times (1+t^2/nu)^(-(nu+1)/2);

S(q,nu)=1-2 integral from 0 to sqrt(q) of f_nu(t) dt;

f21(t)=4^10/[pi choose(20,10) sqrt(21)] / (1+t^2/21)^11.

The exponent in f_nu is a real exponent. Mathlib's real power at positive base x is exp(y log x); the U formula above also has positive base. Real Gamma is the real part of the complex Gamma function; for positive arguments it is the ordinary Euler gamma integral. The interval integrals are oriented Lebesgue/Bochner integrals: integral over (a,b] minus integral over (b,a], using real Lebesgue measure. Mathlib defines a nonintegrable integral to be zero, but here the normal integrand is continuous and, at nu=21 or 28, the Student integrand has positive base and denominator and is continuous on each finite interval. Thus those cases are ordinary finite integrals. No statistical null-distribution assertion is built into N or S. On q>=0 and nu>0 they are the usual two-sided normal and Student-t reference tail areas at absolute statistic sqrt(q).

Let Z denote the conjunction R2(N(q_(true,2)),58/100), not R2(N(q_(true,2)),59/100), R2(N(q_(true,1)),28/100), and not R2(N(q_(true,1)),29/100).

## SAP.P040.T4

This theorem asserts all of the following without hypotheses:

1. X1.mulVecLin is injective; rank(X1)=9; rank(Xfull)=9; and df_true=21.
2. beta(X1,cafe)_1=b_c, V(X1,cafe,1)=V_c, beta(X1,bulk)_1=b_b, and V(X1,bulk,1)=V_b.
3. V_c>0 and V_b>0; b_c^2/V_c=Q_c; b_b^2/V_b=Q_b; q_(true,2)=Q_c; and q_(true,1)=Q_b.
4. 0<Q_c<8/5 and 0<Q_b<8/5.
5. R1(b_c,-89/10), R1(sqrt(V_c),162/10), R1(b_b,232/10), and R1(sqrt(V_b),212/10).
6. The following eight six-place assertions all hold:

| quantity x | center w in R6(x,w) |
|---|---|
| b_c | -8891107/1000000 |
| sqrt(V_c) | 16151244/1000000 |
| Q_c | 303040/1000000 |
| sqrt(Q_c) | 550491/1000000 |
| b_b | 23178816/1000000 |
| sqrt(V_b) | 21247014/1000000 |
| Q_b | 1190109/1000000 |
| sqrt(Q_b) | 1090921/1000000 |

7. 58198/100000<N(q_(true,2))<58199/100000 and 27530/100000<N(q_(true,1))<27531/100000.
8. Z.
9. R2(S(q_(true,2),21),59/100) and R2(S(q_(true,1),21),29/100).

## SAP.P040.T5

This theorem asserts the following conjunction, without hypotheses:

1. The cardinality of {0,...,29} is 30; rank(X0)=2; rank(X1)=9; rank(Xfull)=9; and both X0.mulVecLin and X1.mulVecLin are injective.
2. For every row i, sum over c=0,...,6 of w_ci is zero. The column spaces of Xfull and X1 are equal.
3. For every Boolean a, df_a=21 if a=true and df_a=28 otherwise.
4. For every real t, f_21(t)=f21(t).
5. 58779/100000<S(q_(true,2),21)<58780/100000 and 28766/100000<S(q_(true,1),21)<28767/100000.
6. R2(S(q_(true,2),df_true),59/100) and R2(S(q_(true,1),df_true),29/100).
7. For every Boolean a, then every outcome o in {0,1,2,3}, simultaneously:
   * q_(a,o)=s_(a,o).
   * 0<q_(a,o)<=q_(false,1).
   * 1/10<S(q_(a,o),df_a) and 1/10<N(q_(a,o)).
   * S(q_(false,1),28)<=S(q_(a,o),df_a) and N(q_(false,1))<=N(q_(a,o)).
8. q_(false,1)<8/5.
9. 22533/100000<S(q_(false,1),28)<22534/100000 and 21504/100000<N(q_(false,1))<21505/100000.
10. Z.

The minimum in item 7 compares numerical reference values for these eight actual data-derived statistics. It is not a statement about an exact finite-sample null law or arbitrary regression data.

## Mathlib source trace

The interpretations above follow `Nat.choose` in `Data/Nat/Choose/Basic.lean:50`; real square root in `Analysis/Real/Sqrt.lean:112`; real power in `Analysis/SpecialFunctions/Pow/Real.lean:35`; real Gamma and its positive-argument integral in `Analysis/SpecialFunctions/Gamma/Basic.lean:402,405`; interval integral and its Lebesgue notation in `MeasureTheory/Integral/IntervalIntegral/Basic.lean:659,668`; matrix-vector multiplication in `Data/Matrix/Mul.lean:698`; `Matrix.mulVecLin` in `LinearAlgebra/Matrix/ToLin.lean:286`; matrix inverse in `LinearAlgebra/Matrix/NonsingularInverse.lean:169`; matrix rank in `LinearAlgebra/Matrix/Rank.lean:134`; real dimension in `LinearAlgebra/Dimension/Finrank.lean:62`; linear-map range in `Algebra/Module/Submodule/Range.lean:57`; closed/open intervals in `Order/Interval/Set/Defs.lean:51,76`; strict monotonicity in `Order/Monotone/Defs.lean:99,106`; continuity in `Topology/Defs/Basic.lean:155`; and derivative in `Analysis/Calculus/Deriv/Basic.lean:130`. Paths are relative to the provided Mathlib source root.

## Complete fixed regression data

| row i | day | treatment | book | cafe | bulk |
|---|---|---|---|---|---|
| 0 | 1 | 0 | 18171/100 | 9838/25 | 421/5 |
| 1 | 2 | 0 | 2687/20 | 36757/100 | 1623/20 |
| 2 | 3 | 1 | 3271/20 | 5867/20 | 2001/20 |
| 3 | 4 | 0 | 1713/20 | 5048/25 | 341/20 |
| 4 | 6 | 1 | 1419/10 | 29321/100 | 10271/100 |
| 5 | 7 | 0 | 171 | 30503/100 | 6919/100 |
| 6 | 8 | 1 | 1199/10 | 10524/25 | 1963/20 |
| 7 | 9 | 1 | 1338/5 | 7572/25 | 3207/20 |
| 8 | 10 | 1 | 5803/20 | 38119/100 | 17251/100 |
| 9 | 11 | 1 | 168 | 5051/20 | 99/5 |
| 10 | 12 | 1 | 4981/20 | 29613/100 | 5549/100 |
| 11 | 13 | 0 | 4511/20 | 8559/20 | 18031/100 |
| 12 | 14 | 0 | 1293/10 | 8971/25 | 4008/25 |
| 13 | 15 | 0 | 982/5 | 34107/100 | 2899/50 |
| 14 | 16 | 1 | 801/4 | 16459/50 | 4051/50 |
| 15 | 17 | 0 | 10589/25 | 7773/25 | 647/20 |
| 16 | 18 | 0 | 739/4 | 24609/100 | 2541/50 |
| 17 | 19 | 1 | 3573/20 | 31499/100 | 154/5 |
| 18 | 20 | 1 | 839/10 | 6391/20 | 3059/25 |
| 19 | 21 | 0 | 2647/20 | 36247/100 | 1247/25 |
| 20 | 22 | 1 | 2241/20 | 389 | 3831/50 |
| 21 | 23 | 1 | 2413/20 | 16343/50 | 849/20 |
| 22 | 24 | 1 | 9019/20 | 40049/100 | 1517/10 |
| 23 | 25 | 1 | 523/4 | 233 | 1261/20 |
| 24 | 26 | 0 | 387/4 | 359 | 12013/100 |
| 25 | 27 | 0 | 1679/10 | 329 | 381/20 |
| 26 | 28 | 0 | 719/5 | 349 | 5991/100 |
| 27 | 29 | 1 | 200 | 10711/25 | 2853/25 |
| 28 | 30 | 0 | 443/5 | 33407/100 | 2497/100 |
| 29 | 31 | 1 | 738/5 | 286 | 2703/25 |
