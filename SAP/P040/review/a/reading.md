# Blind reading of P040

Saved before opening `claims.json` or `record.json`. This reads the proposition bodies, not the theorem docstrings as additional hypotheses. All five theorems are closed propositions: there are no parameters, typeclass assumptions, or top-level premises. Their internal implications and quantifiers are given below.

## Shared objects and Mathlib meanings

The count space is `Fin 16`, namely the nonempty finite ordered set of integers 0 through 15. For real p and count k, put

* b_p(k) = choose(15,k) p^k (1-p)^(15-k).
* P_p(E) = sum over k=0,...,15 of b_p(k) if E(k), and 0 otherwise.
* C_p(I) = P_p({k : p belongs to I(k)}), for any function I from counts to subsets of the reals.
* h_k = k/15, v_k = h_k(1-h_k)/15, r_z(k) = z sqrt(v_k), and W_z(k) = [h_k-r_z(k),h_k+r_z(k)]. These are closed, untruncated real intervals.
* A_p(k) = P_p({j : k <= j}) and B_p(k) = P_p({j : j <= k}), both inclusive tails.
* E(k) = {p in [0,1] : A_p(k) >= 1/40 and B_p(k) >= 1/40}.
* H(k) = {p in [0,1] : A_p(k) >= 1/20}.
* f(p) = p^14(15-14p).
* R2(x,w) means w-1/200 <= x < w+1/200. R6(x,w) means w-1/2000000 <= x < w+1/2000000. R1(x,w) means w-1/20 <= x < w+1/20. All are half-open rounding cells; negative ties are handled by the same inequalities.

`Nat.choose` is the ordinary natural binomial coefficient. The subtraction 15-k in its exponent is natural subtraction, but k<=15, so it is the ordinary nonnegative difference. P is defined for every real p as a finite polynomial sum; the probability interpretation applies for p in [0,1]. Set.Icc and Set.Ioo mean inclusive and strict endpoint inequalities, respectively. The square root is Mathlib's nonnegative real square root (zero on nonpositive arguments). Every v_k above is nonnegative.

Define the following two reusable propositions by their full content:

**Arithmetic A:** h_14=14/15; v_14=14/3375; r_(49/25)(14)^2=33614/2109375; 8070/10000 < h_14-r_(49/25)(14) < 8071/10000; 10595/10000 < h_14+r_(49/25)(14) < 10596/10000; R2(h_14-r_(49/25)(14),81/100); R2(h_14+r_(49/25)(14),106/100); 1 < h_14+r_(49/25)(14); and 4/5 is not in W_(49/25)(14).

**Obstruction O:** First, for every I : {0,...,15} -> subsets of R, if 4/5 is not in I(14), then C_(4/5)(I) <= 5298209257/6103515625 and C_(4/5)(I) < 19/20. Independently, for every real-valued function ell on {0,...,15}, if 4/5 < ell(14), then P_(4/5)({k : ell(k)<=4/5}) <= 5298209257/6103515625 and that probability is <19/20. There is no monotonicity or interval-shape assumption on I or ell.

## T1

The conjunction of all the following assertions:

1. b_(4/5)(14)=805306368/6103515625 and this mass is >1/20.
2. O holds.
3. 4/5 is not in the open interval (81/100,106/100).
4. For every real l, R2(l,81/100) implies 4/5<l.
5. A holds.
6. For every real z, if 19599/10000<=z and z<=19601/10000, then all of the following hold:
   * For every k in {0,...,15}, membership 4/5 in W_z(k) is equivalent to 9<=k<=13; separately, that membership is equivalent to (4/5-h_k)^2 <= z^2 v_k; separately, h_k-r_z(k)<=4/5 is equivalent to k<=13.
   * C_(4/5)(W_z)=24866193408/30517578125, and it is <19/20.
   * P_(4/5)({k : h_k-r_z(k)<=4/5})=25417304461/30517578125, and it is <19/20.
   * P_(4/5)({k : 4/5<h_k-r_z(k)})=5100273664/30517578125, and it is >1/20 and >1/40.

The order in the last clause is universal z, first range premise, second range premise, then the conjunction, with universal k confined to its first component. There is no definition or assertion of a normal quantile in this theorem.

## T2

The conjunction of:

1. R2(h_14,93/100).
2. For every real p (without a [0,1] premise), A_p(14)=f(p) and B_p(14)=1-p^15.
3. f is continuous on R; f is strictly increasing on [0,1]; p -> 1-p^15 is strictly decreasing on [0,1]. Strict increase/decrease on a set quantifies over every pair of its elements in increasing order.
4. For every real p, f has derivative 210p^13(1-p) at p. For every p in (0,1), that derivative expression is positive. Also f(0)=0 and f(1)=1.
5. There exist real L, then real U, then real L_one, such that all the following are true together:
   * .680515<L<.680516, .998313<U<.998314, and .720603<L_one<.720604.
   * f(L)=1/40, f(L_one)=1/20, U^15=39/40, and U=(39/40)^(1/15), with the last power a real power.
   * For every p in [0,1], f(p)=1/40 implies p=L. Independently, for every p in [0,1], f(p)=1/20 implies p=L_one. Independently, for every p in [0,1], 1-p^15=1/40 implies p=U.
   * E(14)=[L,U], H(14)=[L_one,1], L<L_one<4/5, R2(L,.68), and R2(U,1).
6. For every real L, then every real U, if L in [0,1], U in [0,1], f(L)=1/40, and U^15=39/40, then R6(L,.680515) and R6(U,.998314).
7. A_(4/5)(14)=5100273664/30517578125, B_(4/5)(14)=29443836301/30517578125, A_(4/5)(14)>1/20, and B_(4/5)(14)>=1/40.
8. 4/5 belongs to E(14) and H(14).
9. For every p in [0,1], C_p(E)>=19/20 and C_p(H)>=19/20.
10. O holds.

The existential endpoints in item 5 are actual real roots, not their rounded approximations. The implications in item 6 do not stand in place of endpoint existence: item 5 separately asserts it.

## T3

R2(h_14,.93) and the entire arithmetic proposition A. In particular this includes the squared-radius identity, both strict endpoint brackets, both two-place rounding assertions, the upper endpoint exceeding one, and exclusion of .8 from the reconstructed closed Wald interval. It has no stochastic coverage assertion.

## Regression data and objects used by T4 and T5

The data have 30 rows, indexed by Fin 30 in the following order. Treatment, book, cafe, and bulk entries are exact reals (the decimal notation in this table represents terminating rationals):

|day|treatment|book|cafe|bulk|
|---:|---:|---:|---:|---:|
|1|0|181.71|393.52|84.20|
|2|0|134.35|367.57|81.15|
|3|1|163.55|293.35|100.05|
|4|0|85.65|201.92|17.05|
|6|1|141.90|293.21|102.71|
|7|0|171.00|305.03|69.19|
|8|1|119.90|420.96|98.15|
|9|1|267.60|302.88|160.35|
|10|1|290.15|381.19|172.51|
|11|1|168.00|252.55|19.80|
|12|1|249.05|296.13|55.49|
|13|0|225.55|427.95|180.31|
|14|0|129.30|358.84|160.32|
|15|0|196.40|341.07|57.98|
|16|1|200.25|329.18|81.02|
|17|0|423.56|310.92|32.35|
|18|0|184.75|246.09|50.82|
|19|1|178.65|314.99|30.80|
|20|1|83.90|319.55|122.36|
|21|0|132.35|362.47|49.88|
|22|1|112.05|389.00|76.62|
|23|1|120.65|326.86|42.45|
|24|1|450.95|400.49|151.70|
|25|1|130.75|233.00|63.05|
|26|0|96.75|359.00|120.13|
|27|0|167.90|329.00|19.05|
|28|0|143.80|349.00|59.91|
|29|1|200.00|428.44|114.12|
|30|0|88.60|334.07|24.97|
|31|1|147.60|286.00|108.12|

Total is exactly book+cafe+bulk rowwise. Outcomes o=0,1,2,3 are, respectively, total, bulk, cafe, book. Put dbar=(sum of the days)/30, f_c=(number of rows with day mod 7=c)/30 for c=0,...,6, and w_c(i)=1_{day_i mod 7=c}-f_c. These are seven centered weekday columns.

X_0 is the 30-by-2 matrix with rows (1,treatment). X_1 is the 30-by-9 matrix with rows (1,treatment,day-dbar,w_0,...,w_5). X_orig is the 30-by-10 matrix obtained by also including w_6. All indexing starts at zero, so coefficient 1 means treatment.

For any natural K, matrix X with 30 rows and K columns, outcome vector y, and t in Fin K, define M_X=(X^T X)^(-1)X^T, beta_X(y)=M_X y, e_X(y)=y-X beta_X(y), V_X(y,t)=[30/(30-K)] sum_i [M_X(t,i)e_X(y)(i)]^2, and Q_X(y,t)=beta_X(y)(t)^2/V_X(y,t). Matrix inverse is Mathlib's nonsingular inverse (zero on a singular matrix). Matrix multiplication and matrix-vector multiplication use finite sums. Rank is the real dimension of the image of v -> Xv; `mulVecLin` is precisely this linear map, so injectivity means column independence. Scalar divisions are total real divisions, with 1/0=0. Only K=2 and K=9 are used for the statistics in these theorems.

For Boolean a (false = unadjusted, true = adjusted), q_(a,o)=Q_(X_a)(outcome_o,1), and nu_a=30-rank(X_0) if false, or 30-rank(X_orig) if true. This subtraction is performed in the naturals before coercion to R.

Constants:

* b_c=-146561/16484; V_c=42131842162249950707521/161509653387533360000; Q_c=12767624825803755635000/42131842162249950707521.
* b_b=955199/41210; V_b=10415886991743115636339/23072807626790480000; Q_b=12396039010057804992800/10415886991743115636339.
* The table of stated q values is:

|a|o=0 (total)|o=1 (bulk)|o=2 (cafe)|o=3 (book)|
|---|---|---|---|---|
|false|263679812816672/522999591200175|23273498735648/15141092298015|1492978176032/21949506186495|9067019347232/22381571766655|
|true|1200277903320876335774/280628848000463708694463|Q_b|Q_c|3084161273413343448962/24391999904970062376441|

The two reference functions are

N(q)=1-sqrt(2/pi) integral_0^(sqrt(q)) exp(-u^2/2) du,

g_nu(t)=Gamma((nu+1)/2)/[sqrt(nu*pi)Gamma(nu/2)] (1+t^2/nu)^(-(nu+1)/2),

S(q,nu)=1-2 integral_0^(sqrt(q)) g_nu(t) dt.

`Gamma` is Mathlib's real Gamma function, the real part of its complex Gamma function; at positive arguments it is Euler's Gamma function. The power in g is real exponentiation, exp(exponent*log(base)) when base>0. The interval integrals are oriented Lebesgue/Bochner integrals for real volume: integral over (a,b] minus integral over (b,a]. They are zero if not interval integrable. Here the relevant q's are asserted positive and nu is asserted 21 or 28, so the intended integrands are continuous on finite intervals, with strictly positive bases and nonsingular Gamma factors.

Put g21(t)=4^10/[pi*choose(20,10)*sqrt(21)] /(1+t^2/21)^11. Finally, the reusable **mismatch M** says R2(N(q_(true,2)),.58), not R2(N(q_(true,2)),.59), R2(N(q_(true,1)),.28), and not R2(N(q_(true,1)),.29).

## T4

The conjunction of:

1. X_1 is injective; rank(X_1)=9; rank(X_orig)=9; nu_true=21.
2. beta_(X_1)(cafe)(1)=b_c; V_(X_1)(cafe,1)=V_c; beta_(X_1)(bulk)(1)=b_b; V_(X_1)(bulk,1)=V_b; V_c>0; V_b>0.
3. b_c^2/V_c=Q_c; b_b^2/V_b=Q_b; q_(true,2)=Q_c; q_(true,1)=Q_b; and each of Q_c,Q_b lies strictly between 0 and 8/5.
4. R1(b_c,-8.9), R1(sqrt(V_c),16.2), R1(b_b,23.2), R1(sqrt(V_b),21.2).
5. The eight R6 assertions in this table:

|quantity|six-place center|
|---|---:|
|b_c|-8.891107|
|sqrt(V_c)|16.151244|
|Q_c|.303040|
|sqrt(Q_c)|.550491|
|b_b|23.178816|
|sqrt(V_b)|21.247014|
|Q_b|1.190109|
|sqrt(Q_b)|1.090921|

6. .58198<N(q_(true,2))<.58199 and .27530<N(q_(true,1))<.27531.
7. M holds.
8. R2(S(q_(true,2),21),.59) and R2(S(q_(true,1),21),.29).

## T5

The conjunction of:

1. Fin 30 has cardinality 30; rank(X_0)=2; rank(X_1)=9; rank(X_orig)=9; X_0 and X_1 are injective.
2. For every row i, sum_(c=0,...,6) w_c(i)=0. The image of X_orig equals the image of X_1.
3. For every Boolean a, nu_a is 21 if a is true, otherwise 28.
4. For every real t, g_21(t)=g21(t).
5. .58779<S(q_(true,2),21)<.58780 and .28766<S(q_(true,1),21)<.28767.
6. R2(S(q_(true,2),nu_true),.59) and R2(S(q_(true,1),nu_true),.29).
7. For every Boolean a, then every o in Fin 4, all of these hold together: q_(a,o) equals its table value above; 0<q_(a,o); q_(a,o)<=q_(false,1); S(q_(a,o),nu_a)>.1; N(q_(a,o))>.1; S(q_(false,1),28)<=S(q_(a,o),nu_a); N(q_(false,1))<=N(q_(a,o)).
8. q_(false,1)<8/5; .22533<S(q_(false,1),28)<.22534; .21504<N(q_(false,1))<.21505.
9. M holds.

## Mathlib source checks performed while blind

Read the definitions of `Matrix.inv` in `LinearAlgebra/Matrix/NonsingularInverse.lean` (inverse determinant times adjugate; singular matrices give zero), `Matrix.rank` in `LinearAlgebra/Matrix/Rank.lean` (finrank of the image), matrix-vector multiplication/linearization in `Data/Matrix/Mul.lean` and `LinearAlgebra/Matrix/ToLin.lean`, real powers in `Analysis/SpecialFunctions/Pow/Real.lean`, real Gamma in `Analysis/SpecialFunctions/Gamma/Basic.lean`, square root in `Analysis/Real/Sqrt.lean`, interval integrals in `MeasureTheory/Integral/IntervalIntegral/Basic.lean`, and interval and strict-monotonicity definitions in `Order/Interval/Set/Defs.lean` and `Order/Monotone/Defs.lean`. No SAP definition is treated as an unexplained mathematical assumption.
