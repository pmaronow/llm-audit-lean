# Blind reading

This file was saved before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. I read the five Challenge statements and docstrings, all five Defs source files, both import aggregators, and every entry in `closure.json`. I also printed all 249 distinct compiler-generated proof declarations in the closures in `scratch/ClosureProofs.lean` (output in `scratch/ClosureProofs.out`). Those declarations only supply natural-numeral `AtLeastTwo` instances, `NeZero` instances for finite types, the ordinary continuous real scalar action, and surjectivity of the identity ring homomorphism. They contain no statistical hypothesis or conclusion. Source locations below refer to the text actually read.

For mathematical readability, the following are mathematical abbreviations for fully unfolded expressions, not additional assumptions:

* Counts are the sixteen integers D = {0,...,15}, implemented by Mathlib `Fin 16` (a natural value with proof that it is less than 16).
* b_p(k) = choose(15,k) p^k (1-p)^(15-k), with choose the natural binomial coefficient, cast into the real numbers. All powers in this formula have natural exponents.
* P_p(E) = sum over k=0,...,15 of b_p(k) if E(k), otherwise 0. A rule I assigns an arbitrary subset of the real numbers to each count; C_p(I) = P_p({k : p belongs to I(k)}). The predicates in the sums are decided classically.
* h_k = k/15, v_k = h_k(1-h_k)/15, r_z(k) = z sqrt(v_k), and W_z(k) = the closed real interval [h_k-r_z(k),h_k+r_z(k)]. Square root is Mathlib's nonnegative real square root.
* R2(x,w) means w-1/200 <= x < w+1/200. R6(x,w) means w-1/2000000 <= x < w+1/2000000. R1(x,w) means w-1/20 <= x < w+1/20. These predicates specify proximity to the displayed value, with the lower tie included and upper tie excluded; they do not themselves require w to be on a decimal grid.
* T_p(k) = P_p({j : j>=k}) and S_p(k) = P_p({j : j<=k}). E(k) = {p in [0,1] : T_p(k)>=1/40 and S_p(k)>=1/40}. E1(k) = {p in [0,1] : T_p(k)>=1/20}. These are inversion sets of finite binomial tail tests.

## SAP.P040.T1

Location: `SAP/P040/Challenge/Part1.lean:7-20`. There are no outer parameters or hypotheses. The theorem asserts the conjunction below, with definitions in `Defs/Part1.lean` and `Defs/WholeW1.lean`.

1. b_(4/5)(14) = 805306368/6103515625 > 1/20. The same mass is 15(4/5)^14(1/5) = 3*4^14/5^14 = 0.13194139533312. Its complement is 5298209257/6103515625 = 0.86805860466688.
2. For every rule I:D -> subsets of R, if 4/5 is not in I(14), then C_(4/5)(I) <= 5298209257/6103515625 and C_(4/5)(I)<19/20. For every function ell:D -> R, if ell(14)>4/5, then P_(4/5)({k:ell(k)<=4/5}) has the same upper bound and strict inequality. Each universally quantified function is chosen before its exclusion/endpoint hypothesis.
3. 4/5 is outside the open interval (81/100,106/100). For every real l with R2(l,81/100), l>4/5, l>=161/200, and for every real set J contained in [l,infinity), 4/5 is not in J.
4. h_14=14/15; v_14=14/3375; r_(49/25)(14)^2=33614/2109375. The lower Wald endpoint lies strictly between .8070 and .8071; the upper lies strictly between 1.0595 and 1.0596. They satisfy R2 with .81 and 1.06 respectively; the upper is >1 and 4/5 is not in W_(49/25)(14).
5. For every real z in [19599/10000,19601/10000], and then every k in D, 4/5 belongs to W_z(k) iff 9<=k<=13, and equivalently iff (4/5-h_k)^2<=z^2 v_k. Its lower endpoint is <=4/5 iff k<=13. C_(4/5)(W_z) = 24866193408/30517578125 = .814815425593344 <19/20, and equals the sum of b_(4/5)(k) for k=9,...,13. P_(4/5)({k:h_k-r_z(k)<=4/5}) = 25417304461/30517578125 = .832874232578048 <19/20 and also equals 1-T_(4/5)(14). Its complement P_(4/5)({k:4/5<h_k-r_z(k)}) = 5100273664/30517578125 = 19*4^14/5^15 = .167125767421952, greater than both 1/20 and 1/40. The lower failure event is exactly k>=14 and T_(4/5)(14) is that same fraction. For this z the lower rule does not have uniform coverage 19/20 or 39/40: each uniform predicate means, literally, for all real p with 0<=p<=1, the corresponding finite-sum coverage is at least that level.
6. For every real z (no sign restriction) and k in D, r_z(k)^2=z^2 v_k.
7. Let Phi(t) be Mathlib's `ProbabilityTheory.cdf (gaussianReal 0 1) t`. This is the cumulative probability of (-infinity,t] under the actual real Gaussian measure of mean 0 and variance 1. Let A={t in R:39/40<=Phi(t)}, and let q=inf A in the conditionally complete real order. A is nonempty and bounded below; Phi(q)=39/40; for every real t, Phi(t)=39/40 implies t=q. Moreover q belongs to [1.9599,1.9601] and 195996398454005/10^14 < q <195996398454006/10^14. The lower endpoint h_14-r_q(14) is strictly between .807099 and .807100; the upper is strictly between 1.059567 and 1.059568. They satisfy R2 with .81 and 1.06, the upper exceeds 1, and 4/5 is outside W_q(14). Existence and uniqueness here are conclusions, not premises.
8. Every count-based real-set rule excluding 4/5 at 14 fails both uniform levels 19/20 and 39/40, and every real lower rule above 4/5 at 14 fails both levels. These quantifiers impose no interval shape or monotonicity condition.

The docstring describes these as a finite-sample calibration counterexample under an added independent common-probability binomial model. The statement itself operates directly with its binomial count law; it does not construct fifteen independent random variables or assert historical facts about customer observations.

Junk conventions: `15-k` is natural truncated subtraction, but k<=15, so it is the ordinary nonnegative exponent. For p=0 or p=1, natural 0^0=1 is the correct limiting binomial convention. Probabilities are used at p=4/5 or on [0,1]; the algebraic mass function would otherwise be a signed polynomial. Divisors 15, 25, 100, 200, all displayed integer denominators, and 10^14 are positive. `Real.sqrt x` is 0 for x<0, but every v_k>=0 because 0<=k<=15. At k=0 or 15 the zero radius is intentional. Negative z can reverse W_z endpoints and produce the empty set, but membership/coverage statements restrict z to a positive interval, and the unrestricted radius-squared identity is still meaningful. Real `sInf` returns its fallback value (0) on an empty or unbounded-below set; both pathologies are excluded by explicit conclusions about A. The Gaussian variance is 1, excluding the `gaussianReal` zero-variance Dirac branch; its CDF uses real measure values, and the measure is a probability, so conversion of infinity to 0 is immaterial. All count types are inhabited and finite, numerals 9,13,14 are in range, all casts are ordinary exact natural-to-real casts, and finite sums need no integrability assumptions. No log, real power, limsup/liminf, empty index type, or partial-function default occurs in this statement's relevant expressions.

## SAP.P040.T3

Location: `SAP/P040/Challenge/Part1.lean:29-35`. There are no parameters or hypotheses. The assertion is R2(h_14,.93), together with every item of reconstructed arithmetic in item 4 of T1 above: h_14=14/15, v_14=14/3375, r_(49/25)(14)^2=33614/2109375, lower endpoint in (.8070,.8071), upper in (1.0595,1.0596), R2 endpoint values .81 and 1.06, upper >1, and exclusion of .80 from the closed interval. In completely elementary terms the endpoints are 14/15 +/- (49/25)sqrt(14/3375). This is an unconditional arithmetic statement about a supplied count 14 out of 15; it asserts neither the actual customer count nor confidence coverage.

The docstring calls this retained mathematical content P1 and P2, explicitly treating the counts as inputs. Quantification consists only of finite constants; the R2 definitions expand to the two half-open inequalities, without any existential rounding algorithm.

Junk conventions: the only nonrational operation is square root of 14/3375>0. All divisors are positive, count 14 is a valid `Fin 16` numeral (so no reduction modulo the bound changes it), and all powers are natural squares. No natural subtraction, infinite measure, integral, log, real power, infimum, limit, empty index type, or partial-function default influences the result. The general definition of W would permit an empty interval for negative z, but the only multiplier here is 49/25>0.

## SAP.P040.T2

Location: `SAP/P040/Challenge/Part1.lean:22-27`. There are no parameters or outer hypotheses. The assertion is the following conjunction.

1. R2(14/15,.93). For every real p (including p outside [0,1]), T_p(14)=F(p)=p^14(15-14p) and S_p(14)=1-p^15. F is continuous on R, strictly increasing on [0,1], and p -> 1-p^15 is strictly decreasing there. At every real p, F has derivative 210 p^13(1-p); that derivative is positive at every p in (0,1). F(0)=0 and F(1)=1.
2. There exist real numbers L,U,L1, in that order, with .680515<L<.680516, .998313<U<.998314, and .720603<L1<.720604. They obey F(L)=1/40, F(L1)=1/20, U^15=39/40, and U=(39/40)^(1/15), where this last power is real exponentiation. Each root is unique among p in [0,1]: the two F equations identify L and L1, and 1-p^15=1/40 identifies U. E(14)=[L,U] and E1(14)=[L1,1]; L<L1<4/5; R2(L,.68) and R2(U,1).
3. For all reals L,U, if L,U belong to [0,1], F(L)=1/40, and U^15=39/40, then R6(L,.680515) and R6(U,.998314). These are implications about all roots, with L chosen before U and all four premises preceding the conclusion.
4. T_(4/5)(14)=5100273664/30517578125>1/20; S_(4/5)(14)=29443836301/30517578125>=1/40; 4/5 belongs to E(14) and to E1(14).
5. For every real p in [0,1], C_p(E)>=19/20 and C_p(E1)>=19/20. These are uniform finite-sample binomial coverage guarantees for the inversion sets at all counts, not just for count 14.
6. For every arbitrary rule I:D -> subsets of R excluding 4/5 at count 14, C_(4/5)(I)<=5298209257/6103515625<19/20. For every lower rule ell:D -> R with ell(14)>4/5, its lower coverage at p=4/5 obeys the same upper bound and strict inequality. No other restriction is imposed on these rules.

The docstring calls these corrected exact equal-tailed and one-sided binomial intervals and describes endpoint uniqueness, rounding, inclusion, and uniform .95 coverage. The quantification directly uses a fixed binomial law, rather than introducing a sampling process.

Junk conventions: finite-count arithmetic, natural truncated subtraction in b, endpoint 0^0, and exact real casts behave as described for T1. The tail-polynomial identities for all reals are purely algebraic even when their sums are not probabilities. All displayed divisors are positive. The real power uses positive base 39/40 and exponent the inverse of positive real 15, so Mathlib's extension to negative bases or 0^0 is irrelevant. There is no infimum-defined endpoint or default root selection: three actual roots with strict brackets are existential conclusions. The universal-root rounding implication is nonvacuous because those roots are also asserted to exist. Inversion sets are closed level sets intersected with [0,1], so there is no off-domain p in their coverage meaning. No integral, log outside real powers, infinite measure conversion, limit, empty index type, or partial-function default occurs.

## SAP.P040.T4

Location: `SAP/P040/Challenge/Part1.lean:37-42`. There are no parameters or hypotheses. The statement uses the fixed real dataset reproduced below (each decimal is the exact rational with that finite decimal expansion). Row index i is Mathlib `Fin 30`.

|i|day d_i|treatment x_i|book|cafe|bulk|
|--:|--:|--:|--:|--:|--:|
|0|1|0|181.71|393.52|84.20|
|1|2|0|134.35|367.57|81.15|
|2|3|1|163.55|293.35|100.05|
|3|4|0|85.65|201.92|17.05|
|4|6|1|141.90|293.21|102.71|
|5|7|0|171.00|305.03|69.19|
|6|8|1|119.90|420.96|98.15|
|7|9|1|267.60|302.88|160.35|
|8|10|1|290.15|381.19|172.51|
|9|11|1|168.00|252.55|19.80|
|10|12|1|249.05|296.13|55.49|
|11|13|0|225.55|427.95|180.31|
|12|14|0|129.30|358.84|160.32|
|13|15|0|196.40|341.07|57.98|
|14|16|1|200.25|329.18|81.02|
|15|17|0|423.56|310.92|32.35|
|16|18|0|184.75|246.09|50.82|
|17|19|1|178.65|314.99|30.80|
|18|20|1|83.90|319.55|122.36|
|19|21|0|132.35|362.47|49.88|
|20|22|1|112.05|389.00|76.62|
|21|23|1|120.65|326.86|42.45|
|22|24|1|450.95|400.49|151.70|
|23|25|1|130.75|233.00|63.05|
|24|26|0|96.75|359.00|120.13|
|25|27|0|167.90|329.00|19.05|
|26|28|0|143.80|349.00|59.91|
|27|29|1|200.00|428.44|114.12|
|28|30|0|88.60|334.07|24.97|
|29|31|1|147.60|286.00|108.12|

Define y_0=book+cafe+bulk, y_1=bulk, y_2=cafe, y_3=book. Let dbar=(sum_i d_i)/30, f_c=(sum_i 1_{d_i mod 7=c})/30 for c=0,...,6, and g_ci=1_{d_i mod 7=c}-f_c. The 30x2 matrix X0 has row [1,x_i]. The 30x9 matrix X1 has row [1,x_i,d_i-dbar,g_0i,...,g_5i]. The 30x10 matrix Xall appends g_6i to X1. For any 30xK real matrix X, define A(X)=(X^T X)^(-1) X^T using Mathlib matrix inverse; beta(X,y)=A(X)y; e_i=y_i-(X beta)_i; V(X,y,t)=30/(30-K) sum_i (A(X)_(t,i)e_i)^2, with 30-K subtraction in R; Q(X,y,t)=beta_t^2/V(X,y,t). Q_a(o) uses X1 if Boolean a=true and X0 if a=false, outcome y_o, and treatment coordinate t=1. df_a is the natural difference 30-rank(Xall) for true and 30-rank(X0) for false, then cast to R. Matrix rank is the dimension (`finrank`) of the range of its real linear map.

Define N(q)=1-sqrt(2/pi) integral from 0 to sqrt(q) of exp(-u^2/2) du. Define f(nu,t)=Gamma((nu+1)/2)/(sqrt(nu*pi)Gamma(nu/2)) * (1+t^2/nu)^(-(nu+1)/2), where Gamma is Mathlib's real Gamma and the last power has real exponent. Define T(q,nu)=1-2 integral from 0 to sqrt(q) of f(nu,t) dt. These integrals are real Bochner interval integrals against Lebesgue measure, oriented as the integral over (0,b] minus the integral over (b,0].

The unconditional conjunction asserts:

* X1's linear map is injective, rank X1=rank Xall=9, and df_true=21.
* beta(X1,cafe,1)=bC=-146561/16484; V(X1,cafe,1)=vC=42131842162249950707521/161509653387533360000. beta(X1,bulk,1)=bB=955199/41210; V(X1,bulk,1)=vB=10415886991743115636339/23072807626790480000. Both vC,vB are strictly positive.
* bC^2/vC=qC=12767624825803755635000/42131842162249950707521, bB^2/vB=qB=12396039010057804992800/10415886991743115636339, Q_true(2)=qC, and Q_true(1)=qB. Both qC,qB are strictly between 0 and 8/5.
* R1(bC,-8.9), R1(sqrt(vC),16.2), R1(bB,23.2), R1(sqrt(vB),21.2).
* R6(bC,-8.891107), R6(sqrt(vC),16.151244), R6(qC,.303040), R6(sqrt(qC),.550491); R6(bB,23.178816), R6(sqrt(vB),21.247014), R6(qB,1.190109), R6(sqrt(qB),1.090921).
* .58198<N(Q_true(2))<.58199 and .27530<N(Q_true(1))<.27531. The former satisfies R2 at .58 and fails R2 at .59; the latter satisfies R2 at .28 and fails R2 at .29. In contrast R2(T(Q_true(2),21),.59) and R2(T(Q_true(1),21),.29).

The docstring describes the actual fixed adjusted regressions and the discrepancy between normal-reference rounding and printed Student-reference rounding. It does not state a probabilistic sampling model, an exact null distribution, or a theorem about every possible regression dataset.

Junk conventions: the general matrix inverse is total and is 0 for a singular real square matrix; the supplied injectivity of X1 makes X1^T X1 nonsingular, so it is the ordinary inverse in the actual fitted adjusted regressions. Xall is deliberately singular (10 columns, rank 9), but is used only for rank and never inverted in this assertion. The generic definition of V has real denominator 30-K, which could vanish when K=30; the actual adjusted K=9 gives 21. The unadjusted branch has K=2 and denominator 28, and is defined in the closure although T4's concrete Q uses only true. Generic Q divides by V and would return 0 for V=0; actual adjusted cafe/bulk variances are positive conclusions. Square roots return 0 for negative arguments, but all actual q,v and 2/pi are positive. Natural 30-rank in df could truncate; actual rank=9 avoids it. The integrals return 0 for nonintegrable functions; these functions are continuous on the finite intervals for actual nu=21 and actual q>0. Real Gamma is total (at poles it has default values); arguments here are 11 and 21/2, both positive. All bases 1+t^2/21 are >=1, so real-power extensions at 0 or negative bases do not occur; sqrt(21*pi) and Gamma(21/2) are positive. `mod 7` has positive divisor 7 and labels seven categories; all vector accesses are bounded `Fin` indices, no partial lookup occurs. The finite sums and row mean have fixed nonempty types and positive denominator 30. There is no sInf/sSup, limsup/liminf, or infinity conversion in these regression expressions.

## SAP.P040.T5

Location: `SAP/P040/Challenge/Part1.lean:44-50`. There are no outer parameters or hypotheses. Use exactly the fixed table, outcome order, matrices X0,X1,Xall, OLS/HC1 formulas, Q_a(o), df_a, and functions N,T,f unfolded in the preceding section; no different dataset or estimator is introduced.

The unconditional assertion is:

1. The cardinality of `Fin 30` is 30; rank X0=2, rank X1=rank Xall=9; both X0 and X1 give injective linear maps. For every row i in {0,...,29}, sum_{c=0}^6 g_ci=0. The ranges of the linear maps of Xall and X1 are equal. For every Boolean a (false or true), df_a is 28 if false and 21 if true.
2. For every real t,
   f(21,t) = 4^10 / (pi choose(20,10) sqrt(21)) / (1+t^2/21)^11.
   The exponent 11 in this rationalized density is a natural exponent.
3. .58779<T(Q_true(2),21)<.58780; .28766<T(Q_true(1),21)<.28767. The same cafe and bulk p values with df_true substituted for 21 satisfy R2 at .59 and .29 respectively.
4. For every Boolean a, then every outcome index o in {0,1,2,3}, Q_a(o) equals the table entry below, is >0, is <=Q_false(1), and satisfies T(Q_a(o),df_a)>1/10 and N(Q_a(o))>1/10. Also T(Q_false(1),28)<=T(Q_a(o),df_a) and N(Q_false(1))<=N(Q_a(o)). These minimum-p comparisons concern the actual, possibly different degrees of freedom, not an unstated common reference.

|a|o=0 total|o=1 bulk|o=2 cafe|o=3 book|
|--|--|--|--|--|
|false|263679812816672/522999591200175|23273498735648/15141092298015|1492978176032/21949506186495|9067019347232/22381571766655|
|true|1200277903320876335774/280628848000463708694463|12396039010057804992800/10415886991743115636339|12767624825803755635000/42131842162249950707521|3084161273413343448962/24391999904970062376441|

5. Q_false(1)<8/5; .22533<T(Q_false(1),28)<.22534; .21504<N(Q_false(1))<.21505.
6. R2(N(Q_true(2)),.58), not R2(N(Q_true(2)),.59), R2(N(Q_true(1)),.28), and not R2(N(Q_true(1)),.29).

The docstring calls this the corrected Student-t reference, the eight observed effects' non-significance under both references, and the normal alternative. It explicitly disclaims any assertion that the robust statistic has an exact Student null distribution.

Junk conventions: this target independently supplies injectivity of both fitted matrices, eliminating singular-inverse defaults in every Q it actually evaluates. The singular Xall is again used only for rank/range; the redundant seventh centered weekday indicator is explicitly accounted for. Both K=2 and K=9 have positive HC1 denominators 28 and 21. For every one of eight actual Q values, positivity is asserted. Since the defining HC1 expression is a positive factor times a sum of squares, V>=0, and Q>0 rules out V=0 and a zero treatment coefficient; hence Q is not exploiting real division by zero. Each df is a natural truncated subtraction cast to R; ranks 2 and 9 ensure ordinary positive df. Every Student density is used at nu=21 or 28, so positive Gamma arguments, positive denominator, and positive real-power base exclude the generic off-domain extensions. Integrands are continuous on finite intervals, excluding the Bochner 0 default. Actual square roots have positive arguments. No empty row/outcome/Boolean type, partial array default, infinite measure conversion, infimum, or limit enters. All displayed decimal predicates use the explicit half-open convention above, including ties.
