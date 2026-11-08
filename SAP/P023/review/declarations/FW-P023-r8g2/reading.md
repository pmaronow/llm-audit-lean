# Blind reading

This file was written before opening `claims.json` or `record.json`. The five Challenge declarations and every named declaration in their `closure.json` closures were read. All 37 distinct generated auxiliary declarations (the entries whose line is 0) were also printed with Lean in `scratch/BlindClosure.lean`; the complete successful output is `scratch/BlindClosure.out`. They supply numeral typeclass instances, nonemptiness for choice, finite-index bounds, or the scalar tower for ENNReal measures. They add no statistical assumptions.

## Mathematical notation used below

All finite sums are real sums over the indicated finite type, or over the specified finite subset. For real vectors, write `<a,b> = sum_i a_i b_i`. Prediction by a design X and coefficient vector c means `sum_j X_ij c_j`. An OLS coefficient vector is a solution of the normal equations `sum_i X_ij (y_i - sum_l X_il c_l)=0` for every column j. Full rank means that a vector with zero prediction at every row is the zero vector. The chosen OLS vector is Hilbert choice of a solution of these normal equations, not an inverse matrix definition.

Write `D(x)=1` for x >= 0 and `D(x)=0` for x < 0. The degree-J polynomial design has J+2 columns, numbered 0 through J+1: `1,D,x,x^2,...,x^J`. Its chosen party coefficient is coordinate 1 of the chosen normal-equation solution. With arbitrary finite party data d_i the same design uses d_i in place of D(x_i). The nuisance polynomial design has J+1 columns `1,x,...,x^J`.

For a real measure mu write `E_mu f = integral f dmu`, the real Bochner integral. A probability law means exactly `mu(univ)=1`. Margin support means `mu([-1,1]^c)=0`. Write U for `(1/2) * Lebesgue restricted to [-1,1]`. For a polynomial q, the population projection condition is `q.natDegree <= J` and `E_mu[(D-q)x^j]=0` for all natural j <= J; q_J is Hilbert choice of such a polynomial. Set `r_J=D-q_J`, `v_J=E_mu r_J^2`, `A_J=E_mu |r_J|/v_J`, and `B_J(h)=E_mu(r_J h)/v_J`. The population party coefficient b_J(m) is coordinate 1 of Hilbert choice of a vector c satisfying `E_mu[X_j(m-Xc)]=0` for every column of `(1,D,x,...,x^J)`.

Positive definite moments mean `E_mu (Xc)^2 > 0` for every nonzero real coefficient vector c of length J+2. The least moment eigenvalue lambda_J is the real infimum of all values `E_mu (Xa)^2` with `sum_j a_j^2=1`. Uniform approximation error is the real supremum of `|h(x)-p(x)|` over x in [-1,1]. RMS approximation error is `sqrt(E_mu(h-p)^2)`.

For a measure nu on real pairs (X,Y), its margin law is the pushforward by the first coordinate. The conditional-mean assertion for m says that Y and m(X) are integrable and that `integral t(X)Y dnu = integral t(X)m(X) dnu` for every globally bounded Borel measurable real t. This is the tested integral definition, rather than an unexpanded conditional-expectation symbol.

The close subset for finite data and real k is `C={i: -k < x_i <= k}`. The finite RD value is `(sum_C d_i y_i)/(sum_C d_i) - (sum_C (1-d_i)y_i)/(sum_C (1-d_i))`. The population RD value is `(integral_(0,k] m dmu)/mu((0,k]).toReal - (integral_(-k,0) m dmu)/mu((-k,0)).toReal`. The two population intervals exclude zero; the sample close subset includes it.

For bins put `b=Nat.ceil((1-k)/(2k))`, `M=2b`. The bin label at x is `min(M,Nat.ceil((x/k+M-1)/2))`, as an element of {0,...,M}; the central label is b. Bin j=0 is the interval described by `-M-1 <= x/k <= -M+1`; for j>0 the interval is `2j-M-1 < x/k <= 2j-M+1`. For labels B_i, the bin mean of z in bin j is `(sum_(B_i=j) z_i)/#{i:B_i=j}`, and the demeaned value at i is z_i minus the mean in bin B_i. A bin OLS fit with intercepts a_j and party coefficient beta means `sum_(B_i=j)(y_i-a_(B_i)-beta d_i)=0` for every j and `sum_i d_i(y_i-a_(B_i)-beta d_i)=0`. Coarsened OLS means that some such intercept vector exists for the labels just defined.

Two-party data means that every x_i lies in [-1,1], every d_i is 0 or 1, d_i=1 when x_i>0, and d_i=0 when x_i<0. At x_i=0 either binary d_i is allowed. Condition 1 means there is an observation strictly between 0 and k and another strictly between -k and 0.

## SAP.P023.T6

This is a closed conjunction, with no external hypotheses. First U is a probability law supported on [-1,1]. Next:

1. A_J for U tends to positive infinity as natural J tends to infinity. There exist C >= 0 and a natural J0 such that for every J >= J0 with J >= 1, `|A_J-(4/pi)log(J)| <= C` (J is cast to a real before log).
2. For each natural J >= 1 the supremum of the set of real values B_J(h), where h is any function R -> R continuous on [-1,1], h(0)=0, and |h|<=1 on that interval, equals A_J. The set uses the signed functional, not its absolute value.
3. There exist ONE function h:R -> R and ONE sequence of natural degrees d:N -> N, chosen before the following universal quantifiers. The function is continuous on [-1,1], h(0)=0, |h|<=1/12 there, and d is strictly increasing. For every m>=1, `B_(d(m))(h) >= m/4`. For every J>=1, `b_J(1/2+h)=B_J(h)`. For every m>=1, `b_(d(m))(1/2+h)>=m/4`. For every real B and natural J0, there exists J>=J0 with `b_J(1/2+h)>=B`. The mean 1/2+h is continuous on [-1,1], takes value 1/2 at zero, and takes values in [5/12,7/12]. Its coefficients along d tend to positive infinity; the full coefficient sequence does not tend to zero. Its population RD tends to zero as positive real k tends to zero. There is no real L satisfying `|h(x)-h(x')| <= L|x-x'|` for all x,x' in [-1,1].
4. Independently, for EVERY h:R -> R and EVERY d:N -> N, if h is continuous on [-1,1], zero at zero, bounded in absolute value by 1/12 there, d is strictly increasing, and `B_(d(m))(h)>=m/4` for every m>=1, then h has no real Lipschitz constant on [-1,1].

The docstring describes a fixed-law continuous example with increasing-degree divergence and excludes Lipschitz functions meeting its growth conditions. There is no joint outcome law or sample limit in this statement.

Conventions: U is finite and the constrained continuous functions and all polynomials are bounded on its support, so its integrals are genuine. Choices q_J and b_J are meaningful here because the ordinary finite-dimensional uniform-law moment systems are nonsingular. In general these choices would be arbitrary without existence, and real division by zero would return zero; neither is intended at U. Supremum over the unit ball of anchored continuous functions is nonempty (zero function) and bounded for each degree, so the real conditional-complete supremum is meaningful. `log(0)=0` in Mathlib; the logarithmic estimate explicitly restricts J>=1, so this convention is harmless. Natural-to-real casts in m/4 and log are exact. Strict increase of d makes d(m)>=m; the degree-zero first term cannot affect the limits. Population RD has zero-denominator values away from positive windows but the one-sided limit concerns positive small k, whose masses are positive. There are no empty index types, truncated subtractions, square roots, or extended-real infinities in the substantive clauses.

## SAP.P023.T7

This is a conjunction of four universally quantified assertions, plus closed uniform-law numerical facts.

Population assertion: for EVERY pair measure nu, assuming probability, margin support in [-1,1], integrability of Y^2, EVERY real alpha,beta, EVERY globally measurable h bounded on [-1,1], assuming the above tested conditional mean `m=alpha+beta D+h`, and EVERY natural J>=1 with positive definite moments, let mu be the margin law, v=v_J, and b=b_J(m). Then:

- q_J satisfies its projection condition, v>0, `E_mu r_J p=0` for every polynomial p with natDegree<=J, `E_mu r_J=0`, and `E_mu(r_J D)=v`.
- `b=B_J(m)`. For every such p, `b-beta=B_J(h)=B_J(h-p)`, `|b-beta|<=A_J supError(h,p)`, and `|b-beta|<=rmsError(h,p)/sqrt(v)`.
- A_J>=2. If any degree-at-most-J polynomial equals h mu-almost everywhere then b=beta.
- For every real t>0, `|b-beta|<=t` iff `|E_mu r_J h|<=t v`. Also either `A_J * inf_{deg(p)<=J} supError(h,p)<=t` or `inf_{deg(p)<=J} rmsError(h,p)<=t sqrt(v)` is separately sufficient for `|b-beta|<=t`.

Uniform-law facts: U is a probability law with the stated support. For every J>=1, `v_J= [choose(2n,n)/4^n]^2/4`, where `n=(J+1)/2` uses NATURAL division. The projection polynomials evaluate everywhere to `1/2+3x/4` at J=1 and `1/2+(11025x-40425x^3+63063x^5-32175x^7)/4096` at J=7. The corresponding variances are 1/16 and 1225/65536. At J=1, `E|r|=5/24`, A=10/3, and `1/sqrt(v)=4`; at J=7, `1/sqrt(v)=256/35` and A lies strictly between 4.7642006857252250 and 4.7642006857252260.

Finite residual/weight assertion: for EVERY finite type I with decidable equality, natural J>=1, two-party x,d and full-rank `(1,d,x,...,x^J)`, let `r_i=d_i-sum_(j=0)^J x_i^j a_j`, where a is the chosen nuisance OLS fit to d, and `w_i=r_i/<r,r>`. Then `<r,d>=<r,r>>0`; `<r,x^j>=0` for all natural j<=J; for every outcome vector y the party coefficient is `<r,y>/<r,r>=<w,y>`; `sum_i w_i=0`, `sum_i w_i x_i^j=0` for 1<=j<=J, and `sum_i w_i d_i=1`. For every y, observation i, and real perturbation delta, replacing y_i by y_i+delta changes the coefficient by exactly w_i delta.

Finite conditional-bias assertion: for EVERY finite type I, measurable sample space Omega and probability measure P, EVERY J>=1, two-party x,d with additionally d_i=D(x_i) even at ties and full rank, EVERY alpha,beta,h and integrable random outcome family Y_i with `integral Y_i dP=alpha+beta d_i+h(x_i)`, the residual sum of squares is positive and the mean chosen party coefficient minus beta is `<r,h(x)>/<r,r>`. This is conditional-on-fixed-design mathematics, not a claim of independence of Y_i.

Conventions: all finite normal-equation systems have solutions; full rank of the full design implies uniqueness and positive residual norm, so neither arbitrary coefficient choice nor division by zero affects the finite assertions. Empty I cannot meet that rank condition. Population probability/support, bounded h, and finite Y^2 give the requisite finite integrals, projection existence/uniqueness and positive v. The real supremum defining supError is of a nonempty bounded set, although h need not be continuous. Both error infima have the zero-polynomial candidate and are bounded below by zero. Their empty/unbounded-set defaults therefore do not apply. Square roots have nonnegative radicands, and sqrt(v)>0. The natural division in n is intentionally floor division; all natural casts are exact. Exponents and array dimensions are natural and never negative; j.val-1 in the full design is truncated subtraction but occurs after excluding j=0 (and j=1 for powers), giving exactly the listed columns. There are no logarithms, rpow, or extended-real-to-real conversions in this target.

## SAP.P023.T8

For EVERY measurable space Omega, measures P on Omega and nu on R^2, sample sequence `Z_i:Omega -> R^2`, reals alpha,beta,c,delta,L,sigma2 and h:R -> R, assume ALL of:

- nu is a probability, its margin mu is supported on [-1,1] and has no atom at zero, and Y^2 is integrable;
- c>0, 0<delta<=1, L>=0, sigma2>=0;
- for every measurable A subset [-delta,delta], `ofReal(c) Lebesgue(A) <= mu(A)` in ENNReal;
- h(0)=0, and `|h(x)-h(x')|<=L|x-x'|` for all x,x' in [-1,1];
- the tested conditional-mean property for `m=alpha+beta D+h`;
- for every measurable A subset [-delta,delta], `integral_{X in A}(Y-m(X))^2 dnu <= sigma2 * mu(A).toReal`;
- P is a probability, every Z_i is measurable, its pushforward law is nu, and the family is mutually independent in Mathlib's `iIndepFun` sense;
- a real bandwidth sequence k_N is positive for EVERY natural N, tends to zero, and N*k_N tends to positive infinity.

Sample OLS at (N,J) is the previously defined chosen coefficient on the first N draws indexed by Fin N; sample RD uses those same draws with d_i=D(X_i). Convergence in probability to z means that for every real epsilon>0, the ENNReal probabilities of `{omega: epsilon<|stat_N(omega)-z|}` tend to zero.

Then, with the preceding quantifiers fixed:

1. For every J>=1, the regressor moments are positive definite, lambda_J>0, q_J is a genuine projection, v_J>0 and `v_J>=c delta/[4(J+1)]`.
2. For every J>=1, there exists a real polynomial p of natDegree<=J with p(0)=0 and `supError(h,p)<=4 K L/(J+1)`, where `K=3(1+pi^4)/(4pi)`.
3. For every J>=1, `|b_J(m)-beta|<=8 K L/sqrt(c delta (J+1))`, and b_J(m) tends to beta as natural J tends to infinity.
4. For every fixed J>=1, sample OLS tends in probability to b_J(m) as N tends to infinity.
5. For every real k' with 0<k'<=delta, `|populationRD(mu,m,k')-beta|<=2Lk'`. Sample RD at k_N tends in probability to beta.
6. For every epsilon>0 there exists J0 such that for EVERY J>=J0 with J>=1, the sample OLS-minus-RD sequence tends in probability to b_J(m)-beta and that limiting bias has absolute value <epsilon.
7. For EVERY degree sequence d_N tending to infinity and satisfying `(d_N+2)^2/[N lambda_(d_N)^3] -> 0`, sample OLS minus b_(d_N)(m) tends in probability to zero, and sample OLS minus sample RD tends in probability to zero.
8. There EXISTS a degree sequence d_N>=1 for every N tending to infinity and satisfying that rate.

There are no assumed singular-design or empty-window probability bounds. Their asymptotic negligibility must follow from these hypotheses. This matches the docstring's scope on its face.

Conventions: Hilbert choice makes sample OLS total even for singular designs and N=0, and RD's real divisions make an empty sample/window return a total value (zero for each empty mean). These choices have no usual estimator interpretation on those finite-sample events; the theorem's claimed limits require those events to vanish in probability. For finite sample OLS a normal-equation solution always exists but need not have a unique party coefficient at a singular design. All population integrals are finite on bounded margins and a Lipschitz h; finite Y^2 supplies outcome integrability. The eigenvalue infimum ranges over a nonempty finite-dimensional unit sphere and nonnegative, continuous moment values, so it is a genuine finite attained minimum, positive under the supplied density condition. Lambda_0 also is positive by the same density argument, even though the first explicit positivity conclusion starts at J=1. Thus the growing-degree rate cannot be satisfied spuriously by lambda=0 at large N. At N=0 its denominator is zero and its total value is zero; finitely many initial terms have no bearing on a limit. No infinity has positive probability-law mass, so every measure `.toReal` used here is finite. All population RD denominators at the asserted k' are positive by density domination and finite. The approximation supremum is nonempty/bounded by Lipschitzness. Every displayed square root has strictly positive argument. K uses pi>0. No logarithms, rpow, limsup, or liminf occur. Natural subtraction in polynomial column indices is guarded as described for T7; all other casts and finite dimensions are ordinary.

## SAP.P023.T9

For EVERY finite set S of ordered natural-number pairs, real 0<k<1, and real functions x,d,y on the subtype of pairs belonging to S, assume two-party data, Condition 1, and that beta is a coarsened OLS coefficient (some bin intercepts satisfy all the normal equations). Define B to be the above clamped bin labels, r to be the bin-demeaned d, and z to be the bin-demeaned y. Then:

- for every observed pair p and EVERY bin label j in {0,...,M}, x_p lies in the stated interval for j iff B_p=j;
- the observed pairs with central label b are exactly C;
- for every observed pair outside C, r_p=0;
- `sum_(p in C) r_p^2>0`;
- `beta = [sum_(p in C) r_p^2]^(-1) * sum_(p in C) r_p z_p`.

The index domain is S itself, not the Cartesian product of its marginal projections. Binning and demeaning retain each observed pair once. The docstring calls this the corrected pair-indexed Appendix A formula.

Conventions: Nat.ceil returns a natural number (zero when the real argument is sufficiently negative), and binLabel clips it at M. For x in [-1,1] and 0<k<1 these choices reproduce the displayed endpoint conventions and do not silently assign an out-of-range observation. Division by k is safe. The binCount and centralLabel finite-index proofs have no extra assumptions. Bin means of empty bins are 0/0=0, but a demeaned value at an observed pair always uses its own nonempty bin; empty bins contribute only empty normal equations. Condition 1 prevents empty S and makes both central party counts positive, hence the displayed residual denominator positive. Bin-count casts to reals are exact. There are no integrals, infinities, roots, logarithms, infima, or suprema here.

## SAP.P023.T10

This is a conjunction of a universal coarsened-localization result and a negated universal polynomial-localization assertion.

First, for EVERY finite type I, real 0<k<1, two-party x,d and outcome vectors y,y', assume both central party counts `sum_C d_i` and `sum_C(1-d_i)` positive and y_i=y'_i for every i in C. For EVERY beta,beta', if each is a coarsened OLS coefficient for its respective outcomes, then beta=beta'. There is no requirement that all bins be populated or that Condition 1 hold.

Second, it is NOT the case that for EVERY natural n,J, real data x,d on Fin n and bandwidth k, the following implication holds: if J>=1, 0<k<1, two-party data, Condition 1, full rank of `(1,d,x,...,x^J)`, and there exists a coefficient vector c of length J+2 whose fitted predictions lie strictly between 0 and 1 at every observation, then the chosen polynomial party-coefficient estimator is localized. Localized here means: for EVERY two real outcome vectors y,y' agreeing on C, their chosen polynomial party coefficients are equal. Thus classically there is an admissible design with a pair of outcomes agreeing on C but different coefficients. The fitted-prediction existence condition is not an outcome-specific model condition: the constant prediction 1/2 always supplies it.

The Challenge docstring explicitly says "The printed claim is false" and describes failure of a universal localization assertion. At this blind stage, which printed assertion is meant has not been consulted.

Conventions: finite OLS is selected by Hilbert choice of a normal-equation solution. Full rank eliminates ambiguity in the polynomial counterexample. Full rank and Condition 1 also eliminate the empty-type cases. Coarsened fits can have empty bins or redundant bin columns; the conclusion concerns their uniquely identified party coefficient under the positive central counts. Coarsened bin means are not used by this target. The binLabel conventions, finite bounds, guarded natural column subtraction, exact casts, and safe positive k are as above. The Localized predicate itself imposes no outcome range; a bounded-outcome counterexample would independently establish that failure is substantive. No integrals, square roots, infinities, infima, suprema, logarithms, or asymptotic limits occur.
