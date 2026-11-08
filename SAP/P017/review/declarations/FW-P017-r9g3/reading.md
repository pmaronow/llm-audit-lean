# Blind reading

This file was written before opening `claims.json` or `record.json`. Sources read: all five target docstrings and statements, every source declaration listed in their closures, and the 34 generated auxiliary declarations printed in `scratch/ClosureProofs.out` by a successful Lean run. The descriptions below concern the elaborated propositions, independently of their intended claims.

## Mathematical notation used in the five sections

All random variables are real valued. A measure called a probability measure has total mass one. Write `P(A)` for the real number `(P A).toReal`; this is the definition of `pr`, not a conditional probability. Write `gamma(m,v)` for Mathlib's `gaussianReal m v`, whose second parameter is the nonnegative **variance**. Write Phi(x) = gamma(0,1)((-infinity,x]) and phi(x) = `gaussianPDFReal 0 1 x`.

Here is the complete expansion of the shared population and clipping definitions. Given a measurable space Omega, a probability measure G, and a real effect function tau, put

* mu = the Bochner integral of tau against G;
* S = support of the pushforward measure G.map(tau), that is, the real x for which every neighborhood has positive pushforward measure;
* l = infimum, in EReal, of the image of S under the real-to-EReal embedding;
* h = supremum in EReal of that image;
* c = `(min (h - mu) (mu - l)).toENNReal`.

Thus c is an extended nonnegative radius. For a finite nonnegative real d, C(mu,d,x) = min(mu+d,max(mu-d,x)). For extended c define K(mu,c,x) = x when c is infinity, and C(mu,c.toReal,x) otherwise. The predicate `inside` means `ENNReal.ofReal(abs(x-mu)) <= c`, so for finite c it is exactly abs(x-mu) <= c.toReal, and for infinite c it is always true.

For a sequence V_n and deterministic real a_n, `LittleOp P V a` means: for every real eta > 0, as natural n tends to infinity, P(abs(V_n) > eta*a_n) tends to zero. No positivity of a is built into this definition. `RootNNormal P hat mu` means there exists a nonnegative real variance v > 0 such that sqrt(n)*(hat_n-mu) converges in distribution to gamma(0,v). Mathlib's distributional convergence includes almost-everywhere measurability at each index and weak convergence of probability laws (equivalently convergence of integrals of bounded continuous test functions). The limiting random variable is the identity on the Gaussian probability space. `sqrtN n` is the real square root of the natural number n cast to a real.

`NormalRemainder P hat Z epsilon mu v` is a conjunction, in this order: for every n >= 1, Z_n is measurable with pushforward law gamma(0,v); for every n >= 1, epsilon_n is measurable and its square is integrable; for every n >= 1, sqrt(n)*(hat_n-mu) = Z_n+epsilon_n almost surely. It asserts no independence. `SmallRemainderMS` means sqrt(n)*integral(epsilon_n^2) tends to zero. `SmallMSE P V` means n*integral(V_n^2) tends to zero.

Two explicit sampling spaces recur. Their precise definitions, all unfolded, are:

* Normal example: a single observation is (X,T) in R^2 with law G_N = gamma(0,1) product (half delta_-1 + half delta_1). The potential outcomes are Y0=0, Y1=T, so tau=T. The sample law P_N is the countable product of G_N over natural coordinates, and coordinates are IID. Let M_n(s) = (sum over 0 <= i < n of X_i)/n, H_n=M_n+1/n, Z_n=sqrt(n)*M_n, epsilon_n=1/sqrt(n), and D_n=M_n-C(0,1,H_n). These expand `normalPopulation`, `normalY0`, `normalY1`, `normalEffect`, `normalMean`, `shiftedNormalMean`, `normalZ`, `normalEpsilon`, and `shiftedDifference`; `sampleMean` is the displayed finite sum divided by n. `fairPair a b` is half delta_a + half delta_b, including if a=b.
* Rare example: a single observation is (X,(U,(T,A))) in R^4 with product law G_R = gamma(0,1) product (Lebesgue restricted to [0,1)) product nu product (half delta_0 + half delta_1), where nu = (1/4)delta_-1 + (1/4)delta_1 + (1/4)Lebesgue restricted to [-1,1]. The last Lebesgue measure has mass two, so nu has total mass one. The potential outcomes are Y0=0, Y1=T and tau=T. The observed record is O=(X,(U,(A,A*T+(1-A)*0))). The sample law P_R is the countable product of G_R; all observation coordinates and all product factors have the stated independence. Put B_n=(sum X_i)/n, Q_n=C(0,1/2,B_n), U_n=fract(sum U_i), I_n=1 if U_n<p_n and 0 otherwise, H_n^p=Q_n+10*I_n, and R_n^p=sqrt(n)*(Q_n-B_n+10*I_n). Here fract(x)=x-floor(x), with the mathematical floor into integers. These expand `slowPopulation`, `uniformHalfOpen01`, `slowEffectLaw`, `slowY0`, `slowY1`, `slowEffect`, `slowObserved`, `smallNormalMean`, `smallNormalClip`, `rareUniform`, `rareFlag`, `rareEstimator`, `rareRemainder`, and their shared `iidSamples` and `sampleMean` definitions. Finally q_n=`slowP n` is 1/(1+floor(log_2 n)) for positive n, where `Nat.log 2 n` is the integer floor logarithm (with value 0 at n=0).

The real second-moment tail expression used below is

T(n,c,sigma) = 2 integral over x>c of x^2 * [sqrt(n)/(sigma*sqrt(2*pi))] * exp(-x^2*n/(2*sigma^2)) dx.

This expands `normalTail`. The expression in the integrand is `wholeTailIntegrand n sigma x`; all these integrals are Bochner/Lebesgue integrals on the real line.

## SAP.P017.T11

The target asserts `T11WholeStatement`, a conjunction of the following clauses. There are no hypotheses on the theorem itself; quantifiers and hypotheses occur inside its conjuncts.

1. For every natural n >= 1, every real c>0, and every real sigma>0,
   T(n,c,sigma) = c*sigma*sqrt(2/pi)*exp(-c^2*n/(2*sigma^2))/sqrt(n) + (2*sigma^2/n)*Phi(-c*sqrt(n)/sigma).
   Independently, for each fixed c>0 and sigma>0, n*T(n,c,sigma) tends to zero; and, for every real k>0, n^k*T(n,c,sigma) tends to zero. These are the two conjuncts of `T11Statement`.
2. The real function z -> z^2*phi(z) is integrable over all R. For each real a>0, its integral over (a,infinity) equals a*phi(a)+Phi(-a).
3. For every natural n>=1, then every c>0 and sigma>0, set s=sigma/sqrt(n), a=c/s. Both s and a are positive; the unstandardized tail integrand is integrable on (c,infinity); T(n,c,sigma) = 2*s^2*integral over z>a of z^2*phi(z); and T(n,c,sigma) = 2*c*s*phi(c/s)+2*s^2*Phi(-c/s). For every measurable space Omega of type universe zero, probability measure P on it, and measurable W:Omega->R, if its pushforward law is gamma(0,s^2), then W^2 and the function equal to W^2 on abs(W)>c and zero elsewhere are integrable, and the integral of the latter equals T(n,c,sigma). The choices of W and P are quantified after n,c,sigma; no coupling or independence is imposed.
4. For every natural n>=1 and c>0,sigma>0, the extended expression E(n,ofReal(c),sigma) equals T(n,c,sigma), where E(n,d,sigma) is twice the integral of the same integrand over `{x : d < ofReal(x)}`. This is `extendedNormalTail`.
5. For every natural n and real sigma, E(n,infinity,sigma)=0. For every measurable space Omega, every measure P (without a probability assumption here), and every real function W, the function equal to W^2 when infinity<ofReal(abs(W)) and zero otherwise is integrable and has integral zero. For every sigma, n*E(n,infinity,sigma) tends to zero and, for every k>0, n^k*E(n,infinity,sigma) tends to zero.

Docstring reading: corrected Gaussian tail identity, integration by parts, law-based truncated moment, integrability, all positive power limits, and a separately defined infinite-radius extension, with usual measure conditions.

Junk-value audit: division by n, sqrt(n), sigma, and s is used in finite-radius formulas only under n>=1 and sigma>0. The functions themselves are total at n=0 or sigma=0: real division by zero is zero, so the displayed integrand is identically zero in these degenerate cases; they are excluded from the finite formulas. Positive c ensures `{ofReal(c)<ofReal(x)}` means x>c. At infinity that set is literally empty; the zero result does not use infinity.toReal. The arbitrary W and P in the infinite-radius clause cause no undefined expectation: the integrand is identically zero. Positive powers n^k use nonnegative integer bases and k>0; at n=0 this power is zero and the initial term cannot affect a limit. No negative square-root argument, empty probabilistic type, support bound, truncated subtraction, limsup, liminf, or partial-function default is involved. Probabilities are of a finite Gaussian measure and integrability is asserted for every finite-radius moment in the theorem. The generated proof declarations are only numeral exponent instances and the proof that s^2>=0.

## SAP.P017.T12

The target asserts `T12WholeStatement`. Its first conjunct, `T12Statement`, is itself a conjunction of the following complete groups.

1. For **every** real sequence p with 0<p_n<=1 at every n>=1 and p_n->0, the rare example's effect tau is measurable and integrable, mu=0, S=[-1,1], c=1, and H^p is root-n asymptotically normal with some strictly positive variance. For every n>=1:
   * U_n has law Lebesgue restricted to [0,1); P_R(I_n=1)=p_n; I_n and B_n are independent; sqrt(n)*B_n has law gamma(0,1).
   * For every sample s, sqrt(n)*H_n^p = sqrt(n)*B_n+R_n^p. For every delta>0, P_R(abs(R_n^p)>delta)<=4/n+p_n.
   * The three sets `{H_n^p outside S}`, `{abs(H_n^p)>1}`, and `{H_n^p != C(0,1,H_n^p)}` each equal `{I_n=1}` exactly. The clipping-failure probability equals p_n and the probability of H_n^p in S equals 1-p_n.
   * For every sample, I_n=0 implies H_n^p=Q_n and its actual clipping error is zero. For every sample, I_n=1 implies 19/2<=H_n^p<=21/2, C(0,1,H_n^p)=1, and H_n^p-C(0,1,H_n^p)=Q_n+9.
   * The actual clipping-error second moment lies between (289/4)*p_n and (361/4)*p_n.
   Also, for every n>=4, integral((R_n^p)^2)>=100*(n-4)*p_n. Both R^p and sqrt(n)*(H_n^p-C(0,1,H_n^p)) are little-o in probability of the constant sequence one, with the quantification over every positive threshold specified above.
2. The explicit q=slowP obeys 0<q_n<=1 for n>=1 and tends to zero; H^q is root-n asymptotically normal; tau is measurable/integrable with mu=0, S=[-1,1], c=1; and the exact clipping-failure probability is q_n for each n>=1. Furthermore q_1000=1/10, q_(10^12)=1/40, q_(2^k)=1/(k+1) for every natural k. For every real alpha>0, (2^k)^alpha*q_(2^k) tends to positive infinity; no positive C eventually bounds q_n by C/n^alpha. The remainder R^q fails the condition sqrt(n)*integral((R_n^q)^2)->0. For every positive-for-n>=1 vanishing real rate r, **there exists** a positive-for-n>=1 sequence p<=1 tending to zero such that H^p is root-n asymptotically normal, its clipping-failure probability is exactly p_n for every n>=1, and p_n/r_n tends to positive infinity.
3. Independently, for every sequence p (no probability or limit conditions here), then every n>=1, then every sample: -1/2<=Q_n<=1/2; if I_n=1 its actual clipping error lies in [17/2,19/2]; if abs(B_n)<=1/2 and I_n=0, then R_n^p=0.
4. There is no positive real C such that eventually q_n<=C*2*Phi(-sqrt(n)).

The remaining conjuncts of `T12WholeStatement` assert:

5. The observed-record map O is measurable. For every p and every n>=1, the six real functions U_n,I_n,B_n,Q_n,H_n^p,R_n^p are measurable; B_n^2, (R_n^p)^2, and the actual squared clipping error are integrable under P_R; and P_R(abs(B_n)>1/2)<=4/n. This is the full expansion of `RareFiniteCertificate p n`, a conclusion here rather than an input assumption.
6. For every p, n>=1, and sample s, H_n^p(s)=F(p,n,empirical_O(n,s)). The empirical measure is (1/n) times the sum of point masses at the n observed records. For an arbitrary measure F on R^4, the functional is C(0,1/2,integral(z.first)dF) + 10*1{fract(n*integral(z.second.first)dF)<p_n}. This expands `empiricalObserved` and `rareEmpiricalFunctional`. No measurability of this functional as a function of an arbitrary measure F is separately asserted.
7. For every p satisfying the positive, at-most-one, vanishing conditions, every n>=1, and every delta>0, P_R(abs(R_n^p)>delta)<=P_R(abs(B_n)>1/2)+p_n<=4/n+p_n, and P_R(sqrt(n)*abs(actual clipping error)>delta)<=p_n.
8. For every r positive at n>=1 and tending to zero, the **specified** sequence p_n=min(1,sqrt(r_n)) is positive and <=1 for n>=1, tends to zero, equals sqrt(r_n) eventually, and has p_n/r_n->positive infinity. H^p is root-n asymptotically normal and has clipping-failure probability exactly this p_n for every n>=1. This expands `sqrtFailureRate` and strengthens the existential rate assertion in item 2.

Docstring reading: a valid IID observed-data rare-outlier family can have arbitrarily slow clipping-failure decay even though it satisfies root-n normality. The wording explicitly limits the refutation to an interpretation assigning a universal rate to “quickly.”

Junk-value audit: all finite-sample probability and moment claims use n>=1 (or n>=4), so real and ENNReal division by n is legitimate. `sampleMean 0` is 0/0=0. `empiricalObserved` at n=0 is infinity times the zero measure, hence zero under the ENNReal convention infinity*0=0; that index is excluded from its asserted factorization. The sums at n=0 are empty, and fract(0)=0. q_0=1 because `Nat.log 2 0=0`; the denominator of q is always a positive natural cast. The bound n-4 is real subtraction, **not** truncated natural subtraction, and is used only for n>=4. Powers (2^k) cast a positive natural into R without overflow or truncation; n^alpha only appears in eventual bounds. `sqrtFailureRate` is zero for a nonpositive r_n because real sqrt is zero there; the rate assumptions exclude that case at positive indices. p_0 and r_0 are unrestricted and affect no asymptotic conclusion. Finite empirical measures integrate each finite observed coordinate without an integrability default; the functional's values at arbitrary nonintegrable F do use the Bochner zero convention, but only its values on positive-size empirical measures enter the factorization. All random moment integrability is explicitly concluded. The support is a genuine nonempty closed pushforward support, and its bounds are finite here; no infinity.toReal is used in this construction. Probability measures avoid infinite-mass toReal. Floor/fract is total, including for negative sample coordinates; this is mathematical fractional part, not a remainder with a truncation-to-zero convention. No limsup/liminf or default-valued partial functions occur. The generated auxiliary declarations are probability-instance proofs, positive numeral instances, and no substantive restrictions.

## SAP.P017.T13

This theorem is `T13Statement`, the conjunction of three independently quantified assertions.

1. For every measurable population space Omega and sampling space Xi (in universes u1,u2), then probability G, measurable integrable tau with c>0 as computed above, probability P, and sequence hat_n:Xi->R, assume every hat_n is measurable and hat is root-n asymptotically normal about mu. For every natural n, the set where abs(hat_n-mu) is at most the extended radius c equals exactly the set where hat_n=K(mu,c,hat_n); and the probability of the first set tends to one as n->infinity.
2. For every real sequence p with 0<p_n<=1 at n>=1 and p_n->0, the explicitly defined rare population has measurable integrable effect, mu=0, support [-1,1], radius 1, and root-n normal estimator H^p. For every n>=1 both P_R(abs(H_n^p)>1) and P_R(H_n^p!=C(0,1,H_n^p)) equal p_n. The explicit underlying population, potential outcomes, independent sample law, sample means, flags, and estimator are precisely the expanded rare construction above; they are not arbitrary supplied data.
3. For every measurable space Xi (universe u3), probability P, and measurable real functions tilde and u, then real mu,c,sigma with c>0 and sigma>0, and natural n>=1, assume P.map(tilde)=gamma(mu,sigma^2/n). Then
   P(abs(tilde+u-mu)>c) <= 2*Phi(-c*sqrt(n)/(2*sigma)) + P(abs(u)>c/2).
   No independence, mean bound, rate, or integrability condition on u is imposed. This is one finite-sample bound, not a claim that u has a particular limiting distribution.

Docstring reading: exact zero-error event, convergence of its probability to one, arbitrary positive vanishing failure probabilities, and a normal-plus-remainder bound that retains the remainder probability.

Junk-value audit: the radius for general populations has extended bounds l,h; the infimum of an empty embedded support would be top and supremum bottom, while unbounded supports produce infinite bounds. Measurable real effects under probability G have nonempty support. An integrable mean is a genuine finite integral; EReal subtraction here subtracts or is subtracted from a **finite** mean, so indeterminate infinity-infinity never occurs. EReal.toENNReal clips negative values to zero and maps positive infinity to infinity; positivity of c excludes a collapsed negative radius. `clipTarget` tests infinity before taking toReal (which would send infinity to zero), so unbounded radius clips identically. For finite c, c.toReal>=0, and `ofReal(abs(...))` does not truncate a negative input. The finite bound has n>=1 and sigma>0, excluding zero denominators; variance is sigma^2/n>0. All event probabilities are of finite probability measures. Root-n normality includes the ordinary measurable-law conditions; all hats are also explicitly measurable. For the explicit rare example, all n=0, empty-sum, real division, floor log, and support conventions are as in T12; the asserted finite-sample identities use n>=1. There are no limsup/liminf or arbitrary partial-function values. Generated declarations supply only the probability instance, square/variance nonnegativity, and numeral exponent instances.

## SAP.P017.T14

`T14WholeStatement` is a conjunction with the following complete content.

1. (`T14Statement`.) For every measurable population space Omega and sampling space Xi in universes u,v; probability G; measurable integrable tau with computed c>0; probability P; and sequence hat: assume root-n asymptotic normality about mu. Then for every eta>0,
   P(abs(sqrt(n)*(hat_n-K(mu,c,hat_n)))>eta) -> 0.
   There is no extra explicit global Borel-measurability hypothesis on hat here; distributional convergence includes a.e. measurability of the scaled errors, sufficient at n>=1.
2. In the explicit normal population G_N with tau=T, tau is measurable and integrable, mu=0, support {-1,1}, and c=1. Under the genuine IID law P_N, H_n=M_n+1/n is root-n asymptotically normal, and Z_n=sqrt(n)*M_n, epsilon_n=1/sqrt(n) satisfy `NormalRemainder` about mu=0 with variance 1. The deterministic sequence sqrt(n)/n is little-o in probability of one.
3. For every natural n and every sample s, the intermediate error D_n=M_n-C(0,1,H_n) equals M_n-K(population mu, population c,H_n). For every n>=1, M_n has Gaussian law gamma(0,1/n), H_n=M_n+1/n pointwise, P_N(D_n!=0)=1, and 2*Phi(-sqrt(n))<1.
4. The deterministic real sequence a_0=1 and a_n=1/n for n!=0 is positive at every natural index. (`positiveReciprocal`.) The intermediate D is **not** little-o in probability of this a. Thus there is at least one eta>0 for which P_N(abs(D_n)>eta*a_n) fails to tend to zero.

Docstring reading: it calls the printed claim false, distinguishing the intermediate error from the **actual** clipping error; it also asserts that the root-n actual-error conclusion holds under its original conditions. Whether “printed claim” refers to the proposition or to proof clauses cannot be decided in the blind stage.

Junk-value audit: all general-population support, EReal, Bochner, probability, and infinite-radius conventions are as detailed for T13; c>0 is substantive, and integrability of tau excludes a default population mean. The explicit effect support has two points, so c=1 is an ordinary finite number. For positive n all Gaussian variances and reciprocal/square-root denominators are positive. At n=0 the empty sample mean, 1/n, and 1/sqrt(n) are zero by field conventions; pointwise equalities mentioning all n are still defined and true there, while distributional and finite-probability statements require n>=1. `positiveReciprocal` deliberately gives a_0=1; it avoids using a zero scale in the negated little-o assertion. The little-o of sqrt(n)/n uses scale one. D_n is not the actual H_n-K(H_n); that difference of definitions is essential to the mathematical content. No limsup/liminf, truncated subtraction, or arbitrary partial-function defaults are used. Generated auxiliary declarations establish only probability, nonnegativity of 1/n (including n=0), and numeral exponents.

## SAP.P017.T15

`T15WholeStatement` has these conjuncts.

1. For every measurable population space Omega and sampling space Xi in universes u,v, probability G, and measurable integrable tau with computed c>0, then every probability P, sequences hat,Z,epsilon with each hat_n measurable for n>=1, and nonnegative real variance v>0: if Z,epsilon,hat satisfy the Gaussian-plus-remainder conditions about mu (at each n>=1, measurable Z_n with law gamma(0,v), measurable epsilon_n with integrable square, and sqrt(n)*(hat_n-mu)=Z_n+epsilon_n almost surely), and sqrt(n)*integral(epsilon_n^2)->0, then
   n*integral((hat_n-K(mu,c,hat_n))^2)->0.
   Independence is not assumed. This is written directly inside `T15WholeStatement`; the separate `T15Statement` definition is not in the target's dependency closure.
2. In the explicit normal example G_N, tau is measurable/integrable, mu=0, support {-1,1}, and c=1. Under IID P_N, H,Z,epsilon satisfy the normal-remainder conditions with variance 1; sqrt(n)*integral(epsilon_n^2)->0; and for each n>=1, integral(epsilon_n^2)=1/n.
3. For all n and all samples, D_n=M_n-K(population mu,population c,H_n). For every sample with abs(M_25)<=1/2, C(0,1,H_25)=H_25 and D_25^2=1/625. P_N(abs(M_25)<=1/2)>=21/25. The square D_25^2 is integrable and
   integral(D_25^2) - T(25,1,1) >= 6/15625 > 0.

Thus the final countercomparison is about the intermediate M_n-K(H_n), while the first universal assertion proves the actual-error mean-square limit for H_n-K(H_n).

Docstring reading: it calls the printed claim false, gives a valid moment-controlled shifted-normal construction exposing a finite intermediate-error bound failure, and explicitly retains the universal actual-error mean-square conclusion without independence. Whether that labeling is faithful remains for comparison with the canonical claim.

Junk-value audit: the general-population conventions are those detailed for T13. Integrability of tau makes mu meaningful; every epsilon_n^2 used for positive n is integrable by hypothesis, and Gaussian Z_n has finite second moments. The exact decomposition then makes hat_n square integrable for n>=1; measurable clipping and domination make its actual squared error integrable. Consequently `SmallMSE` is not relying on the Bochner zero value for nonintegrable errors. At n=0 these definitions are total and an arbitrary integral could have its default value, but a single index cannot change either atTop limit. The concrete epsilon, sample mean, and empty sample conventions at n=0 are as in T14; their asserted fixed-size law and remainder moment require n>=1. The only tail integral comparison is n=25,c=sigma=1, so no zero denominator, nonintegrable Gaussian tail, or out-of-domain square root enters. No limsup, liminf, truncated subtraction, or default-valued partial functions occur. The generated auxiliary declarations are the normal sampling probability instance already described and positive numeral exponent instances.

## Closure accounting

All source-level names in `closure.json` are expanded above, including aliases `T11Statement`, `T11WholeStatement`, `T12Statement`, `T12WholeStatement`, `RareFiniteCertificate`, `T13Statement`, `T14Statement`, `T14WholeStatement`, and `T15WholeStatement`. The generated declarations were read individually in `scratch/ClosureProofs.out`: `RareFiniteCertificate._proof_1`; `RootNNormal._proof_1` and `_proof_2`; `T11WholeStatement._proof_1`; `T12Statement._proof_1` through `_proof_12`; `T12WholeStatement._proof_1`; `T13Statement._proof_1`; `T14WholeStatement._proof_1` through `_proof_3`; `T15WholeStatement._proof_1` through `_proof_5`; `T8Statement._proof_1`; `fairPair._proof_1` and `_proof_2`; and `_proof_1` for `normalTail`, `rareEmpiricalFunctional`, `rareEstimator`, `slowEffectLaw`, and `wholeTailIntegrand`. They introduce no additional substantive axioms, conditions, or definitions of the quantities under review.
