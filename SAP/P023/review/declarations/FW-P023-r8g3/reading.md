# Blind reading

Saved before opening claims.json, record.json, earlier.json, or architect-report.md.
Sources: closure.json and the current Challenge/Defs sources. All named SAP
declarations in both closures were read, including the generated proof constants
inspected in scratch/Inspect.lean. No claim or record was used in this reading.

## SAP.P023.T11

The Challenge declaration (Challenge/Part1.lean:79–90) asserts the proposition
defined in Defs/WholeW2.lean:22–29. Its docstring explicitly omits a claimed
necessity remark and states a sufficient-conditions estimator equality.

For every finite type I (an arbitrary Fintype, not initially assumed nonempty),
every real k with 0 < k < 1, and every three functions x,d,y : I -> R, assume:

1. For every i, -1 <= x_i <= 1.
2. For every i, d_i is either 0 or 1.
3. For every i, x_i > 0 implies d_i = 1, and x_i < 0 implies d_i = 0.
   At x_i = 0 either binary value is allowed.
4. There exists i with 0 < x_i < k, and there exists j with -k < x_j < 0.

These are exactly TwoParty and Condition1, fully unfolded. No hypothesis is
imposed on the real outcomes y_i.

Let C = {i : -k < x_i and x_i <= k}. All sums below are finite sums over I or C.
Let r be the natural-number ceiling of (1-k)/(2k), and let b = 2r. Define

- B_0(t) to mean -b-1 <= t/k <= -b+1;
- B_j(t), for natural j > 0, to mean 2j-b-1 < t/k <= 2j-b+1;
- H_j(t) to be 1 if B_j(t), and 0 otherwise.

The design has b+2 real columns indexed by Fin(b+2): X_i0 = 1, X_i1 = d_i,
and X_iq = H_(q-1)(x_i) for 2 <= q < b+2. Thus it includes bin dummies
1,...,b, and omits bin 0 in the presence of an intercept. For the allowed k,
r >= 1, the central bin j=r is (-k,k], and the bins cover [-1,1]. The lower
endpoint of bin 0 is closed; every later bin is open on the left and closed on
the right. This endpoint convention is part of the statement.

The conclusion is the conjunction

    sum_(i in C) d_i > 0,
    sum_(i in C) (1-d_i) > 0,
    for every c : Fin(b+2) -> R,
      [for every column q,
         sum_i X_iq * (y_i - sum_p X_ip*c_p) = 0]
      implies
        c_1 = [sum_(i in C) d_i*y_i]/[sum_(i in C) d_i]
              - [sum_(i in C) (1-d_i)*y_i]/[sum_(i in C) (1-d_i)].

Here dot is sum of pairwise products, predict is the finite linear prediction,
and IsOLS is precisely the displayed normal equations, equivalent to minimizing
the finite sum of squared residuals. The quantifier over c follows the data and
the positivity conclusions. It does not require a unique full coefficient
vector: every solution must have this same party coefficient. In particular,
empty nuisance bins and redundant columns are permitted. The formula on the
right is rd; its close set includes +k and excludes -k, and ties are allocated
according to d, not by an additional strict-sign rule.

Junk/default conventions:

- Real division is total and a/0 = 0 in the definitions of rd, inBin, and
  binCount. In this theorem k > 0, and the two asserted RD denominators are
  also forced positive by the binary/sign/interior hypotheses. No zero
  denominator gives meaning to the conclusion.
- Nat.ceil is natural ceiling, with negative inputs truncated to zero. Its
  input is strictly positive here, so that convention is not used.
- Natural subtraction q.val-1 is truncated subtraction. It is used for the
  bin column only after ruling out q.val=0 and q.val=1, so q.val >= 2.
- Natural numbers are cast exactly into R in the bin inequalities. There is
  no machine overflow or integer division.
- Empty finite sums are zero. Condition1 forces at least two distinct
  observations, one of each sign, so an empty observation type cannot satisfy
  the hypotheses. Individual empty bins remain harmless.
- There are no integrals, logarithms, square roots, real powers, extrema, or
  sequence limsups/liminfs in this closure. No arbitrary estimator selection
  is used: the theorem quantifies over normal-equation solutions themselves.
- T11WholeStatement_W2._proof_2 only certifies that column 1 belongs to
  Fin(b+2). binCount._proof_1 supplies the AtLeastTwo instance for numeral 2;
  neither changes any data or hypothesis.

## SAP.P023.T12

The Challenge declaration (Challenge/Part1.lean:92–95) asserts T12Statement,
which is the negation of PrintedPropositionTwo (Defs/Part5.lean:13–32).
The docstring calls this an adopted fixed-law reading and acknowledges extra
moment assumptions; it does not say the printed claim itself is false.

The proposition being negated is the following universal implication. Choose,
in the following order, an arbitrary measurable space Omega, a measure P on
Omega, a Borel measure nu on R x R, a sequence of functions
S_i : Omega -> R x R, functions g,f : R -> R, and alpha : R. Assume:

1. nu(R x R) = 1 (ProbabilityLaw).
2. With mu = the pushforward of nu by the first projection (marginLaw),
   mu(R minus [-1,1]) = 0 (MarginSupport).
3. The function (x,y) -> y^2 is Bochner integrable under nu.
4. g is continuous on [-1,0), f is continuous on [0,1], and g(t) -> alpha
   as t increases to 0 from strictly negative reals.
5. Define m(x) = g(x) if x < 0, and m(x) = f(x) otherwise (appendixMean).
   Both y and m(x) are integrable under nu, and for every Borel measurable
   bounded function t : R -> R,

       integral t(x)*y dnu = integral t(x)*m(x) dnu.

   Bounded means there exists a real B with |t(x)| <= B for every real x.
   This is the test-function formulation of the conditional mean m(X).
6. The samples are genuinely IID: P(Omega)=1; each S_i is measurable; each
   pushforward (S_i)_*P equals nu; and the full sequence is independent in
   Mathlib's iIndepFun sense.
7. For every natural J >= 1 and every nonzero vector
   a : Fin(J+2) -> R,

       integral [a_0 + a_1*D(x) + sum_(j=1)^J a_(j+1)*x^j]^2 dmu > 0,

   where D(x) = 1 if 0 <= x, and 0 otherwise (party). This is
   MomentPositiveDefinite, not an assumed coefficient limit.

Next choose k : N -> R and assume:

8. Every k_N > 0; k_N -> 0 as N -> infinity; and N*k_N -> +infinity.
9. There exists k0 > 0 such that for every real a,b with
   -k0 <= a < b <= k0, mu((a,b)) > 0.
10. UsualRDRegularity means all of the following, with this same m,k,nu:
    mu({0})=0;
    N*mu((0,k_N]) -> +infinity and N*mu((-k_N,0)) -> +infinity;
    there exist real delta>0 and sigma2>=0 such that for every Borel set
    A contained in [-delta,delta],

       integral_(x in A) (y-m(x))^2 dnu <= sigma2*mu(A).

The displayed masses in (10) are ENNReal measures converted to reals before
multiplication, as is the right side of the variance bound.

For the first N samples (indices Fin N, hence 0,...,N-1), let R_N be the
finite formula rd with bandwidth k_N, margins X_i, indicators D(X_i), and
outcomes Y_i; explicitly it is the mean Y of observations in (-k_N,k_N]
having D=1 minus the mean of those having D=0. Because mu({0})=0 this
is almost surely the positive-window mean minus negative-window mean.

For degree J, let X^J have rows (1,D(X_i),X_i,...,X_i^J). IsOLS asserts
sum_i X^J_iq*(Y_i-sum_p X^J_ip*c_p)=0 for every column q. olsCoefficients
uses Classical.epsilon to select a vector satisfying these equations;
polynomialOLS and samplePolynomial return its column-1 coefficient, A_NJ.

For the population, PopNormal(mu,J,m,c) asserts, for every column q,

    integral X^J_q(x)*(m(x)-sum_p X^J_p(x)*c_p) dmu = 0.

populationCoefficient selects such a vector by Classical.epsilon and returns
its column-1 entry, theta_J. expectation is just the real Bochner integral.

The conclusion of the proposition being negated is:

    R_N -> (f(0)-alpha) in probability,
    and for every real epsilon>0 there exists natural J0 such that
      for every natural J>=J0, if J>=1 then
        A_NJ-R_N -> theta_J-(f(0)-alpha) in probability (N -> infinity),
        and |theta_J-(f(0)-alpha)| < epsilon.

ConvergesInProbability(P,Z,z) is fully unfolded as: for every real eta>0,
the ENNReal number P({omega : eta < |Z_N(omega)-z|}) tends to zero as
N -> infinity. These are fixed-J sampling limits, followed by an all-large-J
population bias assertion. No J(N) or uniform-in-J sampling limit appears.
The tolerance epsilon chooses J0 after the law, functions, sampling system,
and bandwidth have already been fixed.

T12 asserts that this entire universal implication is false. Classically it
asserts existence of at least one choice of all the preceding objects
satisfying all ten assumptions and violating at least one part of that
conclusion. It neither names a witness nor limits the failure specifically
to the bias clause. Before calling it a refutation of any external claim,
that claim's exact quantifiers and all its conditions must be compared with
this negated proposition.

Junk/default conventions:

- The same finite-sum, division-by-zero, and half-open-window conventions as
  T11 apply to sampleRD, but here positive sample denominators are not
  assumed for every N and omega. Empty winner/loser windows have mean zero
  by total real division. In particular R_0=0. The two divergent expected
  window counts and IID assumptions should force these exceptional events
  to have probability tending to zero; finite-N defaults need not spoil an
  asymptotic statement.
- Fin N may be empty, and designs may be singular. Classical.epsilon
  chooses a normal-equation solution when one exists, and otherwise a
  total arbitrary inhabitant. Finite real least squares always has a
  solution, but its coefficients may be nonunique. The definition does not
  stipulate a pseudoinverse, a zero coefficient in singular cases, or a
  measurability-preserving selection. For a fixed J, positive-definite
  population moments and IID bounded regressors should make singularity
  probabilities tend to zero. Those facts require justification when
  using this convention to read asymptotic statements.
- populationCoefficient similarly uses an arbitrary epsilon choice if no
  PopNormal solution exists. Here the compact margin support, boundedness
  of m on that support (from continuity and its one-sided limit), and
  positive-definite moments for J>=1 give an ordinary unique population
  least-squares solution. Degrees J=0 have no positivity premise but are
  excluded from the conclusion by J>=1.
- Every Bochner integral is defined to be zero for a non-integrable
  integrand. nu is a probability, Y has a finite second moment, m is
  integrable by ConditionalMean, and regressors are bounded mu-almost
  everywhere. Thus the normal-equation and squared-regressor integrals
  for relevant degrees have their intended finite meanings. The local
  residual-square integral is finite from these bounds as well. No
  non-integrable-integral zero is intended to produce the failure.
- ENNReal.toReal sends infinity to zero. All masses converted here are
  bounded by one, so infinity is excluded by ProbabilityLaw and the
  pushforward construction.
- Probability events are expressed as measure of a set without an
  explicit MeasurableSet hypothesis. A measure is total on sets; the
  usual measurability assumptions matter when interpreting this as
  convergence of random variables. No nonmeasurable witness is exhibited
  in this statement.
- The exponent j.val-1 in polynomialDesign is natural truncated
  subtraction, but used only for columns j.val>=2. Powers are natural
  integer powers, including ordinary x^0 where relevant; there are no
  real powers. N and column indices cast exactly into R.
- Auxiliary proof constants olsCoefficients._proof_1 and
  populationCoefficient._proof_1 assert that the coefficient-function
  spaces are nonempty; polynomialOLS._proof_2 proves 1<J+2. They impose
  no statistical assumptions.
- No logarithms, square roots, sInf/sSup, or limsup/liminf occur in this
  closure. The limits used are Tendsto to 0 or +infinity, not default
  conditional extrema of unbounded sequences.
