# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. This reads the current Challenge declarations and all the
unit declarations in their `closure.json` closures. Auxiliary declarations with
line 0 were also printed from Lean in `scratch/BlindPrint.lean`; their complete
output is `scratch/BlindPrint.out`. They supply numeral/typeclass facts, the
nonnegative Bernoulli/Poisson parameters, and the indicated measurable-space
inclusions. They add no statistical hypotheses or alternative definitions.

Throughout, a finite matrix is a function of two finite indices, multiplication
and transpose use finite sums, a vector equality is equality at every coordinate,
and a displayed rational is a real rational. A derivative means Mathlib's real
Fréchet derivative, or its one-variable version `HasDerivAt`; `deriv` is the total
derivative operation. Expectations of six-atom variables below mean explicitly
weighted finite sums, not an unspecified averaging operation.

## SAP.P015a.T8

Location: `SAP/P015a/Challenge/Part1.lean:54–69`; the actual proposition is
`T8WholeStatement`, defined at `Defs/WholeW1.lean:261`. It is the conjunction of
the following ten assertions. There are no outer hypotheses on this conjunction.

For notation, for a real matrix W with n rows and q columns, put
eta_i(theta) = sum_j W_ij theta_j. For vectors n_i,k_i and a real scalar function m,
the three objects used throughout are exactly

* L(theta) = sum_i [k_i log(m(eta_i(theta))) +
  (n_i-k_i) log(1-m(eta_i(theta)))];
* R_j(theta) = sum_i W_ij [k_i-n_i m(eta_i(theta))];
* G_j(theta) = sum_i W_ij h(eta_i(theta))
  [k_i-n_i m(eta_i(theta))], where
  h(eta) = m'(eta)/(m(eta)(1-m(eta))).

The continuous linear functional represented by g is v |-> sum_j g_j v_j.
For an interval or open set I, admissible theta means every eta_i(theta) lies in I.
There is no independence assumption in these finite-sum calculus identities.

1. **Bernoulli derivative and maximum equation.** For every natural n,K, real
   n-by-(K+2) matrix W, and real vector Y of length n, assume each Y_i is 0 or 1
   and each W_i0 is 1. For every open real set I, every real function m
   differentiable on I with 0 < m(eta) < 1 on I, and every admissible theta,
   L with n_i=1,k_i=Y_i has Fréchet derivative v |-> sum_j G_j(theta)v_j.
   Also, if L(t) <= L(theta) for every admissible t, then G(theta)=0.
   Openness makes this an interior maximum condition. No rank or uniqueness is
   assumed or concluded.

2. **Logistic.** For every real eta, m(eta)=1/(1+exp(-eta)) has derivative
   m(eta)(1-m(eta)), h(eta)=1, and h'(eta)=0. For every n,K,W,Y,theta of the
   above dimensions, without restrictions on W or Y, G(theta)=R(theta) with
   n_i=1,k_i=Y_i and this logistic m.

3. **Canonical finite-sum derivative.** For every n,K,W, real function kappa,
   and real s>0, for every pair of real row vectors Y,c and theta, assume kappa
   is differentiable at every eta_i(theta). The function
   sum_i [(Y_i eta_i(theta)-kappa(eta_i(theta)))/s+c_i]
   has derivative represented by
   s^(-1) W^T (Y_i-kappa'(eta_i(theta)))_i.
   This vector is zero iff W^T(Y_i-kappa'(eta_i(theta)))_i=0.
   No probability normalization, support, common intercept, or binary-response
   premise is imposed on this calculus identity.

4. **Normalized canonical families.** For every measure nu on real numbers,
   real function kappa, real s, real carrier function c(y), and real sets I,S,
   assume s>0, I open, S measurable, nu(S complement)=0, and, for each eta in I,
   exp((y eta-kappa(eta))/s+c(y)) is integrable under nu and its integral is 1.
   Additionally assume kappa differentiable on I. Then for each eta in I the
   measure nu.withDensity(ofReal(exp((y eta-kappa(eta))/s+c(y)))) is a probability
   measure; y is integrable under it; its integral is kappa'(eta); kappa is real
   analytic at eta; and kappa' is differentiable there. In particular these
   are conclusions about the actual density measure, not about a defined mean
   set equal to kappa'. The set S is only a measurable full-measure support set;
   it is not required to be minimal or topological support.

5. **Named canonical means.** For every real eta, the two-point measure
   p delta_1+(1-p)delta_0, with p=1/(1+exp(-eta)), is a probability measure,
   has integrable identity and mean p, and p is the derivative at eta of
   log(1+exp(a)). Also the Poisson measure on natural numbers with rate exp(eta)
   is a probability measure, its natural-number-to-real identity is integrable,
   its mean is exp(eta), and exp(eta) is the derivative of exp at eta.

6. **Probit.** Let Phi(a) be the distribution function of the real Gaussian
   probability measure of mean 0 and variance 1, phi its real density, and
   h_P(a)=phi(a)/(Phi(a)(1-Phi(a))). For every n,K,W,Y with binary Y and intercept
   W_i0=1, and every theta, the Bernoulli L for m=Phi has derivative represented
   by sum_i W_ij h_P(eta_i(theta))(Y_i-Phi(eta_i(theta))). For every real a,
   the multiplier defined using `deriv Phi` equals h_P(a), and h_P(a)>0.
   There is no real constant c with h_P(a)=c for all a. Phi(0)=1/2 and
   h_P'(0)=0. The full fixed six-cell/48-observation proposition of T6 below is
   also a conjunct; all of its numerical, nonmaximum, quantile, and directional
   derivative assertions are included, not an implication conditional on them.

7. **Mean-only linearization.** For every n,K,W,Y, with W_i0=1, every real m
   differentiable at eta0, set p0=m(eta0), f0=m'(eta0),
   r=W^T(Y-p0), A=W^T W. Let e(eta) be the length-(K+2) vector with coordinate
   0 equal to eta and all other coordinates zero. Define F_{b,c}(theta)=e(b)+c theta.
   For every delta, the residual equation with scalar mean
   a |-> p0+f0(a-eta0) evaluated at e(eta0)+delta is zero iff
   f0 A delta=r. The ordinary least-squares normal equation
   W^T(Y-W F_{p0-f0 eta0,f0}(e(eta0)+delta))=0 is equivalent to the same equation.
   If f0 != 0, for every theta, F_{-(p0-f0 eta0)/f0,1/f0} and
   F_{p0-f0 eta0,f0} compose in either order to theta. There is no rank condition,
   no selected least-squares coefficient, and no assertion that f0 is nonzero
   without this premise.

8. **Full-score linearization.** For every n,K,W,Y with binary Y and intercept,
   every open I, and every real m differentiable on I with values strictly
   between 0 and 1, for every eta0,p0 with eta0 in I, 0<p0<1, m(eta0)=p0,
   assume m' differentiable at eta0. Put f0=m'(eta0), h0=h(eta0), h1=h'(eta0),
   r=W^T(Y-p0), A=W^T W, B_jk=sum_i (Y_i-p0)W_ij W_ik. For each delta the
   vector whose j coordinate is
   sum_i W_ij [h(eta0)(Y_i-m(eta0)) +
   (d/deta)(h(eta)(Y_i-m(eta)))|eta0 (W delta)_i]
   equals h0 r+(-h0 f0 A+h1 B)delta. This is the first Taylor polynomial,
   not the nonlinear score at eta0+(W delta)_i. If h0 != 0, then f0 != 0,
   this polynomial equals zero iff (f0 A-(h1/h0)B)delta=r, and, for every delta,
   if h1=0 or B delta=0, its left side equals f0 A delta.
   No remainder bound or small-delta error statement occurs.

9. **Square-link illustration.** Every assertion of T7 below is included,
   including the actual six-atom probabilities, independent uniform latent
   variable and conditional independence, the admissible unique maximizing
   branches, their treatment-coordinate derivatives 120/119 and 1, finite
   moments and score derivatives, and the invertible treatment-preserving basis
   change. These are not extra assumptions on a general family.

10. **Cox illustration.** For every n,q,e, real n-by-q covariate matrix Z,
    event map k |-> event_k from Fin e to Fin n, and risk-set map R_k to finite
    subsets of Fin n, assume event_k belongs to R_k for each k. For every theta,
    every denominator sum_{j in R_k} exp((Z theta)_j) is positive, and
    sum_k [(Z theta)_{event_k}-log(sum_{j in R_k}exp((Z theta)_j))]
    has derivative represented by the vector with a coordinate
    sum_k [Z_{event_k,a} -
    (sum_{j in R_k} exp((Z theta)_j) Z_ja)/(sum_{j in R_k}exp((Z theta)_j))].
    In the fixed example Z has rows (1,0),(1,1), there is one event, event=0,
    and theta=(0,0): coordinate 1 of this score is 0 for risk set {0} and -1/2
    for risk set {0,1}. There are no general duration-model claims beyond this.

The docstring describes precisely these score/Taylor identities, mentions the
two named canonical examples, and explicitly disclaims a quadratic nonlinear
remainder and blanket ordered/multinomial/duration extensions. It calls the
square-link example a discrepancy without explicitly saying in this docstring
that the conditional mean may be misspecified.

**Totalizations and domains.** Real division uses 1/0=0. The Bernoulli
denominator is protected by 0<m<1, including at the derivative center. The
canonical scale is positive. The two divisions by f0 are in a conclusion
guarded by f0 != 0; the score-equation division by h0 is guarded by h0 != 0.
The unguarded identity defining the score polynomial still makes sense if
f0=h0=0. `deriv f` is zero at a nondifferentiability point, but differentiability
is supplied wherever it is used as an actual derivative in the general
assertions; logistic/probit and the named families are the standard smooth
functions. Real.log is defined at nonpositive arguments (log 0=0, log(-x)=log x),
but all Bernoulli log arguments at the relevant points and in the maximization
domain are positive. Cox risk membership makes each log argument positive.
Canonical `withDensity` uses `ENNReal.ofReal`, which truncates negative numbers
to 0; it is applied to a strictly positive exponential. The normalized-family
integrals have integrability in the premises or conclusions. The named-law
means also assert integrability. Its I may be empty, making that particular
universal instance have no eta, but nonempty normalized examples exist and the
whole conjunction has substantive fixed examples. n and e can be zero, giving
empty sums; K+2 is always positive, and q=0 is allowed for Cox's zero-dimensional
calculus. All finite-index casts are their ordinary nonnegative integer values;
K+2, n, q, e involve no truncated subtraction. No limsup/liminf, partial-function
default, nonreal rpow, or out-of-domain sqrt is involved. The sInf, matrix
inverse, conditional expectation, and finite-measure conversions inherited
through T6/T7 are accounted for in those sections. Merely reused auxiliary
proof names such as `outsideTaylorWitness._proof_1` do not import the definitions
or sSup expressions of the unrelated T12 assertion.

## SAP.P015a.T5

Location: `Challenge/Part1.lean:71–78`, with proposition at
`Defs/Part3.lean:56–58` and fixed witness at `Defs/Part2.lean:124–142`.
This is an unconditional conjunction about completely fixed grouped binary data,
plus universal derivative statements. Index the six cells by d in {0,1},
x in {0,1,2}. W_{(d,x)}=(1,d,x); n_{(d,x)}=12; k_{(d,x)}=(7,6,10)_x;
m(eta)=eta/(1+eta); theta0=(1,0,1). Thus there are 72 individual binary
observations, with the same counts for each value of d. Set eta_i(theta)=W_i theta,
L(theta)=sum_i[k_i log m(eta_i)+(12-k_i)log(1-m(eta_i))],
R_j(theta)=sum_i W_ij(k_i-12m(eta_i)), and
G_j(theta)=sum_i W_ij [m'(eta_i)/(m(eta_i)(1-m(eta_i)))]
(k_i-12m(eta_i)). The statement asserts every one of the following:

* eta_i(theta0)>0 for all six cells; 0<k_i<12; R(theta0)=0;
  G(theta0)=(2/3,1/3,-2/3), and G(theta0) != 0.
* It is not the case that for every real three-vector theta, if all
  eta_i(theta)>0 then L(theta)<=L(theta0). Classically, there is an admissible
  theta with strictly greater likelihood. No selected alternative theta or
  explicit positive step size occurs in the statement.
* det(W^T W)=36. Every first column is 1 and every treatment value is 0 or 1;
  counts have the given three values. At theta0 the means are (1/2,2/3,3/4)_x.
  det(12(W^T W))=62208.
* For every real three-vector v, the real function
  t |-> L(theta0+t v) has derivative
  (2/3)v_0+(1/3)v_1-(2/3)v_2 at t=0.
* For every real eta>0, m'(eta)/(m(eta)(1-m(eta)))=1/eta.

There are no hidden hypotheses on the fixed data. The docstring describes a
residual root which is not a maximum, and expressly distinguishes this from the
necessary implication from a maximum to a residual root.

**Totalizations and domains.** m has a division by 1+eta and a pole-totalization
at eta=-1; the likelihood and score are formally total real functions even
outside the statistical domain. All fixed predictors are 1,2,3, and the
nonmaximum comparison is explicitly restricted to all predictors positive,
where 0<m<1 and all log arguments are positive. A line theta0+t v can leave this
domain far from 0, but positivity persists near 0, as needed for the asserted
derivative. `deriv` at a nonsmooth point, real log at zero/negative inputs and
1/0 do not furnish this witness. The displayed 1/eta is guarded by eta>0.
Counts are typed as real numbers but are the specified integer counts. Fin 2,
Fin 3 and their product are nonempty. Determinants, finite sums, and vector
operations have no partial defaults, and no matrix inverse, integral,
toReal(infinity), infimum, supremum, limit, rpow or sqrt is used.

## SAP.P015a.T6

Location: `Challenge/Part1.lean:80–87`; proposition at `Defs/Part3.lean:60–68`,
witness at `Defs/Part2.lean:144–157`. Let Phi be the Mathlib standard real
Gaussian CDF and phi its density. Define q as the real infimum of
{a : 3/4 <= Phi(a)}. Index the six cells by d in {0,1}, x in {-1,0,1};
W_i=(1,d,x), n_i=8, k_i=(3,2,7)_x, and theta0=(0,0,q).
For eta_i(theta)=sum_j W_ij theta_j set
L(theta)=sum_i[k_i log Phi(eta_i)+(8-k_i)log(1-Phi(eta_i))],
R_j(theta)=sum_i W_ij(k_i-8Phi(eta_i)),
h(a)=phi(a)/(Phi(a)(1-Phi(a))), and
G_j(theta)=sum_i W_ij [Phi'(eta_i)/(Phi(eta_i)(1-Phi(eta_i)))]
(k_i-8Phi(eta_i)). This is an unconditional conjunction asserting:

* 0<q<7/10; Phi(-q)=1/4, Phi(0)=1/2, Phi(q)=3/4.
* R(theta0)=0 and G(theta0)=(4(h(q)-h(0)),2(h(q)-h(0)),0).
* h(q)=(16/3)phi(q), h(0)=4phi(0), and 13/625<2(h(q)-h(0)).
* It is not the case that all real three-vectors theta have L(theta)<=L(theta0).
* Every cell has intercept 1, treatment 0 or 1, and 0<k_i<8;
  det(8(W^T W))=18432. The 48 individual observations therefore have full rank.
* {a : 3/4<=Phi(a)} is nonempty and bounded below.
* For every real three-vector v, t |-> L(theta0+t v) has derivative at 0 equal
  to sum_i h(eta_i(theta0))(k_i-8Phi(eta_i(theta0)))(Wv)_i.

The fixed data are not supplied as hypotheses. The docstring calls this the
whole fixed residual-root/nonmaximum example and distinguishes it from the
printed necessary implication about ML fits.

**Totalizations and domains.** Real sInf is total even on an empty or unbounded
set; both obstructions are expressly excluded here by a conjunct, and the
stated CDF values identify the intended quantile. No other infimum appears.
For all finite real a, 0<Phi(a)<1 and phi(a)>0 for the standard normal law;
in particular the asserted values protect the fixed witness denominators and
logs. The likelihood's global comparison remains inside the valid probit
domain for every theta. `deriv Phi` is the actual normal density rather than
the default zero value at nondifferentiability. The mean/variance parameters
of `gaussianReal 0 1` and `gaussianPDFReal 0 1` are admissible. There are no
empty finite index types, casts changing signs, natural subtraction, matrix
inverse, Bochner mean, infinite toReal, limsup/liminf, sqrt or rpow issues.

## SAP.P015a.T7

Location: `Challenge/Part1.lean:89–101`; proposition at `Defs/Part3.lean:70–79`;
main conjunction at `Defs/Part2.lean:159–208`. This is unconditional, except
for the internal universally quantified parameter restrictions written below.

The six rows i=0,...,5 have (X_i,D_i)=(-1,0),(-1,1),(0,0),(0,1),(1,0),(1,1)
and p_i=(1/4,1/12,1/6,1/6,1/12,1/4). Put e(x)=1/2+x/4,
b_a(x)=1/4+a(3x^2-2), V_i=(1,D_i-e(X_i),X_i),
r_i(a,epsilon)=b_a(X_i)+epsilon(D_i-e(X_i)), and m(eta)=eta^2.
Every use of a finite mean here is sum_i p_i times the given value.
The expected log likelihood is exactly
ell_{a,epsilon}(theta)=sum_i p_i [r_i(a,epsilon)log((V_i theta)^2)
+(1-r_i(a,epsilon))log(1-(V_i theta)^2)].
An admissible theta satisfies 0<V_i theta<1 for every i; this selects the
positive branch of the square inverse link.

1. There exists a function theta : real -> real three-vectors for a=1/16,
   with theta(0)=(1/2,0,0), such that there exists a real r with
   0<r<=1/16 and, for every real epsilon with |epsilon|<r, theta(epsilon)
   is admissible, ell(t)<=ell(theta(epsilon)) for every admissible t, and equality
   forces t=theta(epsilon). The treatment coordinate theta_1(epsilon) has
   derivative 120/119 at epsilon=0. Separately there exists such a function and
   radius for a=0, with treatment derivative 1. The functions and radii can
   differ between the two cases. Differentiability of the other two coordinates
   or of the whole path is not asserted. 120/119 != 1 is expressly included.

2. For every real epsilon with |epsilon|<=1/16,
   sum_i p_i r_i(1/16,epsilon)=1/4, and the treatment coordinate of the actual
   weighted coefficient
   (sum_i p_i V_i V_i^T)^(-1) (sum_i p_i V_i r_i(1/16,epsilon))
   is epsilon. Both assertions are repeated in the conjunction.

3. Every p_i is nonnegative and their sum is 1. Write
   A=sum_i p_i V_i V_i^T=diag(1,5/24,2/3),
   B=sum_i p_i V_i V_i^T(b_{1/16}(X_i)-1/4)
   =diag(0,-1/384,1/24). Then
   H=(-32/9)B-(16/3)A=diag(-16/3,-119/108,-100/27).
   For every real three-vector t, Ht+(0,10/9,0)=0 iff t=(0,120/119,0).

4. On the standard Borel space ((real x real) x real), use the measure
   P=sum_i p_i [delta_{(X_i,D_i)} product (Lebesgue restricted to [0,1])].
   The weights in Lean use real-to-nonnegative-real conversion, which is
   harmless because the displayed p_i are positive. U is the last coordinate,
   X and D the first two coordinates. Define, for all real a,epsilon,d,
   Y_{a,epsilon}(d)=1_{U <= b_a(X)+epsilon(d-e(X))} and
   tau_{a,epsilon}=Y_{a,epsilon}(1)-Y_{a,epsilon}(0).
   Both the restricted Lebesgue law and P are probability measures.
   For every a,epsilon, assuming a=0 or a=1/16 and |epsilon|<=1/16:
   each x in {-1,0,1} has P(X=x)=1/3; D is binary almost surely; U is in [0,1]
   almost surely; for every real u with 0<=u<=1, P(U<=u)=ofReal(u);
   U is independent of (X,D); (Y(0),tau) and D are conditionally independent
   given the sigma algebra generated by X; E[D|X]=e(X) almost surely;
   Y(D)=Y(0)+tau D almost surely; E[Y(D)|X,D]=b_a(X)+epsilon(D-e(X))
   almost surely; and E[Y(D)]=1/4. Conditional independence and conditional
   expectations are Mathlib's actual measure-theoretic notions, not finite-cell
   stand-ins. The finite instances `squareLinkUnitLaw_finite` prove finiteness
   of this same measure by finite summation and product/restriction instances.

5. For every real eta with 0<eta<1, the Bernoulli multiplier of m(eta)=eta^2
   is h(eta)=2/(eta(1-eta^2)). At eta=1/2, m'=1, h=16/3, h'=-32/9.
   Define S_j(a,epsilon,theta)=sum_i p_i V_ij
   [m'(V_i theta)/(m(V_i theta)(1-m(V_i theta)))]
   [r_i(a,epsilon)-m(V_i theta)]. Then S(1/16,0,(1/2,0,0))=0.
   For every real three-vector v, the derivative at t=0 of
   S(1/16,0,(1/2,0,0)+t v) is Hv. The derivative at epsilon=0 of
   S(1/16,epsilon,(1/2,0,0)) is (0,10/9,0). For every real a,epsilon,theta,v,
   assuming a=0 or a=1/16, |epsilon|<=1/16 and theta admissible, the derivative
   at t=0 of ell_{a,epsilon}(theta+t v) is sum_j S_j(a,epsilon,theta)v_j.

6. For every real three-vector theta, put
   gamma=(theta_0-theta_1/2,theta_1,theta_2-theta_1/4).
   Then gamma_1=theta_1 and, for every i,
   (1,D_i,X_i) dot gamma=V_i theta. For every real alpha,beta,gamma there
   exists a theta whose transformed coordinates equal (alpha,beta,gamma).
   Thus the change to unresidualized treatment and covariate is onto and
   preserves the treatment coefficient.

7. D is integrable under P, and for every real a,epsilon the observed binary
   outcome Y_{a,epsilon}(D) is integrable under P (without the small-parameter
   restriction for this boundedness assertion).

The docstring explicitly describes a restriction to expected-likelihood
projections that allow misspecification. At a=1/16,epsilon=0 the actual
conditional probabilities for X=-1,0,1 are 5/16,1/8,5/16; the maximizing fit
at the constant theta(0) gives 1/4 in all rows. Thus the statement does not
require the true mean to be the square of a linear predictor. The second law's
common mean follows from the asserted E[Y(D)]=1/4; its own maximizing branch
has the same intercept center.

**Totalizations and domains.** The matrix inverse in the finite population
coefficient is Mathlib's total nonsingular inverse, which uses a zero result
when the determinant is zero over real scalars. The explicit A has determinant
5/36, so the coefficient here is an actual unique least-squares coefficient.
The functions ell and S are total even outside the square-link parameter
domain, where log and division totalizations would be statistically invalid;
all maxima and their derivatives are on 0<V theta<1. The existential radius is
strictly positive and its interval is nonempty. For a in {0,1/16} and
|epsilon|<=1/16, the potential-outcome thresholds at supported X and binary d
are strictly between 0 and 1 (in particular bounded below by 5/64 and above
by 23/64). They are genuine Bernoulli probabilities, not clipped probabilities
misreported as the thresholds. For arbitrary a,epsilon the potential outcome
is still a well-defined indicator and remains integrable, but its threshold
need not itself equal a probability outside the restricted assertions.
The latent uniform endpoint event U=0 has probability 0, so using <= changes
no claimed mean. No quotient by a null covariate-cell mass occurs. Bochner
integrals and conditional expectations have zero defaults if the requisite
integrability or sigma-finiteness fails; here the measure is a probability
measure and all variables are bounded on its support, with the relevant
integrability expressly included or immediate. Standard Borel and measurable
sub-sigma-algebra witnesses are present. No toReal(infinity), empty finite
index type, sInf/sSup, limsup/liminf, truncated natural subtraction, sqrt,
rpow or unspecified partial-function default occurs.

## SAP.P015a.T16

Location: `Challenge/Part1.lean:103–106`; proposition at
`Defs/Part3.lean:175–189`. It is the following unconditional conjunction:

1. 10800420763/10000000000 < exp(77/1000)
   < 10800420765/10000000000, the latter upper bound is <6/5, and
   800420763/100000000 < 100(exp(77/1000)-1)
   < 800420765/100000000. Thus the multiplicative factor is approximately
   1.0800420764 and the percent conversion approximately 8.00420764.
2. For every real alpha,beta,d,c,
   exp(alpha+beta(d+1)+c)/exp(alpha+beta d+c)=exp(beta).
   This is an identity about exponentiated linear fitted contrasts.
3. Fix W with four rows (1,0),(1,0),(1,1),(1,1), spending vector
   S=(1,1,0,3), and Y_i=log((1+S_i)/2). Define the fitted coefficient by the
   actual formula (W^T W)^(-1)W^T Y. Its treatment coordinate is 0 and the
   exponential of that coordinate is 1. Also
   (log(1/2)+log 2)/2=0; the first group's arithmetic S mean is 1 and the
   second group's arithmetic S mean is 3/2; ((3/2)/1-1)100=50.
4. For this same W, det(W^T W)=4.

There is no universal claim that exponentiation recovers arithmetic spending
means, or that 0.077 is 20 percent. The docstring describes the numerical
conversion, fitted ratio identity and four-observation separation.

**Totalizations and domains.** The exponential denominator is strictly positive
for all four universally quantified real arguments. The fixed logarithm
arguments are 1,1,1/2,2, so all are positive, including for S=0. Each fixed
numeric denominator is nonzero. The OLS inverse is nonsingular since its
determinant is 4; singular-inverse defaults cannot explain the zero treatment
coefficient. All index sets are nonempty Fin 4 or Fin 2. The means in this
example are finite arithmetic sums divided by 2, not nonintegrable Bochner
integrals. There are no truncating casts, natural subtractions, infinite
toReal, infima/suprema, limsup/liminf, rpow, sqrt or partial-function defaults.
