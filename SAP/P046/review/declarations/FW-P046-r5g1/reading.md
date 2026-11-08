# Blind reading of P046-T1–T5

This file was saved before opening `claims.json` or `record.json`. I read all
entries of `closure.json`, the corresponding source declarations in Part1,
Part2, Part3, Part4 and WholeW1, and the five Challenge docstrings. The 79
distinct generated proof helpers in the union of the closures were also printed
in `scratch/ClosureChecks.lean` (output `scratch/closure-checks.out`). They are
numeral-denominator certificates, finite-index certificates, ordinary measurable/
probability-space instances, or the two proof fields of the explicit cross-fit;
they introduce no additional hypotheses. Structure constructors and projections
in the closure have the fields described below.

## Common notation, fully unfolded

The full-data space is the standard Borel product
`R × (Bool × (Bool × Bool))`. Write an element as `(w,(x,(y0,y1)))`, and identify
each Boolean with its indicator in `{0,1}`. Then W=w, X=x, Y(0)=y0,
Y(1)=y1, and observed Y=(1-X)Y(0)+XY(1). The observed triple is
`(W,(Y,X))`; the sigma algebra used for conditioning on W is the pullback
of the Borel sigma algebra on R along the first projection.

A study M is a measure P on this space, real functions p,m on R, and a real
number delta. “Valid” means ALL of the following: P is a probability measure;
P(W=w)=0 for every real w; p,m are Borel measurable; delta>0;
delta<p(W)<1-delta P-almost surely;
E[X|sigma(W)]=p(W) and E[Y(1)|sigma(W)]=m(W) P-almost surely;
0<=m(W)<=1 P-almost surely; and Y(0) and X, and separately Y(1) and X,
are conditionally independent given sigma(W), in Mathlib's `CondIndepFun`
sense. Joint conditional independence of the pair of potential outcomes is
not required. The stored conditional-mean versions can be arbitrary off a null
set. The parameter mu is the Bochner integral E_P[Y(1)].

A size-n sample is a function from `Fin n` into the full-data space, with
law P_n equal to the finite product of n copies of P. The covariate sigma
algebra G_n is the pullback of the Borel product sigma algebra along
`a -> (W(a_i))_i`. All probabilities below are measured using these actual
product laws. Define

* H_n(a)=(sum_i X_i Y_i/p(W_i))/n;
* xi_n(a)=(sum_i p(W_i)^(-2))/n;
* mbar_n(a)=(sum_i m(W_i))/n;
* r_print(alpha,a)=sqrt(xi_n(a) log(2/alpha)/(2n));
* r_corr(alpha,a)=(sqrt(xi_n(a))+1)sqrt(log(4/alpha)/(2n));
* Tail(est,r)=P_n(r(a)<=|est(a)-mu|), converted from ENNReal to R;
* Coverage(est,r)=P_n(est(a)-r(a)<=mu<=est(a)+r(a)), similarly converted;
* strict printed noncoverage=P_n(r_print(alpha,a)<|H_n(a)-mu|), similarly converted.

Each real expectation is Mathlib's Bochner integral. Conditional expectations
are Mathlib `condExp`, and conditional probabilities are the conditional
expectations of the displayed real-valued indicator functions. All a.e.
equalities and inequalities allow the null set to depend on parameters outside
the a.e. quantifier.

For regressions g, the fixed summand is
B_g(o)=X(o)(Y(o)-g(W(o)))/p(W(o))+g(W(o)); its estimator is the average of
B_g. A cross-fit at size n consists of a deterministic fold map
`s:Fin n -> Bool` and functions `g_j(a,w)`, jointly Borel measurable in (a,w).
If two full-data samples have identical observed triples at every index with
s(i)!=j, their entire functions g_j(a,.) agree. Thus fit j uses only the
observed opposite fold. The adjusted estimator is
A_n(a)=n^(-1) sum_i B_{g_{s(i)}(a,.)}(a_i).
For a sequence of cross-fits, balanced means: for each Boolean j, the number
of indices of fold j divided by n tends to 1/2 as n tends to infinity.

Write q(w)=(1-p(w))/p(w),
R(g)=E[q(W)(Y(1)-g(W))^2], Nq(g)=E[q(W)g(W)^2],
N2(g)=E[g(W)^2], and V(g)=Var_P(Y(1))+R(g). Here R,Nq,N2 are real
Bochner integrals. For a training subset T of `Fin n`, the empirical objective
is the finite sum Q_T(g)=sum_{i in T} X_i(1-p_i)/p_i^2 (Y_i-g(W_i))^2.
“Zero benchmark” for a set G of functions means the zero function is in G,
OR there exists a sequence h_k in G with real Nq(h_k) tending to zero.

“Normal limit with variance v” means v>=0, P is a probability measure, and
the random variables sqrt(n)(est_n-mu), with underlying laws P_n, converge
in distribution to the identity variable on R with law `gaussianReal 0 v.toNNReal`.
This is the ordinary centered Gaussian with variance v, including the point
mass at zero when v=0. Variance itself is Mathlib's extended integral of the
squared distance from the real Bochner mean, followed by ENNReal.toReal.

Global totalization conventions to keep in view: real inverse/division at zero
is zero; Real.sqrt is zero for nonpositive inputs; Real.log(0)=0 and
Real.log(x)=log|x| for x<0; a nonintegrable/non-a.e.-strongly-measurable
Bochner integrand has integral zero. Mathlib's conditional expectation is zero
if the conditioning sigma algebra is not a sub-sigma algebra, its trimmed
measure is not sigma-finite, or the function is not integrable. ENNReal.toReal
sends infinity to zero, and Real.toNNReal clips negative numbers to zero.
The uses below must be checked against these conventions individually.

## SAP.P046.T1

This is a closed conjunction, with no theorem-level premises or free parameters.
The population is generated from two independent uniform [0,1] real variables
(W,U), using restricted Lebesgue measures and `Measure.map`:
p(w)=13/20 when w<=3/5 and 99/100 otherwise;
X=1{U<=p(W)}, Y(0)=0, Y(1)=1{W<=3/5},
m(w)=1{w<=3/5}, delta=1/200. The theorem first asserts all the validity
conditions above, the uniform W marginal, and mu=3/5.

The categories are low treated, low untreated, and high (the last category
ignores treatment). Let K count the first two and S count the first.
The theorem asserts their single-unit probabilities are respectively
39/100,21/100,40/100, and that for EVERY pair of natural numbers s<=k<=100,
P_100(K=k,S=s)=binom(100,k)binom(k,s)39^s 21^(k-s)40^(100-k)/100^100.
The category map is measurable. For every n and every sample, S<=K<=n.
For every size-100 sample obeying the stated potential-outcome design equations
(with arbitrary W and treatment values), and also P_100-almost surely,
H_100=S/65, H_100-mu=(S-39)/65, and
xi_100=xi(k)=[400k/169+10000(100-k)/9801]/100 at k=K.

For every feasible (k,s), xi(k)>0; strict exclusion from the closed printed
interval is equivalent to
xi(k)log(20000000)/200 < (s-39)^2/65^2,
and this is equivalent to log(20000000)<200(s-39)^2/(4225 xi(k)).
The strict noncoverage probability equals the finite sum of the displayed
count masses over this last test. There are 5151 feasible states, of which
1946 satisfy the real strict exclusion test.

Separately, define the natural integer mass numerator
b(k,s)=binom(100,k)binom(k,s)39^s21^(k-s)40^(100-k), and a Boolean integer
test
200*7840800*absNat(s-39)^2 > 3363*(3920400*k+1690000*(100-k)),
where absNat(s-39) is `39-s` if s<=39 and `s-39` otherwise.
The certified numerator C is the sum of b(k,s) passing this integer test over
0<=k<=100 and 0<=s<=k. The statement fixes

`C = 11979291069795625472576722625601454579193931030581441019247695948117336197717708252113744670235734049700195915329948439938976976688794607547282140972800735873954434550061258658968400997158933003`.

At n=100, alpha=1/10000000, strict noncoverage is C/100^100,
is greater than 119/1000000000, which is greater than alpha. Coverage of the
closed interval equals 1-C/100^100 and is less than 1-alpha. The non-strict
population-centered tail Tail(H,r_print) is also greater than alpha.
No SAP conclusion is an assumption: the validity, reductions, counts and
probability equality are all conjunctive assertions.

Junk conventions: all statistical divisions here use positive fixed n and
propensities bounded away from zero, including at every real w. All logarithms
have the positive argument 20000000 and their square-root arguments are
nonnegative on feasible counts. The `100-k` in xi(k) is REAL subtraction;
in b(k,s) and the integer test it is NATURAL truncated subtraction. The latter
and k-s occur only at feasible k,s in the operative sums. The branch in
absNat selects a nonnegative natural difference. `Nat.choose` outside its
usual range is zero, but the operative ranges already enforce feasibility.
Natural casts into R and division by 100^100 are exact, not integer division.
The enormous numerator is a natural integer. `Fin 100` is nonempty. Uniform
restriction and all mapped/product measures are finite probabilities, so no
infinity-to-zero conversion occurs. All integrated outcomes/indicators are
bounded and measurable. No empty supremum/infimum, limsup/liminf, rpow, partial
function default, or unbounded-sequence convention is used.

## SAP.P046.T2

This too is a closed conjunction. From independent uniform [0,1] (W,U), use
X=1{U<=9/10}, Y(0)=0, Y(1)=1{1/2<=W}, p=9/10,
m(w)=1{1/2<=w}, delta=1/20. All standing validity conditions, uniform W
marginal and mu=1/2 are asserted. Let E be the size-100 covariate event
`all W_i<1/2`. Then P_100(E)=(1/2)^100>0.

For EVERY size-100 sample a, xi(a)=100/81,
r_print(1/20,a)=sqrt(log(40)/162), and the denominator
D(a)=sum_i [100p(W_i)]^(-2) equals 1/81. The theorem asserts
log(40)/162<1/4, sqrt(log(40)/162)<1/2, and
2exp(-log(40))=1/20. It also asserts for every a that
2exp(-[2*(xi(a)log(2/(1/20))/(2*100))]/D(a))=1/20.

For EVERY real covariate vector w and Boolean treatment vector x, if every
w_i<1/2, form the design-respecting sample
(w_i,(x_i,(false,1{1/2<=w_i}))). Every observed Y_i is zero; H=0;
mbar=0; and |H-mu|=1/2. No conditioning on a singleton W=w is asserted.
Globally E[H|G_100]=mbar almost surely. Almost surely with respect to
P_100 restricted to E, mbar=0, the actual conditional expectation of H is
zero, and mu!=0. Also P_100-restricted-to-E almost surely,
E[1{r_print(1/20)<=|H-mu|}|G_100]=1>1/20.
The conditioning in this last assertion uses the ORIGINAL sample law, not
the restricted law. This establishes the specified conditional population-tail
failure on a positive-probability covariate event.

Junk conventions: n=100, p=9/10, D=1/81, alpha=1/20, and all log arguments
are positive. Sqrt receives a positive argument. The law and its restriction
are finite; toReal never acts on infinity. H and all indicators are bounded
and Borel measurable, G_100 really is a sub-sigma algebra, and the trimmed
probability law is finite; hence no zero-default conditional expectation is
being invoked. E has explicitly positive probability, so its a.e. assertions
are not assertions on a null event. Pointwise assertions use design-respecting
samples; they do not silently force arbitrary full-data tuples to obey the
design. No empty index, truncated subtraction, rpow, supremum/infimum,
limsup/liminf, or partial-function convention enters.

## SAP.P046.T3

This is a conjunction of universal propositions. Each component first
quantifies over EVERY study M and assumes the complete ValidStudy conditions.
There is no extra hypothesis asserting a tail bound or independence conclusion.
For each alpha with 0<alpha<1 and each natural n>0,
Tail(H,r_corr)<=alpha. For each such n, almost surely,
r_corr < (delta^(-1)+1)sqrt(log(4/alpha)/(2n)). For each M and alpha
there exists a real C>0, chosen BEFORE n, such that for every n>0 the
width 2r_corr<=C/sqrt(n) almost surely. C can depend on M and alpha.
For EVERY b>0 with b<=p(W) almost surely, EVERY n>0 and alpha in (0,1),
the constant radius b^(-1)sqrt(log(2/alpha)/(2n)) has non-strict tail <=alpha.

The other conjuncts spell out the corrected proof, with the following exact
quantifier orders and meanings:

1. For each valid M,n>0, H=sum_i A_i pointwise, where
   A_i=X_iY_i/(n p(W_i)). For each index i, almost surely X_iY_i=X_iY(1)_i
   and the chain of equalities holds:
   E[A_i|G_n]=E[XY(1)|sigma(W)](a_i)/(np_i)
   =E[X|sigma(W)](a_i)E[Y(1)|sigma(W)](a_i)/(np_i)=m(W_i)/n.
   Also E[H|G_n]=mbar almost surely, E[H]=E[mbar]=mu, and for each i
   E[m(W_i)]=mu.
2. For each valid M,n>0, G_n is a sub-sigma algebra and the family A_i is
   conditionally independent given it (`iCondIndepFun`). Almost surely all
   A_i lie in [0,1/(np_i)], xi>0, D=sum_i(np_i)^(-2)>0,
   D=xi/n and sqrt(xi)<delta^(-1).
3. For each valid M,n>0, and THEN each fixed t>=0, almost surely
   E[1{t<=|H-mbar|}|G_n] <= 2exp(-2t^2/D)
   =2exp(-2nt^2/xi).
4. For each valid M,n>0,alpha in (0,1), put
   c=sqrt(log(4/alpha)/(2n)). Almost surely
   E[1{sqrt(xi)c<=|H-mbar|}|G_n]<=alpha/2, and
   2exp(-2n(sqrt(xi)c)^2/xi)=2exp(-2nc^2).
   The unconditional probability of this same event is <=alpha/2.
   This is the particular covariate-measurable random threshold displayed;
   it is not a universal theorem about all random thresholds.
5. For each valid M and every n (including zero), the m(W_i) are independent
   under P_n and each coordinate has the one-unit m(W) distribution.
   Also 0<=m(W)<=1 almost surely and E[m(W)]=mu. For each n>0 and alpha
   in (0,1), P_n(c<=|mbar-mu|)<=2exp(-2nc^2)
   =2exp(-log(4/alpha))=alpha/2.
6. For each valid M,n>0,alpha in (0,1), pointwise triangle inequality holds.
   The event {r_corr<=|H-mu|} is contained in the union of
   {sqrt(xi)c<=|H-mbar|} and {c<=|mbar-mu|}. Its probability is at most
   the sum of those probabilities, the sum is <=alpha, and the closed
   corrected interval has coverage >=1-alpha.
7. For each valid M and b>0 with b<=p(W) almost surely, HT single-unit
   summands XY/p(W) are independent and identically distributed under P_n
   for every n, lie in [0,b^(-1)] almost surely, and have mean mu.
   For each n>0 THEN t>=0 their average has non-strict population tail
   <=2exp(-2nt^2/(b^(-1))^2). For each n>0 THEN alpha in (0,1),
   substitution of b^(-1)sqrt(log(2/alpha)/(2n)) into this bound gives
   exactly alpha, and the resulting closed interval has coverage >=1-alpha.

Junk conventions: n>0 in every estimator bound; alpha in (0,1) makes log
arguments greater than one; b,delta and propensities are strictly positive
on all operative probability-one sets. Therefore square-root arguments and
denominators are proper there. Outside that set arbitrary samples may have
zero or negative p; all universal pointwise algebraic identities and event
inclusions are meaningful with the totalized arithmetic, and all substantive
probability bounds are a.e. Sample integrands are bounded a.e. by positivity;
conditional expectations are genuine integrable conditional expectations.
All toReal inputs are probabilities. The n=0 IID assertions quantify over
an empty family and are harmless, while the statistical conclusions exclude
n=0. Natural-to-real casts are exact. No sInf/sSup, limsup/liminf, rpow, or
partial-function convention enters; the explicit width quantifiers are used
instead of any ambiguous asymptotic supremum.

## SAP.P046.T4

This is another closed conjunction. Take three independent uniform [0,1]
variables (W,V,U), L=1{W<=1/2}, Z=1{V<=1/10},
p(W)=1/4 on L and 3/4 otherwise, X=1{U<=p(W)},
Y(0)=Y(1)=LZ, m(W)=L/10, delta=1/8. The theorem asserts all validity
conditions, the uniform marginal, and mu=1/20. The real-parameter family is
g_theta(w)=1/2 on w<=1/2 and theta on w>1/2.
The explicit cross-fit uses folds s(i)=1{floor(n/2)<=i.val} and ALWAYS
returns g_0, irrespective of training data. It is measurable, depends only on
the opposite observed fold (by being constant in the data), and its two fold
fractions tend to 1/2.

For each fold, its real squared L2 error relative to g_0 converges to zero
in probability: for every eps>0 the probability that N2(error)>eps tends to
zero. Stronger pointwise assertions give fit_j(a)=g_0 and N2(error)=0 for
every n,j,a. For every n,j, almost every sample, g_0 minimizes the empirical
treated-case objective over all real theta. All sample sizes n, all subsets
T, all real covariate vectors w and Boolean vectors z,x are covered by a
separate algebraic training theorem: use design data with both potentials
1{w_i<=1/2}z_i, and let N_U count upper-half treated training indices.
The weights (1-p)/p^2 are 12 on the lower half and 4/9 on the upper half.
Q_T(g_theta)=C_T+(4/9)N_U theta^2,
where C_T=12 sum_{i in T,w_i<=1/2} x_i(z_i-1/2)^2.
Thus Q_T(g_0)<=Q_T(g_theta); equality holds iff N_U=0 OR theta=0.

For every real theta, the population treated-case loss equals R(g_theta),
and R(g_theta)=3/8+theta^2/6. It equals R(g_0) iff theta=0, giving the
unique minimizing parameter. Also Nq(g_theta)=3/8+theta^2/6,
R(0)=3/20, R(g_0)=3/8 and R(g_0)-R(0)=9/40>0.
Every g_theta differs from the zero function; Nq(g_theta)>=3/8 for every
theta; and the zero-benchmark disjunction fails for the range of this family.

Write H=XY/p(W) and A=X(Y-g_0(W))/p(W)+g_0(W).
For every design-respecting scalar datum, on the lower half
H=4xz and A=4xz+(1/2)(1-4x); on the upper half H=A=0.
Almost surely the four cases give A=0,1/2,-3/2,5/2, respectively:
upper half (probability 1/2); lower untreated (3/8);
lower treated with Y(1)=0 (9/80); lower treated with Y(1)=1 (1/80).
Almost surely 0<=H<=4 and -3/2<=A<=5/2. Both and their squares are
integrable; E[H]=E[A]=1/20; E[H^2]=1/5; E[A^2]=17/40;
Var(H)=79/400; Var(A)=169/400; Var(Y(1))=19/400.
For every n their sample summands are independent with the corresponding
one-unit laws. Pointwise for every n,a the HT and adjusted estimators are
respectively the averages of H and A; adjusted also equals the fixed-g_0
estimator. For every positive n both means are mu and their variances are
79/(400n) and 169/(400n). Their centered sqrt(n) errors converge in
distribution to the centered Gaussians with variances 79/400 and 169/400.
The latter variance is larger, the gap is 9/40 and their ratio is 169/79.

Junk conventions: the sample-size-zero average identities are formally
included: empty sums divided by zero give zero on both sides. They are
algebraic identities only; expectation and variance formulas require n>0
and limits ignore initial terms. The fold split uses natural floor division
n/2 intentionally; empty folds at small n are allowed. The real squared L2
definition could return zero for nonintegrable errors generally, but here
the error function is identically zero. The family is bounded for each fixed
theta, so all real risks and norms are finite and coincide with the genuine
integrals. All p values are positive at every real w. Gaussian variances
are strictly positive and so toNNReal does not clip. Probability conversions
are finite; no default condExp is used. No rpow, sInf/sSup, limsup/liminf,
or partial-function convention enters.

## SAP.P046.T5

This is a conjunction of four universal propositions. In each the study is
quantified first and assumed valid, with ALL the common validity assumptions.
Here extended L2 and weighted quantities are additionally defined by Lebesgue
integrals taking values in [0,infinity]:
E2(g)=integral^+ ofReal(g(W)^2),
Eq(g)=integral^+ ofReal(q(W)g(W)^2),
ER(g)=integral^+ ofReal(q(W)(Y(1)-g(W))^2).
There is no toReal on these quantities. For a fixed fold j and target g,
“extended L2 convergence in probability” means for EVERY real eps>0,
P_n(ofReal(eps)<E2(fit_{n,j}(a,.)-g)) tends to zero. Infinite errors are
counted in these events, not converted to zero.

1. For every valid M, delta<=q(W)<=delta^(-1) almost surely. For EVERY
   Borel measurable real g, ofReal(delta)E2(g)<=Eq(g)
   <=ofReal(delta^(-1))E2(g). For EVERY sequence of Borel measurable
   functions u_k, Eq(u_k) tends to zero in ENNReal iff E2(u_k) does.
2. For every valid M and real function g with `MemLp(g o W,2,P)`
   (a.e. strongly measurable, finite L2 norm),
   Var_P(B_g)=Var_P(Y(1))+R(g). All three quantities here are real.
3. Family theorem, in quantifier order: for every valid M, every natural d,
   every family `(Fin d -> R) -> (R -> R)`, and every sequence of cross-fits F,
   assume F balanced; every family member composed with W is MemLp 2;
   the zero-benchmark disjunction holds for the family range; for EVERY n,j,
   almost every training sample admits a parameter theta such that the fitted
   function equals family(theta) AS A FUNCTION ON ALL R and is an exact
   minimizer of Q_T over every eta, where T={i:s_n(i)!=j}.
   THEN for EVERY gstar in the family range, if R(gstar)<=R(family(theta))
   for every theta and the fits converge to gstar in the extended L2 sense
   in both folds, the following three conclusions hold: adjusted has NormalLimit
   V(gstar); HT has NormalLimit V(0); and V(gstar)<=V(0).
   The population minimizer and L2 convergence are premises, not asserted
   consequences of empirical minimization. The dimension d may be zero.
4. Direct theorem, in quantifier order: for every valid M and balanced
   cross-fit sequence F, EVERY Borel measurable gstar such that both fits
   converge to gstar in the extended L2 sense and ER(gstar)<=ER(0),
   the function gstar composed with W is MemLp 2, ER(gstar)<infinity,
   R(gstar)<=R(0), and the same two Gaussian limits and variance comparison
   hold. No family, exact minimization, finite-sample fitted L2 premise or
   explicit L2 premise for gstar appears in this direct theorem.

The Gaussian efficiency conclusion is exactly the conjunction of these two
NormalLimit statements and the inequality between their specified limiting
variances; it makes no separate assertion about finite-n variance ordering.

Junk conventions: extended integrals can be infinite and retain infinity;
ofReal clips negative arguments, but the integrands are nonnegative almost
surely since q>0 almost surely, so clipping off-support values has no effect.
All outer probability toReal operations are on finite probability values.
MemLp 2 for every family member protects the real Nq in ZeroBenchmark,
the real R comparisons and the fixed-summand variance identity from
nonintegrability defaults. In the direct theorem the finite ER(0), bounded
Y(1), and two-sided positivity force finite ER(gstar) and L2 membership;
the real risks used in its conclusion then have their genuine values.
Individual fits in the direct theorem may fail L2 on rare events: their
errors are measured by E2, so this cannot be mistaken for error zero.
The hypotheses do not require estimator means or variances at every n in
this case. n=0 only contributes irrelevant initial estimator values (zero
from empty sums and zero division) and possibly an empty training objective.
The zero-dimensional parameter space has one element and causes no empty
existence condition. All Gaussian variances are asserted nonnegative by
NormalLimit, and variance zero is explicitly a point mass; toNNReal cannot
hide a negative variance in a satisfied conclusion. No rpow, empty/unbounded
infimum/supremum, limsup/liminf, or partial-function default is involved.
