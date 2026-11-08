# Blind reading

This file was saved before opening `claims.json` or `record.json`. Sources read:
the five docstrings and declarations in `SAP/P001e/Challenge/Part1.lean`, every
source declaration named in their `closure.json` entries, and every generated
`._proof_*` declaration (printed by `scratch/Blind.lean`, which compiled).
Throughout, `Fin n` is the set of natural numbers less than n, a vector is a
function on that finite set, and all arithmetic displayed below is real unless
explicitly stated otherwise. All finite sums/products range over the entire
indicated `Fin` type. No solution proofs were consulted.

## SAP.P001e.T77

The statement is the conjunction of the following two universally quantified
assertions (`Defs/Part3.lean:15–19`, `Defs/WholeW1.lean:14–34`).

1. For every type Ω, natural parameter dimension τ, subset Θ of R^τ, function
   Y:Ω→R, natural covariate dimension K, function X:Ω→R^K, and real function
   g:R×R^K×R^τ→R, if g(y,x,t)≥0 for every y,x and every t∈Θ, there exists
   L:Ω→Θ→R≥0 such that for every ω∈Ω and t∈Θ its real coercion equals
   g(Y(ω),X(ω),t). Here R≥0 is Mathlib's subtype of nonnegative real numbers,
   and Θ as a type is the subtype of parameter vectors belonging to the set.
   There are no measure, density, sample-size, normalization, continuity,
   measurability or maximization hypotheses in this first assertion. The
   existential L is after all the data and the nonnegativity hypothesis and
   before the universal ω,t. This is a representation of finite nonnegative
   realized function values, not an assertion that arbitrary g is a density.
2. For every m,s∈R with s>0, let
   d(y)=exp(-(y-m)^2/(2s^2))/(s sqrt(2π)). Then d is Bochner integrable for
   Lebesgue measure, d(y)≥0 for every real y, its Lebesgue integral is 1,
   d(m)=1/(s sqrt(2π)), and s<1/sqrt(2π) implies d(m)>1.

The docstring describes a finite realized likelihood as a function on a real
parameter set, and the normal-density demonstration that a density value may
exceed one. The second conjunct supplies a genuine normalized density, rather
than just an arbitrary value exceeding one.

Junk and boundary conventions: real division by zero is zero, and real sqrt is
zero on nonpositive inputs. In the definition of d at s=0 this would give the
zero function; at negative s it is not a density. All uses in the theorem have
s>0 and 2π>0, excluding these cases. A Bochner integral is zero when its
integrand is not integrable, but integrability is explicitly concluded here.
There is no infinity in the real codomain. Ω or Θ may be empty, making that
particular pointwise representation empty, but the assertion also quantifies
over nonempty choices. τ=0 or K=0 gives the legitimate singleton empty-vector
space; it does not introduce a default coordinate. There is no log, rpow,
truncated subtraction, infimum, supremum or limit operation. The generated
`W1normalDensity._proof_1` merely certifies that the numeral 2 is at least two.

## SAP.P001e.T78

For every n,K∈N, first assume n>0, then take a matrix X with n rows and K+1
real columns, an outcome vector Y∈R^n and coefficient vector b∈R^(K+1).
Assume, in order:

- X(i,0)=1 for every row i (an intercept column);
- for every c∈R^(K+1), Q(b)≤Q(c), where
  Q(c)=Σ_i (Y_i-Σ_j X(i,j)c_j)^2;
- Q(b)>0.

Define residuals e_i=Y_i-Σ_j X(i,j)b_j and m=(Σ_i e_i)/n. The conclusion is
the conjunction:

- sqrt(Q(b)/n)>0 and sqrt(Q(b)/n)^2=Q(b)/n;
- for every c∈R^(K+1) and s∈R, s>0 implies
  ell(c,s)≤ell(b,sqrt(Q(b)/n)), where the SAP log likelihood unfolds to
  ell(c,s)=-n log(s)-(n/2)log(2π)-Q(c)/(2s^2);
- Σ_i e_i=0 and m=0;
- (Σ_i (e_i-m)^2)/n=Q(b)/n;
- (Σ_i e_i^2)/n-m^2=Q(b)/n.

This is exactly the proposition defined at `Defs/WholeW1.lean:42–56`, using
`residualSS` and `gaussianLogLikelihood` from `Defs/Part1.lean:43–51`.
Matrix multiplication here is just the displayed finite coordinate sum. The
docstring calls the last two expressions the centered residual second moment
and plug-in variance. There is no rank, uniqueness, stochastic error model,
coefficient-existence assertion or general assertion for zero residual sum.
The least-squares minimizer b is supplied as data.

Junk and boundary conventions: the cast of n to R is an exact natural-number
cast, nonzero because n>0. All divisions by n and 2s^2 in the assertion thus
have nonzero denominators. The square-root argument at the proposed optimum
is positive by Q(b)>0. Real.log(0)=0, and Real.log at a negative real is the
logarithm of its absolute value, but every scale being compared is positive
and 2π>0. The excluded n=0 and Q=0 cases would be materially different. K=0
is permitted and gives an intercept-only model, with one coefficient; K+1
is never empty. All subtraction is in R, not truncated natural subtraction.
No integrals, extended-real values, extrema of sets or limits occur. The
generated `T78WholeStatement._proof_1` supplies `NeZero (K+1)` for coordinate
0, and `gaussianLogLikelihood._proof_1` certifies the numeral 2.

## SAP.P001e.T79

The statement is a conjunction of a population assertion, a fitted discrete
assertion and a fitted density assertion (`Defs/WholeW1.lean:58–143`). Here are
all the shared definitions, unfolded:

- For x∈R^K, O_x={u∈R^K : u_k≤x_k for every k}. Thresholds may differ by
  coordinate.
- For a measure ν on R×R^K, C_ν(y,x)=ν{(v,u):v≤y and u∈O_x}.toReal.
  The SAP `probability` is precisely extended measure followed by `toReal`.
- A `W1JointCDF K` is a function F:R×R^K→R together with the property that
  F=C_ν for some ν which is a probability measure. It is not an arbitrary
  function carrying only the label CDF.
- For n conditional laws ν_i on R and covariates X_i∈R^K, the fitted measure
  is M=(n:R≥0∞)^(-1) • Σ_i (ν_i × δ_(X_i)).
- For a Mathlib PMF p:R→R≥0∞ with sum 1, H_p(y)=Σ'_(v∈R)
  (if v≤y then p(v).toReal else 0). Its nonzero support is countable.
- A density predicate on (ν,f) means: f is a.e. measurable for Lebesgue
  measure, f(y)≥0 for every y, f is Bochner integrable, and
  ν=Lebesgue.withDensity(y↦ENNReal.ofReal(f(y))). It does not by itself
  assert mass one; probability status comes from the law in each use.
- A supplied t is an MLE for Θ,g,Y,X if t∈Θ and, for every s∈Θ,
  Π_i g(Y_i,X_i,s)≤Π_i g(Y_i,X_i,t). There is no existence or selection
  theorem for the maximizer.
- The functional plug-in operation is defined by Plugin(T,F)=T(F) for
  T from the type of actual joint CDFs to R.
- The fitted-display predicate for X,ν,H asserts: M is a probability
  measure; there exists a single Fhat in the above CDF type with Fhat=C_M;
  for every y,x,
  Fhat(y,x)=[Σ_i (if X_i∈O_x then H_i(y) else 0)]/n; and for every such
  real functional T, Plugin(T,Fhat)=T(Fhat). The existential Fhat precedes
  the universal thresholds and functional.

Population part: for every measurable space Ω and probability measure μ on
it, every K∈N and functions Y:Ω→R, X:Ω→R^K, assume first Y is measurable
and then X is measurable. There exists one actual joint CDF F, namely the
CDF of the pushforward law μ.map(ω↦(Y(ω),X(ω))), satisfying all of:

1. For every y,x, F(y,x)=μ{ω:Y(ω)≤y and X(ω)∈O_x}.toReal.
2. For every y,x, ω↦1_(O_x)(X(ω)) times
   (condDistrib(Y|X)(X(ω))(Iic y)).toReal is integrable and its μ-integral
   is F(y,x). The indicator product is implemented by an if/else-zero.
3. For every p:R^K→PMF R, assume for μ.map(X)-almost every u that the
   conditional law at u equals (p(u)).toMeasure. Then for every y,x the
   integrand 1_(O_x)(X(ω))H_(p(X(ω)))(y) is integrable and has integral
   F(y,x).
4. For every f:R×R^K→R, assume for μ.map(X)-almost every u the density
   predicate above for the conditional law at u and v↦f(v,u). Then for
   every y,x the integrand 1_(O_x)(X(ω))∫_(v≤y) f(v,X(ω))dv is
   integrable and has integral F(y,x).

The same F precedes all PMF/density choices. Conditional laws are Mathlib
regular conditional distributions, Markov kernels obtained by disintegrating
the pushforward of (X,Y); the identities use them as a.e. versions. There
are no global measurability hypotheses on the supplied p or f; their tail
expressions agree a.e. with the measurable conditional probabilities.

Fitted PMF part: for every natural n,K,τ, assume n>0; for every parameter
set Θ⊆R^τ, family p:R^K×R^τ→PMF R, sample Y,X and vector t∈R^τ, if t is
an MLE for g(y,x,s)=p(x,s)(y).toReal, the fitted-display predicate holds
with ν_i=p(X_i,t).toMeasure and H_i=H_(p(X_i,t)).

Fitted PDF part: for every n,K,τ with n>0, every Θ⊆R^τ, real family
g:R×R^K×R^τ→R and measure family ν:R^K×R^τ→Measure R, assume for every
x,t with t∈Θ that ν(x,t) is a probability measure and the density
predicate holds for (ν(x,t),y↦g(y,x,t)). Then for every sample Y,X and
t which is an MLE, the fitted-display predicate holds with
ν_i=ν(X_i,t) and H_i(y)=∫_(v≤y)g(v,X_i,t)dv.

The docstring describes these population identities, the common attained ML
parameter, normalized fitted displays, and the definition of the plug-in
functional. The finite mixture conclusions themselves need no optimality;
the hypothesis identifies the particular parameter used as an ML parameter.

Junk and boundary conventions: `ENNReal.toReal ∞=0`, but every probability
law or kernel evaluation in these conclusions is finite; PMF values are
at most 1. `ENNReal.ofReal` would truncate negative inputs to zero, but all
density predicates explicitly require nonnegativity. The real infinite
sum defaults to zero when not summable, but a normalized PMF has summable
nonnegative real tails, so that convention is inactive. The ENNReal inverse
at n=0 would be infinity, and the empty-measure mixture would be zero;
n>0 excludes that case and all sample-mean divisions by zero. Bochner
integrals default to zero without integrability. This is excluded by
the density predicates on the relevant a.e. covariates, by finite
probability laws, and by the explicit integrability conclusions for
population integrands. Badly chosen density values on exceptional
covariates do not affect the integrals. Conditional-law values off the
support of the covariate law are versions, not pointwise identified
conditional probabilities. Measurable maps in the population part
exclude the junk pushforward of a nonmeasurable map. K=0 gives a singleton
covariate space and a vacuously full orthant, correctly giving a marginal
CDF. τ=0 gives a singleton parameter space. Empty Θ has no MLE witness,
but nonempty choices are also included. The functionals are arbitrary
functions on the genuine CDF type, with no continuity hypothesis.
There is no logarithm, square root, rpow, set extremum or limit operation.

The generated population proofs supply (1) the standard Borel structure
of R, (2) finiteness of a probability measure and (3) the outer-measure
structure of the covariate measure type. The generated fitted-law proof
is the ENNReal scalar-tower instance. These add no substantive hypotheses.

## SAP.P001e.T80

The statement is a population sharp-bounds assertion conjoined with a fixed
six-observation calculation (`Defs/WholeW1.lean:145–189`).

For every measurable space Ω and probability measure μ, real-valued functions
Y,R on Ω, assume Y and then R are measurable. For every real a,b, assume in
order a≤b, Y∈[a,b] a.e., R∈{0,1} a.e., p0=μ{R=0}.toReal>0 and
p1=μ{R=1}.toReal>0. Define

- Ys(ω)=Y(ω)R(ω)-99(1-R(ω));
- m=[∫_{R=1}Ys dμ]/p1;
- L=m p1+a p0 and U=m p1+b p0;
- C_c(ω)=Ys(ω)R(ω)+c(1-R(ω)).

The conclusion states that Y,Ys,C_a,C_b are all integrable, ∫C_a=L,
∫C_b=U, and L≤∫Y≤U. Finally, for every c∈[L,U], there exists a function
Y':Ω→R (chosen after c) such that Y' is measurable, Y'∈[a,b] a.e., Y' is
integrable, ∫Y'=c, its recorded outcome Y'R-99(1-R) equals Ys a.e., and
the pushforward laws of (Y'R-99(1-R),R) and (Ys,R) are exactly equal.
The response function and the underlying probability space are unchanged
in this existential construction. No independence or MAR hypothesis appears.

For the finite example, `boundsRecorded` is [1,-99,1,0,1,-99] and
`boundsResponse` is [1,0,1,1,1,0] (zero-based indexing). `recordedOutcome`
is the expression y r-99(1-r), and `completeMissing` is ys r+c(1-r).
The theorem asserts both full vector equalities C_0=[1,0,1,0,1,0] and
C_1=[1,1,1,0,1,1], their means 1/2 and 5/6 (the `BoundsExample`
conjunct), and additionally repeats that the C_0 mean is 1/2 and is not
5/6. These are fixed real sums divided by 6.

The docstring claims sharp bounds including respondent-mean endpoint
formulas, all intermediate compatible means and the finite correction.

Junk and boundary conventions: m would be zero by real division convention
if p1=0; that case is explicitly excluded. The probability measure excludes
infinite measure values, so `toReal ∞=0` is inactive. Bochner integrals
default to zero outside integrability, but measurability and a.e. boundedness
under a probability measure ensure integrability, which is also concluded
explicitly. Off the null set on which R is binary, the algebraic recording
and completion formulas need not represent missingness, but every asserted
law or integral is insensitive to that null set. The -99 value is an
explicit missing-data code; it need not be outside [a,b] because R remains
observed and records which values are missing. The finite example uses
binary responses exactly and nonzero denominator 6. a=b is allowed; its
interval of attainable means then collapses correctly to a point, with
no interpolation division in the stated definitions. No log, sqrt, rpow,
truncated subtraction, set extrema, limits or partial selections occur.
An empty probability space cannot satisfy the probability-measure instance.
Both positive response probabilities are additional explicit hypotheses
to be checked against the later claim.

The generated auxiliary proofs for `BoundsExample` and `W1BoundsExample`
only certify the numerals 6,2,5; those for `boundsRecorded` and
`recordedOutcome` certify 99; the referenced normal-density proof certifies
2. They do not encode any bounds assertion.

## SAP.P001e.T81

This is a closed conjunction with no assumptions or free data
(`Defs/Part3.lean:55–85`). Define the score vector
s=[33/100,14/100,73/100,35/100,78/100,70/100] and candidate set
A={0,2,3,4}⊆Fin 6. Define N(i,j,A) to mean j∈A and, for every k∈A,
k≠j implies |s_j-s_i|<|s_k-s_i|. The statement unfolds to all of:

1. The four distances from score 14/100 to respondent scores 33/100,
   35/100,73/100,78/100 are respectively 19/100,21/100,59/100,64/100.
   The distances from 70/100 to scores 33/100,73/100,35/100,78/100
   are respectively 37/100,3/100,35/100,8/100.
2. N(1,0,A) and N(5,2,A); moreover, for every k∈A with k≠0,
   |s_3-s_1|≤|s_k-s_1|, and
   |s_3-s_1|-|s_0-s_1|=2/100. Thus donor 3 is second nearest for
   missing unit 1, and its distance exceeds the nearest distance by 2/100.
3. Define the donor map j=[0,0,2,3,4,2], data vector
   z=[2,0,3,10,12,0], and completed vector h_i=z_(j_i).
   Then h=[2,2,3,10,12,3] and (Σ_i h_i)/6=16/3.

The docstring describes corrected distances, the two selected donors,
the second donor and its gap, and the completed mean. All comparisons
and all arithmetic are in R. A nearest-neighbor choice is verified for
the explicit donor map rather than defined by an opaque selection.

Junk and boundary conventions: all indices are valid elements of Fin 6;
the set A is nonempty; every denominator is one of 3,6,100 and nonzero.
Vector notation is a total finite function, so no out-of-range lookup or
default value occurs. The zero entries in z at nonrespondents are explicit
unused placeholders: the donor map takes only the values 0,2,3,4. These
zeros therefore cannot change the completed vector or mean. Strict
nearest comparisons exclude ties in this instance. No truncated natural
subtraction, casts of negative integers, measure, integral, infinity,
log, sqrt, rpow, infinite sum, extremum, limit or partial function appears.

The generated proofs for `DonorDistances` certify numerals 19,21,59,64,
37,3,8; those for `exampleScores` certify 33,100,14,73,35,78,70;
`hotDeckData` certifies 10,12; `T81Statement` certifies 16;
`respondents` supplies `NeZero 6`. The two referenced `BoundsExample`
proofs certify 6 and 2. All these declarations were printed and read;
none adds a hypothesis or hides a substantive claim.
