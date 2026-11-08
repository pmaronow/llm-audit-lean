# Blind statement reading

This file was written before opening `claims.json` or `record.json`. The sources
of the four statements, all declarations listed in `closure.json`, and the
relevant Mathlib definitions were read. Generated declarations with source line
zero were inspected by compiling `scratch/BlindCheck.lean`.

## SAP.P001d.T73

Location: `SAP/P001d/Challenge/Part2.lean:47–55`; statement definition:
`SAP/P001d/Defs/WholeW2.lean:95–107`.

This is a closed proposition about four explicitly specified, equally weighted
atoms. There is no hypothesis and no universally quantified underlying model.
The atom type is `Fin 4`, namely the integers 0, 1, 2, 3. On these atoms set

| i | X(i) | Y(i) | e(i) = Y(i) - (2 + X(i)) |
|---|---|---|---|
| 0 | 0 | 1 | -1 |
| 1 | 0 | 3 | 1 |
| 2 | 1 | 0 | -3 |
| 3 | 1 | 6 | 3 |

All quantities here are real numbers. For any real functions U,V on `Fin 4`
and any predicate A on `Fin 4`, the SAP definitions expand to

* M(U) = sum over i of U(i)/4;
* P(A) = sum over i of (1/4 if A(i), otherwise 0);
* C(U,V) = M((U-M(U))(V-M(V)));
* H(U,V,x) = [sum over i of (U(i)/4 if V(i)=x, otherwise 0)] / P(V=x);
* V(U) = M((U-M(U))^2);
* W(U,V,x) = H(i ↦ (U(i)-H(U,V,x))^2,V,x).

These are finite Mathlib sums, classical conditionals, and ordinary real
arithmetic, rather than Bochner integrals. `heteroX`, `heteroY`,
`heteroResidual`, `finiteMean`, `finiteProb`, `finiteCov`, `finiteCond`,
`wholeFiniteVariance` and `wholeFiniteCondVariance` are exactly the functions
just displayed.

The entire statement, including the `T73Statement` conjunct, is:

1. P(X=0)=1/2 and P(X=1)=1/2.
2. H(Y,X,0)=2 and H(Y,X,1)=3.
3. M(e)=0 and C(X,e)=0.
4. P(X=0 and |e|=1)=1/2, whereas P(X=0)P(|e|=1)=1/4, and 1/2≠1/4.
5. As functions on `Fin 4`, e equals the vector (-1,1,-3,3).
6. For every real r, P(e=r) is 1/4 if r belongs to {-1,1,-3,3}, and zero otherwise.
7. For every i in `Fin 4`, H(Y,X,X(i))=2+X(i).
8. For every real x belonging to {0,1}, H(e,X,x)=0.
9. For every function g : R → R, C(g composed with X,e)=0.
10. For every real x belonging to {0,1}, W(e,X,x)=W(Y,X,x), and
    W(Y,X,x) is 1 if x=0 and 9 otherwise.
11. V(e)=5 and M(i ↦ W(Y,X,X(i)))=5.

The universally quantified r, i, x and g occur in separate conjuncts; there is
no assumption of measurability on g. Its composition with this finite X is a
function on four atoms, so every quantity is a finite sum.

The docstring calls this a refutation of an asserted independence of CEF
residuals and X, including when the CEF is linear. The formal assertion gives
the numerical failure of the event-probability product identity rather than
using Mathlib's `IndepFun` predicate. The conditional means at all realized
values, the zero mean, and the variance and covariance facts are also asserted.

Junk-value audit:

* Real division is total, with a/0=0. `finiteCond` is therefore zero at any x
  outside the support of its conditioning function. Here every evaluated
  conditional mean or variance conditions on X=0 or X=1, each of mass 1/2.
  No conclusion relies on the off-support default. In particular the linear
  conditional-mean identity is only asserted at realized X values.
* All other denominators are 2 or 4. The finite index type is nonempty. All
  subtraction is in R; there is no truncated natural subtraction.
* There are no infinite-valued probabilities, integrals, logarithms, square
  roots, real powers, extrema, limits, or partial-function defaults.
* `instDecidable_sAP` is classical propositional decidability for the if-tests.
  The line-zero closure declarations are numeric typeclass certificates:
  `T73WholeStatement._proof_1` certifies `(8+1).AtLeastTwo`, `_proof_2`
  certifies `(4+1).AtLeastTwo`; `finiteMean._proof_1` certifies
  `(3+1).AtLeastTwo`; `heteroY._proof_1` and `_proof_2` certify
  `(2+1).AtLeastTwo` and `(5+1).AtLeastTwo`; `normalDensity._proof_1`
  certifies `(1+1).AtLeastTwo`; and `wholeTrianglePDF._proof_1`, `_proof_3`,
  `_proof_4` certify `(3+1)`, `(2+1)`, `(1+1)` are at least two. These are
  numeral infrastructure, not density or triangle assumptions in this theorem.

## SAP.P001d.T74

Location: `SAP/P001d/Challenge/Part2.lean:57–71`; statement definition:
`SAP/P001d/Defs/WholeW1.lean:191–215`.

This is a conjunction of two universal theorems and the fixed finite
counterexample `T73Statement`. The latter is explicitly unfolded below.

First universal theorem, in quantifier order: choose any types Ω and E with
measurable spaces, any measure μ on Ω with μ(Ω)=1, and any measurable
X : Ω → E. Choose any measurable Y : Ω → R and any m : E → R satisfying
all of the following (`IsCEF`):

* m is measurable;
* Y is Bochner integrable for μ;
* m composed with X is Bochner integrable for μ;
* for every measurable A in E,
  integral over X^(-1)(A) of Y equals integral over X^(-1)(A) of m(X).

Define e(ω)=Y(ω)-m(X(ω)) and let G be the sigma algebra
`MeasurableSpace.comap X` of the measurable space on E. The conclusions are:

1. e is integrable.
2. The function identically zero on E is a conditional mean of e in precisely
   the event-integral sense above: it is measurable, both e and its zero
   version are integrable, and all integrals of e over X^(-1)(A) vanish.
3. The integral of e is zero.
4. The zero function on Ω equals Mathlib's conditional expectation μ[e|G]
   μ-almost everywhere.
5. For every g : E → R, if g is measurable, g(X) is integrable, and g(X)e
   is integrable, then
   integral of (g(X)-integral g(X))(e-integral e) is zero.
   This displayed integral is Mathlib's covariance.
6. If e^2 is integrable, the following existence and identities hold. For any
   real random variable Z define
   Q(Z)=μ[(Z-μ[Z|G])^2|G], a real-valued function on Ω.
   There exists v : E → R such that v is measurable, e^2 and v(X) are
   integrable, and their integrals agree on X^(-1)(A) for every measurable A;
   Q(e)=Q(Y) almost everywhere; Q(Y)=v(X) almost everywhere; Q(Y) is
   integrable; and Var(e)=integral Q(Y). Here Mathlib's Var(e) is
   `(lintegral of ‖e-integral e‖ₑ^2).toReal`.

Thus `wholeConditionalVariance` is Q, and `WholeResidualVarianceFacts` is the
existential statement in item 6. In particular v is a conclusion, not a
hypothesis that already assumes the variance identities.

Second universal theorem, in quantifier order: choose any measurable space Ω,
probability measure μ on Ω, natural number K, measurable
X : Ω → (Fin(K+1) → R), and measurable Y : Ω → R. Assume X(ω)(0)=1 for
every ω. Then choose any β : Fin(K+1) → R and real s>0. Write
l(x)=sum over k in Fin(K+1) of x(k)β(k). This expands `wholeLinearMean`.
Define κ(x)=`gaussianReal l(x) ⟨s^2,sq_nonneg s⟩`, which expands
`wholeNormalKernel`.

Assume that κ is a specified conditional probability law of Y given X in the
following exact sense (`WholeConditionalLaw`):

* κ(x) is a probability measure for every x;
* for every Borel B in R, x ↦ κ(x)(B) is measurable as an extended
  nonnegative-real-valued function;
* for all measurable A in the covariate space and Borel B in R,
  μ{X∈A and Y∈B} = integral over A of κ(x)(B) with respect to μ.map X,
  using the nonnegative Lebesgue integral.

Then:

1. For every vector x in the entire covariate space, the pushforward of κ(x)
   by y ↦ y-l(x) is `gaussianReal 0 ⟨s^2,sq_nonneg s⟩`.
2. The constant kernel with that centered normal value is a conditional law
   of e(ω)=Y(ω)-l(X(ω)), with all the probability, measurability and rectangle
   identities just stated.
3. The pushforward μ.map e is that centered normal law.
4. X and e are independent (`IndepFun`), meaning the probability of
   {X∈A and e∈B} is μ{X∈A}μ{e∈B} for all measurable A and B.

For positive s, Mathlib's `gaussianReal a ⟨s^2,...⟩` is the Borel measure
with density
`ENNReal.ofReal ((sqrt(2*pi*s^2))^(-1) * exp(-(y-a)^2/(2*s^2)))`
with respect to Lebesgue measure. Its definition at variance zero is the
Dirac measure at a, but that branch is excluded here. The pointwise law in
item 1 concerns the specified normal kernel even off the support of X, and
does not assert uniqueness of arbitrary conditional-law versions there.

Final conjunct, with no further hypotheses: on `Fin 4` take
X=(0,0,1,1), Y=(1,3,0,6), e=Y-(2+X), and use M(U)=sum U(i)/4,
P(A)=sum (if A(i) then 1/4 else 0),
H(U,V,x)=sum (if V(i)=x then U(i)/4 else 0)/P(V=x), and
C(U,V)=M((U-M(U))(V-M(V))). It asserts P(X=0)=P(X=1)=1/2,
H(Y,X,0)=2, H(Y,X,1)=3, M(e)=C(X,e)=0,
P(X=0 and |e|=1)=1/2, P(X=0)P(|e|=1)=1/4, and 1/2≠1/4.
This is exactly `T73Statement`; T74 does not include all the additional
variance facts in `T73WholeStatement`.

The docstring describes these general residual mean, covariance and variance
identities, the lack of general independence, and independence and the
specified centered normal conditional law in the classical normal model.

Junk-value audit:

* Bochner integrals default to zero for nonintegrable functions. `IsCEF`
  explicitly ensures integrability of Y and m(X); hence e is integrable.
  The covariance branch also assumes g(X) and g(X)e integrable, which makes
  the centered covariance integrand integrable. The variance branch assumes
  e^2 integrable, so no infinite variance is converted to zero by `toReal`.
* Conditional expectation defaults to zero if its sigma algebra is not a
  subalgebra, its trimmed measure is not sigma finite, or its integrand is
  nonintegrable. Measurable X ensures G is a subalgebra and a probability
  measure remains finite on trimming. In item 6 the squared centered
  integrands agree almost everywhere with e^2 (and e has zero conditional
  mean), so they are integrable even without a separate assumption Y∈L2.
  Conditional expectations and conditional variances are used up to almost
  everywhere equality, as appropriate for their choice of versions.
* `Measure.map` and restriction have degenerate branches for nonmeasurable
  inputs/sets; the measurability hypotheses here exclude those branches.
* The Gaussian kernel uses a nonnegative variance subtype certified by
  `wholeNormalKernel._proof_1 : forall s, 0≤s^2`, inspected directly.
  Positive s excludes its zero-variance branch and all bad square-root or
  division cases in the density. The rectangle integrals are nonnegative
  integrals of bounded probabilities over probability measures.
* The finite counterexample conditions only on X=0 or 1, each of mass 1/2;
  its totalized H outside the support is immaterial. All its sums are finite.
* `T66WholeStatement._proof_1` is only `forall K, NeZero(K+1)`. The other
  line-zero declarations in this closure (`finiteMean._proof_1`,
  `heteroY._proof_1`, `_proof_2`, `normalDensity._proof_1`) are the numeral
  typeclass certificates described for T73; `instDecidable_sAP` is classical
  propositional decidability. None adds a mathematical premise.
* A probability-measure instance excludes an empty measurable sample space.
  A measurable X from such a space also rules out an empty codomain in a
  realized instance. K+1 is positive. No natural subtraction, extrema,
  asymptotic limits, logarithms, or partial-function defaults are involved.

## SAP.P001d.T75

Location: `SAP/P001d/Challenge/Part2.lean:73–78`; statement definition:
`SAP/P001d/Defs/Part4.lean:104–106`.

Quantifier order: for every natural K, every pair of real vectors
x,b : Fin(K+1) → R, and every function h : R → R, assume
for every real t that 0≤h(t) and h(t)≤1. Write z=sum over k of x(k)b(k).
Then

`0*(1-h(z)) + 1*h(z) = h(z)`

and the expression on the left belongs to the real interval [0,1].
This expression is the entire definition of `binaryChoiceMean`; its two
terms are the two outcome values times their proposed probabilities.
`Set.Icc 0 1` means precisely the conjunction of the lower and upper bounds.
There is no probability space, random response, conditional kernel, or
conditional expectation in the theorem. The docstring explicitly limits the
result to this fixed-covariate calculation and says the implication from a
conditional law to a CEF of an arbitrary binary response is omitted.

Junk-value audit: the statement uses only finite sums, real products, and real
subtraction. K+1 is nonzero, though the algebraic identity itself would also
hold for an empty sum. There is no division, integral, `toReal`, logarithm,
square root, real power, extremum, limit, partial-function default, or other
domain extension. No measurability of h is assumed or needed for evaluation
of this fixed two-point mean. The two weights are nonnegative and sum to one
under the stated bounds. The closure consists exactly of `T75Statement` and
`binaryChoiceMean`, both read in full.

## SAP.P001d.T76

Location: `SAP/P001d/Challenge/Part2.lean:80–89`; statement definition:
`SAP/P001d/Defs/WholeW1.lean:66–92`.

Quantifier order: for every pair of natural numbers n,K, every real matrix
X : Fin n → Fin(K+1) → R, and every response vector Y : Fin n → R, the
following five conjuncts hold. Define d=K+1 and, for b : Fin d → R,

* fitted_i(b)=sum over k in Fin d of X(i,k)b(k) (`Matrix.mulVec`);
* R(b)=sum over i in Fin n of (Y(i)-fitted_i(b))^2 (`olsRSS`);
* f(a,s,y)=exp(-(y-a)^2/(2s^2))/(s sqrt(2pi)) (`normalDensity`);
* L(b,s)=product over i of f(fitted_i(b),s,Y(i)) (`wholeNormalLikelihood`);
* ell(b,s)=-n log(s)-(n/2)log(2pi)-R(b)/(2s^2)
  (`normalLogLikelihood`), with n cast to R;
* G(j,k)=sum over i of X(i,j)X(i,k), so G=X.transpose*X;
* a=G^(-1).mulVec(X.transpose.mulVec Y) (`olsCoef`, specialized to d).

These formulas expand every SAP-valued definition in the statement.

1. For every b and every real s>0, L(b,s) equals the product of
   `(1/(s sqrt(2pi)))*exp(-(Y(i)-fitted_i(b))^2/(2s^2))`; L(b,s)>0;
   log L(b,s) equals the sum over i of
   `log(1/(s sqrt(2pi)))-(Y(i)-fitted_i(b))^2/(2s^2)`; and
   log L(b,s)=ell(b,s).
2. For every b and every real s>0,
   [for every c : Fin d → R, L(c,s)≤L(b,s)] iff
   [for every c, ell(c,s)≤ell(b,s)]; and the latter is equivalent to
   [for every c, R(b)≤R(c)]. All comparisons are global over the entire
   coefficient space, and scale is fixed within each comparison.
3. For every b and every pair of positive real s,t,
   [for every c, L(c,s)≤L(b,s)] iff [for every c, L(c,t)≤L(b,t)].
4. If `IsUnit G.det`, then for every real s>0:
   for every b, [for every c, L(c,s)≤L(b,s)] iff b=a; and
   there exists exactly one b with [for every c, L(c,s)≤L(b,s)].
   Over R, the unit-determinant condition is exactly det(G)≠0, so a is the
   ordinary inverse-Gram least-squares coefficient.
5. If 0<n, then for every b, [for every c, R(b)≤R(c)] iff
   [for every c, R(b)/(n:R)≤R(c)/(n:R)].

No intercept-column assumption is imposed on X. No random sample, sampling
law, maximization over s, or assertion of uniqueness for singular G is
included. The likelihood is defined directly for a fixed realized data matrix
and response vector. The docstring describes exactly a fixed positive-scale
normal likelihood, equivalent coefficient optimization, scale invariance,
the invertible-Gram unique coefficient, and the positive-n mean-square
normalization.

Junk-value audit:

* Every use of f, L and ell in a substantive conclusion has s>0. Thus s,
  2s^2 and s sqrt(2pi) are strictly positive; sqrt(2pi) is the positive root.
  Real.log is totalized (log 0=0 and log of a negative number uses its absolute
  value), but every logarithm here has a positive argument. The positive
  exponential factors also prevent log L from using a zero/negative branch.
* The general definition f at s=0 is zero through real division by zero,
  and ell has totalized values at nonpositive s, but these are never used.
* Mathlib's matrix inverse is the usual inverse for invertible matrices and
  zero for singular matrices. The only asserted identifying formula for a
  is inside `IsUnit G.det`, so it does not exploit the singular default.
* n=0 is allowed in the first three conjuncts. The empty product is 1, empty
  sums R and ell are zero, and the coefficient optimization predicates all
  hold for every b. This is a consistent empty-data extension. Since d=K+1
  is nonzero, G cannot be invertible when n=0, so the unique-maximizer clause
  cannot activate there. The division by n in the last conjunct is expressly
  guarded by 0<n.
* Natural-number casts and K+1 are ordinary finite-size casts with no
  truncation or overflow. There is no natural subtraction, integral,
  infinite-to-real conversion, real power, extremum of a set, asymptotic
  limit, or partial-function default.
* `T76WholeStatement._proof_1` and `normalDensity._proof_1` are only the
  certificates `(1+1).AtLeastTwo`, inspected directly. They introduce no
  assumptions or extra mathematical definitions.
