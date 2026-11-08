# Blind reading

This file records step 1, before opening `claims.json` or `record.json`.
All five theorem docstrings and all entries of their elaborated closures in
`closure.json` were read. Generated proof dependencies were also expanded with
`#print` in `scratch/Inspect.lean`; they supply only scalar-tower, norm,
additive-subgroup, exponent, and composition-measurability proofs.

## SAP.P001g.T115

The statement is the conjunction of two universally quantified assertions.

First choose any measurable space Ω, a probability measure μ on Ω, and
measurable real functions Y₀, Y₁, D. Assume Y₀ and Y₁ are Bochner integrable,
D belongs to {0,1} μ-almost everywhere, and both events D=0 and D=1 have
strictly positive probability. Put Y=Y₁D+Y₀(1−D) and τ=Y₁−Y₀. For any real
function Z define A_d(Z)=(∫_{D=d} Z dμ)/(μ{D=d}). Here and below finite
measure values are converted from extended nonnegative reals to reals.
The conclusions, in order, are:

1. If the random pair (Y₀,Y₁) is independent of D in Mathlib's `IndepFun`
   sense, then ∫τ dμ=A₁(Y)−A₀(Y).
2. A₁(Y)−A₀(Y)=A₁(Y₁)−A₀(Y₀).
3. A₁(Y₁)−A₀(Y₀)=A₁(τ+Y₀)−A₀(Y₀).
4. A₁(τ+Y₀)−A₀(Y₀)=A₁(τ)+A₁(Y₀)−A₀(Y₀).

Independence is an antecedent of conclusion 1 only; the other three identities
are asserted for every assignment satisfying the preceding conditions.

Second, independently of those population objects, choose a natural n>0,
real arrays y,d indexed by `Fin n`, assume each dᵢ is 0 or 1, and assume
Σdᵢ>0 and Σ(1−dᵢ)>0. Define the measure on ℝ×ℝ
Q=n⁻¹Σᵢδ_(yᵢ,dᵢ), where the reciprocal and scaling use ℝ≥0∞. Then Q is a
probability measure,

    (∫_{v=1} u dQ)/Q{v=1} = (Σyᵢdᵢ)/(Σdᵢ),
    (∫_{v=0} u dQ)/Q{v=0} = (Σyᵢ(1−dᵢ))/(Σ(1−dᵢ)),

and the difference of the two conditional-mean functionals is the difference
of these two fractions. This last difference is precisely the definition
`wholeATEFunctional Q`. The finite arrays need not be random or iid.

Unfolded SAP dependencies: `mean` is the Bochner integral; `prob μ A` is
`(μ A).toReal`; `observedOutcome y₀ y₁ d=y₁*d+y₀*(1−d)`;
`conditionalMeanAt μ X Z x=(∫_{X=x}Z dμ)/(μ{X=x}).toReal`;
`wholeEmpiricalPairs` and `wholeATEFunctional` are exactly the expressions
above. The generated empirical-law proof is `IsScalarTower.right`.

Junk conventions: real division by zero returns zero, so the general
conditional-mean definition assigns zero on null conditioning events; both
uses here have positive denominators. The empirical ENNReal reciprocal is
∞ at n=0, but n>0 excludes this. Natural-number casts are exact; there is
no natural subtraction. An empty `Fin n` is excluded, and the positive arm
counts actually require at least two observations. Probability measures are
finite, so `toReal ∞=0` never occurs. Bochner integrals return zero on
nonintegrable functions, but population integrability follows from the
stated assumptions and almost-everywhere binary D; finite empirical
integrals are integrable. No logarithm, square root, real power, supremum,
infimum, limit superior, or partial-function default occurs. A probability
space cannot have an empty underlying type.

## SAP.P001g.T116

This is `DiscreteATEStatement ∧ GeneralIgnorabilityStatement`. The latter is
itself a conjunction of two separately quantified assertions; its second
domain does not assume potential-outcome moments.

Here is the complete common notation, unfolded. On a measurable probability
space (Ω,μ), let X:Ω→E be measurable and let Y₀,Y₁,D:Ω→ℝ be measurable.
In each domain D is binary at every ω. Write Y=Y₁D+Y₀(1−D).
`IsCEF μ X Z m` means all four of:

* m:E→ℝ is measurable;
* Z is Bochner integrable under μ;
* m∘X is Bochner integrable under μ;
* for every measurable A⊆E, ∫_{X⁻¹A}Z dμ=∫_{X⁻¹A}m(X) dμ.

This definition can also be used with μ restricted to an assignment arm.
`CI μ X hX U V` means: for every measurable A in the value space of U and
B in the value space of V,

    Eμ[1_{U∈A,V∈B} | σ(X)]
      = Eμ[1_{U∈A} | σ(X)] Eμ[1_{V∈B} | σ(X)]  μ-a.e.,

where σ(X) is `MeasurableSpace.comap X` and each conditional expectation
is Mathlib's real Bochner conditional expectation. The null exceptional set
can depend on A,B. The supplied hX is the proof of measurability of X.

The discrete domain first chooses Ω,E with E countable and measurable
singletons, then μ,X,Y₀,Y₁,D and their measurability proofs. It assumes
Y₀,Y₁ integrable; chooses p:E→ℝ with `IsCEF μ X D p`; chooses ε>0 with
ε<p(Xω)<1−ε for every ω; assumes the pair (Y₀,Y₁) and D conditionally
independent given X; then chooses m₀,m₁ that are CEFs of Y given X for
μ restricted respectively to {D=0},{D=1}. It additionally assumes both
m₀∘X and m₁∘X integrable under the full μ. It concludes

    ∫(Y₁−Y₀)dμ
      = Σ'_{x:E} m₁(x) (μ{X=x}).toReal
        − Σ'_{x:E} m₀(x) (μ{X=x}).toReal.

The first general domain independently chooses arbitrary measurable Ω,E,
then exactly the same μ,X,Y₀,Y₁,D,p,ε,m₀,m₁ and hypotheses just listed,
without countability or measurable-singleton assumptions. It concludes both
that m₁−m₀ is a CEF of Y₁−Y₀ given X under μ and that

    ∫(Y₁−Y₀)dμ=∫(m₁(X)−m₀(X))dμ.

The second general domain independently chooses arbitrary measurable Ω,E,
μ,X,Y₀,Y₁,D,p and ε>0. It assumes measurability, pointwise binary D,
`IsCEF μ X D p`, pointwise ε<p(X)<1−ε, and conditional independence of
(Y₀,Y₁) and D given X. It does not assume integrability of Y₀ or Y₁ and
does not introduce m₀ or m₁. Put S=p∘X. It concludes all four of:

1. D and X are conditionally independent given S;
2. (Y₀,Y₁) and D are conditionally independent given S;
3. `IsCEF μ S D id` (in particular S is its own propensity score);
4. there exists δ>0 such that δ<S<1−δ μ-almost everywhere.

The two general domains have independent universe parameters; they are
separate assertions, not nested conditions on one set of objects.

Junk conventions: `prob` uses `toReal` only on finite measures. `mean`
and restricted integrals are guarded by the integrability hypotheses.
Mathlib's unordered `tsum` is zero on a nonsummable family, but countability,
singleton measurability and full-law integrability of m∘X make the displayed
families absolutely summable. Conditional expectation defaults to zero
when its sigma algebra is not below the ambient one, when its trimmed
measure is not sigma finite, or its integrand is not integrable. Here X is
measurable, μ is finite, and all indicator functions involved are measurable
and bounded; the defaults are excluded. The two declared decidability
instances are classical proposition decidability, not numerical defaults.
The generated general-ignorability proof is exactly measurability of p∘X.
No division, natural subtraction, log, square root, real power, extremum or
limsup is used in this statement. E cannot be empty for instantiated data,
since X has a probability-space domain.

## SAP.P001g.T117

Choose a measurable probability space (Ω,μ), a natural K, measurable
X:Ω→(Fin K→ℝ), and measurable real Y₀,Y₁,D with integrable Y₀,Y₁. Assume
D is binary μ-almost everywhere, and P(D=0)>0 and P(D=1)>0. Next choose a
measurable CEF p of D given X (`IsCEF`, fully unfolded in T116 above),
assume there exists ε>0 such that ε<p(X)<1−ε μ-almost everywhere, and
assume (Y₀,Y₁) and D conditionally independent given X (the indicator
conditional-expectation identity described in T116). Put Y=Y₁D+Y₀(1−D).

Define the real score I(y,d,p)=yd/p−y(1−d)/(1−p).
The first two conclusions say I(Y,D,p(X)) is Bochner integrable and

    ∫(Y₁−Y₀)dμ=∫I(Y,D,p(X))dμ.

For every subsequent triple of real-valued functions m₀,m₁,q on ℝ^K,
assume all three are measurable and the COMPLETE real score

    A(y,d,m₀,m₁,q)
      = m₁+d(y−m₁)/q−m₀−(1−d)(y−m₀)/(1−q)

is integrable after composition with Y,D,X. Assume either:

* m₀ and m₁ are CEFs of Y given X under the respective arm restrictions
  of μ, and some η>0 satisfies η<q(X)<1−η μ-almost everywhere; or
* q∘X=p∘X μ-almost everywhere.

Then ∫(Y₁−Y₀)dμ=∫A(Y,D,m₀(X),m₁(X),q(X))dμ. In the second alternative
there is no assumption that m₀∘X or m₁∘X separately is integrable. In the
first alternative their arm-restricted integrability is part of `IsCEF`.
All SAP integrals, probabilities, observed outcomes and scores have been
unfolded above.

Junk conventions: both score definitions use real division and thus assign
zero to a term with denominator zero. The relevant p and q denominators
are bounded away from zero almost everywhere in both alternatives, so any
zero denominators on exceptional null sets do not change an integral.
Every expectation has an integrability guard or is asserted integrable as
a conclusion. `prob` never converts ∞. The conditional-expectation defaults
are excluded for the same reasons as T116. K=0 is allowed and gives the
one-point empty-coordinate vector space, an ordinary no-covariate case;
it does not make Ω empty or a hypothesis impossible. No other listed junk
operation occurs.

## SAP.P001g.T118

This is a conjunction of two negated universal assertions, with a shared
but independent sample-space universe parameter in the first assertion.

The first assertion being negated quantifies successively over every
measurable probability space (Ω,μ), every IID sequence Xᵢ:Ω→ℝ, and EVERY
functional T:(ℝ→ℝ)→ℝ. `IID` means each Xᵢ is measurable, the family is
jointly independent (`iIndepFun`), and each Xᵢ has Mathlib `IdentDistrib`
with X₀ under μ. Put F(x)=(μ{X₀≤x}).toReal. If `CDFHadamard T F`, the
assertion requires the existence of a real φ>0 such that

    √n [T(F_{n,ω})−T(F)] →d N(0,φ²),

where Q_{n,ω}=n⁻¹Σ_{i<n}δ_{Xᵢω} and F_{n,ω}(x)=(Q_{n,ω}(-∞,x]).toReal.
Distributional convergence here means convergence of these real CDFs at
every continuity point of the Gaussian CDF, with probabilities again
computed as `toReal` of measures of sublevel sets.

Here `CDFHadamard T F` unfolds as existence of an algebraically real-linear
L:(ℝ→ℝ)→ℝ (on all functions) with a constant C≥0 such that
|Lh|≤C supₓ|h(x)| for every bounded h. For every bounded h, every sequence
tₙ>0 tending to 0, and every sequence of bounded functions hₙ converging
uniformly to h, provided each F+tₙhₙ is a real CDF, it requires

    [T(F+tₙhₙ)−T(F)]/tₙ → Lh.

`IsRealCDF` means values in [0,1], monotonicity, right continuity expressed
using `nhdsWithin x (Ici x)`, and limits 0 at −∞ and 1 at +∞.
`uniformNorm h` is literally the real supremum of the range of |h|.
The assertion does not require the derivative or asymptotic variance to
be nonzero in its hypotheses, and it supplies no measurability condition
on T or T of the empirical CDF.

The second assertion being negated quantifies over every probability
measure ν on ℝ for which `MemLp id 2 ν` holds. It requires some continuous
real-linear map L from `lp (fun _:ℝ => ℝ) ∞` to ℝ satisfying the following.
This lp space consists of bounded real functions on ℝ with the supremum
norm. Put F=the bounded-function embedding of the CDF of ν. Let D be the
set of bounded functions G that are CDFs of some probability measure with
square-integrable identity. For G∈D define T(G) as the integral of the
identity under a classically chosen such measure; outside D set T(G)=0.
For EVERY h in the entire bounded-function space, positive tₙ→0, and
hₙ→h in that space with F+tₙhₙ∈D for all n, require

    [T(F+tₙhₙ)−T(F)]/tₙ → Lh.

That is `HadamardAt D Set.univ cdfMeanFunctional F L`. The chosen measure
is not a free parameter of the theorem; its CDF specifies it uniquely.
The assertion concludes only the negations of the two universals, not
an explicit named witness.

Junk conventions: real `sSup` for an empty or unbounded-above set has a
default value (zero for reals). The range of |h| is nonempty since its index
is ℝ, and every norm used in `CDFHadamard` is on bounded functions or
differences of bounded functions. `kolmogorovEmbed f` returns 0 if f is not
in lp∞; the embedded functions here are CDFs, bounded between 0 and 1.
`cdfMeanFunctional` returns 0 outside D, but its base point and every
perturbed point used by `HadamardAt` are in D. Its chosen measures have
finite second moment, hence integrable identity. Empirical measures at
n=0 use ∞ times the zero measure, giving the zero measure and zero CDF;
finite initial terms do not affect the asserted atTop limit. At n>0 the
empirical measures are probability measures. `Real.sqrt (n:ℝ)` has a
nonnegative argument; its negative-argument convention is irrelevant.
All tₙ divisions have positive denominators. All probability measures
are finite, so `toReal ∞` is absent. The predicate `CD` itself permits
nonmeasurable sample statistics and then measures their sublevel sets by
outer values; the first negated universal lacks a separate guard. Whether
a refuting example respects measurability must therefore be checked rather
than inferred from this definition. No logarithms, truncated subtraction,
unbounded limsup/liminf, empty-type sum, or other partial-function default
occurs. All generated proof declarations are structural proofs only.

## SAP.P001g.T119

This negates the following universal assertion. Quantifiers and conditions
are in this order:

1. Any universe-zero type Ω with a measurable space, probability measure μ,
   and sequences X,Y:ℕ→Ω→ℝ such that (Xᵢ,Yᵢ) are IID (individual
   measurability, joint independence, identical distributions).
2. Y₀ is integrable AND `MemLp (Y 0) 2 μ` (finite second moment).
3. Any reals a<b and density f:ℝ→ℝ for μ.map X₀. The density condition is
   precisely: f is volume-a.e. measurable, f≥0 everywhere, f is Bochner
   integrable under volume, and μ.map X₀ equals volume with density
   `ENNReal.ofReal ∘ f`. Additionally, f(x)>0 iff x∈[a,b], for every x,
   including the endpoints.
4. Any m:ℝ→ℝ with `ContDiff ℝ ⊤ m` and `IsCEF μ X₀ Y₀ m`. The latter
   is the measurable, integrable, set-integral characterization fully
   written under T116. In THIS Mathlib version the differentiability
   order belongs to `WithTop ℕ∞`; literal ⊤ is the analytic order ω,
   stronger than the smooth order ∞. Thus the literal condition is
   global real analyticity, not merely all finite orders of differentiability.
5. Any J:ℕ→ℕ with Jₙ→∞ and (Jₙ:ℝ)/(n:ℝ)→0.
6. Any selected fits `fit:ℕ→Ω→Polynomial ℝ` such that for EVERY n,ω the
   natural degree of fitₙω is ≤Jₙ and its sample sum of squared residuals
   on i<n is ≤ that of EVERY real polynomial p of natural degree ≤Jₙ.

The asserted conclusion being negated is convergence in probability to 0
of the integrated prediction error

    Rₙ(ω)=∫ [(fitₙω)(x)−m(x)]² d(μ.map X₀)(x).

In full, for every real ε>0, the real probabilities
(μ{ω:ε≤dist(Rₙ(ω),0)}).toReal tend to zero. `dist` here is the ordinary
absolute difference on ℝ. Fits need not be measurable or even be functions
only of the first n observations in the literal predicate. Consequently
risk events are not expressly assumed measurable. The definition
`polynomialSieveLeastSquares` specifies the squared finite residual sums
and a degree bound; it is not itself an argmin operator. The theorem does
not supply an explicit witness in its statement.

Junk conventions: the degree of the zero polynomial is `natDegree 0=0`,
so a degree bound zero includes both zero and every constant polynomial.
This is the intended finite-dimensional sieve, not a negative-degree
default. At n=0 both residual sums are empty and zero; any degree-admissible
fit minimizes them. The rate ratio J₀/0 is real zero, which does not affect
an atTop limit. There is no subtraction of naturals. Risk uses a totalized
Bochner integral; for each fixed polynomial and sample point, its square
error against analytic m is bounded on [a,b], and the covariate law is
supported there, so its integral is finite and genuine. `HasPDF` separately
guards the density integral. Outcome moments are explicitly guarded.
`CP` measures potentially nonmeasurable risk events by the measure's outer
values; this can change the intended statistical meaning unless a witness
has measurable fits/risk events. Since μ is finite there is no `toReal ∞`.
The positive support condition allows jumps in f at the endpoints; density
continuity is not assumed. There is no square-root, log, real-power,
supremum/infimum or limsup convention. The generated proof dependency is
just the arithmetic evidence that exponent 2 is at least two.
