# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. Sources read: the five Challenge declarations and every
entry of their `closure.json` closures. All eleven distinct line-zero auxiliary
declarations were inspected with `#print` in `scratch/ClosureChecks.lean`.
They prove only `Nat.AtLeastTwo` facts for the numerals 2, 3, 4, 5, 6, or 99;
they impose no statistical assumptions. No claim or record is used below.

## Common notation, fully unfolded

For a measure μ, write Pμ(A) = `(μ A).toReal` and Eμ(f) for the real Bochner
integral `∫ ω, f ω ∂μ`. A restricted integral is a Bochner integral against
`μ.restrict A`.

The SAP assertion that m is a conditional mean of f given Z under ν means exactly:
(i) m is measurable on the codomain of Z; (ii) f is ν-integrable;
(iii) m ∘ Z is ν-integrable; and (iv) for every measurable codomain set A,
the integrals of f and m ∘ Z over Z⁻¹(A) agree. This defines a version by the
usual integral characterization, with equality only almost everywhere relevant.

The SAP conditional independence assertion for U and V given a measurable Z
means: for all measurable sets A and B in their respective codomains,
`Eν[1_{U∈A,V∈B} | σ(Z)] = Eν[1_{U∈A} | σ(Z)] Eν[1_{V∈B} | σ(Z)]`
ν-almost everywhere. Here σ(Z) is `MeasurableSpace.comap Z` and each expectation
is Mathlib's conditional Bochner expectation. The exceptional null set may
depend on A and B.

For a cell value z, the SAP cell mean is
`Cν(Z,f,z) = (∫_{Z=z} f dν)/Pν(Z=z)`. No positive-mass requirement is built
into this definition.

## SAP.P001e.T87

Location: `SAP/P001e/Challenge/Part1.lean:84–92`;
definition `SAP/P001e/Defs/WholeW2.lean:109–123`.

Quantifiers, in order: for every measurable space Ω, natural number K,
probability measure μ on Ω, measurable covariate vector X : Ω → (Fin K → ℝ),
measurable real Y and R on Ω, an integrability proof for Y under μ, and an
almost-everywhere assertion R ∈ {0,1}, the following conjunction holds.

First, there exists a measurable function m : (Fin K → ℝ) → ℝ that is a
conditional mean of Y given X under ν₁ = μ restricted to {R=1}, in the four
integral-characterization clauses above. Second, for every such m (not merely
the one just obtained), all of the following hold:

* m is also a conditional mean under ν₁ of the recorded outcome
  `Y* = Y R - 99(1-R)` given X.
* The constant function −99 is a conditional mean under
  ν₀ = μ restricted to {R=0} of Y* given X.
* Under μ, a conditional mean of Y* given (R,X) is the measurable function
  `(r,x) ↦ r m(x) - 99(1-r)`. Each claim includes the two integrability
  obligations and all measurable-set integral identities described above.
* For every measurable real function p on the covariate space which is a
  conditional mean of R given X under μ, if there exists ε>0 with
  p(X)>ε μ-almost everywhere, and Y and R are conditionally independent given
  X in the indicator-factorization sense above, then m ∘ X is μ-integrable and
  m is a conditional mean of Y given X under μ.

There is no assumption that either response status has positive probability.
There is no given respondent regression, exact linear model, squared-covariate
model, fit criterion, coefficient, approximation error, or numerical conclusion
in the proposition. The docstring says the two working specifications target
this respondent function and expressly declines an exact approximation or fit
assertion. The covariate dimension may be zero, making X constant-valued.

Junk-value audit: there is no division or cell-mean expression here. All asserted
conditional means include integrability. Y* agrees almost everywhere with an
integrable piecewise choice of Y and −99, even if R is not binary on a null set.
The integrability of m ∘ X on the respondent restriction is a premise for every
version; population integrability is a conclusion in the MAR clause rather than
an extra premise. A zero-mass response stratum makes the conditional-mean
identities on that stratum void, which is normal version behavior and does not
make the full theorem empty. The MAR lower bound prevents complete nonresponse
in its own clause. Conditional expectations in conditional independence have
bounded measurable indicator inputs under a probability measure, and σ(X) is
a sub-σ-algebra with a finite trimmed measure, so their default-zero branches
do not arise. No logarithms, roots, powers, extrema, infinite sums, truncated
subtractions, partial functions, or infinite-to-real casts occur in this closure
apart from ordinary numeral elaboration. The −99 is an explicit recording
sentinel, not a default value introduced by Lean.

## SAP.P001e.T88

Location: `SAP/P001e/Challenge/Part1.lean:94–96`;
definition `SAP/P001e/Defs/Part4.lean:91–117`.

For every measurable space Ω, probability measure μ, three sequences of
real random variables Y₀ᵢ,Y₁ᵢ,Dᵢ (i∈ℕ), proofs that every coordinate is
measurable, and real a,b with a≤b, assume:

1. For each i, almost surely Y₀ᵢ,Y₁ᵢ∈[a,b] and Dᵢ∈{0,1}. Each i may have
   its own exceptional null set.
2. p=Pμ(D₀=1) lies strictly between 0 and 1.
3. The observable pairs (Yᵢ,Dᵢ), where
   `Yᵢ = Y₁ᵢ Dᵢ + Y₀ᵢ(1-Dᵢ)`, are IID. In full Mathlib terms the pair maps
   are measurable; their generated σ-algebras are mutually independent (finite
   intersections have probabilities equal to products); and each pair has the
   same pushforward law as pair zero, including a.e. measurability in the
   `IdentDistrib` witnesses. Independence of the latent triples is not assumed.

Define
`Lᵢ = Yᵢ Dᵢ + a(1-Dᵢ) - Yᵢ(1-Dᵢ) - b Dᵢ`,
`Uᵢ = Yᵢ Dᵢ + b(1-Dᵢ) - Yᵢ(1-Dᵢ) - a Dᵢ`, and

`ℓ = Cμ(D₀,Y₀obs,1) p + a(1-p) - [Cμ(D₀,Y₀obs,0)(1-p) + bp]`,

`u = Cμ(D₀,Y₀obs,1) p + b(1-p) - [Cμ(D₀,Y₀obs,0)(1-p) + ap]`,
where Y₀obs denotes the observable Y at index zero, not potential Y₀.
The conclusion is the conjunction:

* Eμ(L₀)=ℓ, Eμ(U₀)=u, and u−ℓ=b−a.
* Eμ(Y₁₀−Y₀₀)∈[ℓ,u].
* For every real t∈[ℓ,u] there exist measurable A₀,A₁ : Ω→ℝ, taking values
  in [a,b] almost surely, with A₁D₀+A₀(1−D₀)=Y₀obs almost surely and
  Eμ(A₁−A₀)=t. These alternatives live on the original Ω and preserve its
  observable treatment and outcome almost surely.
* For every natural n>0, Eμ(n⁻¹∑_{i<n}Lᵢ)=ℓ and
  Eμ(n⁻¹∑_{i<n}Uᵢ)=u.
* Both those sequences of sample averages converge in probability to their
  respective constants: for every real ε>0 the real probability of
  `{ω : ε ≤ dist(averageₙ(ω),constant)}` tends to zero as n→∞.

The sharpness witnesses are existential after t is chosen. No independence of
potential outcomes and treatment is required. No unbiasedness assertion for
n=0 is made. a=b and ℓ=u are allowed.

Junk-value audit: `sampleAverage` is zero at n=0 (empty sum divided by zero).
The unbiasedness conclusion excludes that n; convergence at infinity is
unaffected by it. Both cell probabilities are positive by binary D and 0<p<1,
so cell division is legitimate. μ is a probability measure, hence `.toReal`
never turns infinity into zero. Every relevant outcome, endpoint, witness, and
finite-sample average is a.e. bounded, measurable and integrable, so Bochner
integrals do not rely on their nonintegrable default zero. The countable sample
index is nonempty; naturals are cast into ℝ only for denominators, with n>0
where needed. No other listed domain or empty-extremum convention is used.

## SAP.P001e.T89

Location: `SAP/P001e/Challenge/Part1.lean:98–107`;
definitions `SAP/P001e/Defs/Part5.lean:15–33` and
`SAP/P001e/Defs/WholeW2.lean:241–261`.

This is a closed conjunction about six explicitly enumerated atoms indexed by
Fin 6, with each atom assigned weight 1/6. There are no hypotheses or external
parameters. In index order, define the real vectors

`y = (0,1,1,0,1,1)`, `x = (0,0,1,0,1,1)`, `d = (0,0,0,1,1,1)`,
`x₀ = (0,0,1,0,0,1)`, and `x₁ = (0,1,1,0,1,1)`.

For any predicate A, finite probability is ∑_{i: A(i)}wᵢ; finite expectation
of f is ∑ᵢ wᵢ fᵢ. Finite conditional independence of U and V given W means,
for every value (z,u,v) with P(W=z)>0,
`P(W=z,U=u,V=v) P(W=z) = P(W=z,U=u) P(W=z,V=v)`.
Finite cell means are
`M(z,t) = [∑_{i: xᵢ=z,dᵢ=t} wᵢ yᵢ]/P(x=z,d=t)`.
The adjusted contrast is ∑_{z=0,1}M(z,1)P(x=z) minus the corresponding
sum with treatment zero.

The theorem asserts all of the following:

* (y,y,x₁,x₀) is conditionally independent of d given the constant Unit-valued
  variable (thus ordinary independence), and P(d=1)=1/2.
* x₁d+x₀(1−d)=x pointwise; E(y−y)=0; (y,y) is not conditionally independent
  of d given x.
* P(y=1,x=1,d=1)=1/3, P(x=0)=P(x=1)=1/2, all four (x,d) binary cells
  have positive probability, and
  M(0,1)=0, M(1,1)=1, M(0,0)=1/2, M(1,0)=1.
  The adjusted contrast is −1/4.
* All weights are nonnegative and their sum is one. The complete vector of
  latent tuples (y,y,x₁,x₀,d) is exactly
  `((0,0,0,0,0),(1,1,1,0,0),(1,1,1,1,0),`
  ` (0,0,0,0,1),(1,1,1,0,1),(1,1,1,1,1))`.
* Pointwise yd+y(1−d)=y and y−y=0; P(x₁−x₀=1)=1/3.
* For every real y',x',d', P(y=y',x=x',d=d') equals the sum of five
  indicator terms: mass 1/6 at each of (0,0,0),(1,0,0),(1,1,0),(0,0,1),
  and mass 1/3 at (1,1,1), zero elsewhere.
* The finite set of these observable cells has cardinality five; the corrected
  masses on it sum to one; assigning 1/6 to each of its five distinct elements
  instead sums to 5/6.
* The four conditioning masses P(x=0,d=0),P(x=1,d=0),P(x=0,d=1),P(x=1,d=1)
  are respectively 1/3,1/6,1/6,1/3.
* P(y=1,x=0,d=0)/P(x=0,d=0)=1/2 and
  P(y=1,x=0,d=1)/P(x=0,d=1)=0.

Junk-value audit: these definitions would permit negative or unnormalized
weights in other uses, but these particular weights are positive and normalized,
and the theorem explicitly verifies this. The four cell denominators and the
two conditional-probability denominators are positive. All sums are over the
nonempty, concrete Fin 6 or the five distinct observable cells. Finset duplicate
removal is deliberate and explicitly counted. The fixed vectors have no partial
indexing or out-of-range access. There are no integrals, infinite sums, limiting
operations, infinity casts, or problematic nonlinear operations in the statement.
The zero effect comes from genuinely identical two potential outcomes; the
nontrivial content is their independence before and dependence after conditioning.

## SAP.P001e.T90

Location: `SAP/P001e/Challenge/Part1.lean:109–111`;
definition `SAP/P001e/Defs/Part5.lean:35–39`.

This also has no hypotheses or variable parameters. Let ν be Lebesgue measure
restricted to the closed interval [0,1], and let s : ℝ→ℝ be the function which
is one at exactly 1/2 and zero at every other real argument. The conjunction is:

1. The ν-pushforward by `t↦(0,t,0)` equals the ν-pushforward by `t↦(s(t),t,0)`.
2. s(1/2)−s(0)=1.
3. s(1/2)−s(1/4)=1.
4. As real numbers, 0≠1.

The docstring calls this a refutation of a printed claim, interpreting the
coordinates as observable outcome, dose, and constant covariate. The process
in the first model is the deterministic zero curve, and in the second the
deterministic spike curve, although neither a process-independence condition nor
a formal definition of effect is explicitly conjoined. The differing deterministic
curve contrasts provide the intended effect comparison.

Junk-value audit: ν has total mass one; both maps and the spike function are
Borel measurable and bounded. The equality arises from agreement off a singleton
of Lebesgue measure zero, not from Mathlib's map-of-nonmeasurable-function
convention. The denominators 2 and 4 are nonzero real numerals. There are no
conditional means evaluated on null cells, nonintegrable expressions, limiting
defaults, or partial functions. Any substantive regularity assumptions required
by an intended refutation must still be checked later against the actual claim.

## SAP.P001e.T91

Location: `SAP/P001e/Challenge/Part1.lean:113–131`;
definitions `SAP/P001e/Defs/Part5.lean:55–74` and
`SAP/P001e/Defs/DoseIdentification.lean:21–60`.

The statement is a conjunction of two independently universally quantified
propositions, not two conclusions about a single shared model.

Clause (a): for all measurable Ω and E with E countable and having measurable
singletons, a probability measure μ, measurable X : Ω→E and D : Ω→ℝ,
and a family Y : ℝ→Ω→ℝ, assume every section Y(t) is measurable and
integrable, the diagonal O(ω)=Y(D(ω),ω) is separately assumed measurable and
integrable, and the entire function-valued process ω↦(t↦Y(t,ω)) is conditionally
independent of D given X. Its codomain has the usual product measurable space,
so independence uses all its measurable cylinder-generated events. Then choose
any two real d,d' such that for every x with P(X=x)>0, both
P(X=x,D=d)>0 and P(X=x,D=d')>0. The conclusion is:

* At each such positive-mass x, Cμ(X,Y(d),x)=Cμ((X,D),O,(x,d)) and the
  analogous equality at d'.
* Eμ(Y(d)) equals `∑' x, if P(X=x)>0 then
  Cμ((X,D),O,(x,d)) P(X=x) else 0`; likewise at d'. This is exactly the
  SAP `standardizedDoseMean` definition.
* Eμ(Y(d')−Y(d)) is the difference of these two standardized sums.

The process includes all real indices, with no supported-dose restriction. The
covariate space is necessarily countable and the two selected doses must be
atoms in every positive covariate stratum. This is a positive-mass result even
though the dose type is ℝ.

Clause (b): independently quantify measurable spaces Ω,E,V, with the same
countability and measurable-singleton requirements on E, probability μ,
measurable X,D, a measurable curve-state map S : Ω→V, and an evaluation
function e : ℝ→V→ℝ. Require joint measurability of (t,s)↦e(t,s), injectivity
of s↦(t↦e(t,s)), conditional independence of S and D given X, integrability
of e(t,S) for every real t, and integrability of O=e(D,S). Choose real d,d'.
For each positive-mass x require continuity at d and d' of
`mₓ(t)=Cμ(X,e(t,S),x)`, and require for every ε>0 that
μ(X=x,D∈ball(d,ε))>0 and μ(X=x,D∈ball(d',ε))>0.

Its conclusions are:

* For every positive-mass x, the function t↦mₓ(t) is a measurable conditional
  mean of O given D under μ restricted to {X=x}, including integrability there.
* For every real t, Eμ(e(t,S)) is the sum over positive-mass x of
  mₓ(t)P(X=x). This sum is SAP `positiveCellAverage`; zero-mass x contribute
  zero by definition.
* Eμ(e(d',S)−e(d,S)) is the difference of those sums at d' and d.
* For every function mobs : E→ℝ→ℝ such that, in each positive-mass x cell,
  mobsₓ is also a conditional-mean version of O given D and is continuous at
  d and d', one has mobsₓ(d)=mₓ(d) and mobsₓ(d')=mₓ(d'). The same effect
  contrast equals the difference of the positive-cell averages of mobs at
  d' and d.

Neither proposition states an equality of means between two different underlying
models with a common observable law. Clause (b) does construct a conditional
mean version of the observed outcome and proves uniqueness at the two selected
supported doses among versions continuous there. No separate conditional mean
of Y(t) given (X,D) is asserted. The docstring discloses the all-real process
assumptions in (a), curve-state/joint-evaluation assumptions in (b), and the
omitted intermediate, support-wide and two-model statements. Its restriction
paragraph does not mention the countability of E.

Junk-value audit: all Bochner integrals of potential sections and the observed
diagonal are protected by explicit integrability. Singleton conditioning is
measurable. In (a), every cell mean actually used at positive X mass has a
positive (X,D) denominator by hpos. Null X cells are expressly discarded before
standardizing. In (b), mₓ is only used as a conditional mean or a uniqueness
target when P(X=x)>0. Its values on zero-mass cells are definitionally zero
and are discarded in the sum. Every `.toReal` is applied to finite measure
under a probability measure. Real `tsum` defaults to zero for a nonsummable
family, but here countability, integrable sections, and conditional-mean bounds
give absolute summability; uniqueness reduces the final mobs sums to those
same families. The arbitrary state V has no standard-Borel hypothesis; the
indicator definition of conditional independence is still meaningful, and no
conditional law of the state is explicitly used. Product-process measurability
in (a) follows from measurable coordinates. All indicator conditional
expectations are integrable under a finite measure, with legitimate σ(X).
Empty E, Ω, or V give no actual probability model with the supplied maps;
nonempty choices are available. No log, sqrt, rpow, extrema, truncated
subtraction, or partial-function defaults occur.
