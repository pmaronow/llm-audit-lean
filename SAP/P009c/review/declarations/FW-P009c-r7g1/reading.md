# Blind reading

This file was saved before opening `claims.json` or `record.json`. Sources read:
`closure.json`, `SAP/P009c/Challenge/Part1.lean`, `SAP/P009c/Challenge.lean`,
`SAP/P009c/Defs.lean`, and the declarations in `Defs/Part1.lean`,
`Defs/Part2.lean`, and `Defs/Part3.lean` listed in each target's closure.
`scratch/Blind.lean` also printed all five statement definitions and the two
generated proof declarations. No Solution was consulted.

## Common mathematical notation, fully expanded

For a natural number n, let U = {0,...,n-1} (Lean `Fin n`) and
A = U → {false,true} (Lean `Fin n → Bool`). All sums and products below range
over the complete indicated finite type. A law P is a real function p on A
with p(z) ≥ 0 for every z and ∑z p(z) = 1. `Law.mk` is exactly the constructor
carrying that function and those two proofs; `Law.mass` is its function.
For any real function f on A, write M_P(f) = ∑z p(z) f(z).
For a predicate B on A, P(B) = ∑z p(z) 1_B(z), where 1_B is 1 on B and 0
elsewhere. Conditional averaging means

    M_P(f | B) = (∑z p(z) (if B(z) then f(z) else 0)) / P(B).

These are ordinary real finite sums, not Bochner integrals. An experiment is
exactly a pair of a law P and arbitrary real potential-outcome tables
Y_i : A → ℝ for each i∈U; `Experiment.mk`, `.design`, and `.outcome` are its
constructor and the two projections. Outcomes are specified even at assignments
of zero probability.

Let z[i←b] be the function equal to b at i and equal to z at every other index
(Mathlib `Function.update`). Put

    Y_i(b;z) = Y_i(z[i←b]),
    Δ_i(z) = Y_i(z[i←true]) - Y_i(z[i←false]),
    t(z) = (∑i Δ_i(z)) / (n : ℝ),
    a = t(all-false),
    e_P = ∑z p(z) t(z),
    p_i(b) = ∑z p(z) 1_{z_i=b},
    s_P = (∑i [M_P(Y_i | z_i=true) - M_P(Y_i | z_i=false)]) / (n : ℝ).

These expand, respectively, SAP `potential`, `effect`, `ateAt`, `ate`, `eate`,
`marginal`, and `adse`. The expectation, probability, and conditional mean
notations above expand SAP `mean`, `prob`, and `cmean`. All scalar arithmetic,
absolute values, inequalities, maxima of two reals, and finite sums are Mathlib
operations. All occurrences of n as a denominator or a real-power base use the
ordinary natural-to-real cast.

For the interference definitions, define R(i,j) to hold when either i=j, or
there exist z,z'∈A agreeing at every index other than i such that
Y_j(z) ≠ Y_j(z'). Define I_ij = 1 if R(i,j), and 0 otherwise. Define D(i,j)
to mean that some ℓ∈U satisfies R(ℓ,i) and R(ℓ,j), and d_ij = 1 if D(i,j),
and 0 otherwise. Then put

    c_i = ∑j I_ij,
    d_i = ∑j d_ij,
    d_bar = (∑i d_i)/(n : ℝ),
    C_1 = (∑i c_i)/(n : ℝ),
    C_2 = sqrt((∑i c_i^2)/(n : ℝ)),
    C_p = ((∑i (c_i)^p)/(n : ℝ))^(1/p),
    C_infinity = sSup {c_i : i∈U}.

Here arbitrary real exponents mean Mathlib `Real.rpow`, and `sqrt` means
`Real.sqrt`. These expand SAP `Interferes`, `I`, `Dependent`, `d`, `outgoing`,
`degree`, `dAvg`, `C1`, `C2`, `Cp`, and `Cinf`. For positive n, 1≤c_i≤n,
the range of c is nonempty and finite, and its real `sSup` is its maximum.
The mandatory diagonal is present even for constant outcome functions.

For assignments, let b(false)=0 and b(true)=1 as real numbers (SAP `bit`). Set

    L_r(z,z') = (∑i |b(z_i)-b(z'_i)|^r)^(1/r),
    H_r = C_infinity                     if r=1,
          C_{r/(r-1)}                    otherwise.

These expand SAP `lrDistance` and `conjugateC`. The distance is an
unnormalized finite-dimensional real ℓ_r distance.

## SAP.P009c.T35

Source: Challenge/Part1.lean:6–9; statement Defs/Part3.lean:26–34.
The docstring promises reduction under no interference, unconditional and
conditional displayed forms, and coincidence under Bernoulli randomization.

**Quantifiers and assertion.** For every natural n, then every proof n>0,
then every experiment (P,Y) on A, the following four clauses hold jointly:

1. If for every i,z,z', z_i=z'_i implies Y_i(z)=Y_i(z') (the complete
   expansion of `NoInterference`), then for every z∈A, t(z)=a, and e_P=a.
   Here a is the all-false assignment's average difference, as defined above.
2. Always, e_P = (∑i [∑z p(z)Y_i(z[i←true]) -
   ∑z p(z)Y_i(z[i←false])])/(n : ℝ).
3. If for every i, 0<p_i(true)<1, then

       s_P = (∑i [M_P(Y_i(true;·) | z_i=true)
                   - M_P(Y_i(false;·) | z_i=false)])/(n : ℝ).

   Each conditional average in this formula and in s_P is the explicit
   quotient of finite sums in the common notation.
4. If for every i, 0<p_i(true)<1, and, for every z,

       p(z) = ∏i (if z_i then p_i(true) else 1-p_i(true)),

   then e_P=s_P. That entire conjunction is the expansion of `Bernoulli`;
   it is full independence with possibly unequal interior coordinate marginals.

The assumptions of clause 1, clause 3, and clause 4 are separate implications,
not global hypotheses on the experiment. The first clause asserts constancy
of assignment-conditional averages as well as the expected-average equality.

**Closure coverage.** `Assignment`; `Law`, `Law.mk`, `Law.mass`; `Experiment`,
`Experiment.mk`, `Experiment.design`, `Experiment.outcome`; `mean`, `prob`,
`cmean`, `marginal`, `potential`, `effect`, `ateAt`, `ate`, `eate`, `adse`,
`NoInterference`, `Bernoulli`, and `T35Statement` are all expanded here.

**Junk conventions.** Real division by zero is totalized to zero. Consequently
the bare `cmean` definition returns zero on a zero-mass event and `adse` can
incorporate that convention for experiments with endpoint marginals. However,
every asserted clause that uses `adse` or conditional averages has interior
marginals (explicitly or inside `Bernoulli`), so both conditioning events have
positive probability. All denominators n are nonzero. There is no appeal to an
empty population, empty probability sample space, nonintegrable expectation,
undefined potential outcome, truncated subtraction, logarithm, square root,
real power, `toReal`, supremum/infimum, limsup/liminf, or partial-function default.
`Function.update` is a total function. The natural-to-real cast preserves n>0.
All sums are finite and all outcomes real, so expectations always exist.

## SAP.P009c.T36

Source: Challenge/Part1.lean:11–14; statement Defs/Part3.lean:36–39.
The docstring calls this the complete interference-count inequality chain.

**Quantifiers and assertion.** For every natural n, then a proof n>0, then
every experiment (P,Y), with R,I,D,d,c_i,d_i,d_bar,C_1,C_2,C_infinity defined
by the explicit indicator relations and finite sums above,

    max(C_1, C_infinity^2/(n : ℝ)) ≤ d_bar,
    d_bar ≤ C_2^2,
    C_2^2 ≤ C_infinity^2.

There are no hypotheses on outcome size, design independence, support, or
interference. The design does not enter any of these quantities. R is
structural outcome interference on the full cube, with i=j included by
definition. D is the shared-influencer relation, not stochastic dependence
under P. C_infinity is the maximum *outgoing* count.

**Closure coverage.** `Assignment`; `Law`, `Law.mk`; `Experiment`,
`Experiment.mk`, `Experiment.outcome`; `Interferes`, `I`, `Dependent`, `d`,
`degree`, `dAvg`, `outgoing`, `C1`, `C2`, `Cinf`, and `T36Statement` are
expanded in the common notation and this assertion.

**Junk conventions.** The denominator n is positive. `Real.sqrt` is total
(zero for nonpositive arguments), but here its argument is a sum of squares
divided by positive n and is nonnegative. The range used for real `sSup`
is nonempty and finite, so conditionally complete real suprema are used only
on their ordinary valid domain; no empty-set or unbounded-set fallback enters.
The type U is nonempty; assignments form a nonempty finite function space.
Indicator counts are real sums of zeros and ones, so there is no natural
subtraction or truncating cast. There are no integrals, conditional means,
real powers, logs, `toReal`, asymptotic extrema, or partial defaults in this
closure. The arbitrary finite probability law is an actual normalized law.

## SAP.P009c.T37

Source: Challenge/Part1.lean:16–19; statement Defs/Part3.lean:41–44.
The docstring describes a total-variation stability bound under bounded
direct effects.

**Quantifiers and assertion.** For every natural n, then a proof n>0, then
every experiment (P,Y), every other law Q on the same A, and every real K,
if for every i∈U and z∈A,

    |Y_i(z[i←true])-Y_i(z[i←false])| ≤ K,

then

    |∑z p(z)((∑i Δ_i(z))/n) - ∑z q(z)((∑i Δ_i(z))/n)|
       ≤ 2 K ((∑z |p(z)-q(z)|)/2).

The same outcomes Y are used on both sides; replacing the design field does
not change the outcomes or Δ. The bound on all individual differences is
the complete expansion of `BoundedEffects`. The final half-sum is the
complete expansion of `totalVariation`. No relation between P and Q,
positive coordinate probabilities, or interference condition is required.
K is not explicitly assumed nonnegative; bounded effects on this nonempty
cube imply K≥0.

**Closure coverage.** `Assignment`; `Law`, `Law.mk`, `Law.mass`; `Experiment`,
`Experiment.mk`, `Experiment.design`, `Experiment.outcome`; `potential`,
`effect`, `ateAt`, `mean`, `eate`, `BoundedEffects`, `totalVariation`, and
`T37Statement` are expanded above. `B1._proof_1` and
`T37Statement._proof_1`, also in the closure, were printed in
`scratch/Blind.lean`: both have type `(1+1).AtLeastTwo` and body
`Nat.instAtLeastTwoHAddOfNat 1`. They only discharge the numeral-instance
requirement; the unrelated numerical definition `B1` is not a hypothesis.

**Junk conventions.** Only real divisions by positive n and by 2 occur.
Expectations are finite weighted sums with actual probability weights.
Neither the finite index set nor the assignment space is empty. No conditional
mean, sqrt, rpow, log, `toReal`, set extremum, sequence extremum, truncated
subtraction, or partial-function default appears. `Function.update` is total
and natural-to-real casts are exact here. No junk value affects the assertion.

## SAP.P009c.T38

Source: Challenge/Part1.lean:21–24; statement Defs/Part3.lean:46–50.
The docstring promises the assignment-conditional Lipschitz inequality for
every real r≥1, using the infinity-count convention when r=1.

**Quantifiers and assertion.** For every natural n, then a proof n>0, then
every experiment (P,Y), then every K,r∈ℝ, if
|Δ_i(z)|≤K for every i,z, and 1≤r, then for every z,z'∈A,

    |(∑i Δ_i(z))/n - (∑i Δ_i(z'))/n|
        ≤ 2 K (n : ℝ)^(-1/r) H_r
                 (∑i |b(z_i)-b(z'_i)|^r)^(1/r).

H_r is explicitly max_i c_i at r=1; for r>1 it is
((∑i c_i^(r/(r-1)))/n)^((r-1)/r). The c_i are the outgoing counts of
the full-cube relation R defined above, including its diagonal. All real
exponents in this formula are `Real.rpow`. The ground distance is not divided
by n; population normalization is in the outside factor n^(-1/r). This
quantifies finite real r, without an extended-real r=∞ case. The law field
has no role in the inequality. K≥0 follows from the nonempty bounded-effects
hypothesis.

**Closure coverage.** `Assignment`; `Law`, `Law.mk`; `Experiment`,
`Experiment.mk`, `Experiment.outcome`; `potential`, `effect`, `ateAt`,
`BoundedEffects`, `Interferes`, `I`, `outgoing`, `Cp`, `Cinf`, `bit`,
`lrDistance`, `conjugateC`, `T38Statement`, and the already printed numeral
proof `T37Statement._proof_1` are all accounted for.

**Junk conventions.** r≥1 gives r>0, so neither 1/r nor -1/r divides by zero.
At r=1 the selected branch is C_infinity, so r/(r-1) in the other branch
does not enter the value. For r>1 the conjugate exponent is finite and >1;
its reciprocal is positive. n is positive and every c_i≥1; thus those rpow
bases are strictly positive. Inner distance bases are 0 or 1 and exponents
r and 1/r are strictly positive: `Real.rpow 0 a=0` for a≠0 gives precisely
the intended zero distance (not a 0^0 or a negative-exponent artifact).
Mathlib also totalizes negative-base rpow via the real part of complex
power, but no negative base is used here. The set defining C_infinity is
nonempty and finite. There are no problematic integrals, conditional means,
sqrt/log calls, `toReal`, sequence extrema, empty populations, truncated
subtractions, or partial-function defaults. Subtraction r-1 is real, not
truncated natural subtraction.

## SAP.P009c.T39

Source: Challenge/Part1.lean:26–29; statement Defs/Part3.lean:52–56.
The docstring describes an expected-distance coupling bound for a design
change under bounded direct effects.

**Quantifiers and assertion.** For every natural n, then a proof n>0, then
every experiment (P,Y), every other law Q on A, and every K,r∈ℝ, if
|Δ_i(z)|≤K for every i,z, and 1≤r, then

    |∑z p(z)((∑i Δ_i(z))/n) - ∑z q(z)((∑i Δ_i(z))/n)|
        ≤ 2 K (n : ℝ)^(-1/r) H_r W_r(P,Q),

where H_r and the outgoing counts have the full expansions in T38, and

    W_r(P,Q) = sInf { ∑(x,y) j(x,y) L_r(x,y) : j≥0,
                      ∑(x,y) j(x,y)=1,
                      ∀x, ∑y j(x,y)=p(x),
                      ∀y, ∑x j(x,y)=q(y) }.

Here j is an ordinary probability law on the finite product A×A.
The two equalities of marginals are exactly `Coupling`. L_r is the
unnormalized ℓ_r distance expanded in the common notation and in T38.
`wasserstein` is the real infimum of the *expected ground distance*, without
raising the cost to power r inside the expectation or taking an additional
rth root outside. Outcomes and their interference counts are held fixed
while the design changes. No independence or marginal positivity is required.

**Closure coverage.** `Assignment`; `Law`, `Law.mk`, `Law.mass`;
`Experiment`, `Experiment.mk`, `Experiment.design`, `Experiment.outcome`;
`potential`, `effect`, `ateAt`, `mean`, `eate`, `BoundedEffects`, `Interferes`,
`I`, `outgoing`, `Cp`, `Cinf`, `bit`, `lrDistance`, `conjugateC`, `Coupling`,
`wasserstein`, `T39Statement`, and the numeral proof
`T37Statement._proof_1` have all been read and expanded.

**Junk conventions.** All denominator, rpow, cast, nonempty-index, and
C_infinity checks are the same as in T38 and hold independently here.
Additionally real `sInf` is total outside the nonempty/bounded-below domain,
but the displayed cost set is nonempty: j(x,y)=p(x)q(y) is a normalized
nonnegative law with the required marginals. Every cost is a finite sum of
nonnegative numbers and is ≥0, so the set is bounded below. Distances on a
finite cube are finite; each valid law has total mass one. Thus the infimum
has its genuine order-theoretic meaning and uses no empty-set or unbounded-set
fallback. All expectations exist as finite sums. No conditioning, `toReal`,
sqrt/log at a bad argument, limsup/liminf, truncated subtraction, or
partial-function default affects this assertion.
