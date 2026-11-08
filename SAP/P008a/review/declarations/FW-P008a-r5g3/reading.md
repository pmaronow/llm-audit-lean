# Blind reading

Written and saved before opening `claims.json` or `record.json`. Sources read:
`closure.json`, the four theorem docstrings/statements in
`SAP/P008a/Challenge/Part1.lean`, and all declarations in their closures.
`scratch/Blind.lean` successfully printed all 50 distinct closure declarations,
including every generated proof and the auxiliary decidability declaration.
The generated proofs supply numeral instances (`Nat.AtLeastTwo`), nonzero
`Fin` modulus instances, or valid interpolation indices. They add no mathematical
hypotheses. The decidability instance decides the actual conjunction of real
inequalities defining the window. Definitions imported but absent from the
elaborated closures play no part in these four statements.

## SAP.P008a.T11

Source: `Defs/Part8.lean:40–54`; docstring: `Challenge/Part1.lean:133–141`.

The proposition is a conjunction of the following three parts, with no outer
parameters or assumptions:

1. In the real numbers,
   `1.491 + 1.550 + 1.550 + 1.691 + 1.714 = 7.996`, and
   `7.996 + 1.700 + 1.678 + 1.002 = 12.376`.
2. For every ordered tuple of real numbers `(a,b,c,e,f)`, and then proofs of all
   five bounds
   `|a−1.491| ≤ 0.0005`, `|b−1.550| ≤ 0.0005`,
   `|c−1.550| ≤ 0.0005`, `|e−1.691| ≤ 0.0005`, and
   `|f−1.714| ≤ 0.0005`, their sum `S=a+b+c+e+f` satisfies all four conclusions:
   `7.9935 ≤ S`, `S ≤ 7.9985`, `0.005 < |S−12.38|`, and `7.975 < S`.
3. `|12.376−12.38| < 0.005`.

Every decimal above denotes an exact real rational, not floating point data.
There are no SAP definitions below the statement wrapper. No rounding function,
actual unrounded data, or empirical permutation law occurs. The last inequality
of part 2 implies that the sum exceeds every real within 0.005 of 7.97, although
that second universal quantifier is not written separately. The docstring
explicitly calls this restricted and excludes the actual unrounded total,
its corrected display, and certification of the empirical percentiles.

Junk-value audit: every divisor is a fixed positive integer (1000, 250, 125,
2000, 200, or 50). Real subtraction is ordinary, not truncated. There are no
integrals, partial functions, empty indices, casts of variable naturals,
logarithms, square roots, powers with problematic domains, extended-real
conversions, infima/suprema, or limits. Closed rounding envelopes include ties;
no tie-breaking convention is encoded or needed for the strict comparisons.

## SAP.P008a.T12

Source: `Defs/Part8.lean:57–66`; docstring: `Challenge/Part1.lean:144–147`.

For `k` in `Fin 5 = {0,1,2,3,4}`, unfold the printed grid as
`G(k) = 5·(k.val:ℝ)/111`. Unfold the window predicate as membership in the
closed real interval `W=[1/111,5/222]`.

The proposition is a conjunction, with no outer parameters or assumptions:

1. For every `k∈Fin 5`, `G(k)∉W`.
2. For every real-valued function `f` on `Fin 5`, the finite sum of `f(k)` over
   all `k∈Fin 5` with `G(k)∈W` is zero.
3. Each of the real constants `−321/10000 = −0.0321`, `−19/625 = −0.0304`,
   and `21/625 = 0.0336` is nonzero.
4. `25/111 > 20/111`.
5. For every natural `n` (implicitly bound first), every array
   `M : Fin (n+1) → Fin 5 → ℝ`, every real `q`, and then the hypotheses
   `0≤q` and `q≤1`, define
   `s(z)=Σ_{j∈Fin 5, G(j)∈W} M(z,j)`.
   Then `(∀z∈Fin(n+1), s(z)=0)` and the following interpolant is zero:
   `h=(n:ℝ)q`, `j=min(Int.toNat(floor(h)),n)`, `g=h−(j:ℝ)`,
   `(1−g)s(j)+g s(min(j+1,n))`.
   Both arguments of `s` are explicitly constructed elements of `Fin(n+1)`.

The last formula fully unfolds `quantile7`; it interpolates entries of its
supplied sequence without sorting. In this theorem every entry is zero, so
the sample is already sorted and the formula is the finite type-7 quantile.
The universal array permits arbitrary observed/replicate values at every grid
point. There is no probability law or independence premise in this arithmetic
incompatibility statement. It does not claim to compute actual nonzero outputs.

Junk-value audit: the filtered index set is deliberately empty. Its sum is the
ordinary additive identity zero, which drives the assertion and is meaningful
as an empty sum. This is not a mean of an empty set. All real divisions have
fixed positive denominators 111, 222, 10000, or 625. `Int.toNat` generally maps
negative integers to zero and the two `min`s clamp indices, but `0≤q≤1`
implies `0≤h≤n`; therefore neither negative truncation nor out-of-range access
changes the interpolant. For `n=0` the sample has one entry, both indices are
zero, and the interpolant is that entry. No sample is empty. All `Fin`/natural
casts into the reals are exact. There are no Bochner integrals, infinite values,
domain-sensitive real operations, partial-function defaults, or limits.

## SAP.P008a.T13

Source: `Defs/Part8.lean:69–77`; docstring: `Challenge/Part1.lean:150–152`.

For `k∈Fin 41={0,…,40}`, unfold the corrected grid as
`C(k)=(k.val:ℝ)/222`. The same window predicate unfolds as
`1/111≤d ∧ d≤5/222`. The proposition conjoins the following, with no outer
parameters or hypotheses:

1. The cardinality of `Fin 41` is 41 and `C(40)=20/111`.
2. For every `k∈Fin 41`, `1/111≤C(k)≤5/222` if and only if
   the natural number `k.val` satisfies `2≤k.val≤5`.
3. For every `f : Fin 41→ℝ`, the finite sum of `f(k)` over the selected
   indices is `f(2)+f(3)+f(4)+f(5)`.
4. For every `k∈Fin 40`, `C(k.succ)−C(k.castSucc)=1/222`.
   Here `k.succ` has value `k.val+1` and `k.castSucc` has value `k.val`.
5. `111 C(2)=1`, `111 C(3)=3/2`, `111 C(4)=2`,
   `111 C(5)=5/2`, and `1/222=(1/2)/111`.

The statement concerns arbitrary arrays of estimates and identifies the four
selected indices; it contains no empirical assignment data or estimator
definition. The factor 111 gives the docstring's numerical km conversion.

Junk-value audit: divisions by 111, 222 and 2 have positive denominators.
Subtraction is real subtraction. All natural/`Fin` casts are exact.
Numerals used as `Fin 41` values are 2, 3, 4, 5, and 40, all strictly below
41, so the modular numeral convention for `Fin` changes none of them.
All finite index types used are nonempty. There are no undefined statistics,
partial functions, means, integrals, limits, or extended-real conversions.

## SAP.P008a.T14

Source: `Defs/Part8.lean:80–86`; docstring: `Challenge/Part1.lean:155–157`.

The proposition is a conjunction of three parts:

1. For every natural `N` (implicitly bound first), then a proof `0<N`, then
   three functions `μ₁, μ₀, τ : Fin N→ℝ`, then the hypothesis
   `∀i∈Fin N, τ(i)=μ₁(i)−μ₀(i)`,
   `(N:ℝ)⁻¹ Σ_i τ(i) = (N:ℝ)⁻¹ Σ_i (μ₁(i)−μ₀(i))`.
2. For every real `A`, `A·A=A` if and only if `A=0` or `A=1`.
3. In the reals, `(3−0+(7−2))/2=4`, `4·4=16`, and `16≠4`.

There are no SAP definitions beyond the statement wrapper. The functions in
part 1 are arbitrary real arrays with a pointwise difference relation, rather
than formal conditional means. Part 2 can be instantiated with the average in
part 1 but does not explicitly name that average. The two-node example gives
means `(3,7)` and `(0,2)` and differences `(3,5)` by its numerical expression.
There is no radius parameter, potential-outcome space, or expectation operator
in this declaration.

Junk-value audit: the inverse of `N` is nonzero-domain-safe because `0<N`
implies `(N:ℝ)≠0`, and `Fin N` cannot be empty. The real inverse-at-zero
convention therefore cannot explain the assertion. The example divides by
2. Natural-to-real casts are exact. There are no unbounded sums, integrals,
domain-sensitive real operations, partial-function defaults, or limits.
