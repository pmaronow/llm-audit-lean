# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. I read the declaration/docstring and every source
declaration listed in `closure.json`. The line-zero generated declarations were
also printed by Lean in `scratch/PrintClosure.lean` (successful compilation).

## SAP.P024.T7

### Objects and all definitions used

All probabilities and outcomes are real numbers. A `Design Ω`, for a finite type
`Ω`, is a function `w : Ω → ℝ` with `w(ω) ≥ 0` for every `ω` and
`∑ ω, w(ω) = 1`. Its constructor packages this function and the two proofs; its
`mass` projection returns `w`. `expectation d X` is exactly the finite sum
`∑ ω, w(ω) X(ω)`. `probability d A` is that sum with `X(ω)` equal to 1 when
`A(ω)` holds and 0 otherwise. `uniformDesign Ω` assigns mass `1/|Ω|` and
requires a nonempty finite type.

Write `J = Fin K = {0,...,K-1}`. Assignments are finite subsets `s ⊆ J`;
`subsetExposure s j` is the Boolean decision of `j ∈ s`. `bernoulliMass p s`
is `(∏ j ∈ s, p)(∏ j ∈ J\s, (1-p))`, or equivalently
`p^|s| (1-p)^(K-|s|)`. `independentClusterLaw d p` asserts that this is
`d.mass s` for **every** subset `s`, specifying the full independent joint
assignment law, not merely its marginals. `bernoulliDesign K p hp0 hp1`
constructs exactly these masses using `0 ≤ p ≤ 1` to prove nonnegativity and
the product expansion to prove total mass one.

A `ClusterPopulation K` packages natural sizes `n_j`, a proof `n_j > 0` for
each `j`, and two functions `y0(j,i), y1(j,i) : ℝ` for each individual
`i ∈ Fin n_j`. These are fixed individual potential outcomes. Let
`a_j = (∑ i, y0(j,i))/n_j` and `b_j = (∑ i, y1(j,i))/n_j`.
These are `clusterMean0` and `clusterMean1`. For arbitrary real functions
`n,a,b` on a finite cluster type, the underlying definitions are

```
clusterDIM(n,a,b,z)
  = (∑ j: z(j)=true, n_j b_j)/(∑ j: z(j)=true, n_j)
    - (∑ j: z(j)=false, n_j a_j)/(∑ j: z(j)=false, n_j),
clusterEffect(n,a,b)
  = (∑ j, n_j (b_j-a_j))/(∑ j, n_j).
```

Sums with a predicate above mean the actual finite sums with a zero term when
the predicate fails. `populationEffect P` substitutes the natural cluster
sizes cast to reals and the two within-cluster means into `clusterEffect`.
Thus it is the average individual treatment effect
`τ(P) = (∑ j ∑ i (y1(j,i)-y0(j,i)))/(∑ j n_j)`.

For any real function `e` on all subsets, `populationEstimator P e s` returns
`e(s)` if `s = ∅` or `s = J`, and otherwise the displayed individual difference
in means with `z(j)` the membership decision. Denote this estimator by
`D(P,e,s)`. `fixedDIM m a b z` is
`(∑ j: z(j)=true, b_j)/m - (∑ j: z(j)=false, a_j)/(|J|-m)`;
the subtraction in this denominator is in the reals.

For `K=k+2`, `NonemptyAllocations k` is the subtype of subsets satisfying
`s ≠ ∅ ∧ s ≠ J`. Define `A_K` to be this set and
`M(k,p) = ∑ s ∈ A_K, p^|s|(1-p)^(K-|s|)`.
`bernoulliNonemptyMass` is `M`; `bernoulliConditionalMass k p s` is the
parent mass divided by `M(k,p)`. `bernoulliConditionalExpectation k p X`
is the finite sum of these conditional masses times `X(s)`.
`conditionalNonemptyDesign k` is uniform on `A_K`. It is a fair-parent
conditional law, not the conditional law at arbitrary `p`. Its construction
uses `{0}` as an explicit proper nonempty subset.

`unequalPairPopulation` is a genuine population with two clusters of sizes
`(1,2)`, all three control potential outcomes zero, and treatment outcomes
zero in cluster 0 and one for both individuals in cluster 1. All vector
notation here is a function on a bounded `Fin` type.

### Quantifiers, hypotheses, and conclusions

The theorem asserts `T7WholeStatement`, a conjunction of these three items:

1. For every natural `k`, real `p`, proof `hp : 0 < p`, and proof
   `hp1 : p < 1`, put `K=k+2` and use the constructed Bernoulli design.
   Its joint masses satisfy `independentClusterLaw`; its event `A_K` has
   probability `C = 1-p^K-(1-p)^K`; `C>0`; for every `s ∈ A_K` the defined
   conditional mass is the actual parent mass divided by `C`; and the sum of
   the conditional masses on `A_K` is one. This item has no population or
   equal-size hypothesis.
2. `T7Statement` is itself the conjunction of (a) and (b):
   (a) For every natural `k,q`, **if** `q>0`, then for every population
   `P : ClusterPopulation (k+2)`, **if** every cluster size is `q`, then for
   every real `p` with `0<p<1`: the constructed parent law is independent;
   its nonempty-arm event has positive probability; for every proper nonempty
   subset its defined conditional mass is the actual parent mass divided by
   that event probability; for **every** extension function `e`, the
   conditional expectation of `D(P,e,s)` equals `τ(P)`; and for **every**
   `s ∈ A_K`, `D(P,0,s)` equals
   `(∑ j ∈ s b_j)/|s| - (∑ j ∉ s a_j)/(K-|s|)`.
   Here `a,b` are within-cluster means, so this last expression compares the
   unweighted averages of cluster means in the two arms.
   (b) For the explicit real vectors `n=(1,2)`, `a=(0,0)`, `b=(0,1)`, the
   uniform law on all four subsets of `Fin 2` has the independent `p=1/2`
   joint masses; its nonempty-arm event has probability `1/2`; for **every**
   `s ∈ A_2`, the uniform conditional mass is the parent mass divided by
   that event probability; the individual effect is `2/3`; the allocations
   `{0}` and `{1}` give estimates `0` and `1`; for **every** empty-arm
   extension `e` the conditional expectation of the corresponding extended
   difference in means is `1/2`; and the conditional expectation of the raw
   cluster-size weighted difference in means is unequal to the effect.
3. The population `unequalPairPopulation` has exactly the stated sizes and
   individual outcomes, its control and treatment cluster-mean vectors are
   `(0,0)` and `(0,1)`, its effect is `2/3`, **every** extension `e` gives
   conditional expected estimator `1/2` under `conditionalNonemptyDesign 0`,
   and **every** proper nonempty allocation has conditional mass `1/2`.

The docstring describes the general conditioning formula, equal-size
conditional unbiasedness, and the unequal-size example. The theorem is not
an unconditional unbiasedness assertion. Parent independence does not assert
independence of cluster assignments after conditioning.

### Junk values and boundary audit

* Real division is total in Lean: division by zero is zero. The bare
  definitions of cluster means, effects, differences, and normalized masses
  would therefore have values even with invalid denominators. In this theorem,
  every population size is a positive natural; `K=k+2≥2`; proper nonempty
  allocations have positive treated and control population and cluster counts;
  and the conditional event mass is asserted strictly positive. Thus every
  denominator used as a mean or conditional probability is positive. The
  standalone functions remain total outside this setting, without affecting
  these assertions.
* On the two empty-arm allocations `populationEstimator` uses the explicitly
  quantified real function `e`; this is a deliberate extension, not a hidden
  default. These allocations are absent from conditional expectations and
  pointwise comparisons. Its branch selecting `e` prevents an empty-arm ratio
  from being used as the statistical mean.
* The direct two-cluster `clusterDIM` expressions are evaluated only on
  singleton allocations, so their arm denominators are 1 and 2 (in one order
  or the other). `fixedDIM` is used with `m=|s|`, `0<m<K`.
* All cardinality and size casts are exact embeddings `ℕ → ℝ`. In the code's
  `fixedDIM`, the denominator `|J|-m` is real subtraction, not truncated
  natural subtraction. The `K-|s|` exponent in my equivalent formula is a
  natural difference justified by `s ⊆ J`; the source actually uses the
  complement product and introduces no truncated subtraction there.
* Empty finite sums equal zero and empty products equal one; the latter are
  intentionally used for the all-treated and all-control Bernoulli masses.
  Uniform designs require nonempty spaces. A `Design` cannot exist on an empty
  finite type, since its total-mass field would give `0=1`.
* There are no Bochner integrals, nonintegrable means, extended real values,
  `toReal`, logarithms, square roots, real powers, infima, suprema, asymptotic
  limits, or default-valued partial functions in this statement's mathematical
  definitions. All outcomes are finite reals and all sums are finite.
* The generated proof declarations in the closure were read with `#print`:
  `T5Statement._proof_1`, `T5WholeStatement._proof_2/_proof_3` and
  `T7Statement._proof_4` certify small numerals are at least two;
  `T7Statement._proof_1/_proof_2` and
  `T7WholeStatement._proof_1/_proof_2` derive weak bounds from strict ones;
  `T7Statement._proof_3` supplies nonemptiness of the subset type;
  `T7Statement._proof_5` and `unequalPairPopulation._proof_2` certify a
  positive numeral is nonzero. The remaining printed generated proofs certify
  the Bernoulli mass nonnegativity/normalization, nonemptiness of `A_K`, the
  two population sizes' positivity, and uniform mass nonnegativity/normalization.
  None adds a mathematical assumption or encodes an estimator conclusion.

## SAP.P024.T8

### Objects and all definitions used

The finite-law `Design`, `mass`, and `expectation` definitions have the exact
finite-sum meanings given above. They are independently part of this theorem's
closure. There are finite types `B` of blocks and `Ω` of assignments, with
`B` explicitly nonempty. Each block `b` has a finite individual type `I(b)`;
the randomized population is the disjoint union of these types. Let
`N_b = |I(b)|` and `N = ∑ b N_b`. The definition `blockPopulation I` is
this sum with each cardinality cast to a real.

An exposure is `z : Ω → (b : B) → I(b) → Bool`. Fixed potential outcomes
are `y0,y1 : (b : B) → I(b) → ℝ`. `indicator true = 1` and
`indicator false = 0`. `observed z y0 y1 ω i` is `y1(i)` when `z(ω,i)` is
true and `y0(i)` otherwise. For each block this is applied to its own
individual outcomes and exposure. `exposureProbability d z i` is
`∑ ω, d.mass(ω) indicator(z(ω,i))`; write it as `π_bi` for the blockwise
exposure. This is the actual marginal under the law, not a supplied number.

`treatedCount (z ω b)` is the natural cardinality of
`{i ∈ I(b) : z(ω,b,i)=true}`; write it as `T_b(ω)`.
The `clusterDIM` definition is exactly the two ratios unfolded in T7.
With its size argument identically one, it is the ordinary within-block
difference of observed arm means,

```
D_b(ω) = (∑ i: z(ω,b,i)=true, y1(b,i))/T_b(ω)
         - (∑ i: z(ω,b,i)=false, y0(b,i))/(N_b-T_b(ω)).
```

In particular the denominators are the observed arm sizes, not a supplied
quota. `actualBlockedHTW3 I d z y0 y1 ω` is exactly

```
H(ω) = (1/N) ∑ b ∑ i,
       [Z_bi(ω) Yobs_bi(ω)/π_bi
        - (1-Z_bi(ω)) Yobs_bi(ω)/(1-π_bi)],
```

where `Z` is the indicator just defined and `Yobs` selects the fixed potential
outcome. This unfolds every SAP definition in the estimator, including the
actual propensity and the observation rule.

### Quantifiers, hypotheses, and conclusions

In order, the theorem universally quantifies:

* Types `B,Ω`, finite-type instances for both, and a nonempty instance for `B`;
* the family `I`, a finite-type instance for every `I(b)`, a normalized
  nonnegative finite law `d` on `Ω`, and a natural quota function `m : B→ℕ`;
* a proof `∀ b, 0<m_b` and a proof `∀ b, m_b<N_b`;
* the exposure function `z` and the two fixed potential-outcome functions;
* a proof `∀ ω b, T_b(ω)=m_b`, including assignments of zero mass;
* a proof `∀ b i, π_bi=m_b/N_b` for the actual law `d`.

Its conclusion is the conjunction:

1. `N>0`;
2. for every `b,i`, `0<π_bi<1`;
3. for every `ω`, `H(ω)=∑ b (N_b/N)D_b(ω)`;
4. `∑ ω d.mass(ω) H(ω) = (∑ b ∑ i (y1(b,i)-y0(b,i)))/N`;
5. `∑ ω d.mass(ω) [∑ b (N_b/N)D_b(ω)]` equals the same individual
   average effect.

There are no independence, blockwise independence, or uniform-joint-mass
assumptions. The two design hypotheses fix counts and actual within-block
marginals. The docstring explicitly calls these extra design assumptions and
excludes varying counts and unequal within-block propensities. Excluded units
are represented by their absence from the disjoint union. The potential
outcome and observation signatures ensure fixed outcomes depending on each
unit's own treatment status.

### Junk values and boundary audit

* The bare formulas use total real division, so invalid populations or
  propensities would still produce numbers. Here `0<m_b<N_b` implies
  `N_b≥2`, both realized arm sizes are positive on every allocation, and
  `0<m_b/N_b<1`. The actual-marginal hypothesis transfers this to `π_bi`.
  Nonempty `B` then gives `N>0`. No division-by-zero value contributes to
  any claimed mean or inverse-probability term.
* The type `Ω` has no explicit nonempty instance, but an empty `Ω` cannot
  support the required `Design`. Empty block types are excluded explicitly;
  empty individual types cannot satisfy the quota hypotheses. These facts do
  not by themselves establish joint satisfiability; that will be tested later.
* The source's `clusterDIM` control denominator is a sum of ones, not natural
  subtraction. The equivalent `N_b-T_b` above denotes its positive cardinality.
  All casts of naturals into reals are exact; quota bounds precede the use of
  the resulting fractions.
* Observed outcomes, Boolean indicators, and finite functions are fully defined;
  there are no hidden defaults or partial indices. Even terms multiplied by
  a zero indicator have positive probability denominators under the hypotheses.
* Expectations are finite real sums, automatically finite and integrable for
  the discrete interpretation. There are no Bochner integral conventions,
  extended real conversions, logs, square roots, real powers, infimum/supremum
  conventions, or limsup/liminf conventions in this closure.
