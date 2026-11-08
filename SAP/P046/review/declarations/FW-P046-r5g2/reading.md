# Blind reading

Saved before opening either `claims.json` or `record.json`. This reading uses
`closure.json`, the Challenge docstrings/statements, every source declaration in
their closures, and Mathlib definitions/Lean prints. The generated proof
declarations listed by the closure were also printed in `scratch/Blind.lean`.

## Common objects (unfolded in all five declarations)

The full-data space is the Borel space
`U = ℝ × (Bool × (Bool × Bool))`. Write a point as `(w,(x,(y0,y1)))`.
Convert a Boolean to the real number 1 if true and 0 if false. Thus `W=w`,
`X=bit(x)`, `Y0=bit(y0)`, `Y1=bit(y1)`; all outcomes and treatment are binary.
The observed outcome is `Y=(1−X)Y0+XY1`. The observed data are the real triple
`(W,(Y,X)) ∈ ℝ × (ℝ × ℝ)`.

A study is a quadruple `(P,p,m,δ)` where `P` is a measure on U, `p,m : ℝ → ℝ`
and `δ : ℝ`. A **valid** study satisfies all of the following:

1. P is a probability measure.
2. For every real w, `P{u : W(u)=w}=0` (atomless W marginal).
3. Both p and m are Borel measurable.
4. `δ>0` and `δ<p(W)<1−δ` P-almost surely, with strict inequalities.
5. On the sub-σ-algebra `σ(W)`, the Mathlib conditional expectation
   `E_P[X | σ(W)]` equals `p(W)` P-almost surely.
6. `E_P[Y1 | σ(W)] = m(W)` P-almost surely, and `0≤m(W)≤1` P-almost surely.
7. Y0 and X are conditionally independent given σ(W), and Y1 and X are
   conditionally independent given σ(W). These are two separate conditional
   independence requirements, not a requirement on the pair (Y0,Y1).

The target is the unconditional population mean `μ=∫Y1 dP`.
A sample of size natural n is a function `a : Fin n → U`, with law
`P_n=∏_{i∈Fin n}P`. This is genuinely an independent identically distributed
product law. Write `Wi=W(a i)`, and similarly Xi, Yi, Y1i. All sums below run
over `Fin n`, and division is real division after casting n to ℝ.

The Horvitz–Thompson statistic is
`H_n(a)=(1/n)∑i Xi Yi/p(Wi)`; its scalar summand is `xy/p`.

These common definitions, including the Study and ValidStudy constructors and
projections listed by the closure, contain no theorem conclusion as a field.
The `sampleLaw_probability` instance constructs the probability instance of
the finite product from that of P. The printed generated declarations only
supply numerical typeclass instances, standard Borel/Borel-space instances,
the measurable-sub-σ-algebra inclusion, and probability/finite-measure
instances. They add no hypotheses.

Common totalization conventions: real division/inversion at zero is zero;
Bochner integrals of nonintegrable functions are zero; conditional expectation
is zero if its conditioning space is not a sub-σ-algebra, the restricted
measure is not σ-finite, or the function is not integrable. Here σ(W) is a
sub-σ-algebra, P and its restrictions to sub-σ-algebras are finite, and the
binary variables are bounded and measurable, so their conditional expectations
and μ are genuine. Positivity bounds inverse propensity by `1/δ` almost
surely. The functions p and m are unrestricted off sets of marginal measure
zero; junk division there does not affect probabilities or integrals. There
are no partial functions or default-selected data points in these definitions.

## SAP.P046.T6

Sources: `Challenge/Part1.lean:58–62`, `Defs/Part4.lean:38–41`, and the common
definitions in `Defs/Part1.lean` listed by its closure.

For a sample define
`ξ_n(a)=(1/n)∑i (p(Wi)⁻¹)²`,
`r_n,α(a)=sqrt(ξ_n(a) log(2/α)/(2n))`.
The tail is the **non-strict** event `r_n,α(a)≤|H_n(a)−μ|`; its probability
is converted from an extended nonnegative real to a real with `.toReal`.

The theorem negates this universal assertion, with quantifiers in this order:
for every study M, if valid, then for every natural n>0, then for every real
α with `0<α<1`,
`P_n{a : r_n,α(a)≤|H_n(a)−μ|}≤α`.
Classically, it asserts the existence of one valid study, one positive integer
n and one `α∈(0,1)` for which that real tail probability is greater than α.
It does not give a witness or exact failure probability in its statement.
Its docstring calls this the failure of the printed population-centred bound.

Junk values: n=0 would make both averages and the inner radius argument zero,
but n>0 is required. `Real.log 0=0` and `Real.log` on a negative argument uses
the absolute value; `Real.sqrt` on a nonpositive real is zero. These cases
cannot affect the asserted bound: `2/α>2`, ξ is a sum of squares, and n>0.
Inverse propensities may be zero on exceptional null sets but are positive and
bounded almost surely. `.toReal ∞=0` is inapplicable to an event probability
under the probability measure P_n. The non-strict tail includes equality at
the radius; it is not literally the complement of a closed confidence interval.
There are no truncated subtractions, real powers, extrema, limsups or liminfs.

## SAP.P046.T7

Sources: `Challenge/Part1.lean:64–68`, `Defs/Part4.lean:43–53`, and its full
`Defs/Part1.lean` closure.

The statement is the conjunction of two parts:

1. For every real δ>0 and then every real ε>0 there exists a real C>0 such
   that for every valid study M whose stored positivity constant equals δ,
   and every natural n>0,
   `P_n{sqrt(n)|H_n−μ|>C}≤ε`.
   C may depend on δ and ε but cannot depend on the study or n. There is no
   eventual-n qualification: the bound holds for every positive n.
2. For every valid study, all the following hold together:
   - For every natural n>0, H_n is Bochner integrable under P_n and
     `∫H_n dP_n=μ`.
   - The Mathlib variance of `T(u)=X(u)Y(u)/p(W(u))` is
     `v=∫m(W)/p(W) dP−μ²`.
   - `v≥0`, P has a probability instance, and the laws of
     `sqrt(n)(H_n−μ)` converge weakly as n→∞ to the law of the identity
     function under `gaussianReal 0 v.toNNReal`.

Here weak convergence is Mathlib `TendstoInDistribution` on the varying sample
spaces U^(Fin n). It includes almost-everywhere measurability of the variables
and convergence of their probability laws. `gaussianReal 0 v.toNNReal` is
the normal law with mean zero and variance v when v>0, and the Dirac mass at
zero when v=0. The variance definition is
`(∫⁻u, ‖T(u)−∫T dP‖ₑ² dP).toReal`, not a hidden sample variance.

Junk values: the uniform and unbiasedness parts exclude n=0. The normal-limit
sequence includes n=0 (H_0=0 by empty sum and zero division), but altering this
one term cannot change convergence at infinity. `sqrt(n)` has a nonnegative
argument. `v.toNNReal` would truncate a negative v to zero; the explicit v≥0
conjunct rules this out. `.toReal ∞=0` in the variance cannot occur because
T is bounded almost surely by positivity and binary outcomes; the displayed
integral for v is likewise finite. μ and the estimators are integrable, with
estimator integrability also explicitly asserted. All tail probabilities are
finite before `.toReal`. If δ≥1/2 there are no valid studies with that constant;
that parameter case is empty, but the statement also covers nonempty cases
`0<δ<1/2`. No other extrema, limsup/liminf, real-power, or partial-function
conventions occur.

## SAP.P046.T8

Sources: `Challenge/Part1.lean:70–78`, `Defs/WholeW2.lean:14–95`, and the common
and CrossFit/adjusted definitions in `Defs/Part1.lean` in the closure.

At natural n, a cross-fit consists of a deterministic map
`s : Fin n → Bool` and `g : Bool → (Fin n → U) → ℝ → ℝ` such that:

- For each j, `(a,w)↦g(j,a,w)` is Borel measurable.
- For each j and samples a,b, if `observe(a i)=observe(b i)` for every i
  with `s(i)≠j`, then `g(j,a,·)=g(j,b,·)` pointwise as functions on ℝ.

Thus the fitted function for fold j depends only on observed triples in the
opposite fold. No fitted accuracy, boundedness, or correctness is assumed.
For each sample define
`B_i(a)=g(s(i),a,Wi)`, `Q_i(a)=Xi B_i(a)/p(Wi)`,
`R_n(a)=(1/n)∑i [Xi(Yi−B_i(a))/p(Wi)+B_i(a)]`.
The conditioning σ-algebra for the fitted chains is **σ(Wi)** on the full
sample space, not σ(W1,…,Wn).

In order, the theorem quantifies over every study M and proof of validity,
every natural n>0, and every such cross-fit. It then asserts this conjunction:

1. If R_n is integrable under P_n, then `∫R_n dP_n=μ`. The guard is on the
   full estimator only; it does not require integrability of each B_i.
2. For every sample a, for each i, `Xi Yi=Xi Y1i`, and
   `R_n=(1/n)∑i Xi Y1i/p(Wi)−(1/n)∑i Q_i+(1/n)∑i B_i`.
3. On the single-unit space, `T1=XY1/p(W)` is integrable, and the following
   three consecutive equalities hold:
   `∫T1 dP = ∫ E[XY1|σ(W)]/p(W) dP`,
   `∫ E[XY1|σ(W)]/p(W) dP
      = ∫ E[X|σ(W)]E[Y1|σ(W)]/p(W) dP`,
   `∫ E[X|σ(W)]E[Y1|σ(W)]/p(W) dP = μ`.
4. For each i, `∫ Xi Y1i/p(Wi) dP_n=μ`.
5. For each i, Xi and B_i are conditionally independent under P_n given
   σ(Wi). This assertion has no fitted-moment guard.
6. For each i, **if B_i is integrable**, Q_i is integrable and:
   `E[Xi B_i|σ(Wi)] = E[Xi|σ(Wi)]E[B_i|σ(Wi)]` P_n-almost surely;
   `∫Q_i dP_n = ∫ E[Xi|σ(Wi)]E[B_i|σ(Wi)]/p(Wi) dP_n`;
   the latter integral equals `∫B_i dP_n`.
7. **If every B_i is integrable**, the integrals of `(1/n)∑Q_i` and
   `(1/n)∑B_i` coincide, `∫R_n dP_n=(1/n)∑i μ`, and `(1/n)∑i μ=μ`.

These are the exact expansions of `wholePrediction`,
`wholeWeightedPrediction`, `wholeOwnSigma`, `wholeHTChain`,
`wholeFitIndependent`, `wholeFitMoments`, `wholeFitChain`, `adjustedTerm`,
and `adjusted`. The folds need not be balanced or even both nonempty.

Junk values: Bochner integrals and conditional expectations of B_i would
collapse to zero if B_i were not integrable. Every chain using their separate
expectations is guarded by integrability. The unguarded conditional
independence assertion does not need such expectations. The estimator's
expectation is separately guarded by its own integrability. All unguarded
single-unit HT integrals and conditional expectations involve bounded variables
and bounded inverse propensities almost surely. σ(Wi) is a genuine
sub-σ-algebra and its measure is finite. Conditional expectations are used
only inside integrals or up to almost-everywhere equality, so versions are
irrelevant. The expansion is a real algebra identity even off the positivity
set, including division by zero there. n>0 rules out the empty sample; an
empty training fold is allowed and its fitted function must then be independent
of the sample. No logarithm, square root, real power, extrema, limsup/liminf,
or `.toReal` appears in this statement beyond common definitions.

## SAP.P046.T9

Sources: `Challenge/Part1.lean:80–88`, `Defs/WholeW2.lean:97–114,132–148`, and
all common, CrossFit, Balanced, RootN, NormalLimit and hahnBound definitions
listed by its closure.

Cross-fits and R_n have the definitions unfolded in the T8 section. A sequence
of cross-fits F_n is **balanced** if, for each Boolean j,
`#{i∈Fin n : s_n(i)=j}/n → 1/2` as n→∞. The assignments remain deterministic.

For a real function h, define the extended squared error
`L_n,j,h(a)=∫⁻u ofReal((g_n(j,a,W(u))−h(W(u)))²) dP ∈ [0,∞]`.
Here `ofReal` maps a real r to max(r,0) in the extended nonnegative reals.
Since the argument is a square it discards no negative information.
Convergence in mean square means
`∫⁻a L_n,j,h(a) dP_n → 0` in the extended nonnegative reals.
Convergence in probability means, for every real ε>0,
`P_n{a : ofReal(ε)<L_n,j,h(a)} → 0`, with just those probabilities
converted to reals. These are the exact definitions used by this target,
not the older real-integral `L2InProbability` or `L2InMeanSquare` definitions.

The theorem has two independently universally quantified implications:

1. For every valid study, every balanced cross-fit sequence, and every pair
   of fixed real functions `h : Bool → ℝ → ℝ`, if each h_j is Borel
   measurable, `h_j∘W` belongs to Mathlib `MemLp · 2 P` (finite L² norm),
   and each fitted function converges to h_j in the extended mean-square
   sense just defined, then R_n is root-n consistent at this **fixed** study.
   Precisely, for every real ε>0 there exist real C>0 and natural N such
   that for every natural n≥N,
   `P_n{a : C<sqrt(n)|R_n(a)−μ|}≤ε`.
   The two h_j can differ. C and N may depend on the study, fits, limits and ε.
2. For every valid study and every balanced cross-fit sequence, if both
   fitted regressions converge to the supplied true m in the extended L²
   probability sense, then R_n has the normal limit defined in T7, with
   variance
   `b=∫ m(W)(1−m(W))/p(W) dP + Var_P(m(W))`.
   Explicitly b≥0, P is a probability law, and the laws of
   `sqrt(n)(R_n−μ)` converge to N(0,b), with N(0,0) the mass at zero.

The second conclusion identifies a numerical variance; it has no explicit
notion of a statistical model, regular estimator, tangent space, information
bound or optimality comparison. There is no finite-n almost-sure L² assumption
on fitted functions in either implication.

Junk values: the nonnegative extended errors retain ∞; no `.toReal` is applied
to an L² error or its expectation, and a non-square-integrable fit is not
mistaken for zero error. Probability convergence can allow an infinite error
on events of probability tending to zero. Mean-square convergence can allow
infinite initial terms but must tend to zero in the extended topology. The
events are measurable from joint fit measurability and measurability of h (or
of m). n=0 gives an empty fold count and ratio 0, but only asymptotic balance
is required. RootN may also include n=0 if N=0; changing finitely many indices
cannot change tightness. NormalLimit has the same n=0 convention and explicit
nonnegative-variance safeguard as T7. The Hahn integral and its variance are
finite because `0≤m≤1` and p>δ almost surely, so Bochner/variance totalization
is harmless there. There is no uniformity over different studies in RootN.
No logarithm, general real power, extrema, limsup/liminf or truncated
natural/integer subtraction is used.

## SAP.P046.T10

Sources: `Challenge/Part1.lean:90–94`, `Defs/Part4.lean:73–80`, and its full
common-definition closure.

An estimator sequence is
`e : ∀ n : ℕ, (Fin n → (ℝ × (ℝ × ℝ))) → ℝ`.
For every such sequence whose e_n is Borel measurable for every n, there
exist real constants ε>0 and c>0 such that, for **every** natural N, there
exist a natural n≥N with n>0 and a study M satisfying every validity condition,
for which
`P_n{a : ε<|e_n(i↦(Wi,(Yi,Xi)))−μ|}≥c`.

The quantifier order is `∀e, measurable(e) → ∃ε>0 ∃c>0 ∀N ∃n≥N,
n>0 ∧ ∃M, valid(M) ∧ failure_probability≥c`. Thus M may vary with n and e,
while ε and c are fixed across arbitrarily large sample sizes for this e.
The estimator receives observed triples only; p, m, δ and the unobserved
potential outcomes are not arguments to e. No propensity estimator is
assumed. This is failure of uniform consistency over the class of **all**
valid studies as defined here. There is no common δ fixed before choosing M:
the positive lower bound may vary across the adversarial studies. It does not
assert failure for a single fixed population at infinitely many n, nor does
it give particular values for ε,c or a witness family in the statement.

Junk values: each event is measurable, and its probability is finite, so
`.toReal ∞=0` cannot erase a failure probability. μ is a genuine bounded
expectation. The error threshold is strict. n>0 excludes the empty sample
even when N=0. The estimator is a total real-valued function, with no
default/partial-function convention. All real-valued means and conditional
means in ValidStudy are protected as in the common section; no division,
logarithm, square root, rpow, extremum, limsup/liminf or integer-subtraction
convention enters the failure assertion itself.
