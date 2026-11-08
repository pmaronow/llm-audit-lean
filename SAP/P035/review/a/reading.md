# Blind reading

This reading was written from `SAP/P035/Defs.lean`, its three imported parts, and `SAP/P035/Challenge.lean` / `Challenge/Part1.lean`, before opening `claims.json` or `record.json`. It describes the propositions, independently of their docstrings' intended interpretation. No theorem has an external hypothesis or a typeclass parameter. In particular, the many assertions in `T1Statement` are conclusions, not assumptions.

## Objects and all definitions

The year set is the inductive type with exactly three constructors, 2012, 2014 and 2015. `years` is the finite set containing all three. Porch assignment, campaign presence and food choice are each `Bool`. Write these as 0/1 for false/true: porch 1 is the implemented Obama package, porch 0 is the pooled comparison package; campaign 1 means initiative present; food 1 is raisins and food 0 is candy. `fruitValue` maps food 0 to rational 0 and food 1 to rational 1; `bit` maps a Boolean to the corresponding natural number.

A potential outcome is an arbitrary function

`Y : {2012,2014,2015} × {0,1} × {0,1} × ℕ → {0,1}`.

Its arguments are year, porch assignment, campaign presence, and latent label, in that order. The type contains no other children's assignments, health-message variable, missingness indicator, or measured population attributes. Every natural number, including 0 and labels outside the finite support below, is in its domain. Outcomes are observed at campaign 1.

The following constants are fixed, not universally quantified data:

| Year | Enrolled porch 0 / 1 | Complete cases porch 0 / 1 | Raisin counts porch 0 / 1 | Latent size N | Thresholds t₀ / t₁ | Exact effect e |
|---|---|---|---|---|---|---|
| 2012 | 69 / 96 | 69 / 95 | 14 / 24 | 6555 | 1330 / 1656 | 326/6555 |
| 2014 | 265 / 157 | 265 / 157 | 58 / 37 | 41605 | 9106 / 9805 | 699/41605 |
| 2015 | 444 / 192 | 444 / 192 | 113 / 61 | 7104 | 1808 / 2257 | 449/7104 |

Here slash-separated pairs in the first columns list the two arms, not division. Define `p(y,z)` (`releasedFrequency`) to be the rational raisin count divided by the complete-case count. These are 14/69 and 24/95; 58/265 and 37/157; 113/444 and 61/192. `reducedDenominator(y,z)` is natural division of the complete-case count by its greatest common divisor with the raisin count.

`latentPopulation(y)` is the finite natural interval `L_y = {1,…,N_y}`. `uniformMean(y,f) = (Σ_{r∈L_y} f(r))/N_y`, with values in ℚ. `outcomeMean(Y,y,z,a)`, abbreviated `m_Y(y,z,a)`, averages `fruitValue(Y(y,z,a,r))` in this way. `successCount(Y,y,z)` is the natural cardinality of `{r∈L_y : Y(y,z,1,r)=1}`.

Two particular functions are defined, using the natural-number threshold difference `t₁−t₀` (which is truncated subtraction as a Lean operation):

* `D(y,z,a,r) = 1` if and only if `r ≤ t₀(y) + bit(z)(t₁(y)−t₀(y))`. It does not depend on `a`.
* `C(y,z,a,r) = 1` if and only if `r ≤ t₀(y) + bit(a)bit(z)(t₁(y)−t₀(y))`.

`campaignDifference(Y,y,z,r)`, abbreviated `δ_Y(y,z,r)`, is the rational difference `fruitValue(Y(y,z,1,r)) − fruitValue(Y(y,z,0,r))`. `campaignMean(Y,y,z)`, abbreviated `k_Y(y,z)`, is `(Σ_{r∈L_y} δ_Y(y,z,r))/N_y`.

Write `n_yz` for enrolled counts, `n_y=n_y0+n_y1` (165, 422, 636). The design definitions are:

* `yearMass(y) = q_y = n_y/1223` in ℚ;
* `assignmentMass(y,z) = s_yz = n_yz/n_y` in ℚ;
* `latentMass(y) = 1/N_y` in ℚ (defined but not directly mentioned in either theorem);
* `conditionalMass(y,z,r) = h_yzr = s_yz/N_y`, for every natural `r`;
* `jointMass(y,z,r) = j_yzr = q_y h_yzr`, also for every natural `r`.

These last two functions are not zero outside `L_y`. Their interpretation as finite probability weights always uses sums restricted to `L_y`; the propositions never normalize over all naturals.

For an arbitrary rational weight function `w : Year → Bool → ℕ → ℚ`, define the array

`O^ℚ_w(Y)(y,z,b) = Σ_{r∈L_y} w(y,z,r) · 1{Y(y,z,1,r)=b}`.

`observedLawWith` is this array. `observedRealLawWith` is the same definition for arbitrary real-valued `w`, yielding a real-valued array `O^ℝ_w(Y)`. There is no positivity or normalization assumption on either kind of arbitrary weight. Equality of arrays is equality of functions, hence equality at every year, arm and food choice. `observedLaw(Y) = O^ℚ_j(Y)` uses the fixed rational design.

`Calibrated(Y)` means `∀ y ∀ z, m_Y(y,z,1)=p(y,z)` (all six frequencies). `overallCampaignEffect(Y)`, abbreviated `E(Y)`, is the rational number

`Σ_{y∈years} q_y [s_y0 k_Y(y,0) + s_y1 k_Y(y,1)]`.

`CampaignIdentified` is the proposition

`∀ U : PotentialOutcome, ∀ V : PotentialOutcome, Calibrated(U) → Calibrated(V) → observedLaw(U)=observedLaw(V) → ∀ y, k_U(y,1)=k_V(y,1)`.

Thus this identification notion concerns the three year-specific campaign means at porch 1, for the fixed design and calibrated binary models. It does not quantify over designs or ask for equality of individual counterfactual outcomes or of porch-0 campaign means.

## Mathlib semantics followed

`Finset.Icc` is the inclusive finite interval (`Mathlib/Order/Interval/Finset/Defs.lean`, `mem_Icc`); its natural-number instance uses a finite consecutive range (`Mathlib/Order/Interval/Finset/Nat.lean`). Thus each `L_y` contains exactly `N_y` labels, starts at 1, and excludes 0. `Finset.filter` retains exactly the elements satisfying its predicate (`Mathlib/Data/Finset/Filter.lean`, `mem_filter`); `Finset.card` is ordinary finite cardinality (`Mathlib/Data/Finset/Card.lean`). The bounded sum notation is `Finset.sum`, ordinary addition over the indicated finite set (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`); none of the propositions uses an infinite sum, integral, limit, or supremum.

`Nat.gcd` and `Nat.lcm` have their ordinary natural-number greatest-common-divisor and least-common-multiple meanings (divisibility properties in `Mathlib/Data/Nat/GCD/Basic.lean`). The division in `reducedDenominator` is natural quotient, while all frequencies, means, masses and effects use rational field division. Natural subtraction in the threshold formula is truncated at zero. All other displayed effect subtraction is rational subtraction. The theorem itself asserts threshold ordering and positive latent sizes, and the concrete complete-case denominators are positive. Thus no informal untruncated subtraction or positive-denominator assumption has been silently added to this reading. Rational field division is total in Lean (inverse of zero is zero, `Mathlib/Algebra/GroupWithZero/Defs.lean`), but none of these fixed denominators is zero. The real-weight arrays use ordinary real addition and multiplication over a finite support. `decide` in `C` and `D` returns the Boolean truth value of the threshold comparison.

## Theorem `SAP.P035.T1`

This theorem asserts the following conjunction, with no hypotheses. The order of the clauses below is the order of the Lean conjunction. All universally bound `y` are years, `z` are Booleans, and `r,s` are natural numbers. Unless a finite summation explicitly restricts a label to `L_y`, a quantifier over labels covers all naturals.

1. For every year `y`, `N_y = lcm(reducedDenominator(y,0), reducedDenominator(y,1))`.
2. For every year `y`, `N_y>0`, `t₀(y)≤t₁(y)`, and `t₁(y)≤N_y`.
3. For every year `y`, then every arm `z`, `t_z(y)=N_y p(y,z)` as rationals.
4. For every year `y`, then every arm `z`, then every natural `r`,
   `h_yzr = (Σ_{s∈L_y} h_yzs) (h_y0r+h_y1r)`.
   This is the displayed product-of-marginals factorization within a year, valid also for labels outside the summation support as a numerical identity.
5. Both: for every `y,z,r`, `j_yzr≥0`; and
   `Σ_{y∈years} [(Σ_{r∈L_y}j_y0r)+(Σ_{r∈L_y}j_y1r)] = 1`.
6. For every `y,z,r`, `C(y,z,1,r)=D(y,z,1,r)`.
7. For every `y,z`, simultaneously the success counts of `D` and `C` equal `t_z(y)`, and `successCount(D,y,z)/N_y=p(y,z)` in ℚ.
8. Both `D` and `C` are calibrated: each one's campaign-present uniform outcome means equal `p(y,z)` for every `y,z`.
9. For every year `y`, `m_D(y,1,1)−m_D(y,0,1)=e_y`, and that porch contrast is strictly positive.
10. For every `y,z,r`, `δ_D(y,z,r)=0`.
11. For every `y,r`, `δ_C(y,0,r)=0`.
12. For every year `y`, `k_C(y,1)=e_y`, `e_y=(t₁(y)−t₀(y))/N_y` (subtracting in ℕ before casting to ℚ), and `k_C(y,1)>0`.
13. `E(D)=0`.
14. All three: `E(C) = (96/1223)(326/6555)+(157/1223)(699/41605)+(192/1223)(449/7104)`; `E(C)=83755728/5240292055`; and `E(C)>0`.
15. For every rational weight function `w`, `O^ℚ_w(D)=O^ℚ_w(C)` as arrays (hence for every year, arm and choice). No distributional assumption on `w` is a hypothesis.
16. For every real weight function `w`, `O^ℝ_w(D)=O^ℝ_w(C)` as arrays, again without assumptions on `w`.
17. `¬CampaignIdentified`: it is not true that for every `U`, every `V`, calibration of both and equality of their fixed observed laws imply equality of all three porch-1 campaign means.
18. There does not exist a function `f : (Year → Bool → Bool → ℚ) → ℚ` such that, for every potential-outcome function `Y`, calibration of `Y` implies `f(observedLaw(Y))=E(Y)`. The existential function is outside the universal quantifier over `Y`; the function may use the entire fixed observed-law array.

The quantifiers in distinct conjunction clauses are independent. The universal weights in clauses 15 and 16 are not existential witnesses or hypothesis variables. This theorem specifies particular witnesses `D,C` and exact numerical identities; it does not assert that either witness is the actual world.

## Theorem `SAP.P035.T2`

This theorem has no hypotheses and asserts two conjoined propositions.

First, there exist two potential-outcome functions `U`, then `V`, each with domain and codomain stated above, such that all of the following hold for the same pair (chosen before every subsequent year/arm/label quantifier):

1. For every `y,z`, `m_U(y,z,1)=p(y,z)`.
2. For every `y,z`, `m_V(y,z,1)=p(y,z)`.
3. `observedLaw(U)=observedLaw(V)` as functions on all years, arms and choices.
4. For every `y,z,r`, `δ_U(y,z,r)=0`.
5. For every year `y`, the following hold together: `k_V(y,1)>0`; `k_V(y,1)=p(y,1)−p(y,0)`; and `k_V(y,1)=e_y`.
6. For every year `y`, then every natural `r`, `V(y,1,0,r)=V(y,0,0,r)`: when the campaign is absent, the two porch assignments have identical individual outcomes.

Second, separately from the existential conjunction, `¬CampaignIdentified`, with precisely the universal model quantifiers and fixed design defined above.

This assertion contains a zero-campaign-effect model and another model whose average campaign effect at porch 1 equals the entire supplied positive campaign-present porch contrast, with no individual porch contrast when the campaign is absent. It does not assert an empirical inferential result, a confidence level, a statement about the actual initiative's effect, a causal mediator mechanism, or an instruction to edit prose. Those are descriptions of what is and is not in this proposition, made without consulting a canonical claim or architect record.
