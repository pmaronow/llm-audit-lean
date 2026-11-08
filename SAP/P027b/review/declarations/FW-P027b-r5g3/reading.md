# Blind reading

This file was saved before opening `claims.json` or `record.json`. The sources inspected were `closure.json`, `SAP/P027b/Defs/Part1.lean`, `SAP/P027b/Defs/Part3.lean`, the target's Challenge file, and the relevant Mathlib definition of real Hölder conjugacy. `scratch/BlindCheck.lean` successfully printed every declaration in the supplied closure, including the two generated proof constants. No canonical-claim or architect-record information is used below.

## SAP.P027b.T24

The theorem's docstring (`SAP/P027b/Challenge/Part1.lean:83–85`) describes a minimum, on every sample, over all positive constant conjugate exponent pairs, attained at `(2,2)`. Its type is the proposition defined at `SAP/P027b/Defs/Part3.lean:51–56`.

### Objects and quantifier order

Universally quantify finite types `U` and `Ω`, with their `Fintype` instances. `U` indexes population units and `Ω` indexes possible sampling outcomes. Next universally quantify a design, namely:

- a real function `w : Ω → ℝ`;
- a proof that `w(t) ≥ 0` for every `t ∈ Ω`;
- a proof that `∑_{t∈Ω} w(t) = 1`;
- an arbitrary selection function `s : Ω → U → Bool`.

For clarity, all sums below are Mathlib finite sums over the entire indicated finite types. Define `I_t(k) = 1` when `s(t,k) = true`, and `I_t(k) = 0` otherwise. Set

`p_k = ∑_{t∈Ω} w(t) I_t(k)`,

`p_kl = ∑_{t∈Ω} w(t) I_t(k) I_t(l)`.

Assume `p_k > 0` for every `k ∈ U`. After this hypothesis, universally quantify an arbitrary real outcome function `y : U → ℝ` and an arbitrary sampling outcome `ω ∈ Ω`.

For this `y,ω`, conclude an equality of two estimates at exponent pair `(2,2)` and, conjunctively, universally quantify real numbers `a,b`. If `a > 0`, `b > 0`, and `a⁻¹ + b⁻¹ = 1`, conclude that the quadratic estimate is at most the estimate using these constant exponents. This is precisely Mathlib `Real.HolderConjugate a b`, via `Real.HolderTriple a b 1`; it implies `a > 1` and `b > 1`.

There is no assumption on the sign of `y`, no independence assumption, no fixed sample size, no positivity assumption on pairwise inclusion probabilities, and no requirement that `w(ω) > 0`. The exponents are constants across all unit pairs; their universal quantifiers occur after those for `y` and `ω`.

### Every SAP definition unfolded

For any real function `f : Ω → ℝ`, `expect D f` is simply `∑_{t∈Ω} w(t) f(t)` (`Defs/Part1.lean:20`). The functions `indicator`, `pi`, and `joint` are exactly `I`, `p_k`, and `p_kl` above (`:22–28`). `Positive D` is the hypothesis `∀ k, p_k > 0` (`:30`). `inclusionCov D k l` is `p_kl - p_k p_l` (`:32`).

Write the following primitive real-valued expressions:

`H(y,ω) = ∑_{k∈U} ∑_{l∈U} [if p_kl > 0 then I_ω(k) I_ω(l) ((p_kl - p_k p_l)/p_kl) (y(k)/p_k) (y(l)/p_l) else 0]`.

`H` is `htVarianceEstimator` (`Defs/Part1.lean:43–46`), including diagonal terms. Let `Z(k,l)` mean `k ≠ l ∧ p_kl = 0`. Both orders of each distinct zero-inclusion pair are counted. For arbitrary exponent functions `A,B : U → U → ℝ`, set

`Y(A,B;y,ω) = ∑_{k∈U} ∑_{l∈U} [if Z(k,l) then I_ω(k)|y(k)|^(A(k,l))/(A(k,l)p_k) + I_ω(l)|y(l)|^(B(k,l))/(B(k,l)p_l) else 0]`.

Here powers with real exponents are Mathlib real powers. This is exactly `youngCorrection` (`:55–59`). In the theorem `A(k,l)=a` and `B(k,l)=b` everywhere. `conservativeEstimator` is the sum `H + Y` (`:61–62`).

`Q(y,ω) = ∑_{k∈U} ∑_{l∈U} [if Z(k,l) then I_ω(k)y(k)^2/(2p_k) + I_ω(l)y(l)^2/(2p_l) else 0]`.

The powers in `Q` are natural-number powers. This is `quadraticCorrection` (`:64–67`), and `c2Estimator` is `H + Q` (`:69–70`).

Thus the entire conclusion is

`H(y,ω) + Y(const 2,const 2;y,ω) = H(y,ω) + Q(y,ω)`

and

`∀ a,b ∈ ℝ, (a>0 ∧ b>0 ∧ a⁻¹+b⁻¹=1) → H(y,ω)+Q(y,ω) ≤ H(y,ω)+Y(const a,const b;y,ω)`.

`Design.mk` constructs the four fields specified above; `Design.weight` and `Design.selected` are projections, not additional predicates. The two other closure entries, `T23Statement._proof_1` and `quadraticCorrection._proof_1`, both prove the Mathlib numeral fact `(1 + 1).AtLeastTwo` by `Nat.instAtLeastTwoHAddOfNat 1`. They introduce no sampling or outcome assumptions and do not encode the comparison.

### Totalization and edge cases

- **Division by zero:** Mathlib real division uses inverse zero equal to zero. Here `p_k > 0` prevents every first-order inclusion denominator from vanishing. Every denominator `p_kl` used by `H` is guarded by `p_kl > 0`; a zero joint probability contributes a literal zero there. In `Y`, the only exponents used are `(2,2)` or a positive conjugate pair, so `A(k,l)p_k` and `B(k,l)p_l` are strictly positive. The denominators `2p_k` in `Q` are positive. No value of an active term relies on zero division. Although the definitions alone accept other exponents and nonpositive first-order probabilities, the target never compares such inputs.
- **Real powers:** the base is always `|y(k)| ≥ 0`, and active exponents are strictly positive. At `y(k)=0`, Mathlib has `0^r=0` for `r>0`, the usual value. Negative-base real powers, `0^0`, and zero to negative powers cannot affect this statement. Natural-number squaring is defined on every real number and equals `|y(k)|^2`.
- **Empty finite types:** `U` may be empty; all double sums are then zero and positivity is vacuous, giving a valid degenerate case. `Ω` cannot be empty for any design, because its normalization would assert `0=1`. Nonempty, nontrivial designs are permitted, so these degenerate cases do not make the universal theorem vacuous.
- **Zero-weight outcomes:** the statement quantifies even outcomes assigned probability zero. A selection function on such an outcome need not respect the almost-sure implication that zero joint probability prevents co-selection. The comparison still has its literal algebraic meaning there. No conditional law or division by outcome probability is used.
- **Signs and ordered pairs:** nonnegative design weights imply `p_kl ≥ 0` and symmetry `p_kl=p_lk`. The zero-pair predicate is symmetric and the sums run over ordered pairs. This symmetry is material to the constant-exponent comparison: collecting both orders yields, for each selected unit, the Young expression `|y(k)|^a/a + |y(k)|^b/b`, whose lower bound is `y(k)^2`.
- **Other conventions:** there are no truncated subtractions, integer or cardinality casts, standalone logarithms, square roots, extended-real conversions, integrals of nonintegrable functions, infinite sums, infima/suprema, limits, or partial-function defaults in the statement's closure. Real subtraction in `p_kl-p_kp_l` is ordinary signed subtraction. Numerals `0,1,2` have their ordinary real or natural-number interpretation. Classical decidability supplies the finite conditional tests and no arbitrary numerical default.

All expectations appearing in these definitions are finite weighted sums of real numbers; their existence does not require extra analytic hypotheses.
