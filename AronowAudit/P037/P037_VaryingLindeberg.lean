/-
Adapted from StatLean/Stat-Lean, module
`StatLean.HypothesisTesting.ForMathlib.LindebergCLT`.
Upstream licence: Apache-2.0, see the file LICENSE-StatLean.txt in this
directory and NOTICE at the repository root.
The probability space and probability measure may differ in each row;
all moment, independence and Lindeberg hypotheses remain explicit.
-/
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Lindeberg central limit theorem for triangular arrays

Suppose that, for each `n`, the finite row
`X n 0, …, X n (m n − 1)` consists of independent, centered, square-integrable variables whose
variances add up to `1` in the limit and which satisfy the **Lindeberg condition**
$$\sum_i \mathbb E\bigl[X_{n,i}^2\,\mathbf 1\{|X_{n,i}| > \varepsilon\}\bigr] \to 0
  \qquad (\forall\,\varepsilon > 0),$$
then the row sums `∑ᵢ Xₙ,ᵢ` converge in distribution to the standard normal law. Rows are
unrelated to each other (no nesting, no common marginal), and their probability
spaces and probability measures may vary with `n`.

## Main results

* `lindeberg_clt` — the triangular-array CLT under the Lindeberg condition.
* `lindeberg_clt_of_bounded` — the uniformly-bounded corollary (`|Xₙ,ᵢ| ≤ cₙ`, `cₙ → 0`),
  which is the form most often applied.

Convergence in distribution is stated in random-variable form, with the underlying
probability space and measure allowed to vary across rows.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 11 (Basic Large-Sample
Theory), §11.2 (Weak Convergence and Central Limit Theorems), **Theorem 11.2.5** (Lindeberg Central
Limit Theorem) for triangular arrays. (`TSH4 §11.2 Thm 11.2.5`.)

**Proof outline.**
* Lindeberg's characteristic-function swapping/telescoping argument bounds
  `|∏ᵢ φₙ,ᵢ(t) − exp(−t²/2)|` by a sum of third-order remainders split at the level `ε`;
  Lévy continuity converts pointwise characteristic-function convergence into weak convergence.
* The variance normalisation is stated as `∑ᵢ Var[Xₙ,ᵢ] → 1` rather than the textbook's
  exact `= 1`; the swapping argument uses this limiting normalization.
* The Lindeberg sums are stated with the *open* truncation set `{ε < |Xₙ,ᵢ|}`. Quantified
  over all `ε > 0` this is equivalent to the closed-set version, and it is the weaker
  hypothesis at each fixed `ε`.
* `lindeberg_clt_of_bounded` does not carry a `MemLp _ 2` hypothesis: a bounded
  measurable function on a probability space is automatically square-integrable.

**Bibliographic comments.** The condition and the theorem are due to J. W. Lindeberg
("Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung,"
*Math. Z.* **15** (1922), 211–225); the triangular-array formulation and the converse
(necessity of the condition under uniform asymptotic negligibility) are due to W. Feller
("Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung," *Math. Z.* **40**
(1935), 521–559). The characteristic-function continuity theorem that closes the argument
is P. Lévy, *Calcul des probabilités*, Gauthier-Villars, 1925.
-/

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal

namespace AronowAudit.P037.LindebergCompletion

variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {P : ∀ n, Measure (Ω n)} {P' : Measure Ω'}
  [∀ n, IsProbabilityMeasure (P n)] [IsProbabilityMeasure P']

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`.** The pointwise estimate driving
Lindeberg's swapping argument:
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both bounds are elementary: the cubic half comes from integrating the exponential's remainder
three times, the quadratic half from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality. -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  -- `|exp (I u)| = 1`.
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  -- Derivative of `u ↦ I u`.
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  -- Continuity of the three integrands.
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  -- Level 0: `‖exp (I z) − 1‖ ≤ z` for `z ≥ 0`.
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0 : ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0 : ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  -- Derivative of `A₁ w = exp (I w) − 1 − I w`.
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  -- Level 1: `‖exp (I z) − 1 − I z‖ ≤ z²/2` for `z ≥ 0`.
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0 : ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0 : ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  -- Derivative of `w ↦ w²/2` (written `w * w / 2`).
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  -- Derivative of `A₂ w = exp (I w) − 1 − I w + w²/2`.
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  -- `A₂ z` as an integral of `A₁ · I`.
  have hA2z : ∀ z : ℝ, (∫ u in (0 : ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  -- The `y ≥ 0` case of the goal (with `|y| = y`).
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0 : ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0 : ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  -- Reduce the goal to `A₂`.
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · -- Reflect to `−y ≥ 0` via conjugation.
    have hz : (0 : ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

-- Telescoping product bound.
private lemma norm_prod_sub_prod_le {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] (s : Finset ι)
    (f g : ι → 𝕜) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) hg'
    have h1 : ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
      calc ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖
            ≤ 1 * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
              mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
        _ = ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := one_mul _
        _ ≤ ∑ i ∈ s, ‖f i - g i‖ := ih hf' hg'
    have h2 : ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ ≤ ‖f a - g a‖ :=
      calc ‖f a - g a‖ * ‖∏ i ∈ s, g i‖
            ≤ ‖f a - g a‖ * 1 := mul_le_mul_of_nonneg_left hpg (norm_nonneg _)
        _ = ‖f a - g a‖ := mul_one _
    linarith

-- Real quadratic remainder for `exp (-u)`.
private lemma abs_exp_neg_sub_one_sub_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp (-u) - (1 - u)| ≤ (3 / 4) * u ^ 2 := by
  have h := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 2) (by norm_num)
  have hs : ∑ m ∈ Finset.range 2, (-u) ^ m / (m.factorial : ℝ) = 1 - u := by
    simp [Finset.sum_range_succ]; ring
  rw [hs, abs_neg, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

-- Convergence to zero from eventual bounds.
private lemma tendsto_zero_of_eventually_le {F : ℕ → ℝ}
    (hF : ∀ᶠ n in atTop, 0 ≤ F n) (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, F n ≤ δ) :
    Tendsto F atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hF] with n hn using lt_of_lt_of_le hb hn
  · filter_upwards [h (b / 2) (by linarith)] with n hn using lt_of_le_of_lt hn (by linarith)

open Complex in
/-- **The analytic core of the Lindeberg CLT.** Under the Lindeberg hypotheses the product
of the row characteristic functions converges pointwise to the standard-normal
characteristic function `t ↦ exp(−t²/2)`. This is the content of Lindeberg's
swapping/telescoping estimate; `lindeberg_clt` merely feeds this pointwise statement through
Lévy's continuity theorem.

Lindeberg's swapping/telescoping estimate, assembled on top of the uniform remainder
bound `norm_cexp_sub_taylor_le`: telescope the two products, bound each factor's
difference by `E[min(|t Xₙᵢ|³/6, t² Xₙᵢ²)]`, split at the level `ε` (the large part is
the Lindeberg sum killed by `hlin`), and match `∏ᵢ (1 − t²σₙᵢ²/2) → exp(−t²/2)`. -/
private lemma tendsto_prod_charFun_lindeberg
    {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → (Ω n) → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hL2 : ∀ n i, MemLp (X n i) 2 (P n))
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; (P n)]) atTop (𝓝 1))
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n)) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => ∏ i, charFun ((P n).map (X n i)) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  -- The `t = 0` case is `∏ 1 → 1`; handle it first, then assume `t ≠ 0`.
  rcases eq_or_ne t 0 with rfl | ht
  · have hone : ∀ n i, charFun ((P n).map (X n i)) 0 = 1 := by
      intro n i
      have : IsProbabilityMeasure ((P n).map (X n i)) :=
        (by infer_instance)
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    have hR : charFun (gaussianReal 0 1) 0 = 1 := by
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    simp only [hone, Finset.prod_const_one, hR]
    exact tendsto_const_nhds
  -- Basic facts about the row entries.
  have hvnn : ∀ n i, (0 : ℝ) ≤ Var[X n i; (P n)] := fun n i => variance_nonneg _ _
  have hunn : ∀ n i, (0 : ℝ) ≤ t ^ 2 * Var[X n i; (P n)] / 2 :=
    fun n i => div_nonneg (mul_nonneg (sq_nonneg t) (hvnn n i)) (by norm_num)
  have hI2 : ∀ n i, Integrable (fun ω => (X n i ω) ^ 2) (P n) := fun n i => (hL2 n i).integrable_sq
  have hI1 : ∀ n i, Integrable (X n i) (P n) := fun n i => (hL2 n i).integrable one_le_two
  have hVeq : ∀ n i, Var[X n i; (P n)] = ∫ ω, (X n i ω) ^ 2 ∂(P n) :=
    fun n i => variance_of_integral_eq_zero (hmeas n i).aemeasurable (hmean n i)
  -- The RHS constant as a genuine exponential.
  have hc : charFun (gaussianReal 0 1) t = Complex.exp (-(↑t ^ 2 / 2)) := by
    rw [charFun_gaussianReal]; push_cast; ring_nf
  -- Measurability of the truncation sets.
  have hset : ∀ ε n i, MeasurableSet {ω | ε < |X n i ω|} := fun ε n i =>
    measurableSet_lt measurable_const (hmeas n i).abs
  -- Nonnegativity of the Lindeberg terms.
  have hLnn : ∀ ε n i, 0 ≤ ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) :=
    fun ε n i => setIntegral_nonneg (hset ε n i) fun ω _ => sq_nonneg _
  -- CENTRAL per-term estimate (crux of the swapping argument).
  have hterm : ∀ ε : ℝ, 0 < ε → ∀ n i,
      ‖charFun ((P n).map (X n i)) t - ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * Var[X n i; (P n)]
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) := by
    intro ε hε n i
    have hsm := hset ε n i
    -- Integrability of the integrand pieces.
    have hIsecond : Integrable (fun ω => Complex.I * (↑(t * X n i ω) : ℂ)) (P n) :=
      (((hI1 n i).const_mul t).ofReal).const_mul Complex.I
    have hIrp : Integrable (fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)) (P n) :=
      ((integrable_const (1 : ℝ)).sub (((hI2 n i).const_mul (t ^ 2)).div_const 2)).ofReal
    have hItX2 : Integrable (fun ω => (t * X n i ω) ^ 2) (P n) := by
      simpa [mul_pow] using (hI2 n i).const_mul (t ^ 2)
    have hIthird : Integrable (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) (P n) := by
      have he : (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => (↑((t * X n i ω) ^ 2) : ℂ) / 2 := by ext ω; rw [← Complex.ofReal_pow]
      rw [he]; exact (hItX2.ofReal).div_const (2 : ℂ)
    have hFmeas : Measurable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp ((hmeas n i).const_mul t)).const_mul Complex.I)
    have hIF : Integrable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) (P n) :=
      (integrable_const (1 : ℝ)).mono' hFmeas.aestronglyMeasurable
        (ae_of_all _ fun ω => le_of_eq (by rw [Complex.norm_exp]; simp))
    have hIG : Integrable (fun ω => 1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) (P n) :=
      ((integrable_const (1 : ℂ)).add hIsecond).sub hIthird
    -- `charFun = ∫ exp`.
    have hFcf : charFun ((P n).map (X n i)) t
        = ∫ ω, Complex.exp (Complex.I * ↑(t * X n i ω)) ∂(P n) := by
      rw [charFun_apply_real, integral_map (hmeas n i).aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      push_cast; ring
    -- The real (variance) part and the vanishing imaginary part.
    have hRp : ∫ ω, (1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) ∂(P n) = 1 - t ^ 2 * Var[X n i; (P n)] / 2 := by
      rw [integral_sub (integrable_const 1) (((hI2 n i).const_mul (t ^ 2)).div_const 2),
        integral_const, probReal_univ, smul_eq_mul, mul_one, integral_div]
      simp only [integral_const_mul]
      rw [← hVeq n i]
    have hTX : ∫ ω, t * X n i ω ∂(P n) = 0 := by
      rw [integral_const_mul t (X n i), hmean n i, mul_zero]
    have hImC : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂(P n) = 0 := by
      have key : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂(P n)
          = Complex.I * ∫ ω, ((t * X n i ω : ℝ) : ℂ) ∂(P n) := integral_const_mul _ _
      rw [key, integral_complex_ofReal, hTX, Complex.ofReal_zero, mul_zero]
    -- `∫ G = 1 - t²σ²/2`.
    have hGint : ∫ ω, (1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) ∂(P n) = ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ) := by
      have hEq : (fun ω => 1 + Complex.I * (↑(t * X n i ω) : ℂ) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)
              + Complex.I * ((t * X n i ω : ℝ) : ℂ) := by
        ext ω; push_cast; ring
      rw [hEq, integral_add hIrp hIsecond, integral_complex_ofReal, hRp, hImC, add_zero]
    -- Assemble the difference as one integral.
    have hab : charFun ((P n).map (X n i)) t - ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ)
        = ∫ ω, (Complex.exp (Complex.I * ↑(t * X n i ω))
            - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)) ∂(P n) := by
      rw [integral_sub hIF hIG, ← hFcf, hGint]
    -- Pointwise remainder bound.
    set g : (Ω n) → ℝ := fun ω => |t| ^ 3 * ε / 6 * (X n i ω) ^ 2
        + t ^ 2 * Set.indicator {ω | ε < |X n i ω|} (fun ω => (X n i ω) ^ 2) ω with hgdef
    have hbound : ∀ ω, ‖Complex.exp (Complex.I * ↑(t * X n i ω))
        - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)‖ ≤ g ω := by
      intro ω
      refine (norm_cexp_sub_taylor_le (t * X n i ω)).trans ?_
      have hnn0 : (0 : ℝ) ≤ |t| ^ 3 * ε / 6 * (X n i ω) ^ 2 :=
        mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hε.le) (by norm_num))
          (sq_nonneg _)
      by_cases hω : ε < |X n i ω|
      · have hωm : ω ∈ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_mem hωm]
        refine (min_le_right _ _).trans ?_
        have h2 : (t * X n i ω) ^ 2 = t ^ 2 * (X n i ω) ^ 2 := by ring
        rw [h2]; linarith [hnn0]
      · have hωm : ω ∉ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_notMem hωm, mul_zero, add_zero]
        refine (min_le_left _ _).trans ?_
        have habs : |t * X n i ω| ^ 3 = |t| ^ 3 * |X n i ω| ^ 3 := by rw [abs_mul, mul_pow]
        have hcube : |X n i ω| ^ 3 ≤ ε * (X n i ω) ^ 2 := by
          have he : |X n i ω| ^ 3 = |X n i ω| * (X n i ω) ^ 2 := by rw [← sq_abs]; ring
          rw [he]; exact mul_le_mul_of_nonneg_right (not_lt.1 hω) (sq_nonneg _)
        rw [habs]; nlinarith [hcube, pow_nonneg (abs_nonneg t) 3]
    have hbint : Integrable g (P n) := by
      rw [hgdef]
      exact ((hI2 n i).const_mul _).add (((hI2 n i).indicator hsm).const_mul _)
    have hg_int : ∫ ω, g ω ∂(P n)
        = |t| ^ 3 * ε / 6 * Var[X n i; (P n)]
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) := by
      rw [hgdef, integral_add ((hI2 n i).const_mul _) (((hI2 n i).indicator hsm).const_mul _)]
      simp only [integral_const_mul, integral_indicator hsm]
      rw [← hVeq n i]
    rw [hab]
    exact (norm_integral_le_of_norm_le hbint (ae_of_all _ hbound)).trans (le_of_eq hg_int)
  -- Uniform asymptotic negligibility of the row variances.
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ i, Var[X n i; (P n)] ≤ c := by
    intro c hc
    have hεpos : (0 : ℝ) < Real.sqrt (c / 2) := Real.sqrt_pos.2 (by linarith)
    have hε2 : Real.sqrt (c / 2) ^ 2 = c / 2 := Real.sq_sqrt (by linarith)
    set ε := Real.sqrt (c / 2) with hεdef
    have hSlt : ∀ᶠ n in atTop,
        ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) ≤ c / 2 :=
      (hlin ε hεpos).eventually_le_const (show (0 : ℝ) < c / 2 by linarith)
    filter_upwards [hSlt] with n hn i
    have hsm := hset ε n i
    have hdecomp : Var[X n i; (P n)]
        = ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n)
          + ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂(P n) := by
      rw [hVeq n i]; exact (integral_add_compl hsm (hI2 n i)).symm
    have hpart1 : ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) ≤ c / 2 :=
      le_trans (Finset.single_le_sum (fun j _ => hLnn ε n j) (Finset.mem_univ i)) hn
    have hpart2 : ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂(P n) ≤ c / 2 := by
      rw [← hε2]
      calc ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂(P n)
          ≤ ∫ ω in {ω | ε < |X n i ω|}ᶜ, ε ^ 2 ∂(P n) := by
            refine setIntegral_mono_on ((hI2 n i).integrableOn) integrableOn_const hsm.compl
              (fun ω hω => ?_)
            simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω
            rw [← sq_abs (X n i ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        _ ≤ ∫ _ω, ε ^ 2 ∂(P n) :=
            setIntegral_le_integral (integrable_const _) (ae_of_all _ fun _ => by positivity)
        _ = ε ^ 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hdecomp]; linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  -- Eventually every row term satisfies `uᵢ = t²σᵢ²/2 ≤ 1`.
  have hev1 : ∀ᶠ n in atTop, ∀ i, t ^ 2 * Var[X n i; (P n)] / 2 ≤ 1 := by
    filter_upwards [hsmall (2 / t ^ 2) (by positivity)] with n hn i
    have hb := (le_div_iff₀ ht2).1 (hn i)
    have hcomm : t ^ 2 * Var[X n i; (P n)] = Var[X n i; (P n)] * t ^ 2 := mul_comm _ _
    linarith
  -- Abbreviations for the two products (`A` characteristic, `B` its quadratic surrogate).
  set A : ℕ → ℂ := fun n => ∏ i, charFun ((P n).map (X n i)) t with hA
  set B : ℕ → ℂ := fun n => ∏ i, ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ) with hB
  -- `∑ᵢ uᵢ → t²/2`.
  have hsum : Tendsto (fun n => ∑ i, t ^ 2 * Var[X n i; (P n)] / 2) atTop (𝓝 (t ^ 2 / 2)) := by
    have h := hvar.const_mul (t ^ 2 / 2)
    have he : ∀ n, ∑ i, t ^ 2 * Var[X n i; (P n)] / 2 = t ^ 2 / 2 * ∑ i, Var[X n i; (P n)] := by
      intro n; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    simpa [he, mul_one] using h
  ------------------------------------------------------------------
  -- The sum of squared quadratic coefficients tends to zero: `∑ᵢ uᵢ² → 0`.
  ------------------------------------------------------------------
  have hGsq : Tendsto (fun n => ∑ i, (t ^ 2 * Var[X n i; (P n)] / 2) ^ 2) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg _) (fun δ hδ => ?_)
    set M : ℝ := δ / (t ^ 2 / 2 + 2) with hMdef
    have hMpos : 0 < M := by rw [hMdef]; exact div_pos hδ (by positivity)
    have hsmallM := hsmall (2 * M / t ^ 2) (div_pos (mul_pos (by norm_num) hMpos) ht2)
    have hsumlt : ∀ᶠ n in atTop, ∑ i, t ^ 2 * Var[X n i; (P n)] / 2 < t ^ 2 / 2 + 1 :=
      hsum.eventually_lt_const (by linarith)
    filter_upwards [hsmallM, hsumlt] with n hnM hnsum
    have huM : ∀ i, t ^ 2 * Var[X n i; (P n)] / 2 ≤ M := by
      intro i
      have hb := (le_div_iff₀ ht2).1 (hnM i)
      have hcomm : t ^ 2 * Var[X n i; (P n)] = Var[X n i; (P n)] * t ^ 2 := mul_comm _ _
      linarith
    calc ∑ i, (t ^ 2 * Var[X n i; (P n)] / 2) ^ 2
        ≤ ∑ i, M * (t ^ 2 * Var[X n i; (P n)] / 2) := by
          apply Finset.sum_le_sum; intro i _
          rw [sq]; exact mul_le_mul_of_nonneg_right (huM i) (hunn n i)
      _ = M * ∑ i, t ^ 2 * Var[X n i; (P n)] / 2 := by rw [Finset.mul_sum]
      _ ≤ M * (t ^ 2 / 2 + 1) := by
          apply mul_le_mul_of_nonneg_left hnsum.le hMpos.le
      _ ≤ δ := by
          rw [hMdef]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [hδ.le]
  ------------------------------------------------------------------
  -- T2 : `B n → charFun gaussian`.
  ------------------------------------------------------------------
  have T2 : Tendsto B atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
    rw [hc, hB]
    -- Reduce to a real product.
    have hLC : Complex.exp (-(↑t ^ 2 / 2)) = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have hBreal : (fun n => ∏ i, ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ))
        = fun n => ((∏ i, (1 - t ^ 2 * Var[X n i; (P n)] / 2) : ℝ) : ℂ) := by
      ext n; rw [Complex.ofReal_prod]
    rw [hLC, hBreal]
    -- Now prove the real limit and lift by `ofReal`.
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    -- Real statement: `∏ (1 - uᵢ) → exp(-t²/2)`.
    have hprodexp : ∀ n, ∏ i, Real.exp (-(t ^ 2 * Var[X n i; (P n)] / 2))
        = Real.exp (-(∑ i, t ^ 2 * Var[X n i; (P n)] / 2)) := by
      intro n; rw [← Real.exp_sum]; rw [← Finset.sum_neg_distrib]
    have hEprod : Tendsto (fun n => ∏ i, Real.exp (-(t ^ 2 * Var[X n i; (P n)] / 2))) atTop
        (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      simp_rw [hprodexp]
      exact (Real.continuous_exp.tendsto _).comp hsum.neg
    have hdiff : Tendsto (fun n => (∏ i, (1 - t ^ 2 * Var[X n i; (P n)] / 2))
        - ∏ i, Real.exp (-(t ^ 2 * Var[X n i; (P n)] / 2))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
        (fun δ hδ => ?_)
      have hsqlt : ∀ᶠ n in atTop, (3 / 4) * ∑ i, (t ^ 2 * Var[X n i; (P n)] / 2) ^ 2 < δ := by
        have hlim : Tendsto (fun n => (3 / 4) * ∑ i, (t ^ 2 * Var[X n i; (P n)] / 2) ^ 2) atTop
            (𝓝 0) := by simpa using hGsq.const_mul (3 / 4)
        exact hlim.eventually_lt_const (by linarith)
      filter_upwards [hev1, hsqlt] with n hn1 hn2
      have htel := norm_prod_sub_prod_le (𝕜 := ℝ) Finset.univ
        (fun i => 1 - t ^ 2 * Var[X n i; (P n)] / 2)
        (fun i => Real.exp (-(t ^ 2 * Var[X n i; (P n)] / 2)))
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hn1 i, hunn n i], by linarith [hunn n i]⟩)
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact (Real.exp_le_one_iff).2 (by linarith [hunn n i]))
      refine htel.trans (le_of_lt (lt_of_le_of_lt ?_ hn2))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 := abs_exp_neg_sub_one_sub_le (u := t ^ 2 * Var[X n i; (P n)] / 2)
        (by rw [abs_le]; exact ⟨by linarith [hunn n i], hn1 i⟩)
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact h2
    have hRealP1 : Tendsto (fun n => ∏ i, (1 - t ^ 2 * Var[X n i; (P n)] / 2)) atTop
        (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      have := hdiff.add hEprod
      simpa using this
    exact hRealP1
  ------------------------------------------------------------------
  -- T1 : `A n - B n → 0`.
  ------------------------------------------------------------------
  have T1 : Tendsto (fun n => A n - B n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
      (fun δ hδ => ?_)
    set ε : ℝ := δ / (|t| ^ 3 + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ (by positivity)
    have hle : |t| ^ 3 * ε ≤ δ := by
      have h0 : (0 : ℝ) < |t| ^ 3 + 1 := by positivity
      rw [hεdef, ← mul_div_assoc, div_le_iff₀ h0]; nlinarith [abs_nonneg t, hδ.le]
    have hVarlt : ∀ᶠ n in atTop, ∑ i, Var[X n i; (P n)] ≤ 2 :=
      (hvar.eventually_lt_const (by norm_num : (1 : ℝ) < 2)).mono fun n h => h.le
    have hLinlt : ∀ᶠ n in atTop,
        t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) < δ / 3 := by
      have hlim : Tendsto (fun n => t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n))
          atTop (𝓝 0) := by simpa using (hlin ε hεpos).const_mul (t ^ 2)
      exact hlim.eventually_lt_const (by linarith)
    filter_upwards [hev1, hVarlt, hLinlt] with n hn1 hn2 hn3
    -- telescoping
    have hpm : ∀ i, IsProbabilityMeasure ((P n).map (X n i)) := fun i =>
      (by infer_instance)
    have htel := norm_prod_sub_prod_le (𝕜 := ℂ) Finset.univ
      (fun i => charFun ((P n).map (X n i)) t)
      (fun i => ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ))
      (fun i _ => norm_charFun_le_one _)
      (fun i _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hn1 i], by linarith [hunn n i]⟩)
    refine htel.trans ?_
    -- sum of per-term bounds
    have hsum2 : ∑ i, ‖charFun ((P n).map (X n i)) t - ((1 - t ^ 2 * Var[X n i; (P n)] / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; (P n)]
          + t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hterm ε hεpos n i
    refine hsum2.trans ?_
    have hterm1 : |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; (P n)] ≤ δ / 3 := by
      have hnn : (0 : ℝ) ≤ |t| ^ 3 * ε / 6 := by positivity
      calc |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; (P n)]
          ≤ |t| ^ 3 * ε / 6 * 2 := by apply mul_le_mul_of_nonneg_left hn2 hnn
        _ ≤ δ / 3 := by nlinarith [hle, hεpos.le, abs_nonneg t]
    linarith [hn3]
  ------------------------------------------------------------------
  -- Combine.
  ------------------------------------------------------------------
  have hcomb := T1.add T2
  simpa using hcomb

/-- **Lindeberg's central limit theorem for triangular arrays.**

For each `n` the row `(X n i)_{i < m n}` consists of independent, centered,
square-integrable random variables; the row variances converge to `1` and the Lindeberg
condition holds. Then the row sums converge in distribution to the standard normal law.

The row sizes `m n` have no separately assumed growth condition; their divergence follows
from the variance and Lindeberg conditions. Rows are unrelated across `n`. -/
theorem lindeberg_clt {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → (Ω n) → ℝ} {Z : Ω' → ℝ}
    -- Every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (X n i))
    -- Entries inside a row are jointly independent (rows are unconstrained).
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- Entries are square-integrable, so the row variances are finite.
    (hL2 : ∀ n i, MemLp (X n i) 2 (P n))
    -- Entries are centered.
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    -- The row variances add up to 1 in the limit (normalisation).
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; (P n)]) atTop (𝓝 1))
    -- The Lindeberg condition.
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n)) atTop (𝓝 0))
    -- `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z P P' where
  forall_aemeasurable n :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hmeas n i).aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hZ.map_eq]
    have hcf : ∀ n, charFun ((P n).map (fun ω => ∑ i, X n i ω)) t
        = ∏ i, charFun ((P n).map (X n i)) t := fun n => by
      rw [iIndepFun.charFun_map_fun_sum_eq_prod (fun i => (hmeas n i).aemeasurable) (hindep n),
        Finset.prod_apply]
    simpa [hcf] using tendsto_prod_charFun_lindeberg hmeas hindep hL2 hmean hvar hlin t

/-- **Uniformly bounded rows.**

If the entries of the `n`-th row are bounded by a constant `c n` tending to `0`, the
Lindeberg condition is automatic (for `ε > 0` the truncation sets are eventually empty), so
the row sums are asymptotically standard normal as soon as the row variances converge
to `1`. This is the form used for randomization and permutation statistics, where the
summands are explicit bounded functions of the data.

No square-integrability hypothesis is needed: a bounded measurable function on a
probability space lies in `L²`. -/
theorem lindeberg_clt_of_bounded {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → (Ω n) → ℝ}
    {c : ℕ → ℝ} {Z : Ω' → ℝ}
    -- Every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (X n i))
    -- Entries inside a row are jointly independent.
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- Entries are centered.
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    -- The row variances add up to 1 in the limit (normalisation).
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; (P n)]) atTop (𝓝 1))
    -- The `n`-th row is bounded by `c n`.
    (hbdd : ∀ n i ω, |X n i ω| ≤ c n)
    -- The bounds are asymptotically negligible.
    (hc : Tendsto c atTop (𝓝 0))
    -- `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z P P' := by
  -- Bounded measurable ⇒ `L²`.
  have hL2 : ∀ n i, MemLp (X n i) 2 (P n) := fun n i =>
    MemLp.of_bound (hmeas n i).aestronglyMeasurable (c n)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbdd n i ω)
  -- Lindeberg condition: for `ε > 0` the truncation sets are eventually empty (`c n < ε`).
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n)) atTop (𝓝 0) := by
    intro ε hε
    have key : ∀ᶠ n in atTop,
        (∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂(P n)) = 0 := by
      filter_upwards [hc.eventually (eventually_lt_nhds hε)] with n hn
      refine Finset.sum_eq_zero fun i _ => ?_
      have hempty : {ω | ε < |X n i ω|} = (∅ : Set (Ω n)) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact le_trans (hbdd n i ω) hn.le
      rw [hempty]; simp
    exact tendsto_const_nhds.congr' (key.mono fun n hn => hn.symm)
  exact lindeberg_clt hmeas hindep hL2 hmean hvar hlin hZ

end AronowAudit.P037.LindebergCompletion
