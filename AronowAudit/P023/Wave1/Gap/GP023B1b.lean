import AronowAudit.P023.P023_Audit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
Exact proofs of the P023-T4 fit criterion and numerical sampling separation.
Population coefficients are
identified by explicit rational Gram inverses. Sampling uses the IID strong
law for finitely many moments and a direct local-noise bound for RD.
-/

namespace AronowAudit.P023.Wave1

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section
open scoped BigOperators
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Risk and fit helpers -/

lemma GP023B1b_continuous (a η : ℝ) : Continuous (sigmoid a η) := by
  unfold sigmoid
  exact continuous_const.mul (continuous_const.max
    (continuous_const.min (continuous_id.div_const η)))

lemma GP023B1b_measurable_party : Measurable party := by
  unfold party
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma GP023B1b_abs_le (a η x : ℝ) (ha : 0 ≤ a) : |sigmoid a η x| ≤ a := by
  have hlo : (-1 : ℝ) ≤ max (-1) (min 1 (x / η)) := le_max_left _ _
  have hhi : max (-1) (min 1 (x / η)) ≤ (1 : ℝ) :=
    max_le (by norm_num) (min_le_left _ _)
  rw [sigmoid, abs_mul, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hlo, hhi⟩) ha).trans_eq (mul_one a)

lemma GP023B1b_witness_map_measurable {h : ℝ → ℝ} (hm : Measurable h) :
    Measurable (fun z : ℝ × ℝ => (z.1, 1 / 2 + h z.1 + z.2)) := by
  exact measurable_fst.prodMk ((measurable_const.add (hm.comp measurable_fst)).add
    measurable_snd)

/-- Replace the product with two pushforwards before expanding an integral.
This permits extracting integrability of each nonnegative squared branch. -/
lemma GP023B1b_witness_split (μ : Measure ℝ) [SFinite μ]
    {h : ℝ → ℝ} (hm : Measurable h) :
    witnessLaw μ h =
      (1 / 2 : ℝ≥0∞) • Measure.map (fun x => (x, 1 / 2 + h x + (-1 / 10))) μ +
      (1 / 2 : ℝ≥0∞) • Measure.map (fun x => (x, 1 / 2 + h x + (1 / 10))) μ := by
  have hT := GP023B1b_witness_map_measurable hm
  unfold witnessLaw noiseLaw
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.map_add _ _ hT, Measure.map_smul _ hT.aemeasurable,
    Measure.map_smul _ hT.aemeasurable]
  congr 1 <;>
    rw [Measure.prod_dirac, Measure.map_map hT measurable_prodMk_right] <;> rfl

lemma GP023B1b_witness_probability (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    {h : ℝ → ℝ} (hm : Measurable h) : ProbabilityLaw (witnessLaw μ h) := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  have hminus : Measurable (fun x => (x, 1 / 2 + h x + (-1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  have hplus : Measurable (fun x => (x, 1 / 2 + h x + (1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  unfold ProbabilityLaw
  rw [GP023B1b_witness_split μ hm]
  norm_num [Measure.add_apply, Measure.smul_apply, Measure.map_apply hminus,
    Measure.map_apply hplus, ENNReal.inv_two_add_inv_two]

lemma GP023B1b_witness_margin (μ : Measure ℝ) [SFinite μ]
    {h : ℝ → ℝ} (hm : Measurable h) : marginLaw (witnessLaw μ h) = μ := by
  have hminus : Measurable (fun x => (x, 1 / 2 + h x + (-1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  have hplus : Measurable (fun x => (x, 1 / 2 + h x + (1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  unfold marginLaw
  rw [GP023B1b_witness_split μ hm, Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst hminus, Measure.map_map measurable_fst hplus]
  have he : (fun x : ℝ => Prod.fst (x, 1 / 2 + h x + (-1 / 10))) = id := rfl
  have he' : (fun x : ℝ => Prod.fst (x, 1 / 2 + h x + (1 / 10))) = id := rfl
  simp only [Function.comp_def, he, he', Measure.map_id]
  rw [← add_smul]
  norm_num [ENNReal.inv_two_add_inv_two]

lemma GP023B1b_integrable_witness_iff (μ : Measure ℝ) [SFinite μ]
    {h : ℝ → ℝ} (hm : Measurable h) {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    Integrable g (witnessLaw μ h) ↔
      Integrable (fun x => g (x, 1 / 2 + h x + (-1 / 10))) μ ∧
      Integrable (fun x => g (x, 1 / 2 + h x + (1 / 10))) μ := by
  have hminus : Measurable (fun x => (x, 1 / 2 + h x + (-1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  have hplus : Measurable (fun x => (x, 1 / 2 + h x + (1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  rw [GP023B1b_witness_split μ hm, integrable_add_measure,
    integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0) (by norm_num),
    integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0) (by norm_num)]
  exact and_congr
    (integrable_map_measure hg.aestronglyMeasurable hminus.aemeasurable)
    (integrable_map_measure hg.aestronglyMeasurable hplus.aemeasurable)

lemma GP023B1b_integral_witness (μ : Measure ℝ) [SFinite μ]
    {h : ℝ → ℝ} (hm : Measurable h) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (hi : Integrable g (witnessLaw μ h)) :
    (∫ z, g z ∂witnessLaw μ h) =
      (1 / 2 : ℝ) * (∫ x, g (x, 1 / 2 + h x + (-1 / 10)) ∂μ) +
      (1 / 2 : ℝ) * (∫ x, g (x, 1 / 2 + h x + (1 / 10)) ∂μ) := by
  have hminus : Measurable (fun x => (x, 1 / 2 + h x + (-1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  have hplus : Measurable (fun x => (x, 1 / 2 + h x + (1 / 10))) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  rw [GP023B1b_witness_split μ hm] at hi ⊢
  rw [integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
    integral_smul_measure, integral_smul_measure,
    integral_map hminus.aemeasurable hg.aestronglyMeasurable,
    integral_map hplus.aemeasurable hg.aestronglyMeasurable]
  norm_num [smul_eq_mul]

/-- Integrability is obtained from the two squares before the expansion.
In particular this lemma never expands a nonintegrable Bochner integral. -/
lemma GP023B1b_risk_decomposition (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    {h f : ℝ → ℝ} (hm : Measurable h) (hf : Measurable f)
    (hi : Integrable (fun z : ℝ × ℝ => (z.2 - f z.1)^2) (witnessLaw μ h)) :
    Integrable (fun x => (1 / 2 + h x - f x)^2) μ ∧
    predictionRisk (witnessLaw μ h) f =
      1 / 100 + expectation μ (fun x => (1 / 2 + h x - f x)^2) := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  have hg : Measurable (fun z : ℝ × ℝ => (z.2 - f z.1)^2) :=
    (measurable_snd.sub (hf.comp measurable_fst)).pow_const 2
  obtain ⟨hminus, hplus⟩ := (GP023B1b_integrable_witness_iff μ hm hg).mp hi
  have hs : Integrable (fun x => (1 / 2 + h x - f x)^2) μ := by
    convert ((hminus.add hplus).const_mul (1 / 2 : ℝ)).sub
      (integrable_const (1 / 100 : ℝ)) using 1
    funext x
    change (1 / 2 + h x - f x)^2 =
      ((1 / 2) * ((1 / 2 + h x + (-1 / 10) - f x)^2 +
      (1 / 2 + h x + (1 / 10) - f x)^2)) - 1 / 100
    ring
  refine ⟨hs, ?_⟩
  unfold predictionRisk expectation
  rw [GP023B1b_integral_witness μ hm hg hi]
  calc
    _ = ∫ x, (1 / 2 : ℝ) *
        ((1 / 2 + h x + (-1 / 10) - f x)^2 +
          (1 / 2 + h x + (1 / 10) - f x)^2) ∂μ := by
      rw [integral_const_mul, integral_add hminus hplus]
      ring
    _ = ∫ x, (1 / 100 : ℝ) + (1 / 2 + h x - f x)^2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := by rw [integral_add (integrable_const _) hs]; simp

lemma GP023B1b_risk_lower (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    {h f : ℝ → ℝ} (hm : Measurable h) (hf : Measurable f)
    (hi : Integrable (fun z : ℝ × ℝ => (z.2 - f z.1)^2) (witnessLaw μ h)) :
    (1 / 100 : ℝ) ≤ predictionRisk (witnessLaw μ h) f := by
  rw [(GP023B1b_risk_decomposition μ hp hm hf hi).2]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

lemma GP023B1b_mean_risk (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    {h : ℝ → ℝ} (hm : Measurable h) :
    predictionRisk (witnessLaw μ h) (fun x => 1 / 2 + h x) = 1 / 100 := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  have hf : Measurable (fun x => 1 / 2 + h x) := measurable_const.add hm
  have hg : Measurable (fun z : ℝ × ℝ => (z.2 - (1 / 2 + h z.1))^2) :=
    (measurable_snd.sub (hf.comp measurable_fst)).pow_const 2
  have hi : Integrable (fun z : ℝ × ℝ => (z.2 - (1 / 2 + h z.1))^2)
      (witnessLaw μ h) := by
    apply (GP023B1b_integrable_witness_iff μ hm hg).mpr
    constructor <;>
      convert (integrable_const (1 / 100 : ℝ) : Integrable (fun _ : ℝ =>
        (1 / 100 : ℝ)) μ) using 1 <;> funext x <;> dsimp only <;> ring
  rw [(GP023B1b_risk_decomposition μ hp hm hf hi).2]
  simp [expectation]

lemma GP023B1b_predict_measurable (J : ℕ) (c : Fin (J + 2) → ℝ) :
    Measurable (predict (polynomialDesign J (fun x : ℝ => x) party) c) := by
  have hz (j : Fin (J + 2)) :
      Measurable (fun x : ℝ => polynomialDesign J (fun x : ℝ => x) party x j) := by
    unfold polynomialDesign
    split_ifs
    · exact measurable_const
    · exact GP023B1b_measurable_party
    · exact measurable_id.pow_const _
  exact Finset.measurable_sum _ (fun j _ => (hz j).mul_const (c j))

/-- A finite coefficient sum bounds every design predictor on the margin
support; no measurability assertion about an epsilon-chosen estimator occurs. -/
lemma GP023B1b_predict_bound (J : ℕ) (c : Fin (J + 2) → ℝ)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |predict (polynomialDesign J (fun x : ℝ => x) party) c x| ≤ ∑ j, |c j| := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hz (j : Fin (J + 2)) :
      |polynomialDesign J (fun x : ℝ => x) party x j| ≤ 1 := by
    unfold polynomialDesign
    split_ifs
    · norm_num
    · unfold party
      split_ifs <;> norm_num
    · rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hxabs
  calc
    _ ≤ ∑ j, |polynomialDesign J (fun x : ℝ => x) party x j * c j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hz j) (abs_nonneg (c j))

lemma GP023B1b_supported_integrable (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) {f : ℝ → ℝ} (hf : Measurable f)
    (B : ℝ) (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ B) : Integrable f μ := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hs
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  filter_upwards [hx] with x hxs
  simpa only [Real.norm_eq_abs] using hb x hxs

lemma GP023B1b_regression_risk_integrable (a η : ℝ) (ha : 0 ≤ a)
    (J : ℕ) (c : Fin (J + 2) → ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      (z.2 - predict (polynomialDesign J (fun x : ℝ => x) party) c z.1)^2)
      (witnessLaw uniformMargins (sigmoid a η)) := by
  have hm := (GP023B1b_continuous a η).measurable
  have hf := GP023B1b_predict_measurable J c
  have hg : Measurable (fun z : ℝ × ℝ =>
      (z.2 - predict (polynomialDesign J (fun x : ℝ => x) party) c z.1)^2) :=
    (measurable_snd.sub (hf.comp measurable_fst)).pow_const 2
  letI : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  apply (GP023B1b_integrable_witness_iff uniformMargins hm hg).mpr
  have hbranch (u : ℝ) : Integrable (fun x =>
      (1 / 2 + sigmoid a η x + u -
        predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2) uniformMargins := by
    apply GP023B1b_supported_integrable uniformMargins uniform_law_normalized.1
      uniform_law_normalized.2
      (((measurable_const.add hm).add measurable_const).sub hf |>.pow_const 2)
      ((1 / 2 + a + |u| + ∑ j, |c j|)^2)
    intro x hx
    have hbound : |1 / 2 + sigmoid a η x + u -
        predict (polynomialDesign J (fun x : ℝ => x) party) c x| ≤
        1 / 2 + a + |u| + ∑ j, |c j| := by
      calc
        _ ≤ |1 / 2 + sigmoid a η x + u| +
            |predict (polynomialDesign J (fun x : ℝ => x) party) c x| := abs_sub _ _
        _ ≤ (|1 / 2 + sigmoid a η x| + |u|) + ∑ j, |c j| :=
          add_le_add (abs_add_le _ _) (GP023B1b_predict_bound J c x hx)
        _ ≤ ((|(1 / 2 : ℝ)| + |sigmoid a η x|) + |u|) + ∑ j, |c j| := by
          linarith [abs_add_le (1 / 2 : ℝ) (sigmoid a η x)]
        _ ≤ _ := by
          norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          linarith [GP023B1b_abs_le a η x ha]
    rw [abs_pow]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hbound
  exact ⟨hbranch (-1 / 10), hbranch (1 / 10)⟩

/-- The order-theoretic part of the fit argument is independent of attaining
the infimum. The sole upper-bound input is one explicitly feasible risk. -/
lemma GP023B1b_infimum_bounds (ν : Measure (ℝ × ℝ)) (J : ℕ) (δ : ℝ)
    (hlo : ∀ c : Fin (J + 2) → ℝ,
      (1 / 100 : ℝ) ≤ predictionRisk ν
        (predict (polynomialDesign J (fun x : ℝ => x) party) c))
    (hfeasible : ∃ c : Fin (J + 2) → ℝ,
      predictionRisk ν (predict (polynomialDesign J (fun x : ℝ => x) party) c) ≤
        1 / 100 + δ) :
    1 / 100 ≤ fittedRisk ν J ∧ fittedRisk ν J ≤ 1 / 100 + δ ∧
    (∀ f : ℝ → ℝ, (1 / 100 : ℝ) ≤ predictionRisk ν f →
      fittedRisk ν J - predictionRisk ν f ≤ δ) ∧
    (fittedRisk ν J - 1 / 100) / fittedRisk ν J ≤ 100 * δ := by
  let S : Set ℝ := {e | ∃ c : Fin (J + 2) → ℝ,
    e = predictionRisk ν (predict (polynomialDesign J (fun x : ℝ => x) party) c)}
  have hne : S.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hb : BddBelow S := ⟨1 / 100, by
    rintro e ⟨c, rfl⟩
    exact hlo c⟩
  have hl : (1 / 100 : ℝ) ≤ fittedRisk ν J := by
    apply le_csInf hne
    rintro e ⟨c, rfl⟩
    exact hlo c
  obtain ⟨c, hc⟩ := hfeasible
  have hu : fittedRisk ν J ≤ 1 / 100 + δ :=
    (csInf_le hb (show predictionRisk ν
      (predict (polynomialDesign J (fun x : ℝ => x) party) c) ∈ S from
        ⟨c, rfl⟩)).trans hc
  have hδ : 0 ≤ δ := by linarith
  have hR : 0 < fittedRisk ν J := by linarith
  refine ⟨hl, hu, ?_, ?_⟩
  · intro f hf
    linarith
  · apply (div_le_iff₀ hR).mpr
    have hmul : δ ≤ 100 * δ * fittedRisk ν J := by
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hl)]
    linarith

/-- The squared approximation error is a continuous even tent, including
at the tie, even though the party indicator itself is discontinuous there. -/
lemma GP023B1b_error_eq (a η x : ℝ) (hη : 0 < η) :
    (sigmoid a η x - a * (2 * party x - 1))^2 =
      a^2 * (max (1 - |x| / η) 0)^2 := by
  by_cases hx : 0 ≤ x
  · have hxdiv : 0 ≤ x / η := div_nonneg hx hη.le
    rw [party, if_pos hx, abs_of_nonneg hx]
    by_cases hxe : x ≤ η
    · have hd : x / η ≤ 1 := (div_le_one hη).mpr hxe
      rw [sigmoid, min_eq_right hd, max_eq_right (by linarith : (-1 : ℝ) ≤ x / η),
        max_eq_left (by linarith : (0 : ℝ) ≤ 1 - x / η)]
      ring
    · have hd : 1 ≤ x / η := (one_le_div hη).mpr (le_of_not_ge hxe)
      rw [sigmoid, min_eq_left hd, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
        max_eq_right (by linarith : 1 - x / η ≤ (0 : ℝ))]
      ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hxdiv : x / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg hxneg.le hη.le
    rw [party, if_neg hx, abs_of_neg hxneg]
    by_cases hxe : -η ≤ x
    · have hd : (-1 : ℝ) ≤ x / η := (le_div_iff₀ hη).mpr (by linarith)
      have ht : 0 ≤ 1 - -x / η := by rw [neg_div]; linarith
      rw [sigmoid, min_eq_right (by linarith : x / η ≤ (1 : ℝ)),
        max_eq_right hd, max_eq_left ht]
      ring
    · have hd : x / η ≤ (-1 : ℝ) := (div_le_iff₀ hη).mpr (by linarith)
      have ht : 1 - -x / η ≤ 0 := by rw [neg_div]; linarith
      rw [sigmoid, min_eq_right (by linarith : x / η ≤ (1 : ℝ)),
        max_eq_left hd, max_eq_right ht]
      ring

lemma GP023B1b_error_integral (a η : ℝ) (hη : 0 < η ∧ η ≤ 1) :
    expectation uniformMargins
      (fun x => (sigmoid a η x - a * (2 * party x - 1))^2) = a^2 * η / 3 := by
  let g : ℝ → ℝ := fun x => a^2 * (max (1 - |x| / η) 0)^2
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have he : (fun x => (sigmoid a η x - a * (2 * party x - 1))^2) = g := by
    funext x
    exact GP023B1b_error_eq a η x hη.1
  have heven (x : ℝ) : g (-x) = g x := by simp only [g, abs_neg]
  have hnear : (∫ x in (0 : ℝ)..η, g x) = a^2 * η / 3 := by
    calc
      _ = ∫ x in (0 : ℝ)..η, a^2 * (1 - 2 * x / η + x^2 / η^2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [uIcc_of_le hη.1.le] at hx
        have hd : x / η ≤ 1 := (div_le_one hη.1).mpr hx.2
        dsimp only [g]
        rw [abs_of_nonneg hx.1, max_eq_left (by linarith : 0 ≤ 1 - x / η)]
        ring
      _ = a^2 * η / 3 := by
        have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 η :=
          intervalIntegrable_const
        have hx : IntervalIntegrable (fun x : ℝ => 2 * x / η) volume 0 η := by
          apply Continuous.intervalIntegrable
          fun_prop
        have hx2 : IntervalIntegrable (fun x : ℝ => x^2 / η^2) volume 0 η := by
          apply Continuous.intervalIntegrable
          fun_prop
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (h1.sub hx) hx2,
          intervalIntegral.integral_sub h1 hx,
          intervalIntegral.integral_div, intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, integral_id,
          integral_pow]
        norm_num only [zero_pow (by decide : 2 ≠ 0),
          zero_pow (by decide : 3 ≠ 0), sub_zero, smul_eq_mul, mul_one]
        field_simp [ne_of_gt hη.1]
        <;> ring
  have hfar : (∫ x in η..(1 : ℝ), g x) = 0 := by
    calc
      _ = ∫ _x in η..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [uIcc_of_le hη.2] at hx
        have hx0 : 0 ≤ x := hη.1.le.trans hx.1
        have hd : 1 ≤ x / η := (one_le_div hη.1).mpr hx.1
        dsimp only [g]
        rw [abs_of_nonneg hx0, max_eq_right (by linarith : 1 - x / η ≤ 0)]
        ring
      _ = 0 := by simp
  have hpos : (∫ x in (0 : ℝ)..1, g x) = a^2 * η / 3 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (a := 0) (b := η))
      (hg.intervalIntegrable (a := η) (b := 1)), hnear, hfar, add_zero]
  have hneg : (∫ x in (-1 : ℝ)..0, g x) = a^2 * η / 3 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, g (-x) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := g) (a := (0 : ℝ)) (b := 1)).symm
      _ = _ := by simp_rw [heven]; exact hpos
  unfold expectation uniformMargins
  rw [he, integral_smul_measure]
  change (1 / 2 : ℝ≥0∞).toReal • (∫ x in Icc (-1 : ℝ) 1, g x) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (a := -1) (b := 0))
    (hg.intervalIntegrable (a := 0) (b := 1)), hneg, hpos]
  norm_num [smul_eq_mul]
  <;> ring

def GP023B1b_feasible (J : ℕ) (a : ℝ) : Fin (J + 2) → ℝ :=
  fun j => if j.val = 0 then 1 / 2 - a else if j.val = 1 then 2 * a else 0

lemma GP023B1b_feasible_predict (J : ℕ) (a x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (GP023B1b_feasible J a) x =
      1 / 2 + a * (2 * party x - 1) := by
  classical
  have hsum (j : Fin (J + 2)) :
      polynomialDesign J (fun x : ℝ => x) party x j * GP023B1b_feasible J a j =
        (if j = 0 then 1 / 2 - a else 0) +
        (if j = 1 then 2 * a * party x else 0) := by
    by_cases h0 : j = 0
    · subst j
      simp [polynomialDesign, GP023B1b_feasible]
    · by_cases h1 : j = 1
      · subst j
        simp [polynomialDesign, GP023B1b_feasible]
        ring
      · have hv0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        have hv1 : j.val ≠ 1 := fun h => h1 (Fin.ext h)
        simp [polynomialDesign, GP023B1b_feasible, hv0, hv1, h0, h1]
  unfold predict
  simp_rw [hsum, Finset.sum_add_distrib]
  simp
  <;> ring

/-- Risk bounds for the sigmoid witness and its polynomial fits. -/
theorem GP023B1b_risk_claims (a η : ℝ) (ha : 0 < a) (hη : 0 < η ∧ η ≤ 1) :
    let ν := witnessLaw uniformMargins (sigmoid a η)
    ProbabilityLaw ν ∧ marginLaw ν = uniformMargins ∧
    predictionRisk ν (fun x => 1/2+sigmoid a η x) = 1/100 ∧
    (∀ J, 1 ≤ J → 1/100 ≤ fittedRisk ν J ∧ fittedRisk ν J ≤ 1/100+a^2*η/3 ∧
      (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
        fittedRisk ν J - predictionRisk ν f ≤ a^2*η/3) ∧
      (fittedRisk ν J-1/100)/(fittedRisk ν J) ≤ 100*a^2*η/3) := by
  dsimp only
  letI : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  have hm := (GP023B1b_continuous a η).measurable
  refine ⟨GP023B1b_witness_probability _ uniform_law_normalized.1 hm,
    GP023B1b_witness_margin _ hm,
    GP023B1b_mean_risk _ uniform_law_normalized.1 hm, ?_⟩
  intro J hJ
  have hlo (c : Fin (J + 2) → ℝ) :
      (1 / 100 : ℝ) ≤ predictionRisk (witnessLaw uniformMargins (sigmoid a η))
        (predict (polynomialDesign J (fun x : ℝ => x) party) c) :=
    GP023B1b_risk_lower _ uniform_law_normalized.1 hm
      (GP023B1b_predict_measurable J c) (GP023B1b_regression_risk_integrable a η ha.le J c)
  have hfeasible : ∃ c : Fin (J + 2) → ℝ,
      predictionRisk (witnessLaw uniformMargins (sigmoid a η))
        (predict (polynomialDesign J (fun x : ℝ => x) party) c) ≤ 1 / 100 + a^2*η/3 := by
    refine ⟨GP023B1b_feasible J a, le_of_eq ?_⟩
    rw [(GP023B1b_risk_decomposition _ uniform_law_normalized.1 hm
      (GP023B1b_predict_measurable J _) (GP023B1b_regression_risk_integrable a η ha.le J _)).2]
    congr 1
    have he : (fun x => (1 / 2 + sigmoid a η x -
        predict (polynomialDesign J (fun x : ℝ => x) party) (GP023B1b_feasible J a) x)^2) =
        (fun x => (sigmoid a η x - a * (2 * party x - 1))^2) := by
      funext x
      rw [GP023B1b_feasible_predict]
      ring
    rw [he]
    exact GP023B1b_error_integral a η hη
  obtain ⟨hl, hu, himprove, hrel⟩ := GP023B1b_infimum_bounds _ J (a^2*η/3) hlo hfeasible
  refine ⟨hl, hu, ?_, ?_⟩
  · intro f hf hi
    exact himprove f (GP023B1b_risk_lower _ uniform_law_normalized.1 hm hf hi)
  · convert hrel using 1 <;> ring


/-! The finite population moment equations. -/

lemma GP023B1b_uniform_halves {f fm fp : ℝ → ℝ}
    (hm : Continuous fm) (hp : Continuous fp)
    (hem : ∀ x ∈ Ioo (-1 : ℝ) 0, f x = fm x)
    (hep : ∀ x ∈ Ioo (0 : ℝ) 1, f x = fp x) :
    expectation uniformMargins f = (1 / 2 : ℝ) *
      ((∫ x in (-1 : ℝ)..0, fm x) + (∫ x in (0 : ℝ)..1, fp x)) := by
  have hem' : (uIoo (-1 : ℝ) 0).EqOn f fm := by
    rw [uIoo_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
    exact fun x hx => hem x hx
  have hep' : (uIoo (0 : ℝ) 1).EqOn f fp := by
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun x hx => hep x hx
  have him : IntervalIntegrable f volume (-1) 0 :=
    (hm.intervalIntegrable (-1) 0).congr_uIoo (fun x hx => (hem' hx).symm)
  have hip : IntervalIntegrable f volume 0 1 :=
    (hp.intervalIntegrable 0 1).congr_uIoo (fun x hx => (hep' hx).symm)
  unfold expectation uniformMargins
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals him hip,
    intervalIntegral.integral_congr_uIoo hem', intervalIntegral.integral_congr_uIoo hep']
  norm_num [smul_eq_mul]

lemma GP023B1b_power_moment (n : ℕ) :
    expectation uniformMargins (fun x => x^n) =
      (1 - (-1 : ℝ)^(n+1)) / (2 * ((n : ℝ)+1)) := by
  rw [GP023B1b_uniform_halves (f := fun x : ℝ => x^n)
    (fm := fun x : ℝ => x^n) (fp := fun x : ℝ => x^n)
    (continuous_id'.pow n) (continuous_id'.pow n)
    (fun _ _ => rfl) (fun _ _ => rfl), integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, zero_sub,
    one_pow, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

lemma GP023B1b_party_power_moment (n : ℕ) :
    expectation uniformMargins (fun x => party x * x^n) =
      1 / (2 * ((n : ℝ)+1)) := by
  rw [GP023B1b_uniform_halves (f := fun x => party x * x^n) (fm := fun _ => 0)
    (fp := fun x : ℝ => x^n) continuous_const (continuous_id'.pow n)
    (fun x hx => by simp [party, not_le.mpr hx.2])
    (fun x hx => by simp [party, hx.1.le]), intervalIntegral.integral_zero, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
    Nat.cast_add, Nat.cast_one, zero_add]
  field_simp
  <;> ring

lemma GP023B1b_column_bound (J : ℕ) (j : Fin (J+2)) (x : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    |polynomialDesign J (fun x : ℝ => x) party x j| ≤ 1 := by
  unfold polynomialDesign
  split_ifs
  · norm_num
  · unfold party
    split_ifs <;> norm_num
  · rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hx)

lemma GP023B1b_column_measurable (J : ℕ) (j : Fin (J+2)) :
    Measurable (fun x => polynomialDesign J (fun x : ℝ => x) party x j) := by
  unfold polynomialDesign
  split_ifs
  · exact measurable_const
  · exact GP023B1b_measurable_party
  · exact measurable_id.pow_const _

lemma GP023B1b_gram_integrable (J : ℕ) (i j : Fin (J+2)) :
    Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x i *
      polynomialDesign J (fun x : ℝ => x) party x j) uniformMargins := by
  apply GP023B1b_supported_integrable _ uniform_law_normalized.1
    uniform_law_normalized.2
    ((GP023B1b_column_measurable J i).mul (GP023B1b_column_measurable J j)) 1
  intro x hx
  change |polynomialDesign J (fun x : ℝ => x) party x i *
    polynomialDesign J (fun x : ℝ => x) party x j| ≤ 1
  rw [abs_mul]
  simpa using mul_le_mul (GP023B1b_column_bound J i x hx)
    (GP023B1b_column_bound J j x hx) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

lemma GP023B1b_positive_clip (a η x : ℝ) (hη : 0 < η) (hx : 0 ≤ x) :
    sigmoid a η x = a * min 1 (x/η) := by
  unfold sigmoid
  rw [max_eq_right (le_trans (by norm_num : (-1 : ℝ) ≤ 0)
    (le_min (by norm_num) (div_nonneg hx hη.le)))]

lemma GP023B1b_sigmoid_odd (a η x : ℝ) :
    sigmoid a η (-x) = -sigmoid a η x := by
  unfold sigmoid
  rw [neg_div]
  by_cases hlo : x/η ≤ -1
  · rw [min_eq_right (by linarith : x/η ≤ 1), max_eq_left hlo,
      min_eq_left (by linarith : 1 ≤ -(x/η)), max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
    ring
  · by_cases hhi : 1 ≤ x/η
    · rw [min_eq_left hhi, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
        min_eq_right (by linarith : -(x/η) ≤ 1), max_eq_left (by linarith : -(x/η) ≤ -1)]
      ring
    · rw [min_eq_right (by linarith : x/η ≤ 1), max_eq_right (by linarith : (-1 : ℝ) ≤ x/η),
        min_eq_right (by linarith : -(x/η) ≤ 1), max_eq_right (by linarith : (-1 : ℝ) ≤ -(x/η))]
      ring

lemma GP023B1b_positive_sigmoid_moment (a η : ℝ) (hη : 0 < η ∧ η ≤ 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, x^n * sigmoid a η x) =
      a * (1 / ((n : ℝ)+1) - η^(n+1) / (((n : ℝ)+1)*((n : ℝ)+2))) := by
  have hc : Continuous (fun x => x^n * sigmoid a η x) :=
    (continuous_id'.pow n).mul (GP023B1b_continuous a η)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 η) (hc.intervalIntegrable η 1)]
  have hn : (∫ x in (0 : ℝ)..η, x^n * sigmoid a η x) =
      (a/η) * η^(n+2) / ((n : ℝ)+2) := by
    calc
      _ = ∫ x in (0 : ℝ)..η, (a/η) * x^(n+1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [uIcc_of_le hη.1.le] at hx
        rw [GP023B1b_positive_clip a η x hη.1 hx.1,
          min_eq_right ((div_le_one hη.1).mpr hx.2), pow_succ]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp only [Nat.cast_add, Nat.cast_one, zero_pow (by omega : n+1+1 ≠ 0), sub_zero]
        rw [show n+1+1 = n+2 by omega]
        ring
  have hf : (∫ x in η..(1 : ℝ), x^n * sigmoid a η x) =
      a * (1 - η^(n+1)) / ((n : ℝ)+1) := by
    calc
      _ = ∫ x in η..(1 : ℝ), a * x^n := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [uIcc_of_le hη.2] at hx
        rw [GP023B1b_positive_clip a η x hη.1 (hη.1.le.trans hx.1),
          min_eq_left ((one_le_div hη.1).mpr hx.1)]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp only [one_pow, Nat.cast_add, Nat.cast_one]
        ring
  rw [hn, hf]
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  field_simp [hη.1.ne', ne_of_gt (show (0 : ℝ) < (n : ℝ)+1 by positivity),
    ne_of_gt (show (0 : ℝ) < (n : ℝ)+2 by positivity)]
  <;> ring

lemma GP023B1b_sigmoid_power_moment (a η : ℝ) (hη : 0 < η ∧ η ≤ 1) (n : ℕ) :
    expectation uniformMargins (fun x => x^n * sigmoid a η x) =
      (1 + (-1 : ℝ)^(n+1)) / 2 *
        (a * (1 / ((n : ℝ)+1) - η^(n+1) / (((n : ℝ)+1)*((n : ℝ)+2)))) := by
  have hc : Continuous (fun x => x^n * sigmoid a η x) :=
    (continuous_id'.pow n).mul (GP023B1b_continuous a η)
  rw [GP023B1b_uniform_halves hc hc (fun _ _ => rfl) (fun _ _ => rfl)]
  have hm : (∫ x in (-1 : ℝ)..0, x^n * sigmoid a η x) =
      (-1 : ℝ)^(n+1) * (∫ x in (0 : ℝ)..1, x^n * sigmoid a η x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (-x)^n * sigmoid a η (-x) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := fun x => x^n * sigmoid a η x)
            (a := (0 : ℝ)) (b := 1)).symm
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        rw [GP023B1b_sigmoid_odd, neg_pow, pow_succ]
        ring
  rw [hm, GP023B1b_positive_sigmoid_moment a η hη n]
  ring

lemma GP023B1b_party_sigmoid_moment (a η : ℝ) (hη : 0 < η ∧ η ≤ 1) :
    expectation uniformMargins (fun x => party x * sigmoid a η x) =
      a / 2 * (1 - η/2) := by
  rw [GP023B1b_uniform_halves (f := fun x => party x * sigmoid a η x)
    (fm := fun _ => 0) continuous_const (GP023B1b_continuous a η)
    (fun x hx => by simp [party, not_le.mpr hx.2])
    (fun x hx => by simp [party, hx.1.le]), intervalIntegral.integral_zero]
  have hp := GP023B1b_positive_sigmoid_moment a η hη 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, zero_add, pow_one] at hp
  rw [hp]
  ring

def GP023B1b_gram : Matrix (Fin 9) (Fin 9) ℝ := ![
  ![1, (1/2), 0, (1/3), 0, (1/5), 0, (1/7), 0],
  ![(1/2), (1/2), (1/4), (1/6), (1/8), (1/10), (1/12), (1/14), (1/16)],
  ![0, (1/4), (1/3), 0, (1/5), 0, (1/7), 0, (1/9)],
  ![(1/3), (1/6), 0, (1/5), 0, (1/7), 0, (1/9), 0],
  ![0, (1/8), (1/5), 0, (1/7), 0, (1/9), 0, (1/11)],
  ![(1/5), (1/10), 0, (1/7), 0, (1/9), 0, (1/11), 0],
  ![0, (1/12), (1/7), 0, (1/9), 0, (1/11), 0, (1/13)],
  ![(1/7), (1/14), 0, (1/9), 0, (1/11), 0, (1/13), 0],
  ![0, (1/16), (1/9), 0, (1/11), 0, (1/13), 0, (1/15)]]

def GP023B1b_gramInverse : Matrix (Fin 9) (Fin 9) ℝ := ![
  ![(5694929/313600), (-32768/1225), 72, (-11025/256), -264, (24255/256), (10296/25), (-15015/256), (-10296/49)],
  ![(-32768/1225), (65536/1225), -144, 0, 528, 0, (-20592/25), 0, (20592/49)],
  ![72, -144, (33075/64), 0, (-72765/32), 0, (243243/64), 0, (-32175/16)],
  ![(-11025/256), 0, 0, (178605/256), 0, (-467775/256), 0, (315315/256), 0],
  ![-264, 528, (-72765/32), 0, (190575/16), 0, (-693693/32), 0, (96525/8)],
  ![(24255/256), 0, 0, (-467775/256), 0, (1334025/256), 0, (-945945/256), 0],
  ![(10296/25), (-20592/25), (243243/64), 0, (-693693/32), 0, (66405339/1600), 0, (-382239/16)],
  ![(-15015/256), 0, 0, (315315/256), 0, (-945945/256), 0, (693693/256), 0],
  ![(-10296/49), (20592/49), (-32175/16), 0, (96525/8), 0, (-382239/16), 0, (2760615/196)]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma GP023B1b_gram_inverse : GP023B1b_gram * GP023B1b_gramInverse = 1 := by
  apply Matrix.ext
  intro i j
  change (∑ k : Fin 9, GP023B1b_gram i k * GP023B1b_gramInverse k j) =
    if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    norm_num [GP023B1b_gram, GP023B1b_gramInverse, Fin.sum_univ_succ]

lemma GP023B1b_party_square (x : ℝ) : party x * party x = party x := by
  unfold party
  split_ifs <;> norm_num

set_option maxRecDepth 4096 in
lemma GP023B1b_gram_moment (i j : Fin 9) :
    expectation uniformMargins (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x i *
      polynomialDesign 7 (fun x : ℝ => x) party x j) = GP023B1b_gram i j := by
  fin_cases i <;> fin_cases j
  · have he := GP023B1b_power_moment 0
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 0
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 1
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 2
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 3
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 0
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 0
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 1
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 2
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 3
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 1
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 1
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 2
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 3
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 2
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 2
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 3
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 9
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 3
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 3
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 9
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 10
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 4
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 9
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 10
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 11
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 5
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 9
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 10
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 11
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 12
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 6
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 9
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 10
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 11
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 12
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 13
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_party_power_moment 7
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 8
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 9
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 10
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 11
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 12
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 13
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring
  · have he := GP023B1b_power_moment 14
    convert he using 1 <;>
      norm_num [GP023B1b_gram, polynomialDesign, GP023B1b_party_square] <;>
      congr 1 <;> funext x <;> ring

lemma GP023B1b_response_integrable (a η : ℝ) (ha : 0 ≤ a) (j : Fin 9) :
    Integrable (fun x => polynomialDesign 7 (fun x : ℝ => x) party x j *
      (1/2 + sigmoid a η x)) uniformMargins := by
  apply GP023B1b_supported_integrable _ uniform_law_normalized.1
    uniform_law_normalized.2
    ((GP023B1b_column_measurable 7 j).mul
      (measurable_const.add (GP023B1b_continuous a η).measurable)) (1/2+a)
  intro x hx
  change |polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2+sigmoid a η x)| ≤ 1/2+a
  rw [abs_mul]
  have hb : |(1/2 : ℝ)+sigmoid a η x| ≤ 1/2+a := by
    calc
      _ ≤ |(1/2 : ℝ)| + |sigmoid a η x| := abs_add_le _ _
      _ ≤ _ := by norm_num; linarith [GP023B1b_abs_le a η x ha]
  exact (mul_le_mul_of_nonneg_right (GP023B1b_column_bound 7 j x hx) (abs_nonneg _)).trans
    (by simpa using hb)

lemma GP023B1b_normal_iff (a η : ℝ) (ha : 0 ≤ a) (c : Fin 9 → ℝ) :
    PopNormal uniformMargins 7 (fun x => 1/2 + sigmoid a η x) c ↔
      GP023B1b_gram.mulVec c = fun j => expectation uniformMargins
        (fun x => polynomialDesign 7 (fun x : ℝ => x) party x j *
          (1/2 + sigmoid a η x)) := by
  have hp (j : Fin 9) :
      expectation uniformMargins (fun x => polynomialDesign 7 (fun x : ℝ => x) party x j *
        predict (polynomialDesign 7 (fun x : ℝ => x) party) c x) =
      GP023B1b_gram.mulVec c j := by
    unfold expectation predict Matrix.mulVec dotProduct
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun i _ => (GP023B1b_gram_integrable 7 j i).mul_const (c i))]
    simp_rw [integral_mul_const]
    change (∑ i, expectation uniformMargins (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j *
        polynomialDesign 7 (fun x : ℝ => x) party x i) * c i) = _
    simp_rw [GP023B1b_gram_moment]
  have hi (j : Fin 9) : Integrable (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j *
        predict (polynomialDesign 7 (fun x : ℝ => x) party) c x) uniformMargins := by
    simp only [predict, Finset.mul_sum, ← mul_assoc]
    exact integrable_finsetSum _ (fun i _ => (GP023B1b_gram_integrable 7 j i).mul_const (c i))
  unfold PopNormal
  simp_rw [mul_sub, expectation, integral_sub (GP023B1b_response_integrable a η ha _) (hi _)]
  change (∀ j, expectation uniformMargins (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2 + sigmoid a η x)) -
      expectation uniformMargins (fun x => polynomialDesign 7 (fun x : ℝ => x) party x j *
        predict (polynomialDesign 7 (fun x : ℝ => x) party) c x) = 0) ↔ _
  simp_rw [hp, sub_eq_zero]
  constructor
  · intro h
    funext j
    exact (h j).symm
  · intro h j
    exact (congrFun h j).symm

lemma GP023B1b_coefficient_matrix (a η : ℝ) (ha : 0 ≤ a) :
    populationCoefficient uniformMargins 7 (fun x => 1/2 + sigmoid a η x) =
      GP023B1b_gramInverse.mulVec (fun j => expectation uniformMargins
        (fun x => polynomialDesign 7 (fun x : ℝ => x) party x j *
          (1/2 + sigmoid a η x))) 1 := by
  have hex : ∃ c, PopNormal uniformMargins 7 (fun x => 1/2 + sigmoid a η x) c := by
    obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
      ⟨GP023B1b_gramInverse, GP023B1b_gram_inverse⟩
        (fun j => expectation uniformMargins (fun x =>
          polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2 + sigmoid a η x)))
    exact ⟨c, (GP023B1b_normal_iff a η ha c).mpr hc⟩
  have hc := (GP023B1b_normal_iff a η ha _).mp (Classical.epsilon_spec hex)
  have hleft : GP023B1b_gramInverse * GP023B1b_gram = 1 :=
    mul_eq_one_comm.mp GP023B1b_gram_inverse
  have he := congrArg (GP023B1b_gramInverse.mulVec) hc
  rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] at he
  exact congrFun he 1

def GP023B1b_response (a η : ℝ) : Fin 9 → ℝ :=
  ![1/2, 1/4+a/2*(1-η/2), a*(1/2-η^2/6), 1/6,
    a*(1/4-η^4/20), 1/10, a*(1/6-η^6/42), 1/14, a*(1/8-η^8/72)]

lemma GP023B1b_response_moment (a η : ℝ) (ha : 0 ≤ a) (hη : 0 < η ∧ η ≤ 1)
    (j : Fin 9) :
    expectation uniformMargins (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2 + sigmoid a η x)) =
        GP023B1b_response a η j := by
  have hi : Integrable (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2 : ℝ)) uniformMargins := by
    convert (GP023B1b_gram_integrable 7 j 0).mul_const (1/2 : ℝ) using 1
    congr 1
    funext x
    simp [polynomialDesign]
  have hs : Integrable (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j * sigmoid a η x) uniformMargins := by
    convert (GP023B1b_response_integrable a η ha j).sub hi using 1
    funext x
    change polynomialDesign 7 (fun x : ℝ => x) party x j * sigmoid a η x =
      polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2+sigmoid a η x) -
        polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2)
    ring
  have he : expectation uniformMargins (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j * (1/2 + sigmoid a η x)) =
      (1/2 : ℝ) * GP023B1b_gram j 0 + expectation uniformMargins (fun x =>
      polynomialDesign 7 (fun x : ℝ => x) party x j * sigmoid a η x) := by
    simp only [mul_add, expectation]
    rw [integral_add hi hs, integral_mul_const]
    have hz := GP023B1b_gram_moment j 0
    have hcol (x : ℝ) : polynomialDesign 7 (fun x : ℝ => x) party x (0 : Fin 9) = 1 := by
      simp [polynomialDesign]
    simp only [hcol, mul_one] at hz
    rw [← expectation, hz]
    ring
  rw [he]
  fin_cases j
  · have he := GP023B1b_sigmoid_power_moment a η hη 0
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign,
      GP023B1b_party_sigmoid_moment a η hη]
  · have he := GP023B1b_sigmoid_power_moment a η hη 1
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · have he := GP023B1b_sigmoid_power_moment a η hη 2
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · have he := GP023B1b_sigmoid_power_moment a η hη 3
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · have he := GP023B1b_sigmoid_power_moment a η hη 4
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · have he := GP023B1b_sigmoid_power_moment a η hη 5
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · have he := GP023B1b_sigmoid_power_moment a η hη 6
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he
  · have he := GP023B1b_sigmoid_power_moment a η hη 7
    norm_num at he
    norm_num [GP023B1b_response, GP023B1b_gram, polynomialDesign]
    simpa only [pow_zero, one_mul] using he

lemma GP023B1b_degree7_coefficient (η : ℝ) (hη : 0 < η ∧ η ≤ 1) :
    populationCoefficient uniformMargins 7 (fun x => 1/2+sigmoid (1/20) η x) =
      1/10-(4096/6125)*η+(6/5)*η^2-(33/25)*η^4+(858/875)*η^6-(143/490)*η^8 := by
  rw [GP023B1b_coefficient_matrix _ _ (by norm_num)]
  simp_rw [GP023B1b_response_moment (1/20) η (by norm_num) hη]
  norm_num [GP023B1b_gramInverse, GP023B1b_response, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem sigmoid_fit_criterion_proof (a η : ℝ) (ha : 0 < a) (hη : 0 < η ∧ η ≤ 1) :
    let ν := witnessLaw uniformMargins (sigmoid a η)
    ProbabilityLaw ν ∧ marginLaw ν = uniformMargins ∧
    predictionRisk ν (fun x => 1/2+sigmoid a η x) = 1/100 ∧
    (∀ J, 1 ≤ J → 1/100 ≤ fittedRisk ν J ∧ fittedRisk ν J ≤ 1/100+a^2*η/3 ∧
      (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
        fittedRisk ν J - predictionRisk ν f ≤ a^2*η/3) ∧
      (fittedRisk ν J-1/100)/(fittedRisk ν J) ≤ 100*a^2*η/3) ∧
    (a=1/20 → populationCoefficient uniformMargins 7 (fun x => 1/2+sigmoid a η x) =
      1/10-(4096/6125)*η+(6/5)*η^2-(33/25)*η^4+(858/875)*η^6-(143/490)*η^8) := by
  obtain ⟨hp, hm, hr, hfit⟩ := GP023B1b_risk_claims a η ha hη
  exact ⟨hp, hm, hr, hfit, fun he => he ▸ GP023B1b_degree7_coefficient η hη⟩

/-! ## Sampling separation -/

def GP023B1b_sample_noiseSum {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (A : Set ℝ) (u : ℝ × ℝ → ℝ) (N : ℕ) (ω : Ω) : ℝ := by
  classical
  exact ∑ i : Fin N, if (sample i ω).1 ∈ A then u (sample i ω) else 0

/-- A centered local-noise bound on the IID sampling space.
Centering for the two-point witness is established below. -/
lemma GP023B1b_sample_local_noise_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (A : Set ℝ) (hA : MeasurableSet A)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    (hmem : MemLp ((Prod.fst ⁻¹' A).indicator u) 2 ν)
    (hcenter : (∫ z, (Prod.fst ⁻¹' A).indicator u z ∂ν) = 0)
    (σ2 : ℝ)
    (hsecond : (∫ z, ((Prod.fst ⁻¹' A).indicator u z)^2 ∂ν) ≤
      σ2 * (marginLaw ν A).toReal)
    (hp : 0 < (marginLaw ν A).toReal) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t < |GP023B1b_sample_noiseSum sample A u N ω /
      sampleWindowCount sample A N ω|} ≤
        ENNReal.ofReal (4 / ((N : ℝ) * (marginLaw ν A).toReal)) +
        ENNReal.ofReal (4 * σ2 / (t^2 * (N : ℝ) * (marginLaw ν A).toReal)) := by
  classical
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  let p : ℝ := (marginLaw ν A).toReal
  let g : ℝ × ℝ → ℝ := (Prod.fst ⁻¹' A).indicator u
  let B : ℕ → Ω → ℝ := fun i => g ∘ sample i
  have hg : Measurable g := hu.indicator (hA.preimage measurable_fst)
  have hBm (i : ℕ) : MemLp (B i) 2 P := by
    have hmap : MemLp g 2 (Measure.map (sample i) P) := by
      rw [hiid.2.2.1 i]
      exact hmem
    exact hmap.comp_of_map (hiid.2.1 i).aemeasurable
  have hBmean (i : ℕ) : (∫ ω, B i ω ∂P) = 0 := by
    have he := integral_map (μ := P) (hiid.2.1 i).aemeasurable hg.aestronglyMeasurable
    rw [hiid.2.2.1 i] at he
    exact he.symm.trans hcenter
  have hBsecond (i : ℕ) : (∫ ω, (B i ω)^2 ∂P) ≤ σ2 * p := by
    have he := integral_map (μ := P) (hiid.2.1 i).aemeasurable
      (hg.pow_const 2).aestronglyMeasurable
    rw [hiid.2.2.1 i] at he
    exact he.symm.trans_le hsecond
  have hBvar (i : ℕ) : ProbabilityTheory.variance (B i) P ≤ σ2 * p :=
    (ProbabilityTheory.variance_le_expectation_sq
      ((hg.comp (hiid.2.1 i)).aestronglyMeasurable)).trans (hBsecond i)
  have hind (i j : Fin N) (hij : i ≠ j) :
      ProbabilityTheory.IndepFun (B i.val) (B j.val) P := by
    have hv : i.val ≠ j.val := by
      intro he
      exact hij (Fin.ext he)
    exact (hiid.2.2.2.indepFun hv).comp hg hg
  let S : Ω → ℝ := fun ω => ∑ i : Fin N, B i.val ω
  have hSmem : MemLp S 2 P :=
    memLp_finsetSum (univ : Finset (Fin N)) (fun i _ => hBm i.val)
  have hSmean : (∫ ω, S ω ∂P) = 0 := by
    change (∫ ω, ∑ i : Fin N, B i.val ω ∂P) = 0
    rw [integral_finset_sum univ (fun i _ => (hBm i.val).integrable (by norm_num))]
    simp only [hBmean, Finset.sum_const_zero]
  have hSvar : ProbabilityTheory.variance S P ≤ (N : ℝ) * σ2 * p := by
    have hv := ProbabilityTheory.IndepFun.variance_sum
      (s := (univ : Finset (Fin N))) (X := fun i : Fin N => B i.val)
      (fun i _ => hBm i.val) (by intro i _ j _ hij; exact hind i j hij)
    have he : (∑ i : Fin N, B i.val) = S := by
      funext ω
      simp only [Finset.sum_apply, S]
    rw [he] at hv
    rw [hv]
    calc
      _ ≤ ∑ _i : Fin N, σ2 * p := Finset.sum_le_sum (fun i _ => hBvar i.val)
      _ = _ := by simp [mul_assoc]
  have hS (ω : Ω) : GP023B1b_sample_noiseSum sample A u N ω = S ω := by
    simp only [GP023B1b_sample_noiseSum, S, B, g, Function.comp_apply,
      Set.indicator_apply, Set.mem_preimage]
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNp : 0 < (N : ℝ) * p := mul_pos hNreal hp
  have hbad : P {ω | t * ((N : ℝ) * p / 2) ≤ |S ω|} ≤
      ENNReal.ofReal (4 * σ2 / (t^2 * (N : ℝ) * p)) := by
    calc
      _ = P {ω | t * ((N : ℝ) * p / 2) ≤ |S ω - ∫ ω, S ω ∂P|} := by
        rw [hSmean]
        simp only [sub_zero]
      _ ≤ ENNReal.ofReal (ProbabilityTheory.variance S P /
          (t * ((N : ℝ) * p / 2))^2) :=
        ProbabilityTheory.meas_ge_le_variance_div_sq hSmem (by positivity)
      _ ≤ ENNReal.ofReal (4 * σ2 / (t^2 * (N : ℝ) * p)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ ((N : ℝ) * σ2 * p) / (t * ((N : ℝ) * p / 2))^2 :=
            div_le_div_of_nonneg_right hSvar (sq_nonneg _)
          _ = _ := by
            field_simp [ne_of_gt ht, ne_of_gt hNreal, ne_of_gt hp]
            <;> ring
  calc
    _ ≤ P ({ω | sampleWindowCount sample A N ω < (N : ℝ) * p / 2} ∪
        {ω | t * ((N : ℝ) * p / 2) ≤ |S ω|}) := by
      apply measure_mono
      intro ω hω
      by_cases hc : sampleWindowCount sample A N ω < (N : ℝ) * p / 2
      · exact Or.inl hc
      · right
        have hc' : (N : ℝ) * p / 2 ≤ sampleWindowCount sample A N ω := le_of_not_gt hc
        have hcpos : 0 < sampleWindowCount sample A N ω := by linarith
        change t < |GP023B1b_sample_noiseSum sample A u N ω /
          sampleWindowCount sample A N ω| at hω
        rw [hS, abs_div, abs_of_pos hcpos] at hω
        have hmul := (lt_div_iff₀ hcpos).mp hω
        exact (mul_le_mul_of_nonneg_left hc' ht.le).trans hmul.le
    _ ≤ P {ω | sampleWindowCount sample A N ω < (N : ℝ) * p / 2} +
        P {ω | t * ((N : ℝ) * p / 2) ≤ |S ω|} := measure_union_le _ _
    _ ≤ _ := add_le_add (iid_window_count_bound P ν sample hiid A hA hp N hN) hbad

/-- Exact local first and second moments under the independent two-point
witness. This statement works for every Borel window, without a support or
regularity condition on its location. -/
lemma GP023B1b_sample_witness_noise_moments (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (h : ℝ → ℝ) (hm : Measurable h) (A : Set ℝ) (hA : MeasurableSet A) :
    let g := (Prod.fst ⁻¹' A).indicator (fun z : ℝ × ℝ => z.2 - (1 / 2 + h z.1))
    MemLp g 2 (witnessLaw μ h) ∧
    (∫ z, g z ∂witnessLaw μ h) = 0 ∧
    (∫ z, (g z)^2 ∂witnessLaw μ h) = (1 / 100 : ℝ) * (μ A).toReal := by
  classical
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  let g := (Prod.fst ⁻¹' A).indicator (fun z : ℝ × ℝ => z.2 - (1 / 2 + h z.1))
  change MemLp g 2 (witnessLaw μ h) ∧
    (∫ z, g z ∂witnessLaw μ h) = 0 ∧
    (∫ z, (g z)^2 ∂witnessLaw μ h) = (1 / 100 : ℝ) * (μ A).toReal
  have hg : Measurable g :=
    (measurable_snd.sub (measurable_const.add (hm.comp measurable_fst))).indicator
      (hA.preimage measurable_fst)
  have hbranch (u : ℝ) :
      (fun x : ℝ => g (x, 1 / 2 + h x + u)) = A.indicator (fun _ => u) := by
    funext x
    by_cases hx : x ∈ A <;> simp [g, hx]
  have hbranch2 (u : ℝ) :
      (fun x : ℝ => (g (x, 1 / 2 + h x + u))^2) = A.indicator (fun _ => u^2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [g, hx]
  have hi : Integrable g (witnessLaw μ h) := by
    apply (GP023B1b_integrable_witness_iff μ hm hg).mpr
    constructor
    · rw [hbranch]
      exact (integrable_const _).indicator hA
    · rw [hbranch]
      exact (integrable_const _).indicator hA
  have hi2 : Integrable (fun z => (g z)^2) (witnessLaw μ h) := by
    apply (GP023B1b_integrable_witness_iff μ hm (hg.pow_const 2)).mpr
    constructor
    · rw [hbranch2]
      exact (integrable_const _).indicator hA
    · rw [hbranch2]
      exact (integrable_const _).indicator hA
  refine ⟨(memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hi2, ?_, ?_⟩
  · rw [GP023B1b_integral_witness μ hm hg hi, hbranch, hbranch,
      integral_indicator_const _ hA, integral_indicator_const _ hA]
    simp only [smul_eq_mul, Measure.real]
    ring
  · rw [GP023B1b_integral_witness μ hm (hg.pow_const 2) hi2, hbranch2, hbranch2,
      integral_indicator_const _ hA, integral_indicator_const _ hA]
    simp only [smul_eq_mul, Measure.real]
    ring

theorem GP023B1b_sample_numerical_local_noise_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample)
    (A : Set ℝ) (hA : MeasurableSet A) (hp : 0 < (uniformMargins A).toReal)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t) :
    P {ω | t < |GP023B1b_sample_noiseSum sample A
      (fun z => z.2 - (1 / 2 + sigmoid (1/20) (1/10000) z.1)) N ω /
      sampleWindowCount sample A N ω|} ≤
        ENNReal.ofReal (4 / ((N : ℝ) * (uniformMargins A).toReal)) +
        ENNReal.ofReal (4 * (1 / 100 : ℝ) /
          (t^2 * (N : ℝ) * (uniformMargins A).toReal)) := by
  letI : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  have hm := (GP023B1b_continuous (1/20) (1/10000)).measurable
  have hmargin := GP023B1b_witness_margin uniformMargins hm
  obtain ⟨hmem, hcenter, hsecond⟩ := GP023B1b_sample_witness_noise_moments uniformMargins
    uniform_law_normalized.1 _ hm A hA
  have hu : Measurable (fun z : ℝ × ℝ =>
      z.2 - (1 / 2 + sigmoid (1/20) (1/10000) z.1)) :=
    measurable_snd.sub (measurable_const.add (hm.comp measurable_fst))
  have hp' : 0 < (marginLaw
      (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) A).toReal := by
    simpa only [hmargin] using hp
  have hs' : (∫ z, ((Prod.fst ⁻¹' A).indicator
      (fun z : ℝ × ℝ => z.2 - (1 / 2 + sigmoid (1/20) (1/10000) z.1)) z)^2
      ∂witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) ≤
      (1 / 100 : ℝ) * (marginLaw
        (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) A).toReal := by
    rw [hmargin]
    exact hsecond.le
  simpa only [hmargin] using GP023B1b_sample_local_noise_bound P _ sample hiid A hA
    _ hu hmem hcenter (1/100) hs' hp' N hN t ht

lemma GP023B1b_sample_local_smooth_bound (a η x : ℝ) (ha : 0 ≤ a) (hη : 0 < η) :
    |sigmoid a η x| ≤ (a / η) * |x| := by
  have hclip : |max (-1) (min 1 (x / η))| ≤ |x / η| := by
    by_cases hl : x / η ≤ (-1 : ℝ)
    · rw [min_eq_right (by linarith : x / η ≤ (1 : ℝ)), max_eq_left hl,
        abs_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0), abs_of_nonpos (by linarith : x / η ≤ 0)]
      linarith
    · by_cases hh : (1 : ℝ) ≤ x / η
      · rw [min_eq_left hh, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), abs_of_nonneg (by linarith : 0 ≤ x / η)]
        exact hh
      · simp only [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl), le_refl]
  calc
    _ = a * |max (-1) (min 1 (x / η))| := by rw [sigmoid, abs_mul, abs_of_nonneg ha]
    _ ≤ a * |x / η| := mul_le_mul_of_nonneg_left hclip ha
    _ = _ := by rw [abs_div, abs_of_pos hη]; ring

lemma GP023B1b_sample_numerical_smooth_bound (k x : ℝ) (hx : |x| ≤ k) :
    |sigmoid (1/20) (1/10000) x| ≤ 500 * k := by
  have hb := GP023B1b_sample_local_smooth_bound (1/20) (1/10000) x (by norm_num) (by norm_num)
  norm_num at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hx (by norm_num))

lemma GP023B1b_average_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (g : ℝ × ℝ → ℝ)
    (hg : Measurable g) (hi : Integrable g ν) :
    ∀ᵐ ω ∂P, Tendsto (fun N => (∑ i : Fin N, g (sample i ω))/(N : ℝ))
      atTop (nhds (∫ z, g z ∂ν)) := by
  have himap : Integrable g (Measure.map (sample 0) P) := by
    rw [hiid.2.2.1 0]
    exact hi
  have hint : Integrable (g ∘ sample 0) P :=
    (integrable_map_measure hg.aestronglyMeasurable (hiid.2.1 0).aemeasurable).mp himap
  have hid (i : ℕ) : ProbabilityTheory.IdentDistrib (sample i) (sample 0) P P :=
    ⟨(hiid.2.1 i).aemeasurable, (hiid.2.1 0).aemeasurable, by rw [hiid.2.2.1 i, hiid.2.2.1 0]⟩
  have hs := ProbabilityTheory.strong_law_ae_real (fun i => g ∘ sample i) hint
    (fun i j hij => (hiid.2.2.2.indepFun hij).comp hg hg)
    (fun i => (hid i).comp hg)
  have he : (∫ ω, g (sample 0 ω) ∂P) = ∫ z, g z ∂ν := by
    rw [← hiid.2.2.1 0]
    exact (integral_map (hiid.2.1 0).aemeasurable hg.aestronglyMeasurable).symm
  simp only [Function.comp_apply] at hs
  rw [he] at hs
  filter_upwards [hs] with ω hω
  have he' (N : ℕ) : (∑ i : Fin N, g (sample i ω)) =
      ∑ i ∈ Finset.range N, g (sample i ω) := Fin.sum_univ_eq_sum_range (fun i => g (sample i ω)) N
  simpa only [he'] using hω

lemma GP023B1b_ae_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : ℕ → Ω → ℝ) (z : ℝ)
    (hm : ∀ N, Measurable (Z N))
    (hl : ∀ᵐ ω ∂P, Tendsto (fun N => Z N ω) atTop (nhds z)) :
    ConvergesInProbability P Z z := by
  have h := tendstoInMeasure_of_tendsto_ae (fun N => (hm N).aestronglyMeasurable) hl
  have hh := tendstoInMeasure_iff_dist.mp h
  intro ε hε
  apply tendsto_const_nhds.squeeze (hh ε hε) (fun _ => bot_le) (fun N => ?_)
  apply measure_mono
  intro ω hω
  change ε < |Z N ω-z| at hω
  change ε ≤ dist (Z N ω) z
  simpa only [Real.dist_eq] using hω.le

lemma GP023B1b_sample_normal {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (N J : ℕ) (hN : N ≠ 0) (ω : Ω) (c : Fin (J+2) → ℝ) :
    IsOLS (polynomialDesign J (fun i : Fin N => (sample i ω).1)
      (fun i : Fin N => party (sample i ω).1)) (fun i : Fin N => (sample i ω).2) c ↔
      (Matrix.of (sampleGram sample N J ω)).mulVec c = sampleCross sample N J ω := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let X := polynomialDesign J (fun i : Fin N => (sample i ω).1)
      (fun i : Fin N => party (sample i ω).1)
  have he (j : Fin (J+2)) :
      (Matrix.of (sampleGram sample N J ω)).mulVec c j =
      dot (fun i => X i j) (predict X c) / (N : ℝ) := by
    unfold Matrix.mulVec dotProduct sampleGram dot predict X
    dsimp only [Matrix.of_apply]
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [polynomialDesign]
    ring
  unfold IsOLS
  simp_rw [dot_sub_right]
  constructor
  · intro h
    funext j
    rw [he]
    have hh := sub_eq_zero.mp (h j)
    change dot (fun i => X i j) (fun i => (sample i ω).2) =
      dot (fun i => X i j) (predict X c) at hh
    rw [← hh]
    rfl
  · intro h j
    have hh := congrFun h j
    rw [he] at hh
    change _ / (N : ℝ) = dot (fun i => X i j) (fun i => (sample i ω).2) / (N : ℝ) at hh
    exact sub_eq_zero.mpr ((div_left_inj' hNr).mp hh).symm

lemma GP023B1b_sample_inverse {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (N J : ℕ) (hN : N ≠ 0) (ω : Ω)
    (hd : (Matrix.of (sampleGram sample N J ω)).det ≠ 0) :
    samplePolynomial sample N J ω =
      (Matrix.of (sampleGram sample N J ω))⁻¹.mulVec (sampleCross sample N J ω) 1 := by
  let A := Matrix.of (sampleGram sample N J ω)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hd
  have hex : ∃ c, IsOLS (polynomialDesign J (fun i : Fin N => (sample i ω).1)
      (fun i : Fin N => party (sample i ω).1)) (fun i : Fin N => (sample i ω).2) c := by
    refine ⟨A⁻¹.mulVec (sampleCross sample N J ω), ?_⟩
    apply (GP023B1b_sample_normal sample N J hN ω _).mpr
    change A.mulVec (A⁻¹.mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hc := (GP023B1b_sample_normal sample N J hN ω _).mp (Classical.epsilon_spec hex)
  have he := congrArg A⁻¹.mulVec hc
  change A⁻¹.mulVec (A.mulVec _) = _ at he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec] at he
  exact congrFun he 1

lemma GP023B1b_fixed_consistency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (J : ℕ)
    (G : Matrix (Fin (J+2)) (Fin (J+2)) ℝ) (t : Fin (J+2) → ℝ)
    (hgm : ∀ j l, Integrable (fun z : ℝ × ℝ =>
      polynomialDesign J (fun x : ℝ => x) party z.1 j *
      polynomialDesign J (fun x : ℝ => x) party z.1 l) ν)
    (htm : ∀ j, Integrable (fun z : ℝ × ℝ =>
      polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2) ν)
    (hG : ∀ j l, (∫ z, polynomialDesign J (fun x : ℝ => x) party z.1 j *
      polynomialDesign J (fun x : ℝ => x) party z.1 l ∂ν) = G j l)
    (ht : ∀ j, (∫ z, polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2 ∂ν) = t j)
    (hd : G.det ≠ 0) :
    ConvergesInProbability P (fun N => samplePolynomial sample N J) (G⁻¹.mulVec t 1) := by
  classical
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  let A (N : ℕ) (ω : Ω) := Matrix.of (sampleGram sample N J ω)
  let v (N : ℕ) (ω : Ω) := sampleCross sample N J ω
  have hAm (N : ℕ) : Measurable (A N) := by
    apply measurable_pi_lambda
    intro j
    apply measurable_pi_lambda
    intro l
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    exact ((GP023B1b_column_measurable J j).comp (hiid.2.1 i).fst).mul
      ((GP023B1b_column_measurable J l).comp (hiid.2.1 i).fst)
  have hvm (N : ℕ) : Measurable (v N) := by
    apply measurable_pi_lambda
    intro j
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    exact ((GP023B1b_column_measurable J j).comp (hiid.2.1 i).fst).mul (hiid.2.1 i).snd
  have hAL : ∀ᵐ ω ∂P, Tendsto (fun N => A N ω) atTop (nhds G) := by
    have hh (j l : Fin (J+2)) := GP023B1b_average_ae P ν sample hiid
      (fun z => polynomialDesign J (fun x : ℝ => x) party z.1 j *
        polynomialDesign J (fun x : ℝ => x) party z.1 l)
      (((GP023B1b_column_measurable J j).comp measurable_fst).mul
        ((GP023B1b_column_measurable J l).comp measurable_fst)) (hgm j l)
    have hall := ae_all_iff.mpr (fun j => ae_all_iff.mpr (hh j))
    filter_upwards [hall] with ω hω
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro l
    have hj := hω j l
    rw [hG j l] at hj
    simpa only [A, sampleGram, Matrix.of_apply, polynomialDesign] using hj
  have hvL : ∀ᵐ ω ∂P, Tendsto (fun N => v N ω) atTop (nhds t) := by
    have hh (j : Fin (J+2)) := GP023B1b_average_ae P ν sample hiid
      (fun z => polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2)
      (((GP023B1b_column_measurable J j).comp measurable_fst).mul measurable_snd) (htm j)
    have hall := ae_all_iff.mpr hh
    filter_upwards [hall] with ω hω
    apply tendsto_pi_nhds.mpr
    intro j
    have hj := hω j
    rw [ht j] at hj
    simpa only [v, sampleCross, polynomialDesign] using hj
  have hdm (N : ℕ) : Measurable (fun ω => (A N ω).det) :=
    continuous_id.matrix_det.measurable.comp (hAm N)
  have him (N : ℕ) : Measurable (fun ω => (A N ω)⁻¹) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hdm N).inv.smul (continuous_id.matrix_adjugate.measurable.comp (hAm N))
  let Z (N : ℕ) (ω : Ω) := (A N ω)⁻¹.mulVec (v N ω) 1
  have hZm (N : ℕ) : Measurable (Z N) := by
    unfold Z Matrix.mulVec dotProduct
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp ((measurable_pi_apply 1).comp (him N))).mul
        ((measurable_pi_apply i).comp (hvm N)))
  have hZL : ∀ᵐ ω ∂P, Tendsto (fun N => Z N ω) atTop (nhds (G⁻¹.mulVec t 1)) := by
    filter_upwards [hAL, hvL] with ω hω hvω
    have hinv := (continuousAt_matrix_inv G (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd)).tendsto.comp hω
    exact ((continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
      (hinv.prodMk_nhds hvω)).apply_nhds 1
  let B (N : ℕ) (ω : Ω) : ℝ := if (A N ω).det = 0 then 1 else 0
  have hBm (N : ℕ) : Measurable (B N) :=
    Measurable.ite (measurableSet_eq_fun (hdm N) measurable_const)
      measurable_const measurable_const
  have hBL : ∀ᵐ ω ∂P, Tendsto (fun N => B N ω) atTop (nhds 0) := by
    filter_upwards [hAL] with ω hω
    have hdet := continuous_id.matrix_det.continuousAt.tendsto.comp hω
    have he : ∀ᶠ N in atTop, (A N ω).det ≠ 0 := hdet.eventually_ne hd
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with N hN
    simp [B, hN]
  have hz := GP023B1b_ae_probability P Z _ hZm hZL
  have hb := GP023B1b_ae_probability P B 0 hBm hBL
  intro ε hε
  apply tendsto_const_nhds.squeeze' (by simpa using (hz ε hε).add (hb (1/2) (by norm_num)))
    (Eventually.of_forall (fun _ => bot_le))
    (show ∀ᶠ N in atTop,
      P {ω | ε < |samplePolynomial sample N J ω - G⁻¹.mulVec t 1|} ≤
        P {ω | ε < |Z N ω - G⁻¹.mulVec t 1|} + P {ω | (1/2 : ℝ) < |B N ω - 0|} from ?_)
  filter_upwards [eventually_ne_atTop 0] with N hN
  calc
    _ ≤ P ({ω | ε < |Z N ω - G⁻¹.mulVec t 1|} ∪
        {ω | (1/2 : ℝ) < |B N ω - 0|}) := by
      apply measure_mono
      intro ω hω
      by_cases hdA : (A N ω).det = 0
      · right
        norm_num [B, hdA]
      · left
        change ε < |samplePolynomial sample N J ω - G⁻¹.mulVec t 1| at hω
        rw [GP023B1b_sample_inverse sample N J hN ω hdA] at hω
        exact hω
    _ ≤ _ := measure_union_le _ _

lemma GP023B1b_rd_windows {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (N : ℕ) (k : ℝ) (hk : 0 < k) (ω : Ω)
    (htie : ∀ i : Fin N, (sample i ω).1 ≠ 0) :
    sampleRD sample (fun _ => k) N ω =
      GP023B1b_sample_noiseSum sample (Ioc 0 k) Prod.snd N ω /
        sampleWindowCount sample (Ioc 0 k) N ω -
      GP023B1b_sample_noiseSum sample (Ioo (-k) 0) Prod.snd N ω /
        sampleWindowCount sample (Ioo (-k) 0) N ω := by
  classical
  have hpos (y : Fin N → ℝ) :
      (∑ i ∈ close k (fun i : Fin N => (sample i ω).1), party (sample i ω).1 * y i) =
      ∑ i : Fin N, if (sample i ω).1 ∈ Ioc 0 k then y i else 0 := by
    simp only [close, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : 0 ≤ (sample i ω).1
    · have hp : 0 < (sample i ω).1 := lt_of_le_of_ne hx (htie i).symm
      have hlo : -k < (sample i ω).1 := by linarith
      simp [party, hx, Set.mem_Ioc, hp, hlo]
    · have hn : (sample i ω).1 < 0 := lt_of_not_ge hx
      have hnp : ¬0 < (sample i ω).1 := by linarith
      simp [party, hx, Set.mem_Ioc, hnp]
  have hneg (y : Fin N → ℝ) :
      (∑ i ∈ close k (fun i : Fin N => (sample i ω).1), (1-party (sample i ω).1) * y i) =
      ∑ i : Fin N, if (sample i ω).1 ∈ Ioo (-k) 0 then y i else 0 := by
    simp only [close, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : 0 ≤ (sample i ω).1
    · have hn : ¬(sample i ω).1 < 0 := not_lt.mpr hx
      simp [party, hx, Set.mem_Ioo, hn]
    · have hn : (sample i ω).1 < 0 := lt_of_not_ge hx
      have hhi : (sample i ω).1 ≤ k := by linarith
      simp [party, hx, Set.mem_Ioo, hn, hhi]
  have hpc := hpos (fun _ => 1)
  have hnc := hneg (fun _ => 1)
  simp only [mul_one] at hpc hnc
  simp only [sampleRD, rd, hpos, hneg, hpc, hnc,
    GP023B1b_sample_noiseSum, sampleWindowCount]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split_ifs <;> rfl

lemma GP023B1b_side_bound {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (A : Set ℝ) (k : ℝ) (N : ℕ) (ω : Ω)
    (hA : ∀ x ∈ A, |x| ≤ k)
    (hc : 0 < sampleWindowCount sample A N ω) :
    |GP023B1b_sample_noiseSum sample A Prod.snd N ω /
        sampleWindowCount sample A N ω - 1/2| ≤ 500*k +
      |GP023B1b_sample_noiseSum sample A
        (fun z => z.2-(1/2+sigmoid (1/20) (1/10000) z.1)) N ω /
        sampleWindowCount sample A N ω| := by
  classical
  let H := GP023B1b_sample_noiseSum sample A
    (fun z => sigmoid (1/20) (1/10000) z.1) N ω
  let U := GP023B1b_sample_noiseSum sample A
    (fun z => z.2-(1/2+sigmoid (1/20) (1/10000) z.1)) N ω
  let C := sampleWindowCount sample A N ω
  have hnum : GP023B1b_sample_noiseSum sample A Prod.snd N ω = (1/2)*C+H+U := by
    simp only [C, H, U, GP023B1b_sample_noiseSum, sampleWindowCount]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hH : |H| ≤ 500*k*C := by
    calc
      _ ≤ ∑ i : Fin N, |if (sample i ω).1 ∈ A then sigmoid (1/20) (1/10000) (sample i ω).1 else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, if (sample i ω).1 ∈ A then 500*k else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : (sample i ω).1 ∈ A
        · simp only [if_pos hi]
          exact GP023B1b_sample_numerical_smooth_bound k _ (hA _ hi)
        · simp [hi]
      _ = _ := by
        unfold C sampleWindowCount
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  have he : GP023B1b_sample_noiseSum sample A Prod.snd N ω / C - 1/2 = H/C+U/C := by
    rw [hnum]
    have hC : C ≠ 0 := hc.ne'
    field_simp [hC]
    <;> ring
  change |GP023B1b_sample_noiseSum sample A Prod.snd N ω / C - 1/2| ≤ 500*k+|U/C|
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  rw [abs_div, abs_of_pos hc]
  exact (div_le_iff₀ hc).mpr hH

lemma GP023B1b_uniform_window (k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1) :
    (uniformMargins (Ioc 0 k)).toReal = k/2 ∧
      (uniformMargins (Ioo (-k) 0)).toReal = k/2 := by
  have hp : Ioc (0 : ℝ) k ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans hk1⟩
  have hm : Ioo (-k) (0 : ℝ) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  constructor
  · rw [uniformMargins, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr hp, Real.volume_Ioc, smul_eq_mul, ENNReal.toReal_mul]
    norm_num [ENNReal.toReal_ofReal hk.le]
    ring
  · rw [uniformMargins, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr hm, Real.volume_Ioo, smul_eq_mul, ENNReal.toReal_mul]
    norm_num [ENNReal.toReal_ofReal hk.le]
    ring

lemma GP023B1b_witness_fst (g : ℝ → ℝ) (hg : Measurable g)
    (hi : Integrable g uniformMargins) :
    Integrable (fun z : ℝ × ℝ => g z.1)
      (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) ∧
    (∫ z, g z.1 ∂witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) =
      expectation uniformMargins g := by
  letI : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  have hm := GP023B1b_witness_margin uniformMargins
    (GP023B1b_continuous (1/20) (1/10000)).measurable
  have hmap : Measure.map Prod.fst
      (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) = uniformMargins := hm
  constructor
  · rw [← hmap] at hi
    exact (integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable).mp hi
  · have he := integral_map (μ := witnessLaw uniformMargins (sigmoid (1/20) (1/10000)))
      measurable_fst.aemeasurable hg.aestronglyMeasurable
    rw [hmap] at he
    exact he.symm

lemma GP023B1b_witness_cross (J : ℕ) (j : Fin (J+2)) :
    Integrable (fun z : ℝ × ℝ => polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2)
      (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) ∧
    (∫ z, polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2
      ∂witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) =
      expectation uniformMargins (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
        (1/2+sigmoid (1/20) (1/10000) x)) := by
  letI : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  let h := sigmoid (1/20) (1/10000)
  let z := fun x => polynomialDesign J (fun x : ℝ => x) party x j
  have hm : Measurable h := (GP023B1b_continuous (1/20) (1/10000)).measurable
  have hz : Measurable z := GP023B1b_column_measurable J j
  have hg : Measurable (fun p : ℝ × ℝ => z p.1 * p.2) := (hz.comp measurable_fst).mul measurable_snd
  have hi : Integrable z uniformMargins := by
    apply GP023B1b_supported_integrable _ uniform_law_normalized.1 uniform_law_normalized.2 hz 1
    exact fun x hx => GP023B1b_column_bound J j x hx
  have hir : Integrable (fun x => z x * (1/2+h x)) uniformMargins := by
    apply GP023B1b_supported_integrable _ uniform_law_normalized.1 uniform_law_normalized.2
      (hz.mul (measurable_const.add hm)) 1
    intro x hx
    change |z x * (1/2+h x)| ≤ 1
    rw [abs_mul]
    have hb : |(1/2 : ℝ)+h x| ≤ 1 := by
      have hh := GP023B1b_abs_le (1/20) (1/10000) x (by norm_num)
      have hadd := abs_add_le (1/2 : ℝ) (h x)
      norm_num at hadd
      dsimp [h] at *
      linarith
    exact (mul_le_mul_of_nonneg_right (GP023B1b_column_bound J j x hx) (abs_nonneg _)).trans
      (by simpa using hb)
  have hbranch (u : ℝ) : Integrable (fun x => z x * (1/2+h x+u)) uniformMargins := by
    convert hir.add (hi.mul_const u) using 1
    funext x
    change z x*(1/2+h x+u)=z x*(1/2+h x)+z x*u
    ring
  have higi : Integrable (fun p : ℝ × ℝ => z p.1 * p.2) (witnessLaw uniformMargins h) :=
    (GP023B1b_integrable_witness_iff uniformMargins hm hg).mpr
      ⟨hbranch (-1/10), hbranch (1/10)⟩
  refine ⟨higi, ?_⟩
  change (∫ p, z p.1*p.2 ∂witnessLaw uniformMargins h) = ∫ x, z x*(1/2+h x) ∂uniformMargins
  rw [GP023B1b_integral_witness uniformMargins hm hg higi]
  have he (u : ℝ) : (∫ x, z x*(1/2+h x+u) ∂uniformMargins) =
      (∫ x, z x*(1/2+h x) ∂uniformMargins) + (∫ x, z x ∂uniformMargins)*u := by
    rw [show (fun x => z x*(1/2+h x+u)) =
      (fun x => z x*(1/2+h x)+z x*u) from funext (fun x => by ring)]
    rw [integral_add hir (hi.mul_const u), integral_mul_const]
  dsimp only
  rw [he, he]
  ring

lemma GP023B1b_degree7_sample {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample) :
    ConvergesInProbability P (fun N => samplePolynomial sample N 7)
      (4896723787999993532000048047999857/49000000000000000000000000000000000) := by
  have hgm (j l : Fin 9) := GP023B1b_witness_fst
    (fun x => polynomialDesign 7 (fun x : ℝ => x) party x j *
      polynomialDesign 7 (fun x : ℝ => x) party x l)
    ((GP023B1b_column_measurable 7 j).mul (GP023B1b_column_measurable 7 l))
    (GP023B1b_gram_integrable 7 j l)
  have hc := GP023B1b_fixed_consistency P _ sample hiid 7 GP023B1b_gram
    (GP023B1b_response (1/20) (1/10000)) (fun j l => (hgm j l).1)
    (fun j => (GP023B1b_witness_cross 7 j).1)
    (fun j l => (hgm j l).2.trans (GP023B1b_gram_moment j l))
    (fun j => (GP023B1b_witness_cross 7 j).2.trans
      (GP023B1b_response_moment (1/20) (1/10000) (by norm_num) (by norm_num) j))
    (Matrix.det_ne_zero_of_right_inverse GP023B1b_gram_inverse)
  have he : GP023B1b_gram⁻¹ = GP023B1b_gramInverse := Matrix.inv_eq_right_inv GP023B1b_gram_inverse
  rw [he] at hc
  norm_num [GP023B1b_gramInverse, GP023B1b_response, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hc
  exact hc

def GP023B1b_gram1 : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 1/2, 0], ![1/2, 1/2, 1/4], ![0, 1/4, 1/3]]

def GP023B1b_inverse1 : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![5, -8, 6], ![-8, 16, -12], ![6, -12, 12]]

lemma GP023B1b_inverse1_cert : GP023B1b_gram1 * GP023B1b_inverse1 = 1 := by
  apply Matrix.ext
  intro i j
  change (∑ k : Fin 3, GP023B1b_gram1 i k * GP023B1b_inverse1 k j) = if i=j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    norm_num [GP023B1b_gram1, GP023B1b_inverse1, Fin.sum_univ_succ]

lemma GP023B1b_degree1_sample {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample) :
    ConvergesInProbability P (fun N => samplePolynomial sample N 1) (99980001/1000000000) := by
  have hgm (j l : Fin 3) := GP023B1b_witness_fst
    (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j *
      polynomialDesign 1 (fun x : ℝ => x) party x l)
    ((GP023B1b_column_measurable 1 j).mul (GP023B1b_column_measurable 1 l))
    (GP023B1b_gram_integrable 1 j l)
  have hGe (j l : Fin 3) : expectation uniformMargins (fun x =>
      polynomialDesign 1 (fun x : ℝ => x) party x j *
      polynomialDesign 1 (fun x : ℝ => x) party x l) = GP023B1b_gram1 j l := by
    have he := GP023B1b_gram_moment (Fin.castLE (by omega : 3 ≤ 9) j)
      (Fin.castLE (by omega : 3 ≤ 9) l)
    convert he using 1 <;> fin_cases j <;> fin_cases l <;>
      norm_num [polynomialDesign, GP023B1b_gram1, GP023B1b_gram]
  let t : Fin 3 → ℝ := ![1/2, 1/4+(1/20)/2*(1-(1/10000)/2), (1/20)*(1/2-(1/10000)^2/6)]
  have hte (j : Fin 3) : expectation uniformMargins (fun x =>
      polynomialDesign 1 (fun x : ℝ => x) party x j * (1/2+sigmoid (1/20) (1/10000) x)) = t j := by
    have he := GP023B1b_response_moment (1/20) (1/10000) (by norm_num) (by norm_num)
      (Fin.castLE (by omega : 3 ≤ 9) j)
    convert he using 1 <;> fin_cases j <;> norm_num [polynomialDesign, t, GP023B1b_response]
  have hc := GP023B1b_fixed_consistency P _ sample hiid 1 GP023B1b_gram1 t
    (fun j l => (hgm j l).1) (fun j => (GP023B1b_witness_cross 1 j).1)
    (fun j l => (hgm j l).2.trans (hGe j l))
    (fun j => (GP023B1b_witness_cross 1 j).2.trans (hte j))
    (Matrix.det_ne_zero_of_right_inverse GP023B1b_inverse1_cert)
  rw [Matrix.inv_eq_right_inv GP023B1b_inverse1_cert] at hc
  norm_num [GP023B1b_inverse1, t, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hc
  exact hc

lemma GP023B1b_rd_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample)
    (k : ℕ → ℝ) (hpos : ∀ N, 0 < k N) (hk : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop) :
    ConvergesInProbability P (sampleRD sample k) 0 := by
  classical
  letI : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  let ν := witnessLaw uniformMargins (sigmoid (1/20) (1/10000))
  have hmargin : marginLaw ν = uniformMargins := GP023B1b_witness_margin uniformMargins
    (GP023B1b_continuous (1/20) (1/10000)).measurable
  have hzero : ∀ᵐ x ∂uniformMargins, x ≠ 0 := by
    rw [ae_iff]
    simp [uniformMargins, Measure.smul_apply, Measure.restrict_apply]
  have htie (i : ℕ) : ∀ᵐ ω ∂P, (sample i ω).1 ≠ 0 := by
    have hmap : Measure.map (fun ω => (sample i ω).1) P = uniformMargins := by
      change Measure.map (Prod.fst ∘ sample i) P = uniformMargins
      rw [← Measure.map_map measurable_fst (hiid.2.1 i), hiid.2.2.1 i]
      exact hmargin
    apply ae_of_ae_map (μ := P) (p := fun x : ℝ => x ≠ 0) ((hiid.2.1 i).fst.aemeasurable)
    rw [hmap]
    exact hzero
  have hties := ae_all_iff.mpr htie
  intro ε hε
  let t : ℝ := ε/8
  have ht : 0 < t := by dsimp [t]; positivity
  let b (N : ℕ) := ENNReal.ofReal (4 / ((N : ℝ)*(k N/2)))
  let d (N : ℕ) := ENNReal.ofReal (4*(1/100 : ℝ) / (t^2*(N : ℝ)*(k N/2)))
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ)*k N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnk
  have hb : Tendsto b atTop (nhds 0) := by
    have he (N : ℕ) : 4 / ((N : ℝ)*(k N/2)) = 8*((N : ℝ)*k N)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      norm_num
      ring
    simpa only [b, he, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hinv :
        Tendsto (fun N : ℕ => 8*((N : ℝ)*k N)⁻¹) atTop (nhds (8*0)))
  have hd : Tendsto d atTop (nhds 0) := by
    have he (N : ℕ) : 4*(1/100 : ℝ) / (t^2*(N : ℝ)*(k N/2)) =
        (8*(1/100 : ℝ)/t^2)*((N : ℝ)*k N)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      norm_num
      ring
    simpa only [d, he, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hinv :
        Tendsto (fun N : ℕ => (8*(1/100 : ℝ)/t^2)*((N : ℝ)*k N)⁻¹)
          atTop (nhds ((8*(1/100 : ℝ)/t^2)*0)))
  apply tendsto_const_nhds.squeeze' (by simpa using (hb.add hb).add ((hb.add hd).add (hb.add hd)))
    (Eventually.of_forall (fun _ => bot_le))
  have hsmall : Tendsto (fun N => 1000*k N) atTop (nhds 0) := by simpa using hk.const_mul 1000
  have hksmall : ∀ᶠ N in atTop, 1000*k N < ε/2 :=
    hsmall.eventually_lt_const (by linarith : (0 : ℝ) < ε/2)
  filter_upwards [hksmall, hk.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with N hks hk1 hN
  let A := Ioc (0 : ℝ) (k N)
  let B := Ioo (-k N) (0 : ℝ)
  have hmass := GP023B1b_uniform_window (k N) (hpos N) hk1.le
  have hpA : 0 < (uniformMargins A).toReal := by rw [hmass.1]; exact half_pos (hpos N)
  have hpB : 0 < (uniformMargins B).toReal := by rw [hmass.2]; exact half_pos (hpos N)
  let CA : Set Ω := {ω | sampleWindowCount sample A N ω < (N : ℝ)*(k N/2)/2}
  let CB : Set Ω := {ω | sampleWindowCount sample B N ω < (N : ℝ)*(k N/2)/2}
  let UA : Set Ω := {ω | t < |GP023B1b_sample_noiseSum sample A
    (fun z => z.2-(1/2+sigmoid (1/20) (1/10000) z.1)) N ω / sampleWindowCount sample A N ω|}
  let UB : Set Ω := {ω | t < |GP023B1b_sample_noiseSum sample B
    (fun z => z.2-(1/2+sigmoid (1/20) (1/10000) z.1)) N ω / sampleWindowCount sample B N ω|}
  have hcA : P CA ≤ b N := by
    have hh := iid_window_count_bound P ν sample hiid A measurableSet_Ioc
      (by rw [hmargin]; exact hpA) N hN
    simpa only [hmargin, hmass.1, CA, b, A] using hh
  have hcB : P CB ≤ b N := by
    have hh := iid_window_count_bound P ν sample hiid B measurableSet_Ioo
      (by rw [hmargin]; exact hpB) N hN
    simpa only [hmargin, hmass.2, CB, b, B] using hh
  have huA : P UA ≤ b N + d N := by
    have hh := GP023B1b_sample_numerical_local_noise_bound P sample hiid A measurableSet_Ioc hpA N hN t ht
    simpa only [hmass.1, UA, b, d, A] using hh
  have huB : P UB ≤ b N + d N := by
    have hh := GP023B1b_sample_numerical_local_noise_bound P sample hiid B measurableSet_Ioo hpB N hN t ht
    simpa only [hmass.2, UB, b, d, B] using hh
  calc
    _ ≤ P ((CA ∪ CB) ∪ (UA ∪ UB)) := by
      apply measure_mono_ae
      filter_upwards [hties] with ω hω
      intro he
      by_contra hn
      have hn' : ω ∉ CA ∧ ω ∉ CB ∧ ω ∉ UA ∧ ω ∉ UB := by
        have hh : (ω ∉ CA ∧ ω ∉ CB) ∧ (ω ∉ UA ∧ ω ∉ UB) := by simpa using hn
        exact ⟨hh.1.1, hh.1.2, hh.2.1, hh.2.2⟩
      have hNp : 0 < (N : ℝ)*(k N/2)/2 := by
        have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have hkN := hpos N
        positivity
      have hca : 0 < sampleWindowCount sample A N ω :=
        hNp.trans_le (le_of_not_gt hn'.1)
      have hcb : 0 < sampleWindowCount sample B N ω :=
        hNp.trans_le (le_of_not_gt hn'.2.1)
      have hsa := GP023B1b_side_bound sample A (k N) N ω
        (fun x hx => by rw [abs_of_pos hx.1]; exact hx.2) hca
      have hsb := GP023B1b_side_bound sample B (k N) N ω
        (fun x hx => by rw [abs_of_neg hx.2]; linarith [hx.1]) hcb
      have hna : |GP023B1b_sample_noiseSum sample A
          (fun z => z.2-(1/2+sigmoid (1/20) (1/10000) z.1)) N ω /
          sampleWindowCount sample A N ω| ≤ t := le_of_not_gt hn'.2.2.1
      have hnb : |GP023B1b_sample_noiseSum sample B
          (fun z => z.2-(1/2+sigmoid (1/20) (1/10000) z.1)) N ω /
          sampleWindowCount sample B N ω| ≤ t := le_of_not_gt hn'.2.2.2
      change ε < |sampleRD sample k N ω - 0| at he
      have hrd := GP023B1b_rd_windows sample N (k N) (hpos N) ω (fun i => hω i)
      change sampleRD sample k N ω = _ at hrd
      rw [hrd, sub_zero] at he
      have habs := abs_sub
        (GP023B1b_sample_noiseSum sample A Prod.snd N ω / sampleWindowCount sample A N ω - 1/2)
        (GP023B1b_sample_noiseSum sample B Prod.snd N ω / sampleWindowCount sample B N ω - 1/2)
      rw [sub_sub_sub_cancel_right] at habs
      change _ ≤ t at hna hnb
      dsimp only [t] at hna hnb
      dsimp only [A, B] at hsa hsb hna hnb habs
      linarith
    _ ≤ (P CA+P CB)+(P UA+P UB) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ _ := add_le_add (add_le_add hcA hcB) (add_le_add huA huB)


theorem sigmoid_sample_separation_proof {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample)
    (k : ℕ → ℝ) (hpos : ∀ N, 0 < k N) (hk : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop) :
    ConvergesInProbability P (fun N => samplePolynomial sample N 1) (99980001/1000000000) ∧
    ConvergesInProbability P (fun N => samplePolynomial sample N 7)
      (4896723787999993532000048047999857/49000000000000000000000000000000000) ∧
    ConvergesInProbability P (sampleRD sample k) 0 := by
  exact ⟨GP023B1b_degree1_sample P sample hiid, GP023B1b_degree7_sample P sample hiid,
    GP023B1b_rd_limit P sample hiid k hpos hk hnk⟩

end
end AronowAudit.P023.Wave1
