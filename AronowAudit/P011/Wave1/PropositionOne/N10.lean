import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.P011_FiniteLawCompletion
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

private lemma square_markov_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ) (a : ℝ) (ha : 0 < a) :
    μ.real {x | |f x| > a} ≤ (∫ x, f x ^ 2 ∂μ) / a ^ 2 := by
  have hsub : {x | |f x| > a} ⊆ {x | a ^ 2 ≤ f x ^ 2} := by
    intro x hx
    have hs : a ^ 2 ≤ |f x| ^ 2 :=
      (sq_le_sq₀ ha.le (abs_nonneg (f x))).mpr hx.le
    change a ^ 2 ≤ f x ^ 2
    simpa only [sq_abs] using hs
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => sq_nonneg (f x))) hf (a ^ 2)
  apply (measureReal_mono hsub).trans
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  simpa only [mul_comm] using hm

theorem n10_proof : N10 := by
  classical
  intro h2 _h5 h7 h8 h9 η hη
  let a : ℝ := min (1 / 2) (5 * η / 108)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha_half : a ≤ 1 / 2 := min_le_left _ _
  have ha_one : a ≤ 1 := by linarith
  have ha_eta : a ≤ 5 * η / 108 := min_le_right _ _
  have ha_small : (54 / 5) * a ≤ η / 2 := by linarith
  have haa : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha_one)]
  have hw (k : ℕ) (y : Fin (PF.size k) → ℝ) : weighted (PF.model k) y = y := by
    funext i
    change (1 : ℝ) * y i = y i
    exact one_mul _
  have hH (k : ℕ) (y : Fin (PF.size k) → ℝ) :
      betaHat (PF.model k) y = average y := by rw [betaHat, hw]
  have hstat (k : ℕ) (y : Fin (PF.size k) → ℝ) :
      scaledOracle PF k y =
        (pathQbar (k + 1) y -
          2 * betaHat (PF.model k) y * pathLbar (k + 1) y +
          7 * betaHat (PF.model k) y ^ 2) / 3 := by
    unfold scaledOracle
    rw [hw]
    simp only [hH]
    exact h8 h2 (k + 1) (Nat.succ_pos k) y
  have hint (k : ℕ) (g : (Fin (PF.size k) → ℝ) → ℝ) (hg : Measurable g) :
      Integrable g (PF.model k).law := by
    change Integrable g (uniformLaw (pathSource (k + 1)))
    haveI : IsProbabilityMeasure (uniformLaw (pathSource (k + 1))) := (PF.model k).probability
    exact (NewFiniteCompletion.finite_memLp (pathSource (k + 1)) g hg 1).integrable
      (by norm_num)
  have htailH (k : ℕ) :
      probability (PF.model k) {y | |betaHat (PF.model k) y| > a} ≤
        (29 / (45 * ((k : ℝ) + 1))) / a ^ 2 := by
    letI : IsProbabilityMeasure (PF.model k).law := (PF.model k).probability
    have hm := square_markov_bound (PF.model k).law (betaHat (PF.model k))
      (hint k (fun y => betaHat (PF.model k) y ^ 2)
        (by unfold betaHat average weighted; fun_prop)) a ha
    change probability (PF.model k) {y | |betaHat (PF.model k) y| > a} ≤
      expectation (PF.model k) (fun y => betaHat (PF.model k) y ^ 2) / a ^ 2 at hm
    rw [(h7 h2 k).1] at hm
    exact hm
  have htailQ (k : ℕ) :
      probability (PF.model k) {y | |pathQbar (k + 1) y + 11 / 5| > a} ≤
        (28836 / (625 * ((k : ℝ) + 1))) / a ^ 2 := by
    letI : IsProbabilityMeasure (PF.model k).law := (PF.model k).probability
    have hm := square_markov_bound (PF.model k).law
      (fun y => pathQbar (k + 1) y + 11 / 5)
      (hint k (fun y => (pathQbar (k + 1) y + 11 / 5) ^ 2)
        (by unfold pathQbar quadratic; fun_prop)) a ha
    change probability (PF.model k) {y | |pathQbar (k + 1) y + 11 / 5| > a} ≤
      expectation (PF.model k) (fun y => (pathQbar (k + 1) y + 11 / 5) ^ 2) /
        a ^ 2 at hm
    rw [(h7 h2 k).2] at hm
    exact hm
  have hdom (k : ℕ) :
      probability (PF.model k) {y | |scaledOracle PF k y - (-11 / 15)| > η} ≤
        probability (PF.model k) {y | |betaHat (PF.model k) y| > a} +
        probability (PF.model k) {y | |pathQbar (k + 1) y + 11 / 5| > a} := by
    letI : IsProbabilityMeasure (PF.model k).law := (PF.model k).probability
    have hinc : {y | |scaledOracle PF k y - (-11 / 15)| > η} ≤ᵐ[(PF.model k).law]
        ({y | |betaHat (PF.model k) y| > a} ∪
          {y | |pathQbar (k + 1) y + 11 / 5| > a}) := by
      filter_upwards [h9 h2 k] with y hL
      intro hy
      by_contra hout
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hout
      rcases hout with ⟨hHy, hQy⟩
      have hHs : betaHat (PF.model k) y ^ 2 ≤ a ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (betaHat (PF.model k) y)) ha.le).mpr hHy
      have hHsq : betaHat (PF.model k) y ^ 2 ≤ a := hHs.trans haa
      have hprod : |betaHat (PF.model k) y * pathLbar (k + 1) y| ≤ a * (61 / 5) := by
        rw [abs_mul]
        exact mul_le_mul hHy hL (abs_nonneg _) ha.le
      have hQbounds := abs_le.mp hQy
      have hprodbounds := abs_le.mp hprod
      have hid : scaledOracle PF k y - (-11 / 15) =
          ((pathQbar (k + 1) y + 11 / 5) -
            2 * (betaHat (PF.model k) y * pathLbar (k + 1) y) +
            7 * betaHat (PF.model k) y ^ 2) / 3 := by
        rw [hstat]
        ring
      have herror : |scaledOracle PF k y - (-11 / 15)| ≤ (54 / 5) * a := by
        rw [hid, abs_le]
        constructor <;> nlinarith only [hQbounds.1, hQbounds.2, hprodbounds.1,
          hprodbounds.2, hHsq, ha.le, sq_nonneg (betaHat (PF.model k) y)]
      change η < |scaledOracle PF k y - (-11 / 15)| at hy
      linarith
    change (PF.model k).law.real _ ≤ (PF.model k).law.real _ + (PF.model k).law.real _
    calc
      _ ≤ (PF.model k).law.real
          ({y | |betaHat (PF.model k) y| > a} ∪
            {y | |pathQbar (k + 1) y + 11 / 5| > a}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)
      _ ≤ _ := measureReal_union_le _ _
  let C : ℝ := ((29 / 45) + (28836 / 625)) / a ^ 2
  have hlim : Tendsto (fun k : ℕ => C / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_) hlim
  calc
    probability (PF.model k) {y | |scaledOracle PF k y - (-11 / 15)| > η} ≤
        probability (PF.model k) {y | |betaHat (PF.model k) y| > a} +
        probability (PF.model k) {y | |pathQbar (k + 1) y + 11 / 5| > a} := hdom k
    _ ≤ (29 / (45 * ((k : ℝ) + 1))) / a ^ 2 +
        (28836 / (625 * ((k : ℝ) + 1))) / a ^ 2 :=
      add_le_add (htailH k) (htailQ k)
    _ = C / ((k + 1 : ℕ) : ℝ) := by
      have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
      dsimp only [C]
      push_cast
      field_simp [ne_of_gt ha, hk0]
      <;> ring

end

end AronowAudit.P011.Wave1.PropositionOne
