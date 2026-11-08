import SAP.P006b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1.P.T25_L1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : IsProbabilityMeasure fairPrivateLaw := fairPrivateLaw_probability

lemma fair_atom (u : Bool) :
    (fairPrivateLaw {u}).toReal = coinMass (1/2 : ℝ) u := by
  rw [fairPrivateLaw_eq]
  cases u <;> norm_num [AronowAudit.P006.Wave1.BinaryExperiment.fairLaw,
    coinMass, Measure.real]

lemma section_integrable {X : Type} [MeasurableSpace X] (Q : Measure X)
    (hQ : IsProbabilityMeasure Q) (π : X × Bool → ℝ) (hπ : Admissible π)
    (u : Bool) : Integrable (fun x => π (x,u)) Q := by
  have hm : Measurable (fun x => π (x,u)) := hπ.1.comp (measurable_prodMk_right (y := u))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  exact ⟨by linarith [(hπ.2 (x,u)).1], (hπ.2 (x,u)).2⟩

lemma policy_mul_private_integrable {X : Type} [MeasurableSpace X]
    (Q : Measure X) (hQ : IsProbabilityMeasure Q) (π : X × Bool → ℝ)
    (hπ : Admissible π) (y : Bool → ℝ) :
    Integrable (fun c : X × Bool => π c * y c.2) (Q.prod fairPrivateLaw) := by
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure (Q.prod fairPrivateLaw) := inferInstance
  have hm : Measurable (fun c : X × Bool => π c * y c.2) :=
    hπ.1.mul ((measurable_of_finite y).comp measurable_snd)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|y false| + |y true| + 1)
  filter_upwards [] with c
  rw [Real.norm_eq_abs, abs_mul]
  have hpa : |π c| ≤ 1 := abs_le.mpr ⟨by linarith [(hπ.2 c).1], (hπ.2 c).2⟩
  cases c.2
  · calc
      |π c| * |y false| ≤ 1 * |y false| := mul_le_mul_of_nonneg_right hpa (abs_nonneg _)
      _ ≤ |y false| + |y true| + 1 := by nlinarith [abs_nonneg (y true)]
  · calc
      |π c| * |y true| ≤ 1 * |y true| := mul_le_mul_of_nonneg_right hpa (abs_nonneg _)
      _ ≤ |y false| + |y true| + 1 := by nlinarith [abs_nonneg (y false)]

lemma integral_policy_private {X : Type} [MeasurableSpace X]
    (Q : Measure X) (hQ : IsProbabilityMeasure Q) (π : X × Bool → ℝ)
    (hπ : Admissible π) (y : Bool → ℝ) :
    (∫ c, π c * y c.2 ∂Q.prod fairPrivateLaw) =
      (y false / 2) * (∫ x, π (x,false) ∂Q) +
      (y true / 2) * (∫ x, π (x,true) ∂Q) := by
  have hi := policy_mul_private_integrable Q hQ π hπ y
  rw [integral_prod _ hi]
  have hin : ∀ x, (∫ u, π (x,u) * y u ∂fairPrivateLaw) =
      (y false / 2) * π (x,false) + (y true / 2) * π (x,true) := by
    intro x
    rw [integral_bool fairPrivateLaw (1/2) fair_atom (fun u => π (x,u) * y u)]
    simp [coinMass]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hin)]
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
  · exact (section_integrable Q hQ π hπ false).const_mul _
  · exact (section_integrable Q hQ π hπ true).const_mul _

lemma integral_private_only {X : Type} [MeasurableSpace X]
    (Q : Measure X) (hQ : IsProbabilityMeasure Q) (y : Bool → ℝ) :
    (∫ c : X × Bool, y c.2 ∂Q.prod fairPrivateLaw) =
      (y false + y true) / 2 := by
  rw [integral_fun_snd]
  rw [integral_bool fairPrivateLaw (1/2) fair_atom y]
  have hqr : Q.real Set.univ = 1 := by
    change (Q Set.univ).toReal = 1
    rw [hQ.measure_univ]
    norm_num
  rw [hqr]
  simp [coinMass]
  ring

lemma coordinates_feasible {X : Type} [MeasurableSpace X] (Q : Measure X)
    (hQ : IsProbabilityMeasure Q) (π : X × Bool → ℝ) (hπ : Admissible π) :
    binaryFeasible (policyCoordinates Q π) := by
  have hi0 := section_integrable Q hQ π hπ false
  have hi1 := section_integrable Q hQ π hπ true
  constructor
  · change 0 ≤ ∫ x, π (x,false) ∂Q
    apply integral_nonneg
    intro x
    exact (hπ.2 (x,false)).1
  constructor
  · change (∫ x, π (x,false) ∂Q) ≤ 1
    calc
      (∫ x, π (x,false) ∂Q) ≤ ∫ _x : X, (1 : ℝ) ∂Q := integral_mono hi0 (integrable_const 1) (fun x => (hπ.2 (x,false)).2)
      _ = 1 := by simp [Measure.real, hQ.measure_univ]
  constructor
  · change 0 ≤ ∫ x, π (x,true) ∂Q
    apply integral_nonneg
    intro x
    exact (hπ.2 (x,true)).1
  · change (∫ x, π (x,true) ∂Q) ≤ 1
    calc
      (∫ x, π (x,true) ∂Q) ≤ ∫ _x : X, (1 : ℝ) ∂Q := integral_mono hi1 (integrable_const 1) (fun x => (hπ.2 (x,true)).2)
      _ = 1 := by simp [Measure.real, hQ.measure_univ]

lemma binaryRule_admissible {X : Type} [MeasurableSpace X] (ρ : BinaryPolicy)
    (hρ : binaryFeasible ρ) : Admissible (fun c : X × Bool => binaryRule ρ c.2) := by
  refine ⟨(SAP.P006b.WH.W1.binary_admissible ρ hρ).1.comp measurable_snd, ?_⟩
  intro c
  change 0 ≤ binaryRule ρ c.2 ∧ binaryRule ρ c.2 ≤ 1
  cases c.2
  · change 0 ≤ ρ.1 ∧ ρ.1 ≤ 1
    exact ⟨hρ.1, hρ.2.1⟩
  · change 0 ≤ ρ.2 ∧ ρ.2 ≤ 1
    exact ⟨hρ.2.2.1, hρ.2.2.2⟩

lemma coordinates_binaryRule {X : Type} [MeasurableSpace X] (Q : Measure X)
    (hQ : IsProbabilityMeasure Q) (ρ : BinaryPolicy) :
    policyCoordinates Q (fun c : X × Bool => binaryRule ρ c.2) = ρ := by
  apply Prod.ext
  · change (∫ x, ρ.1 ∂Q) = ρ.1
    simp [Measure.real, hQ.measure_univ]
  · change (∫ x, ρ.2 ∂Q) = ρ.2
    simp [Measure.real, hQ.measure_univ]

lemma endpoint_false {X : Type} [MeasurableSpace X] (Q : Measure X)
    (hQ : IsProbabilityMeasure Q) (π : X × Bool → ℝ) (hπ : Admissible π) :
    ((∫ x, π (x,false) ∂Q) = 1 ↔ ∀ᵐ x ∂Q, π (x,false) = 1) := by
  have hi := section_integrable Q hQ π hπ false
  have hsub : Integrable (fun x => 1 - π (x,false)) Q := (integrable_const 1).sub hi
  have hnon : ∀ x, 0 ≤ 1 - π (x,false) := fun x => sub_nonneg.mpr (hπ.2 (x,false)).2
  constructor
  · intro heq
    have hz : (∫ x, 1 - π (x,false) ∂Q) = 0 := by
      rw [integral_sub (integrable_const 1) hi]
      simp [Measure.real, hQ.measure_univ, heq]
    have hzero := (integral_eq_zero_iff_of_nonneg hnon hsub).mp hz
    filter_upwards [hzero] with x hx
    dsimp at hx
    linarith
  · intro hae
    have hpi : (fun x => π (x,false)) =ᵐ[Q] (fun _ => (1 : ℝ)) := hae
    have he := integral_congr_ae hpi
    have hqr : Q.real Set.univ = 1 := by
      change (Q Set.univ).toReal = 1
      rw [hQ.measure_univ]
      norm_num
    rw [integral_const, hqr] at he
    simpa using he

lemma endpoint_true {X : Type} [MeasurableSpace X] (Q : Measure X)
    (hQ : IsProbabilityMeasure Q) (π : X × Bool → ℝ) (hπ : Admissible π) :
    ((∫ x, π (x,true) ∂Q) = 0 ↔ ∀ᵐ x ∂Q, π (x,true) = 0) := by
  have hi := section_integrable Q hQ π hπ true
  have hnon : ∀ x, 0 ≤ π (x,true) := fun x => (hπ.2 (x,true)).1
  constructor
  · intro heq
    exact (integral_eq_zero_iff_of_nonneg hnon hi).mp heq
  · intro hae
    exact (integral_congr_ae hae).trans (by simp)

end

end SAP.P006b.WH.W1.P.T25_L1

theorem SAP.P006b.WH.W1.T25_L1_proof : SAP.P006b.WH.W1.T25_L1 := by
  intro X mX Q hQ
  letI : MeasureTheory.IsProbabilityMeasure fairPrivateLaw := fairPrivateLaw_probability
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ
    exact ⟨SAP.P006b.WH.W1.P.T25_L1.binaryRule_admissible ρ hρ,
      SAP.P006b.WH.W1.P.T25_L1.coordinates_binaryRule Q hQ ρ⟩
  · intro α
    constructor
    · have h := SAP.P006b.WH.W1.P.T25_L1.integral_private_only Q hQ
        (fun u => |(0 : ℝ)-lowerBoundY0 α u|)
      simpa [lowerBoundY0] using h
    · intro x
      rw [integral_bool fairPrivateLaw (1/2) SAP.P006b.WH.W1.P.T25_L1.fair_atom
        (lowerBoundY0 α)]
      simp [lowerBoundY0, coinMass]
      ring
  · intro π hπ
    refine ⟨SAP.P006b.WH.W1.P.T25_L1.coordinates_feasible Q hQ π hπ, ?_, ?_, ?_, ?_⟩
    · intro β η
      rw [SAP.P006b.WH.W1.P.T25_L1.integral_policy_private Q hQ π hπ (lowerBoundY1 β η)]
      have hf := SAP.P006b.WH.W1.lowerBound_formulas 0 β η (policyCoordinates Q π)
      rw [hf.1]
      simp [lowerBoundY1, policyCoordinates]
      ring
    · intro α β η
      rw [SAP.P006b.WH.W1.P.T25_L1.integral_policy_private Q hQ π hπ
        (fun u => lowerBoundY1 β η u-lowerBoundY0 α u)]
      rw [SAP.P006b.WH.W1.lowerBound_formulas α β η (policyCoordinates Q π) |>.2.1]
      simp [lowerBoundWelfare, lowerBoundY0, lowerBoundY1, binaryWelfare, policyCoordinates]
      ring
    · exact SAP.P006b.WH.W1.P.T25_L1.endpoint_false Q hQ π hπ
    · exact SAP.P006b.WH.W1.P.T25_L1.endpoint_true Q hQ π hπ
