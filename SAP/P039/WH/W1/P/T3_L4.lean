import SAP.P039.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T3_L4

open scoped ENNReal
open Filter
open MeasureTheory
open Topology

noncomputable def prim (x : ℝ) : ℝ :=
  (Real.arctan (x / Real.sqrt 3) +
    (x / Real.sqrt 3) / (1 + (x / Real.sqrt 3) ^ 2)) / Real.pi

noncomputable def den (x : ℝ) : ℝ :=
  2 / (Real.pi * Real.sqrt 3) * ((1 + x ^ 2 / 3) ^ 2)⁻¹

theorem density_eq (x : ℝ) : SAP.P039.wholeStudentDensity 3 x = den x := by
  have h32 : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  unfold SAP.P039.wholeStudentDensity
  norm_num
  rw [h32]
  simp only [den]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp [hpi, hs, hspi]
  rw [Real.sq_sqrt Real.pi_nonneg]

theorem prim_deriv (x : ℝ) : HasDerivAt prim (den x) x := by
  change HasDerivAt (fun y : ℝ =>
    (Real.arctan (y / Real.sqrt 3) +
      (y / Real.sqrt 3) / (1 + (y / Real.sqrt 3) ^ 2)) / Real.pi)
    (den x) x
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hq : HasDerivAt (fun y : ℝ => y / Real.sqrt 3) (1 / Real.sqrt 3) x := by
    simpa using (hasDerivAt_id x).div_const (Real.sqrt 3)
  have hden : HasDerivAt (fun y : ℝ => 1 + (y / Real.sqrt 3) ^ 2)
      (2 * (x / Real.sqrt 3) * (1 / Real.sqrt 3)) x := by
    convert (hasDerivAt_const x 1).add (hq.pow 2) using 1
    ring
  have hr := hq.div hden (by positivity : 1 + (x / Real.sqrt 3) ^ 2 ≠ 0)
  have ha := (Real.hasDerivAt_arctan (x / Real.sqrt 3)).comp x hq
  have hh := (ha.add hr).div_const Real.pi
  convert hh using 1
  · funext y
    rfl
  · dsimp [den]
    field_simp [hs, Real.pi_ne_zero]
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    ring_nf

theorem den_nonneg (x : ℝ) : 0 ≤ den x := by
  unfold den
  positivity

theorem den_even (x : ℝ) : den (-x) = den x := by
  simp [den]

theorem prim_tendsto_top : Tendsto prim atTop (𝓝 (1 / 2 : ℝ)) := by
  let q : ℝ → ℝ := fun x => x / Real.sqrt 3
  have hq : Tendsto q atTop atTop := by
    dsimp [q]
    exact tendsto_id.atTop_div_const (Real.sqrt_pos.mpr (by norm_num))
  have harctan : Tendsto (fun x => Real.arctan (q x)) atTop
      (𝓝 (Real.pi / 2)) := by
    exact (Real.tendsto_arctan_atTop.comp hq).mono_right nhdsWithin_le_nhds
  have hinv : Tendsto (fun x => (q x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hq
  have hbounds : ∀ᶠ x in atTop,
      0 ≤ q x / (1 + q x ^ 2) ∧ q x / (1 + q x ^ 2) ≤ (q x)⁻¹ := by
    filter_upwards [hq.eventually_ge_atTop 1] with x hx
    have hxpos : 0 < q x := by linarith
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      field_simp [ne_of_gt hxpos]
      nlinarith
  have hr : Tendsto (fun x => q x / (1 + q x ^ 2)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    · filter_upwards [hbounds] with x hx
      exact hx.1
    · filter_upwards [hbounds] with x hx
      exact hx.2
  have hsum := harctan.add hr
  convert hsum.div_const Real.pi using 1
  · funext x
    simp [prim, q, div_eq_mul_inv]
  · congr 1
    field_simp [Real.pi_ne_zero]
    ring

theorem den_integrable : Integrable den volume := by
  have hIoi : IntegrableOn den (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => prim_deriv x)
      (fun x _ => den_nonneg x) prim_tendsto_top
  have hIic : IntegrableOn den (Set.Iic 0) := by
    let m : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    have hcomp : IntegrableOn (fun x : ℝ => den (-x))
        ((fun x : ℝ => -x) ⁻¹' Set.Iic 0) volume := by
      rw [show (fun x : ℝ => -x) ⁻¹' Set.Iic 0 = Set.Ici 0 by
        ext x
        simp]
      simpa [den_even] using (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi
    exact (Measure.measurePreserving_neg volume).integrableOn_comp_preimage m |>.mp hcomp
  have hu : IntegrableOn den Set.univ := by
    rw [← Set.Iic_union_Ioi, integrableOn_union]
    exact ⟨hIic, hIoi⟩
  exact integrableOn_univ.mp hu

theorem den_abs (x : ℝ) : den |x| = den x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), den_even]

theorem tail_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, Set.indicator {x : ℝ | t ≤ |x|} den x ∂volume) =
      2 * (∫ x in Set.Ioi t, den x) := by
  let k : ℝ → ℝ := fun x => if t ≤ x then den x else 0
  have hkernel : (∫ x, Set.indicator {x : ℝ | t ≤ |x|} den x ∂volume) =
      ∫ x, k |x| ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : t ≤ |x| <;> simp [k, den_abs, hx]
  rw [hkernel, integral_comp_abs]
  congr 1
  have hk : k = Set.indicator (Set.Ici t) den := by
    funext x
    by_cases hx : t ≤ x <;> simp [k, hx]
  rw [hk, setIntegral_indicator measurableSet_Ici]
  by_cases ht0 : t = 0
  · subst t
    have hs : Set.Ioi (0 : ℝ) ∩ Set.Ici 0 = Set.Ioi 0 := by
      ext x
      simp
      intro hx
      exact le_of_lt hx
    rw [hs]
  · have htpos : 0 < t := by
      rcases lt_or_eq_of_le ht with h | h
      · exact h
      · exact (ht0 h.symm).elim
    have hs : Set.Ioi (0 : ℝ) ∩ Set.Ici t = Set.Ici t := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨lt_of_lt_of_le htpos h, h⟩
    rw [hs, integral_Ici_eq_integral_Ioi]

end SAP.P039.WH.W1.P.T3_L4

open SAP.P039.WH.W1.P.T3_L4
open MeasureTheory

theorem SAP.P039.WH.W1.T3_L4_proof : SAP.P039.WH.W1.T3_L4 := by
  intro t ht
  let A : Set ℝ := {s | t ≤ |s|}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_Ici.preimage measurable_abs
  have hcalc : (∫ x in Set.Ioi t, den x) = 1 / 2 - prim t :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => prim_deriv x)
      (fun x _ => den_nonneg x) prim_tendsto_top
  have hreal : (∫ x, Set.indicator A den x ∂volume) =
      SAP.P039.studentThreeTail t := by
    rw [tail_integral t ht, hcalc]
    simp [SAP.P039.studentThreeTail, prim]
    ring
  have hi : Integrable (Set.indicator A den) volume := den_integrable.indicator hA
  have hnn : 0 ≤ᵐ[volume] (Set.indicator A den) := by
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ A <;> simp [hx, den_nonneg]
  have htail :
      (volume.withDensity (fun s => ENNReal.ofReal (SAP.P039.wholeStudentDensity 3 s))) A =
        ENNReal.ofReal (SAP.P039.studentThreeTail t) := by
    calc
      _ = ∫⁻ s in A, ENNReal.ofReal (SAP.P039.wholeStudentDensity 3 s) :=
        withDensity_apply _ hA
      _ = ∫⁻ s, ENNReal.ofReal (Set.indicator A den s) := by
        rw [← lintegral_indicator hA]
        apply lintegral_congr_ae
        exact ae_of_all _ fun s => by
          by_cases hs : s ∈ A <;> simp [hs, density_eq]
      _ = ENNReal.ofReal (∫ s, Set.indicator A den s ∂volume) :=
        (ofReal_integral_eq_lintegral_ofReal hi hnn).symm
      _ = ENNReal.ofReal (SAP.P039.studentThreeTail t) :=
        congrArg ENNReal.ofReal hreal
  exact ⟨by simpa [A] using htail, by
    rw [← hreal]
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ A <;> simp [hx, den_nonneg]⟩
