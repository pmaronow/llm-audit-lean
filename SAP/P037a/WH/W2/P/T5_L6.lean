import SAP.P037a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2.P.T5_L6

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

private theorem gamma_lintegralW2 (m : ℕ) :
    ∫⁻ t : ℝ, (Ioi 0).indicator
      (fun t => ENNReal.ofReal (t^m * Real.exp (-t))) t ∂(volume : Measure ℝ) =
      (m.factorial : ℝ≥0∞) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => t^m * Real.exp (-t)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (pow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  calc
    ∫⁻ t : ℝ, (Ioi 0).indicator
        (fun t => ENNReal.ofReal (t^m * Real.exp (-t))) t ∂(volume : Measure ℝ)
        = ∫⁻ t in Ioi 0, ENNReal.ofReal (t^m * Real.exp (-t)) ∂volume :=
          lintegral_indicator measurableSet_Ioi _
    _ = ENNReal.ofReal (∫ t in Ioi 0, t^m * Real.exp (-t) ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal (SAP.P037a.WH.W2.gamma_integrableW2 m) hnn).symm
    _ = (m.factorial : ℝ≥0∞) := by
      rw [AronowAudit.P037.simplex_gamma_integral]
      simp

theorem joint_set_lintegralW2 (m : ℕ) (s : Set (Fin m → ℝ))
    (hs : MeasurableSet s) :
    ∫⁻ z : Fin (m+1) → ℝ,
      (headCoordinatesW2 m ⁻¹' s).indicator (normalizationJointDensityW2 m) z
        ∂(volume : Measure (Fin (m+1) → ℝ)) =
      (m.factorial : ℝ≥0∞) * volume (openSimplex m ∩ s) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) (Fin.last m)
  let F : ℝ × (Fin m → ℝ) → ℝ≥0∞ := fun x =>
    if x.2 ∈ openSimplex m ∩ s ∧ 0 < x.1 then
      ENNReal.ofReal (x.1^m * Real.exp (-x.1)) else 0
  have hsimplex : MeasurableSet (openSimplex m ∩ s) :=
    (measurable_openSimplexW2 m).inter hs
  have hcondition : MeasurableSet {x : ℝ × (Fin m → ℝ) |
      x.2 ∈ openSimplex m ∩ s ∧ 0 < x.1} := by
    exact (hsimplex.preimage measurable_snd).inter
      (measurableSet_lt measurable_const measurable_fst)
  have hF : Measurable F := by
    exact Measurable.ite hcondition (by fun_prop) measurable_const
  have hcoord : ∀ x : ℝ × (Fin m → ℝ),
      headCoordinatesW2 m (e.symm x) = x.2 := by
    intro x
    ext i
    simp [headCoordinatesW2, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.snocEquiv, Fin.snoc]
  have hlast : ∀ x : ℝ × (Fin m → ℝ), e.symm x (Fin.last m) = x.1 := by
    intro x
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.snocEquiv, Fin.snoc]
  have hfun : (fun x : ℝ × (Fin m → ℝ) =>
      (((headCoordinatesW2 m) ⁻¹' s).indicator
        (normalizationJointDensityW2 m)) (e.symm x)) = F := by
    funext x
    rcases x with ⟨t,q⟩
    by_cases hqs : q ∈ s <;> by_cases hopen : q ∈ openSimplex m <;>
      simp [F, normalizationJointDensityW2, normalizationDomainW2,
        Set.indicator_apply, Set.mem_preimage, Set.mem_inter_iff,
        hcoord, hlast, hqs, hopen]
  have hmp : MeasurePreserving e (volume : Measure (Fin (m+1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
    exact (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) (Fin.last m))
  calc
    _ = ∫⁻ x : ℝ × (Fin m → ℝ),
        ((headCoordinatesW2 m ⁻¹' s).indicator
          (normalizationJointDensityW2 m)) (e.symm x)
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
          symm
          exact hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding _
    _ = ∫⁻ x : ℝ × (Fin m → ℝ), F x
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by rw [hfun]
    _ = ∫⁻ q : Fin m → ℝ, ∫⁻ t : ℝ, F (t,q) ∂volume ∂volume :=
          lintegral_prod_symm' F hF
    _ = (m.factorial : ℝ≥0∞) * volume (openSimplex m ∩ s) := by
      rw [lintegral_congr]
      · rw [lintegral_indicator_const (measurable_openSimplexW2 m |>.inter hs)]
      · intro q
        by_cases hq : q ∈ openSimplex m ∩ s
        · rcases hq with ⟨hopen, hqs⟩
          simpa [F, hopen, hqs, Set.indicator_apply] using gamma_lintegralW2 m
        · have hn : ¬ (q ∈ openSimplex m ∧ q ∈ s) := by
            simpa [Set.mem_inter_iff] using hq
          simp [F, Set.mem_inter_iff, hn]

end SAP.P037a.WH.W2.P.T5_L6

namespace SAP.P037a.WH.W2

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

theorem T5_L6_proof : SAP.P037a.WH.W2.T5_L6 := by
  intro m
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_headW2 m) hs, normalizationJointLawW2,
    withDensity_apply _ (hs.preimage (measurable_headW2 m))]
  rw [← lintegral_indicator (hs.preimage (measurable_headW2 m))]
  rw [SAP.P037a.WH.W2.P.T5_L6.joint_set_lintegralW2 m s hs]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply hs]
  simp [Set.inter_comm]

end SAP.P037a.WH.W2
