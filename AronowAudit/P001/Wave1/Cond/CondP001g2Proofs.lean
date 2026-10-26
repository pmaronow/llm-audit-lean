import AronowAudit.Literature.CondP001g2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace AronowAudit.P001.Wave1

universe u v
noncomputable section
local instance instDecidableCondP001g2 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Translate the event definition of CI to the sigma-field formulation of conditional independence. -/
lemma CondP001g2_ci_join
    (hK : AronowAudit.Literature.Kallenberg2002Prop6_6.{u})
    {Ω : Type u} {E : Type v} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y : Ω → ℝ × ℝ) (hY : Measurable Y) (D : Ω → ℝ) (hD : Measurable D)
    (hCI : CI μ X hX Y D) (d : ℝ) :
    μ[Set.indicator {ω | D ω = d} (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap X inferInstance] =ᵐ[μ]
    μ[Set.indicator {ω | D ω = d} (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] := by
  apply (hK Ω inferInstance μ inferInstance
    (MeasurableSpace.comap Y inferInstance) (MeasurableSpace.comap X inferInstance)
    (MeasurableSpace.comap D inferInstance) hY.comap_le hX.comap_le hD.comap_le).mp
  · intro s t hs ht
    rcases hs with ⟨A, hA, rfl⟩
    rcases ht with ⟨B, hB, rfl⟩
    have hs' : (Y ⁻¹' A).indicator (fun _ => (1 : ℝ)) =
        (fun ω => if Y ω ∈ A then 1 else 0) := by
      funext ω
      by_cases h : Y ω ∈ A <;> simp [h]
    have ht' : (D ⁻¹' B).indicator (fun _ => (1 : ℝ)) =
        (fun ω => if D ω ∈ B then 1 else 0) := by
      funext ω
      by_cases h : D ω ∈ B <;> simp [h]
    have hst' : (Y ⁻¹' A ∩ D ⁻¹' B).indicator (fun _ => (1 : ℝ)) =
        (fun ω => if Y ω ∈ A ∧ D ω ∈ B then 1 else 0) := by
      funext ω
      by_cases h : Y ω ∈ A ∧ D ω ∈ B <;> simp [h]
    rw [hs', ht', hst']
    exact hCI A B hA hB
  · exact ⟨{d}, measurableSet_singleton d, rfl⟩

/-- Integrate the arm indicator against an integrable, conditioning-measurable outcome on a cell. -/
lemma CondP001g2_cell_arm
    {Ω : Type u} {E : Type v} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (J : MeasurableSpace Ω) (hJ : J ≤ mΩ)
    (hXJ : Measurable[J] X) (Y : Ω → ℝ) (hYJ : Measurable[J] Y)
    (hi : Integrable Y μ) (A : Set Ω) (hA : MeasurableSet[mΩ] A) (q : E → ℝ)
    (hq : μ[Set.indicator A (fun _ => (1 : ℝ)) | J] =ᵐ[μ] (q ∘ X)) (x : E) :
    (∫ ω in {ω | X ω = x} ∩ A, Y ω ∂μ) =
      q x * (∫ ω in {ω | X ω = x}, Y ω ∂μ) := by
  let C : Set Ω := {ω | X ω = x}
  let f : Ω → ℝ := C.indicator Y
  let g : Ω → ℝ := A.indicator (fun _ => 1)
  have hC : MeasurableSet[mΩ] C := hX (measurableSet_singleton x)
  have hCJ : MeasurableSet[J] C := hXJ (measurableSet_singleton x)
  have hfg : f * g = (C ∩ A).indicator Y := by
    funext ω
    by_cases hc : ω ∈ C <;> by_cases ha : ω ∈ A <;>
      simp [f, g, hc, ha]
  have hiFG : Integrable (f * g) μ := hfg ▸ hi.indicator (hC.inter hA)
  have hiG : Integrable g μ := (integrable_const (1 : ℝ)).indicator hA
  have hCE := condExp_mul_of_stronglyMeasurable_left
    (hYJ.stronglyMeasurable.indicator hCJ) hiFG hiG (m := J)
  have hprod : f * μ[g | J] =ᵐ[μ] (fun ω => q x * f ω) := by
    filter_upwards [hq] with ω hω
    change f ω * (μ[g | J]) ω = q x * f ω
    rw [hω]
    by_cases hc : ω ∈ C
    · have hx : X ω = x := hc
      simp [hx, mul_comm]
    · simp [f, Set.indicator_of_notMem hc]
  calc
    (∫ ω in C ∩ A, Y ω ∂μ) = ∫ ω, (f * g) ω ∂μ := by
      rw [hfg, integral_indicator (hC.inter hA)]
    _ = ∫ ω, (μ[f * g | J]) ω ∂μ := (integral_condExp hJ).symm
    _ = ∫ ω, q x * f ω ∂μ := integral_congr_ae (hCE.trans hprod)
    _ = q x * (∫ ω in C, Y ω ∂μ) := by
      simp only [integral_const_mul, f, integral_indicator hC]

/-- Cancel the strictly positive arm probability on each covariate cell. -/
lemma CondP001g2_identify_cell
    {Ω : Type u} {E : Type v} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (J : MeasurableSpace Ω) (hJ : J ≤ mΩ)
    (hXJ : Measurable[J] X) (Y : Ω → ℝ) (hYJ : Measurable[J] Y)
    (hi : Integrable Y μ) (A : Set Ω) (hA : MeasurableSet[mΩ] A) (q : E → ℝ)
    (hq : μ[Set.indicator A (fun _ => (1 : ℝ)) | J] =ᵐ[μ] (q ∘ X))
    (hqpos : ∀ ω, 0 < q (X ω)) (Z : Ω → ℝ) (hZ : ∀ ω ∈ A, Z ω = Y ω)
    (m : E → ℝ) (hm : @IsCEF Ω E mΩ _ (μ.restrict A) X Z m) (x : E) :
    (∫ ω in {ω | X ω = x}, Y ω ∂μ) = m x * @prob Ω mΩ μ {ω | X ω = x} := by
  let instAmbientCondP001g2 : MeasurableSpace Ω := mΩ
  let C : Set Ω := {ω | X ω = x}
  have hC : MeasurableSet[mΩ] C := hX (measurableSet_singleton x)
  have hmass := CondP001g2_cell_arm μ X hX J hJ hXJ (fun _ => 1) measurable_const
    (integrable_const 1) A hA q hq x
  have hYarm := CondP001g2_cell_arm μ X hX J hJ hXJ Y hYJ hi A hA q hq x
  have hmcell := hm.2.2.2 {x} (measurableSet_singleton x)
  change (∫ ω in C, Z ω ∂μ.restrict A) = (∫ ω in C, m (X ω) ∂μ.restrict A) at hmcell
  rw [Measure.restrict_restrict hC] at hmcell
  have hleft : (∫ ω in C ∩ A, Z ω ∂μ) = ∫ ω in C ∩ A, Y ω ∂μ :=
    setIntegral_congr_fun (hC.inter hA) (fun ω hω => hZ ω hω.2)
  have hright : (∫ ω in C ∩ A, m (X ω) ∂μ) = m x * @prob Ω mΩ μ (C ∩ A) := by
    calc
      _ = ∫ _ in C ∩ A, m x ∂μ := setIntegral_congr_fun (hC.inter hA)
        (fun ω hω => by rw [show X ω = x from hω.1])
      _ = _ := by simp [prob, mul_comm, Measure.real_def]
  rw [hleft, hright] at hmcell
  have hmass' : @prob Ω mΩ μ (C ∩ A) = q x * @prob Ω mΩ μ C := by
    simpa [prob, Measure.real_def] using hmass
  rw [hmass'] at hmcell
  by_cases he : C.Nonempty
  · obtain ⟨ω, hω⟩ := he
    have hqx : q x ≠ 0 := (show 0 < q x by simpa [show X ω = x from hω] using hqpos ω).ne'
    apply mul_left_cancel₀ hqx
    calc
      q x * (∫ ω in C, Y ω ∂μ) = m x * (q x * @prob Ω mΩ μ C) := hYarm.symm.trans hmcell
      _ = q x * (m x * @prob Ω mΩ μ C) := by ring
  · have hc0 : C = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    change (∫ ω in C, Y ω ∂μ) = m x * @prob Ω mΩ μ C
    simp [hc0, prob]

/-- Sum cell integrals over the countable covariate partition. -/
lemma CondP001g2_sum_cells
    {Ω : Type u} {E : Type v} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E] (μ : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (Y : Ω → ℝ) (hi : Integrable Y μ)
    (m : E → ℝ) (hc : ∀ x, (∫ ω in {ω | X ω = x}, Y ω ∂μ) =
      m x * prob μ {ω | X ω = x}) :
    mean μ Y = ∑' x : E, m x * prob μ {ω | X ω = x} := by
  have hu : (⋃ x : E, {ω | X ω = x}) = Set.univ := by
    ext ω
    simp
  have hd : Pairwise (fun x y : E => Disjoint {ω | X ω = x} {ω | X ω = y}) := by
    intro x y hxy
    exact Set.disjoint_left.mpr (fun ω hx hy => hxy (hx.symm.trans hy))
  have hh := integral_iUnion (s := fun x : E => {ω | X ω = x}) (fun x => hX (measurableSet_singleton x)) hd hi.integrableOn
  rw [hu, Measure.restrict_univ] at hh
  exact hh.trans (tsum_congr hc)

/-- The discrete ATE identity, conditional on the stated published CI theorem. -/
theorem explicit_ignorability_discrete_ate_conditional :
    AronowAudit.P001.explicit_ignorability_discrete_ate_conditional_statement := by
  intro hK Ω E mΩ mE _ _ μ _ X hX Y0 Y1 D h0 h1 hD hi0 hi1 hbinary
    p hp ε hε hpos hCI m0 m1 hm0 hm1 hmi0 hmi1
  have hInd1 : Set.indicator {ω | D ω = 1} (fun _ => (1 : ℝ)) = D := by
    funext ω
    rcases hbinary ω with h | h <;> simp [h]
  have hInd0 : Set.indicator {ω | D ω = 0} (fun _ => (1 : ℝ)) =
      (fun _ => (1 : ℝ)) - D := by
    funext ω
    rcases hbinary ω with h | h <;> simp [h]
  have hpCE := (isCEF_condExp μ X hX D p hp).symm
  have hjoin := CondP001g2_ci_join hK μ X hX (fun ω => (Y0 ω, Y1 ω))
    (h0.prodMk h1) D hD hCI 1
  let J : MeasurableSpace Ω :=
    MeasurableSpace.comap (fun ω => (Y0 ω, Y1 ω)) inferInstance ⊔
      MeasurableSpace.comap X inferInstance
  have hJ : J ≤ mΩ := sup_le (h0.prodMk h1).comap_le hX.comap_le
  have hXJ : Measurable[J] X := measurable_iff_comap_le.mpr le_sup_right
  have hYJ : Measurable[J] (fun ω => (Y0 ω, Y1 ω)) :=
    measurable_iff_comap_le.mpr le_sup_left
  have h0J : Measurable[J] Y0 := measurable_fst.comp hYJ
  have h1J : Measurable[J] Y1 := measurable_snd.comp hYJ
  have hCE1 : μ[Set.indicator {ω | D ω = 1} (fun _ => (1 : ℝ)) | J] =ᵐ[μ] p ∘ X := by
    exact hjoin.trans (by simpa only [hInd1] using hpCE)
  have hCED : μ[D | J] =ᵐ[μ] p ∘ X := by simpa only [hInd1] using hCE1
  have hCE0 : μ[Set.indicator {ω | D ω = 0} (fun _ => (1 : ℝ)) | J] =ᵐ[μ]
      (fun x => 1 - p x) ∘ X := by
    rw [hInd0]
    have hs := condExp_sub (integrable_const (1 : ℝ)) hp.2.1 J
    filter_upwards [hs, hCED] with ω hsω hdω
    simpa only [Pi.sub_apply, condExp_const hJ, hdω, Function.comp_apply] using hsω
  let instAmbientCondP001g2Final : MeasurableSpace Ω := mΩ
  have hc0 : ∀ x : E, (∫ ω in {ω | X ω = x}, Y0 ω ∂μ) =
      m0 x * prob μ {ω | X ω = x} := by
    intro x
    refine CondP001g2_identify_cell μ X hX J hJ hXJ Y0 h0J hi0
      {ω | D ω = 0} (hD (measurableSet_singleton 0)) (fun x => 1 - p x) hCE0
      ?_ (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) ?_ m0 hm0 x
    · intro ω
      have hh := (hpos ω).2
      linarith
    · intro ω hω
      simp [observedOutcome, show D ω = 0 from hω]
  have hc1 : ∀ x : E, (∫ ω in {ω | X ω = x}, Y1 ω ∂μ) =
      m1 x * prob μ {ω | X ω = x} := by
    intro x
    refine CondP001g2_identify_cell μ X hX J hJ hXJ Y1 h1J hi1
      {ω | D ω = 1} (hD (measurableSet_singleton 1)) p hCE1
      ?_ (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) ?_ m1 hm1 x
    · intro ω
      exact lt_trans hε (hpos ω).1
    · intro ω hω
      simp [observedOutcome, show D ω = 1 from hω]
  have hs0 := CondP001g2_sum_cells μ X hX Y0 hi0 m0 hc0
  have hs1 := CondP001g2_sum_cells μ X hX Y1 hi1 m1 hc1
  change (∫ ω, Y1 ω - Y0 ω ∂μ) = _
  rw [integral_sub hi1 hi0]
  exact congrArg₂ (fun a b : ℝ => a - b) hs1 hs0

end
end AronowAudit.P001.Wave1
