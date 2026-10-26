import AronowAudit.P047.Wave1.Impossibility.N13

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n15_proof : N15.{u} := by
  classical
  intro hF s13 s14 R _ Q _ E hE n _hn M
  let r : ℝ := randRisk Q E n (1 / 12)
  let p : ℝ := (1 / 2 : ℝ) ^ (M + 1)
  let θ : Bool → (Fin (M + 1) → Bool) → ℝ := fun f σ => familyEffect f (M + 1) σ
  let bad : Bool → (Fin (M + 1) → Bool) → ℝ := fun f σ =>
    if (1 / 12 : ℝ) ≤ |θ f σ - familyCenter f| then 1 else 0
  let μ : Bool → (Fin (M + 1) → Bool) → Measure ((ℕ → UnitData) × R) :=
    fun f σ => (sampleLaw (familyMeasure M f σ)).prod Q
  let T : Set ((Fin n → ObservedUnit) × R) := {o | (1 / 2 : ℝ) ≤ E n o}
  let T' : Set ((ℕ → UnitData) × R) := {z | (observedSample n z.1, z.2) ∈ T}
  have hT : MeasurableSet T := measurableSet_le measurable_const (hE n)
  have hT' : MeasurableSet T' := hT.preimage (measurable_sample_seed n)
  have hb (f : Bool) : (∑ σ : Fin (M + 1) → Bool, p * bad f σ) ≤ 16 / (M + 1 : ℝ) :=
    s14 f M
  have hrbounded : BddAbove
      (insert (0 : ℝ) {x | ∃ L : CausalLaw, UnknownModel L ∧
        x = ((sampleLaw L.measure).prod Q).real
          {z | (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - ate L|}}) := by
    refine ⟨1, ?_⟩
    rintro x (rfl | ⟨L, _hL, rfl⟩)
    · norm_num
    · exact measureReal_le_one
  have hrnonneg : 0 ≤ r := le_csSup hrbounded (Set.mem_insert _ _)
  have hmodel (f : Bool) (σ : Fin (M + 1) → Bool) :
      (μ f σ).real {z | (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - θ f σ|} ≤ r := by
    obtain ⟨L, hmeasure, hL, hate⟩ := hF M f σ
    have hh : ((sampleLaw L.measure).prod Q).real
        {z | (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - ate L|} ≤
        randRisk Q E n (1 / 12) :=
      le_csSup hrbounded (Set.mem_insert_of_mem _ ⟨L, hL, rfl⟩)
    simpa only [hmeasure, hate] using hh
  have hA (σ : Fin (M + 1) → Bool) : 1 - r - bad true σ ≤ (μ true σ).real T' := by
    by_cases hbad : (1 / 12 : ℝ) ≤ |θ true σ - familyCenter true|
    · have hprob : 0 ≤ (μ true σ).real T' := measureReal_nonneg
      simp only [bad, if_pos hbad]
      linarith
    · have hgood : |θ true σ - familyCenter true| < (1 / 12 : ℝ) := lt_of_not_ge hbad
      have hlow := (abs_lt.mp hgood).1
      change -(1 / 12 : ℝ) < θ true σ - 2 / 3 at hlow
      have hincl : T'ᶜ ⊆
          {z | (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - θ true σ|} := by
        intro z hz
        change ¬ (1 / 2 : ℝ) ≤ E n (observedSample n z.1, z.2) at hz
        have hzlt := lt_of_not_ge hz
        change (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - θ true σ|
        by_contra! herr
        have herror := (abs_lt.mp herr).1
        linarith
      have herr : (μ true σ).real T'ᶜ ≤ r :=
        (measureReal_mono hincl).trans (hmodel true σ)
      have hsum : (μ true σ).real T' + (μ true σ).real T'ᶜ = 1 := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using
          (measureReal_add_measureReal_compl (μ := μ true σ) hT')
      simp only [bad, if_neg hbad, sub_zero]
      linarith
  have hB (σ : Fin (M + 1) → Bool) : (μ false σ).real T' ≤ r + bad false σ := by
    by_cases hbad : (1 / 12 : ℝ) ≤ |θ false σ - familyCenter false|
    · have hprob : (μ false σ).real T' ≤ 1 := measureReal_le_one
      simp only [bad, if_pos hbad]
      linarith
    · have hgood : |θ false σ - familyCenter false| < (1 / 12 : ℝ) := lt_of_not_ge hbad
      have hhigh := (abs_lt.mp hgood).2
      change θ false σ - 1 / 3 < (1 / 12 : ℝ) at hhigh
      have hincl : T' ⊆
          {z | (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - θ false σ|} := by
        intro z hz
        change (1 / 2 : ℝ) ≤ E n (observedSample n z.1, z.2) at hz
        change (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - θ false σ|
        by_contra! herr
        have herror := (abs_lt.mp herr).2
        linarith
      have herr : (μ false σ).real T' ≤ r :=
        (measureReal_mono hincl).trans (hmodel false σ)
      simpa only [bad, if_neg hbad, add_zero] using herr
  let pA : ℝ := ∑ σ : Fin (M + 1) → Bool, p * (μ true σ).real T'
  let pB : ℝ := ∑ σ : Fin (M + 1) → Bool, p * (μ false σ).real T'
  let p0 : ℝ := ((sampleLaw baselineLaw).prod Q).real T'
  have hp : 0 ≤ p := by positivity
  have hAavg : 1 - r - (∑ σ : Fin (M + 1) → Bool, p * bad true σ) ≤ pA := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (M + 1) → Bool)))
      (fun σ _ => mul_le_mul_of_nonneg_left (hA σ) hp)
    have heq : (∑ σ : Fin (M + 1) → Bool, p * (1 - r - bad true σ)) =
        1 - r - (∑ σ : Fin (M + 1) → Bool, p * bad true σ) := by
      simp only [p, mul_sub, Finset.sum_sub_distrib, prior_average_const]
    rw [heq] at hh
    exact hh
  have hBavg : pB ≤ r + (∑ σ : Fin (M + 1) → Bool, p * bad false σ) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (M + 1) → Bool)))
      (fun σ _ => mul_le_mul_of_nonneg_left (hB σ) hp)
    have heq : (∑ σ : Fin (M + 1) → Bool, p * (r + bad false σ)) =
        r + (∑ σ : Fin (M + 1) → Bool, p * bad false σ) := by
      simp only [p, mul_add, Finset.sum_add_distrib, prior_average_const]
    rw [heq] at hh
    exact hh
  have hAtest : 1 - r - 16 / (M + 1 : ℝ) ≤ pA := by linarith [hb true]
  have hBtest : pB ≤ r + 16 / (M + 1 : ℝ) := by linarith [hb false]
  let d : ℝ := (n : ℝ) * (n - 1) / (2 * (M + 1))
  have hTVA : |pA - p0| ≤ d := s13 Q M true n T hT
  have hTVB : |pB - p0| ≤ d := s13 Q M false n T hT
  have hTVA' := (abs_le.mp hTVA).2
  have hTVB' := (abs_le.mp hTVB).1
  change (1 / 2 : ℝ) - 16 / (M + 1) - d ≤ r
  linarith

end

end AronowAudit.P047.Wave1.Impossibility
