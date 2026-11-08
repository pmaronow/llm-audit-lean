import SAP.P027a.WH.W2.P.T13_L2Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P027a SAP.P027a.WH.W2 SAP.P027a.WH.W2.P.T13_L2
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem SAP.P027a.WH.W2.T13_L2_proof : SAP.P027a.WH.W2.T13_L2 := by
  classical
  intro N hN m hm hmN hpos
  let α : Type := Fin N → ℕ
  let μ : MeasureTheory.Measure α := nbProductLawN N
  let ν : MeasureTheory.Measure (ℕ → α) := redrawSizeSequenceLaw N
  let F : Set α := feasibleSizeVectors N m
  let z : α := fun _ => 0
  have hμprob : IsProbabilityMeasure μ := by
    exact AronowAudit.P027.Wave1.all_pps_product_probability N
  letI : IsProbabilityMeasure μ := hμprob
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, redrawSizeSequenceLaw]
    infer_instance
  letI : Countable α := by infer_instance
  have hF : MeasurableSet F := (Set.to_countable _).measurableSet
  let p : ENNReal := μ F
  let q : ENNReal := μ Fᶜ
  have hp : 0 < p := hpos
  have hp_le : p ≤ 1 := by
    calc
      p = μ F := rfl
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ F)
      _ = 1 := measure_univ
  have hp_finite : p ≠ ⊤ := by
    dsimp [p]
    exact measure_ne_top μ F
  have hcomp : p + q = 1 := by
    dsimp [p, q]
    exact (measure_add_measure_compl hF).trans (by simp)
  have hq_eq : q = 1 - p := by
    calc
      q = μ Fᶜ := rfl
      _ = μ Set.univ - μ F := measure_compl hF (measure_ne_top μ F)
      _ = 1 - p := by simp [p]
  have hq_lt : q < 1 := by
    rw [hq_eq]
    exact ENNReal.sub_lt_self (by norm_num) (by norm_num) (ne_of_gt hp)
  have hgeom_factor : 1 - q = p := by
    calc
      1 - q = (p + q) - q := by rw [hcomp]
      _ = p := ENNReal.add_sub_cancel_right (measure_ne_top μ Fᶜ)
  have hgeom_total : (∑' n : ℕ, q ^ n) * p = 1 := by
    rw [ENNReal.tsum_geometric, hgeom_factor]
    exact ENNReal.inv_mul_cancel (ne_of_gt hp) hp_finite
  have hterm_meas : MeasurableSet (⋃ n, firstHit F n) :=
    MeasurableSet.iUnion (fun n => firstHit_measurable F n hF)
  have hterm_measure : ν (⋃ n, firstHit F n) = 1 := by
    change Measure.infinitePi (fun _ : ℕ => μ) (⋃ n, firstHit F n) = 1
    rw [MeasureTheory.measure_iUnion (firstHit_pairwise F)
      (fun n => firstHit_measurable F n hF)]
    simp_rw [firstHit_measure μ F _ hF]
    calc
      (∑' n : ℕ, (μ Fᶜ) ^ n * μ F) =
          (∑' n : ℕ, (μ Fᶜ) ^ n) * μ F := ENNReal.tsum_mul_right
      _ = 1 := hgeom_total
  have hno_eq : noHit F = (⋃ n, firstHit F n)ᶜ := by
    ext w
    simp only [noHit, Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · rintro h ⟨n, hn⟩
      exact h ⟨n, hn.2⟩
    · rintro h ⟨n, hn⟩
      let hex : ∃ n, w n ∈ F := ⟨n, hn⟩
      let k := Nat.find hex
      apply h
      refine ⟨k, ?_⟩
      refine ⟨?_, Nat.find_spec hex⟩
      intro i hi hmem
      have hle := Nat.find_min' hex hmem
      omega
  have hno : ν (noHit F) = 0 := by
    rw [hno_eq, measure_compl hterm_meas (measure_ne_top _ _), measure_univ,
      hterm_measure]
    simp
  have hno_meas : MeasurableSet (noHit F) := by
    rw [hno_eq]
    exact hterm_meas.compl
  have hterm_ae : ∀ᵐ w ∂ν, ∃ n, w n ∈ F := by
    rw [ae_iff]
    simpa [noHit] using hno
  have hmout : Measurable (redrawSizeOutput N m) := by
    apply measurable_to_countable'
    intro x
    rw [show (redrawSizeOutput N m) ⁻¹' {x} =
      (⋃ n, firstExact F n x) ∪ (if x = z then noHit F else ∅) from ?_]
    · apply (MeasurableSet.iUnion (fun n => firstExact_measurable F n x hF)).union
      by_cases hx : x = z
      · simpa [hx] using hno_meas
      · simp [hx]
    · ext w
      simpa [redrawSizeOutput, F, z] using
        (Set.ext_iff.mp (output_preimage F x z) w)
  have hpre_formula : ∀ x : α,
      ν ((redrawSizeOutput N m) ⁻¹' {x}) = p⁻¹ * μ ({x} ∩ F) := by
    intro x
    rw [show (redrawSizeOutput N m) ⁻¹' {x} =
      (⋃ n, firstExact F n x) ∪ (if x = z then noHit F else ∅) from by
      ext w
      simpa [redrawSizeOutput, F, z] using
        (Set.ext_iff.mp (output_preimage F x z) w)]
    let U : Set (ℕ → α) := ⋃ n, firstExact F n x
    let D : Set (ℕ → α) := if x = z then noHit F else ∅
    have hUm : MeasurableSet U := by
      exact MeasurableSet.iUnion (fun n => firstExact_measurable F n x hF)
    have hDm : MeasurableSet D := by
      by_cases hx : x = z
      · simpa [D, hx] using hno_meas
      · simp [D, hx]
    have hD0 : ν D = 0 := by
      by_cases hx : x = z
      · simp [D, hx, hno]
      · simp [D, hx]
    have hdis : Disjoint U D := by
      by_cases hx : x = z
      · dsimp [D]
        rw [if_pos hx]
        apply Set.disjoint_left.mpr
        intro w hwU hwD
        rcases Set.mem_iUnion.mp hwU with ⟨n, hn⟩
        exact hwD ⟨n, hn.2.1⟩
      · simp [D, hx]
    rw [show (⋃ n, firstExact F n x) ∪ D = U ∪ D from rfl,
      measure_union hdis hDm]
    simp only [hD0, add_zero]
    change Measure.infinitePi (fun _ : ℕ => μ) U = p⁻¹ * μ ({x} ∩ F)
    rw [MeasureTheory.measure_iUnion (firstExact_pairwise F x)
      (fun n => firstExact_measurable F n x hF)]
    simp_rw [firstExact_measure μ F _ x hF]
    calc
      (∑' n : ℕ, (μ Fᶜ) ^ n * μ ({x} ∩ F)) =
          (∑' n : ℕ, (μ Fᶜ) ^ n) * μ ({x} ∩ F) := ENNReal.tsum_mul_right
      _ = p⁻¹ * μ ({x} ∩ F) := by rw [ENNReal.tsum_geometric, hgeom_factor]
  constructor
  · simpa [ν, redrawSizeSequenceLaw, F] using hterm_ae
  constructor
  · exact hmout
  · apply Measure.ext_of_singleton
    intro x
    rw [Measure.map_apply hmout (measurableSet_singleton x)]
    rw [hpre_formula x, acceptedSizeLaw, ProbabilityTheory.cond_apply hF]
    simp [μ, p, Set.inter_comm]


