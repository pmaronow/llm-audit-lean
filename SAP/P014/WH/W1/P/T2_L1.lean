import SAP.P014.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open MeasureTheory

theorem SAP.P014.WH.W1.T2_L1_proof : SAP.P014.WH.W1.T2_L1 := by
  classical
  intro Ω hΩ N μ hμ Z hZ
  let mass : TreatmentVector N → ℝ := fun z =>
    eventProbability μ (fun ω => Z ω = z)
  let L := assignmentLaw μ Z
  have hfiber : ∀ z : TreatmentVector N, MeasurableSet {ω | Z ω = z} := by
    intro z
    exact hZ (measurableSet_singleton z)
  have hmass_nonneg (z : TreatmentVector N) : 0 ≤ mass z := by
    simp only [mass, eventProbability]
    exact measureReal_nonneg
  have hsum : (∑ z ∈ Finset.univ, mass z) = 1 := by
    calc
      (∑ z ∈ Finset.univ, mass z) = μ.real (Z ⁻¹' (↑(Finset.univ : Finset (TreatmentVector N)) : Set (TreatmentVector N))) := by
        exact sum_measureReal_preimage_singleton Finset.univ (f := Z)
          (fun z hz => hfiber z) (by finiteness)
      _ = 1 := by simp
  have hnorm : (∑ z ∈ L.atoms, L.weight z) = 1 := by
    have hsubset : L.atoms ⊆ Finset.univ := Finset.subset_univ _
    have hsum' : (∑ z ∈ L.atoms, mass z) = (∑ z ∈ Finset.univ, mass z) := by
      apply Finset.sum_subset hsubset
      intro z hz hznot
      have hn : ¬ 0 < mass z := by
        simpa [L, assignmentLaw, mass] using hznot
      exact le_antisymm (le_of_not_gt hn) (hmass_nonneg z)
    simpa [L, assignmentLaw, mass] using hsum'.trans hsum
  have hpositive : ∀ z ∈ L.atoms, 0 < L.weight z := by
    intro z hz
    simpa [L, assignmentLaw, mass] using (Finset.mem_filter.mp hz).2
  have hprob (P : TreatmentVector N → Prop) :
      probability L P = eventProbability μ (fun ω => P (Z ω)) := by
    let s : Finset (TreatmentVector N) := Finset.univ.filter P
    have hs : ∀ z ∈ s, MeasurableSet {ω | Z ω = z} := by
      intro z hz
      exact hfiber z
    have hsumP : (∑ z ∈ s, mass z) = μ.real (Z ⁻¹' (↑s : Set (TreatmentVector N))) := by
      exact sum_measureReal_preimage_singleton s (f := Z) hs (by finiteness)
    have hfilter : probability L P = ∑ z ∈ s, mass z := by
      calc
        probability L P = ∑ z ∈ L.atoms, (if P z then mass z else 0) := by
          simp [probability, L, assignmentLaw, mass]
        _ = ∑ z ∈ Finset.univ, (if P z then mass z else 0) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro z hz hznot
          have hn : ¬ 0 < mass z := by
            simpa [L, assignmentLaw, mass] using hznot
          have hm0 : mass z = 0 := le_antisymm (le_of_not_gt hn) (hmass_nonneg z)
          simp [hm0]
        _ = ∑ z ∈ s, mass z := by
          simp [s, Finset.sum_filter]
    have hset : {ω | P (Z ω)} = Z ⁻¹' (↑s : Set (TreatmentVector N)) := by
      ext ω
      simp [s]
    calc
      probability L P = μ.real (Z ⁻¹' (↑s : Set (TreatmentVector N))) := hfilter.trans hsumP
      _ = μ.real {ω | P (Z ω)} := by rw [← hset]
      _ = eventProbability μ (fun ω => P (Z ω)) := rfl
  have hae (P : TreatmentVector N → Prop) :
      (∀ᵐ ω ∂μ, P (Z ω)) ↔ ∀ z ∈ L.atoms, P z := by
    constructor
    · intro hP z hz
      by_contra hn
      have hbad : μ {ω | ¬ P (Z ω)} = 0 := ae_iff.mp hP
      have hsub : {ω | Z ω = z} ⊆ {ω | ¬ P (Z ω)} := by
        intro ω hw
        simp only [Set.mem_setOf_eq] at hw ⊢
        rw [hw]
        exact hn
      have hzero : μ {ω | Z ω = z} = 0 := measure_mono_null hsub hbad
      have hpzero : mass z = 0 := by
        simp [mass, eventProbability, hzero]
      have hp : 0 < mass z := by
        simpa [L, assignmentLaw, mass] using (Finset.mem_filter.mp hz).2
      exact (ne_of_gt hp) hpzero
    · intro hP
      have hzero_ae : ∀ z : TreatmentVector N, ∀ᵐ ω ∂μ,
          mass z = 0 → Z ω ≠ z := by
        intro z
        by_cases hm : mass z = 0
        · have hz0 : μ {ω | Z ω = z} = 0 := by
            have hmreal : μ.real {ω | Z ω = z} = 0 := by
              change (μ {ω | Z ω = z}).toReal = 0
              change (μ {ω | Z ω = z}).toReal = 0 at hm
              exact hm
            apply (measureReal_eq_zero_iff (μ := μ) (s := {ω | Z ω = z}) (by finiteness)).mp
            exact hmreal
          have hnot : ∀ᵐ ω ∂μ, Z ω ≠ z := by
            apply ae_iff.mpr
            simpa only [Set.mem_setOf_eq, not_not] using hz0
          filter_upwards [hnot] with ω hω hmass
          exact hω
        · filter_upwards [] with ω hmass
          exact (hm hmass).elim
      have hall : ∀ᵐ ω ∂μ, ∀ z : TreatmentVector N, mass z = 0 → Z ω ≠ z :=
        ae_all_iff.mpr hzero_ae
      filter_upwards [hall] with ω hω
      by_contra hn
      have hmass_ne : mass (Z ω) ≠ 0 := by
        intro h0
        exact hω (Z ω) h0 rfl
      have hmass_pos : 0 < mass (Z ω) := by
        by_contra hnot
        have heq : mass (Z ω) = 0 := le_antisymm (le_of_not_gt hnot) (hmass_nonneg _)
        exact hmass_ne heq
      have hz : Z ω ∈ L.atoms := by
        simpa [L, assignmentLaw, mass] using hmass_pos
      exact hn (hP (Z ω) hz)
  refine ⟨?_, hprob, hae⟩
  exact ⟨hpositive, hnorm⟩
