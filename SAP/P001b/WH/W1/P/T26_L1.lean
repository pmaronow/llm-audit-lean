import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SAP.P001b
open scoped ENNReal

noncomputable section

theorem SAP.P001b.WH.W1.T26_L1_proof : SAP.P001b.WH.W1.T26_L1 := by
  intro Ω _ μ _ X hX hRange hZero
  classical
  let F : ℤ → Set Ω := fun k => {ω | X ω = (k : ℝ)}
  let S : Set ℝ := {x | x ∈ Set.range X ∧ ¬ ∃ k : ℤ, x = (k : ℝ)}
  have hS_count : S.Countable := by
    apply hRange.mono
    intro x hx
    exact hx.1
  have hFiberZero (x : ℝ) (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
      μ {ω | X ω = x} = 0 := by
    have hp : probability μ {ω | X ω = x} = 0 := hZero x hx
    have ht : μ {ω | X ω = x} ≠ ∞ := measure_ne_top μ _
    simpa [probability, ENNReal.toReal_eq_zero_iff, ht] using hp
  have hNset : {ω | ¬ ∃ k : ℤ, X ω = (k : ℝ)} = X ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S]
    constructor
    · intro hω
      refine ⟨⟨ω, rfl⟩, ?_⟩
      intro hbad
      exact hω hbad
    · rintro ⟨_, hω⟩ hbad
      exact hω hbad
  have hN : μ {ω | ¬ ∃ k : ℤ, X ω = (k : ℝ)} = 0 := by
    rw [hNset]
    apply (measure_preimage_eq_zero_iff_of_countable hS_count).2
    intro x hx
    apply hFiberZero x
    intro hk
    exact hx.2 ⟨hk.choose, hk.choose_spec.symm⟩
  have hInt : ∀ᵐ ω ∂μ, ∃ k : ℤ, X ω = (k : ℝ) := by
    rw [ae_iff]
    exact hN
  have hFmeas (k : ℤ) : MeasurableSet (F k) := by
    exact (measurableSet_singleton (k : ℝ)).preimage hX
  have hFdisj : Pairwise fun k l => Disjoint (F k) (F l) := by
    intro k l hkl
    apply Set.disjoint_left.2
    intro ω hk hl
    change X ω = (k : ℝ) at hk
    change X ω = (l : ℝ) at hl
    apply hkl
    exact Int.cast_injective (hk.symm.trans hl)
  have hUnionAE : (Set.univ : Set Ω) =ᵐ[μ] ⋃ k : ℤ, F k := by
    filter_upwards [hInt] with ω hω
    change (ω ∈ (Set.univ : Set Ω)) = (ω ∈ ⋃ k : ℤ, F k)
    apply propext
    simp only [Set.mem_univ, Set.mem_iUnion, F, Set.mem_setOf_eq]
    exact ⟨fun _ => hω, fun _ => trivial⟩
  have hTotal : (∑' k : ℤ, μ (F k)) = 1 := by
    calc
      (∑' k : ℤ, μ (F k)) = μ (⋃ k : ℤ, F k) :=
        (measure_iUnion hFdisj hFmeas).symm
      _ = μ Set.univ := (measure_congr hUnionAE).symm
      _ = 1 := measure_univ
  let q : ℤ → ℝ := fun k => probability μ (F k)
  change Summable q ∧ (∑' k : ℤ, q k) = 1 ∧
    ∀ B : Set ℝ, probability μ {ω | X ω ∈ B} =
      ∑' k : ℤ, if (k : ℝ) ∈ B then q k else 0
  have hq_nonneg (k : ℤ) : 0 ≤ q k := by
    simp [q, probability]
  have hFinite (k : ℤ) : μ (F k) ≠ ∞ := measure_ne_top μ _
  let r : ℤ → NNReal := fun k => ⟨q k, hq_nonneg k⟩
  have hr_coe (k : ℤ) : (r k : ℝ≥0∞) = μ (F k) := by
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal ((μ (F k)).toReal) = μ (F k)
    exact ENNReal.ofReal_toReal (hFinite k)
  have hr_total : (∑' k : ℤ, (r k : ℝ≥0∞)) = 1 := by
    calc
      (∑' k : ℤ, (r k : ℝ≥0∞)) = ∑' k : ℤ, μ (F k) := tsum_congr hr_coe
      _ = 1 := hTotal
  have hr_summable : Summable r :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (by rw [hr_total]; simp)
  have hq_summable : Summable q := (NNReal.summable_mk hq_nonneg).1 hr_summable
  have hRealTotalAux : (∑' k : ℤ, μ (F k)).toReal = ∑' k : ℤ, q k := by
    simpa [q, probability] using
      (ENNReal.tsum_toReal_eq (f := fun k : ℤ => μ (F k)) (fun k => hFinite k))
  have hRealTotal : (∑' k : ℤ, q k) = 1 := by
    calc
      (∑' k : ℤ, q k) = (∑' k : ℤ, μ (F k)).toReal := hRealTotalAux.symm
      _ = 1 := by rw [hTotal]; norm_num
  let G : Set ℝ → ℤ → Set Ω := fun B k =>
    if (k : ℝ) ∈ B then F k else ∅
  have hGmeas (B : Set ℝ) (k : ℤ) : MeasurableSet (G B k) := by
    by_cases hk : (k : ℝ) ∈ B <;> simp [G, hk, hFmeas]
  have hGdisj (B : Set ℝ) : Pairwise fun k l => Disjoint (G B k) (G B l) := by
    intro k l hkl
    apply Set.disjoint_left.2
    intro ω hωk hωl
    change ω ∈ G B k at hωk
    change ω ∈ G B l at hωl
    have hFk : ω ∈ F k := by
      by_cases hk : (k : ℝ) ∈ B
      · simpa [G, hk] using hωk
      · simp [G, hk] at hωk
    have hFl : ω ∈ F l := by
      by_cases hl : (l : ℝ) ∈ B
      · simpa [G, hl] using hωl
      · simp [G, hl] at hωl
    apply hkl
    exact Int.cast_injective (hFk.symm.trans hFl)
  have hBAE (B : Set ℝ) : {ω | X ω ∈ B} =ᵐ[μ] ⋃ k : ℤ, G B k := by
    filter_upwards [hInt] with ω hω
    change (X ω ∈ B) = (ω ∈ ⋃ k : ℤ, G B k)
    apply propext
    simp only [Set.mem_iUnion]
    constructor
    · intro hB
      obtain ⟨k, hk⟩ := hω
      have hkB : (k : ℝ) ∈ B := by simpa [hk] using hB
      refine ⟨k, ?_⟩
      simpa [G, hkB, F] using hk
    · rintro ⟨k, hk⟩
      by_cases hkB : (k : ℝ) ∈ B
      · have hXk : X ω = (k : ℝ) := by simpa [G, hkB, F] using hk
        simpa [hXk] using hkB
      · simp [G, hkB] at hk
  have hBmass (B : Set ℝ) :
      μ {ω | X ω ∈ B} = ∑' k : ℤ, if (k : ℝ) ∈ B then μ (F k) else 0 := by
    calc
      μ {ω | X ω ∈ B} = μ (⋃ k : ℤ, G B k) := measure_congr (hBAE B)
      _ = ∑' k : ℤ, μ (G B k) := measure_iUnion (hGdisj B) (hGmeas B)
      _ = ∑' k : ℤ, if (k : ℝ) ∈ B then μ (F k) else 0 := by
        apply tsum_congr
        intro k
        by_cases hk : (k : ℝ) ∈ B <;> simp [G, hk]
  refine ⟨hq_summable, hRealTotal, ?_⟩
  intro B
  calc
    probability μ {ω | X ω ∈ B} =
        (∑' k : ℤ, if (k : ℝ) ∈ B then μ (F k) else 0).toReal := by
          simp only [probability, hBmass B]
    _ = ∑' k : ℤ, (if (k : ℝ) ∈ B then μ (F k) else 0).toReal :=
      ENNReal.tsum_toReal_eq (by
        intro k
        split_ifs
        · exact hFinite k
        · simp)
    _ = ∑' k : ℤ, if (k : ℝ) ∈ B then q k else 0 := by
      apply tsum_congr
      intro k
      by_cases hk : (k : ℝ) ∈ B <;> simp [hk, q, probability]
