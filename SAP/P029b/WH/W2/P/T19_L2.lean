import SAP.P029b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory

theorem SAP.P029b.WH.W2.T19_L2_proof : SAP.P029b.WH.W2.T19_L2 := by
  intro k
  let S : Finset (Finset (Fin (2 * k))) := Finset.univ.powersetCard k
  let hS : S.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simp [Finset.card_univ]
    omega
  let p : PMF (Finset (Fin (2 * k))) := PMF.uniformOfFinset S hS
  have hprob : IsProbabilityMeasure (balancedLawW2 k) := by
    change IsProbabilityMeasure p.toMeasure
    infer_instance
  have hae : ∀ᵐ s ∂balancedLawW2 k, s.card = k := by
    rw [ae_iff]
    change p.toMeasure {s | s.card ≠ k} = 0
    rw [PMF.toMeasure_uniformOfFinset_apply (s := S) (hs := hS)
      (t := {s | s.card ≠ k}) (MeasurableSet.of_discrete)]
    simp [S, Finset.mem_powersetCard]
  have hmass : ∀ s : Finset (Fin (2 * k)), balancedLawW2 k {s} =
      if s.card = k then (Nat.choose (2 * k) k : ℝ≥0∞)⁻¹ else 0 := by
    intro s
    change p.toMeasure {s} = _
    rw [p.toMeasure_apply_singleton s (measurableSet_singleton s)]
    simp [p, PMF.uniformOfFinset_apply, S, Finset.mem_powersetCard, Finset.card_univ]
  have hhalf : ∀ i : Fin (2 * k), balancedLawW2 k {s | i ∈ s} = 1 / 2 := by
    intro i
    by_cases hk : k = 0
    · subst k
      exact Fin.elim0 i
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      let t : Set (Finset (Fin (2 * k))) := {s | i ∈ s}
      have ht : MeasurableSet t := MeasurableSet.of_discrete
      change p.toMeasure t = 1 / 2
      rw [PMF.toMeasure_uniformOfFinset_apply (s := S) (hs := hS) (t := t) ht]
      letI : DecidablePred (fun s : Finset (Fin (2 * k)) => s ∈ t) :=
        fun s => Classical.propDecidable (s ∈ t)
      have hcount : (S.filter fun s => s ∈ t).card = Nat.choose (2 * k - 1) (k - 1) := by
        have hfilter : S.filter (fun s => s ∈ t) =
            (Finset.univ.powersetCard k).filter ({i} ⊆ ·) := by
          ext s
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hs, hi⟩
            exact ⟨hs, Finset.singleton_subset_iff.mpr (by simpa [t] using hi)⟩
          · rintro ⟨hs, hi⟩
            exact ⟨hs, by simpa [t] using Finset.singleton_subset_iff.mp hi⟩
        rw [hfilter, Finset.card_filter_powersetCard_subset]
        · have huniv : (Finset.univ : Finset (Fin (2 * k))).card = 2 * k := by simp
          have hsingle : ({i} : Finset (Fin (2 * k))).card = 1 := by simp
          rw [huniv, hsingle]
        · simp
        · have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr hkpos
          simpa [Finset.card_singleton] using hk1
      have hden : S.card = Nat.choose (2 * k) k := by
        simp [S, Finset.card_univ]
      rw [hcount, hden]
      have hnum : Nat.choose (2 * k - 1) (k - 1) = Nat.choose (2 * k - 1) k := by
        have heq : 2 * k - 1 = (k - 1) + k := by omega
        exact Nat.choose_symm_of_eq_add heq
      have hchoose : Nat.choose (2 * k) k = 2 * Nat.choose (2 * k - 1) k := by
        calc
          Nat.choose (2 * k) k =
              Nat.choose (Nat.succ (2 * k - 1)) (Nat.succ (k - 1)) := by
                congr 2 <;> omega
          _ = Nat.choose (2 * k - 1) (k - 1) + Nat.choose (2 * k - 1) k := by
                have hk' : Nat.succ (k - 1) = k := by omega
                rw [Nat.choose_succ_succ, hk', hnum]
          _ = 2 * Nat.choose (2 * k - 1) k := by rw [hnum]; omega
      have hnumCast : (Nat.choose (2 * k - 1) (k - 1) : ℝ≥0∞) =
          (Nat.choose (2 * k - 1) k : ℝ≥0∞) := congrArg (fun n : ℕ => (n : ℝ≥0∞)) hnum
      have hchooseCast : (Nat.choose (2 * k) k : ℝ≥0∞) =
          2 * (Nat.choose (2 * k - 1) k : ℝ≥0∞) := by
        rw [hchoose]
        norm_num [Nat.cast_mul]
      rw [hnumCast, hchooseCast]
      have hpos : (Nat.choose (2 * k - 1) k : ℝ≥0∞) ≠ 0 := by
        have hcpos : 0 < Nat.choose (2 * k - 1) k := Nat.choose_pos (by omega)
        exact_mod_cast hcpos.ne'
      have htop : (Nat.choose (2 * k - 1) k : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
      calc
        (Nat.choose (2 * k - 1) k : ℝ≥0∞) /
            (2 * (Nat.choose (2 * k - 1) k : ℝ≥0∞)) =
            (Nat.choose (2 * k - 1) k : ℝ≥0∞) * 1 /
              ((Nat.choose (2 * k - 1) k : ℝ≥0∞) * 2) := by simp [mul_comm]
        _ = 1 / 2 := ENNReal.mul_div_mul_left 1 2 hpos htop
  exact ⟨hprob, hae, hmass, hhalf⟩

