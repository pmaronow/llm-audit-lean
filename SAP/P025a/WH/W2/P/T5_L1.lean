import SAP.P025a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

theorem SAP.P025a.WH.W2.T5_L1_proof : SAP.P025a.WH.W2.T5_L1 := by
  classical
  intro ι hι hιDec Ω hΩ p hp hnorm
  have hnonneg : ∀ ω, 0 ≤ wholeProductProbability p ω := by
    intro ω
    unfold wholeProductProbability
    exact Finset.prod_nonneg fun j hj => hp j (ω j)
  have htotal : (∑ ω, wholeProductProbability p ω) = 1 := by
    unfold wholeProductProbability
    rw [← Fintype.prod_sum]
    simp [hnorm]
  have hind : wholeIndependentCoordinates p := by
    unfold wholeIndependentCoordinates
    intro A
    calc
      wholeEventProbability (wholeProductProbability p)
          (fun ω => ∀ j, A j (ω j)) =
        ∑ ω : (∀ j, Ω j), ∏ j,
          (p j (ω j) * (if A j (ω j) then (1 : ℝ) else 0)) := by
          unfold wholeEventProbability wholeProductProbability
          apply Finset.sum_congr rfl
          intro ω hω
          have hindicator :
              @ite ℝ ((fun ω : (∀ j, Ω j) => ∀ j, A j (ω j)) ω)
                (Classical.propDecidable _) (1 : ℝ) 0 =
                  ∏ j, (if A j (ω j) then (1 : ℝ) else 0) := by
            letI : Decidable (∀ j, A j (ω j)) := Fintype.decidableForallFintype
            calc
              @ite ℝ ((fun ω : (∀ j, Ω j) => ∀ j, A j (ω j)) ω)
                  (Classical.propDecidable _) (1 : ℝ) 0 =
                @ite ℝ (∀ j, A j (ω j)) (inferInstance) (1 : ℝ) 0 := by
                  by_cases h : ∀ j, A j (ω j) <;> simp [h]
              _ = ∏ j, (if A j (ω j) then (1 : ℝ) else 0) := by
                symm
                exact Fintype.prod_boole
          calc
            (∏ j, p j (ω j)) *
                @ite ℝ ((fun ω : (∀ j, Ω j) => ∀ j, A j (ω j)) ω)
                  (Classical.propDecidable _) (1 : ℝ) 0 =
              (∏ j, p j (ω j)) *
                (∏ j, (if A j (ω j) then (1 : ℝ) else 0)) := by
                  exact congrArg (fun z : ℝ => (∏ j, p j (ω j)) * z) hindicator
            _ = ∏ j, (p j (ω j) * (if A j (ω j) then (1 : ℝ) else 0)) := by
              rw [← Finset.prod_mul_distrib]
      _ = ∏ j, wholeEventProbability (p j) (A j) := by
          unfold wholeEventProbability
          change (∑ ω : (∀ j, Ω j), ∏ j,
              (p j (ω j) * (if A j (ω j) then (1 : ℝ) else 0))) =
            ∏ j, ∑ x, p j x * (if A j x then (1 : ℝ) else 0)
          exact (Fintype.prod_sum
            (fun j x => p j x * (if A j x then (1 : ℝ) else 0))).symm
  have hmarg : ∀ j (A : Ω j → Prop),
      wholeEventProbability (wholeProductProbability p) (fun ω => A (ω j)) =
        wholeEventProbability (p j) A := by
    intro j A
    let B : ∀ i, Ω i → Prop := fun i x =>
      if h : i = j then A (h ▸ x) else True
    have hpred (ω : ∀ i, Ω i) : (∀ i, B i (ω i)) ↔ A (ω j) := by
      constructor
      · intro hall
        have hj := hall j
        simpa [B] using hj
      · intro h i
        by_cases hij : i = j
        · subst i
          simpa [B] using h
        · simp [B, hij]
    have hprob :
        wholeEventProbability (wholeProductProbability p) (fun ω => ∀ i, B i (ω i)) =
          wholeEventProbability (wholeProductProbability p) (fun ω => A (ω j)) := by
      unfold wholeEventProbability
      apply Finset.sum_congr rfl
      intro ω hω
      simp only [hpred ω]
    have hleft := hind B
    have hB (i : ι) :
        wholeEventProbability (p i) (B i) =
          if hi : i = j then wholeEventProbability (p j) A else 1 := by
      by_cases hij : i = j
      · subst i
        simp [B, wholeEventProbability]
      · simp [B, hij, wholeEventProbability, hnorm i]
    have hright :
        (∏ i, wholeEventProbability (p i) (B i)) = wholeEventProbability (p j) A := by
      rw [Finset.prod_eq_single j]
      · simp [hB]
      · intro i hi hij
        rw [hB i]
        simp [hij]
      · simp
    calc
      wholeEventProbability (wholeProductProbability p) (fun ω => A (ω j)) =
          wholeEventProbability (wholeProductProbability p) (fun ω => ∀ i, B i (ω i)) :=
        hprob.symm
      _ = ∏ i, wholeEventProbability (p i) (B i) := hleft
      _ = wholeEventProbability (p j) A := hright
  exact ⟨hnonneg, htotal, hind, hmarg⟩
