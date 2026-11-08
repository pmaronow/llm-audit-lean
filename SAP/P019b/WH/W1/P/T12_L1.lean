import SAP.P019b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open MeasureTheory
open Classical

theorem SAP.P019b.WH.W1.T12_L1_proof : SAP.P019b.WH.W1.T12_L1 := by
  intro Ω _ S
  classical
  obtain ⟨J, hJ⟩ := S.bounded
  let α := Fin (J + 1) × (Bool × (Bool × (Bool × Fin (J + 2))))
  let code : Ω → α := fun ω =>
    (⟨min (S.W ω) J, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
      (S.X ω, (S.Y ω, (S.Z ω,
        ⟨min (S.V ω) (J + 1), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩))))
  let E : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let e : Ω → Fin (Fintype.card α) := E ∘ code
  have hW : Measurable (fun ω : Ω =>
      (⟨min (S.W ω) J, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin (J + 1))) := by
    let f : ℕ → Fin (J + 1) := fun n =>
      ⟨min n J, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    exact (measurable_of_countable f).comp S.measurable_W
  have hV : Measurable (fun ω : Ω =>
      (⟨min (S.V ω) (J + 1), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin (J + 2))) := by
    let f : ℕ → Fin (J + 2) := fun n =>
      ⟨min n (J + 1), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    exact (measurable_of_countable f).comp S.measurable_V
  have hcode : Measurable code := by
    dsimp [code, α]
    exact hW.prodMk (S.measurable_X.prodMk
      (S.measurable_Y.prodMk (S.measurable_Z.prodMk hV)))
  have he : Measurable e := by
    dsimp [e]
    exact (measurable_of_finite E).comp hcode
  let m := Fintype.card α
  let mass : Fin m → ℝ := fun i => (S.law {ω | e ω = i}).toReal
  have htotal : ∑ i, mass i = 1 := by
    change ∑ i, (S.law (e ⁻¹' {i})).toReal = 1
    simpa [Measure.real] using
      (sum_measureReal_preimage_singleton (μ := S.law) (s := Finset.univ)
        (f := e) (fun i hi => he (measurableSet_singleton i)))
  let F : Study (Fin m) :=
    { law :=
        { mass := mass
          nonneg := fun i => ENNReal.toReal_nonneg
          total := htotal }
      W := fun i => (E.symm i).1.val
      X := fun i => (E.symm i).2.1
      Y := fun i => (E.symm i).2.2.1
      Z := fun i => (E.symm i).2.2.2.1
      V := fun i => (E.symm i).2.2.2.2.val }
  have hmass (i : Fin m) : S.law {ω | e ω = i} = ENNReal.ofReal (F.law.mass i) := by
    dsimp [F, mass]
    exact (ENNReal.ofReal_toReal (by finiteness)).symm
  have hcoords : ∀ᵐ ω ∂S.law,
      F.W (e ω) = S.W ω ∧ F.X (e ω) = S.X ω ∧ F.Y (e ω) = S.Y ω ∧
        F.Z (e ω) = S.Z ω ∧ F.V (e ω) = S.V ω := by
    filter_upwards [hJ] with ω hω
    simp [F, e, code, Nat.min_eq_left hω.1, Nat.min_eq_left hω.2]
  exact ⟨m, F, e, he, (fun i => hmass i), hcoords⟩
