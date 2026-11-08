import SAP.P014.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.WH.W1.P.T6_L1

open MeasureTheory
open Function
open SAP.P014

lemma fibers_pairwise_disjoint {Ω α : Type*} (X : Ω → α) :
    Pairwise (fun x y => Disjoint {ω | X ω = x} {ω | X ω = y}) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro ω hx hy
  exact hxy (hx.symm.trans hy)

end SAP.P014.WH.W1.P.T6_L1

theorem SAP.P014.WH.W1.T6_L1_proof : SAP.P014.WH.W1.T6_L1 := by
  classical
  intro Ω mΩ N μ hμ X hX k hk hmass
  let A : (Fin N → ℝ) → Set Ω := fun x => {ω | X ω = x}
  let ε : ENNReal := ENNReal.ofReal (1 / (k : ℝ))
  have hε : 0 < ε := by
    dsimp [ε]
    exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Nat.cast_pos.mpr hk))
  have hA_meas : ∀ x, MeasurableSet (A x) := by
    intro x
    dsimp [A]
    exact measurableSet_eq_fun hX measurable_const
  have hA_disj : Pairwise (fun x y => Disjoint (A x) (A y)) :=
    SAP.P014.WH.W1.P.T6_L1.fibers_pairwise_disjoint X
  have hA_union : (⋃ x, A x) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨X ω, rfl⟩
  have hfinite : μ (⋃ x, A x) ≠ ⊤ := by
    rw [hA_union]
    exact MeasureTheory.measure_ne_top μ Set.univ
  have hlarge : Set.Finite {x | ε ≤ μ (A x)} :=
    MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion μ hε hA_meas hA_disj hfinite
  apply hlarge.subset
  intro x hx
  dsimp [A, ε]
  have hreal : (μ {ω | X ω = x}).toReal = 1 / (k : ℝ) := by
    simpa [eventProbability] using hmass x hx
  rw [← ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ {ω | X ω = x}), hreal]

