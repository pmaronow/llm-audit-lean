import SAP.P031.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter Finset
open SAP.P031 SAP.P031.Bridge SAP.P031.WH.W2

noncomputable section
namespace SAP.P031.WH.W2.Luna

private theorem eventProbability_nonnegW2 (Q : Population)
    (E : Finset (Fin Q.N) → Prop) : 0 ≤ eventProbability Q E := by
  rw [← Bridge.eventProbability_eq Q E]
  exact (AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof
    (Bridge.toPopulation Q)).1 E

private theorem eventProbability_monoW2 (Q : Population)
    (E F : Finset (Fin Q.N) → Prop)
    (h : ∀ s ∈ (Finset.univ : Finset (Fin Q.N)).powersetCard Q.M, E s → F s) :
    eventProbability Q E ≤ eventProbability Q F := by
  rw [← Bridge.eventProbability_eq Q E, ← Bridge.eventProbability_eq Q F]
  exact (AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof
    (Bridge.toPopulation Q)).2.1 E F h

private theorem eventProbability_unionW2 (Q : Population)
    (E F : Finset (Fin Q.N) → Prop) :
    eventProbability Q (fun s => E s ∨ F s) ≤ eventProbability Q E + eventProbability Q F := by
  rw [← Bridge.eventProbability_eq Q (fun s => E s ∨ F s),
    ← Bridge.eventProbability_eq Q E, ← Bridge.eventProbability_eq Q F]
  exact (AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof
    (Bridge.toPopulation Q)).2.2.1 E F

theorem T5_L6_solution : T5_L6 := by
  intro P A B b hEq hB ε hε
  let δ : ℝ := min 1 (ε / 2)
  let η : ℝ := ε / (2 * (|b| + 1))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδOne : δ ≤ 1 := min_le_left _ _
  have hδHalf : δ ≤ ε / 2 := min_le_right _ _
  have hηden : 0 < 2 * (|b| + 1) := by positivity
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos hε hηden
  have hηeq : η * (|b| + 1) = ε / 2 := by
    dsimp [η]
    field_simp [ne_of_gt hηden]
  have hBbad : Tendsto (fun n => eventProbability (P n) (fun s =>
      δ < |(P n).N * B (P n) s - b|)) atTop (𝓝 (0 : ℝ)) := hB δ hδpos
  have hRelbad : Tendsto (fun n => eventProbability (P n) (fun s =>
      η * |B (P n) s| < |A (P n) s - B (P n) s|)) atTop (𝓝 (0 : ℝ)) := hEq η hηpos
  have hContain (n : ℕ) (s : Finset (Fin (P n).N))
      (hbad : ε < |(P n).N * A (P n) s - b|) :
      (δ < |(P n).N * B (P n) s - b|) ∨
        (η * |B (P n) s| < |A (P n) s - B (P n) s|) := by
    by_contra hnot
    have hsmallB : |(P n).N * B (P n) s - b| ≤ δ :=
      le_of_not_gt (fun h => hnot (Or.inl h))
    have hsmallRel : |A (P n) s - B (P n) s| ≤ η * |B (P n) s| :=
      le_of_not_gt (fun h => hnot (Or.inr h))
    have hN : (0 : ℝ) ≤ (P n).N := Nat.cast_nonneg _
    have hNB : (P n).N * |B (P n) s| ≤ |b| + 1 := by
      have hAbs : |(P n).N * B (P n) s| ≤ δ + |b| := by
        calc
          |(P n).N * B (P n) s| =
              |((P n).N * B (P n) s - b) + b| := by congr 1 <;> ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ δ + |b| := add_le_add hsmallB le_rfl
      rw [abs_mul, abs_of_nonneg hN] at hAbs
      nlinarith [hδOne]
    have hPoint : |(P n).N * A (P n) s - b| ≤ ε := by
      calc
        |(P n).N * A (P n) s - b| =
            |(P n).N * (A (P n) s - B (P n) s) +
              ((P n).N * B (P n) s - b)| := by congr 1 <;> ring
        _ ≤ |(P n).N * (A (P n) s - B (P n) s)| +
              |(P n).N * B (P n) s - b| := abs_add_le _ _
        _ = (P n).N * |A (P n) s - B (P n) s| +
              |(P n).N * B (P n) s - b| := by rw [abs_mul, abs_of_nonneg hN]
        _ ≤ (P n).N * (η * |B (P n) s|) + δ :=
              add_le_add (mul_le_mul_of_nonneg_left hsmallRel hN) hsmallB
        _ = η * ((P n).N * |B (P n) s|) + δ := by ring
        _ ≤ η * (|b| + 1) + δ :=
              add_le_add_left (mul_le_mul_of_nonneg_left hNB hηpos.le) δ
        _ = ε / 2 + δ := by rw [hηeq]
        _ ≤ ε := by linarith
    exact (not_lt_of_ge hPoint) hbad
  have hUpper : Tendsto (fun n =>
      eventProbability (P n) (fun s => δ < |(P n).N * B (P n) s - b|) +
        eventProbability (P n) (fun s =>
          η * |B (P n) s| < |A (P n) s - B (P n) s|)) atTop (𝓝 0) := by
    simpa only [add_zero] using hBbad.add hRelbad
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
  · intro n
    exact eventProbability_nonnegW2 (P n) _
  · intro n
    exact (eventProbability_monoW2 (P n) _ _ (by
      intro s hs hbad
      exact hContain n s hbad)).trans (eventProbability_unionW2 (P n) _ _)

example : T5_L6 := T5_L6_solution

#print axioms T5_L6_solution

end SAP.P031.WH.W2.Luna
end
