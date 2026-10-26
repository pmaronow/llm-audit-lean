import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- Factorization on value fibres extends to every pair of measurable events. -/
theorem n2_proof : N2 := by
  classical
  intro L A B _ _ _ _ _ _ _ p hp V W hF
  have hPnonneg (E : L → Prop) : 0 ≤ fP p E := by
    unfold fP
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hp.1 i
    · exact le_rfl
  have hmass (S : Set L) :
      (atomicMeasure p) S = ENNReal.ofReal (fP p (fun i => i ∈ S)) := by
    have hS : MeasurableSet S := MeasurableSet.of_discrete
    unfold atomicMeasure
    rw [Measure.finsetSum_apply]
    calc
      (∑ i, (ENNReal.ofReal (p i) • Measure.dirac i) S) =
          ∑ i, ENNReal.ofReal (if i ∈ S then p i else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' i hS]
        by_cases hi : i ∈ S <;> simp [Set.indicator, hi]
      _ = ENNReal.ofReal (fP p (fun i => i ∈ S)) := by
        unfold fP
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i _
        split_ifs
        · exact hp.1 i
        · exact le_rfl
  -- The codomain C need not be finite: only the values attained by R are summed.
  have hsplit {C : Type} (R : L → C) (D : Set C) (E : L → Prop) :
      fP p (fun i => R i ∈ D ∧ E i) =
        ∑ a ∈ (Finset.univ.image R).filter (fun a => a ∈ D),
          fP p (fun i => R i = a ∧ E i) := by
    let T : Finset C := (Finset.univ.image R).filter (fun a => a ∈ D)
    have hmem (i : L) : R i ∈ T ↔ R i ∈ D := by
      change R i ∈ (Finset.univ.image R).filter (fun a => a ∈ D) ↔ R i ∈ D
      rw [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hi
        exact ⟨Finset.mem_image_of_mem R (Finset.mem_univ i), hi⟩
    change fP p (fun i => R i ∈ D ∧ E i) =
      ∑ a ∈ T, fP p (fun i => R i = a ∧ E i)
    calc
      fP p (fun i => R i ∈ D ∧ E i) =
          ∑ i ∈ Finset.univ.filter (fun i => R i ∈ T),
            (if E i then p i else 0) := by
        rw [Finset.sum_filter]
        unfold fP
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hD : R i ∈ D <;> by_cases hE : E i <;> simp [hmem i, hD, hE]
      _ = ∑ a ∈ T, ∑ i ∈ Finset.univ.filter (fun i => R i = a),
          (if E i then p i else 0) :=
        (Finset.sum_fiberwise_eq_sum_filter Finset.univ T R
          (fun i => if E i then p i else 0)).symm
      _ = ∑ a ∈ T, fP p (fun i => R i = a ∧ E i) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_filter]
        unfold fP
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hR : R i = a <;> by_cases hE : E i <;> simp [hR, hE]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t _ _
  let VA : Finset A := (Finset.univ.image V).filter (fun a => a ∈ s)
  let WB : Finset B := (Finset.univ.image W).filter (fun b => b ∈ t)
  have hV : fP p (fun i => V i ∈ s) = ∑ a ∈ VA, fP p (fun i => V i = a) := by
    simpa only [and_true] using hsplit V s (fun _ => True)
  have hW : fP p (fun i => W i ∈ t) = ∑ b ∈ WB, fP p (fun i => W i = b) := by
    simpa only [and_true] using hsplit W t (fun _ => True)
  have hjoint : fP p (fun i => V i ∈ s ∧ W i ∈ t) =
      fP p (fun i => V i ∈ s) * fP p (fun i => W i ∈ t) := by
    calc
      fP p (fun i => V i ∈ s ∧ W i ∈ t) =
          ∑ a ∈ VA, fP p (fun i => V i = a ∧ W i ∈ t) :=
        hsplit V s (fun i => W i ∈ t)
      _ = ∑ a ∈ VA, ∑ b ∈ WB, fP p (fun i => V i = a ∧ W i = b) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        simpa only [and_comm] using hsplit W t (fun i => V i = a)
      _ = ∑ a ∈ VA, ∑ b ∈ WB,
          fP p (fun i => V i = a) * fP p (fun i => W i = b) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b _
        exact hF a b
      _ = (∑ a ∈ VA, fP p (fun i => V i = a)) *
          (∑ b ∈ WB, fP p (fun i => W i = b)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = fP p (fun i => V i ∈ s) * fP p (fun i => W i ∈ t) := by
        rw [← hV, ← hW]
  rw [hmass (V ⁻¹' s ∩ W ⁻¹' t), hmass (V ⁻¹' s), hmass (W ⁻¹' t)]
  change ENNReal.ofReal (fP p (fun i => V i ∈ s ∧ W i ∈ t)) =
    ENNReal.ofReal (fP p (fun i => V i ∈ s)) *
      ENNReal.ofReal (fP p (fun i => W i ∈ t))
  rw [hjoint, ENNReal.ofReal_mul (hPnonneg (fun i => V i ∈ s))]

end

end AronowAudit.P029.Wave1.FiniteMeasure
