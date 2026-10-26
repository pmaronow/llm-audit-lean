import AronowAudit.P013.Wave1.CorrectedCoverage.N1

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

open Classical in
/-- Partition a finite-valued event into its point events, using only finite sums. -/
private theorem probability_event_atoms {Ω T : Type*} [Fintype Ω] [Fintype T]
    (P : Design Ω) (f : Ω → T) (s : Set T) :
    probability P (fun z => f z ∈ s) =
      ∑ t : T, if t ∈ s then probability P (fun z => f z = t) else 0 := by
  classical
  unfold probability
  calc
    (∑ z, if f z ∈ s then P.weight z else 0) =
        ∑ z, ∑ t : T, if t ∈ s then (if f z = t then P.weight z else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      symm
      calc
        _ = (if f z ∈ s then (if f z = f z then P.weight z else 0) else 0) := by
          apply Finset.sum_eq_single (f z)
          · intro t _ ht
            simp [Ne.symm ht]
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ _))
        _ = _ := by simp
    _ = ∑ t : T, ∑ z, if t ∈ s then (if f z = t then P.weight z else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ t : T, if t ∈ s then (∑ z, if f z = t then P.weight z else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t ∈ s <;> simp [ht]

/-- Point-event factorization gives independence of the complete restricted vectors. -/
theorem n2_proof : N2 := by
  classical
  intro Ω _ _ _ N K hK P D A B hVI
  let U : Ω → (A → Fin K) := fun z i => D z i.1
  let V : Ω → (B → Fin K) := fun z j => D z j.1
  -- Extend each restricted pattern without imposing any condition off its index set.
  let extend (C : Finset (Fin N)) (a : C → Fin K) : Fin N → Fin K :=
    fun i => if hi : i ∈ C then a ⟨i, hi⟩ else ⟨0, hK⟩
  have hpattern (C : Finset (Fin N)) (a : C → Fin K) (z : Ω) :
      (∀ i ∈ C, D z i = extend C a i) ↔ (fun i : C => D z i.1) = a := by
    constructor
    · intro hz
      funext i
      simpa only [extend, dif_pos i.2] using hz i.1 i.2
    · intro hz i hi
      have heq : D z i = a ⟨i, hi⟩ := congrFun hz ⟨i, hi⟩
      simpa only [extend, dif_pos hi] using heq
  have hpair (a : A → Fin K) (b : B → Fin K) :
      probability P (fun z => U z = a ∧ V z = b) =
        probability P (fun z => U z = a) * probability P (fun z => V z = b) := by
    simpa only [hpattern] using hVI (extend A a) (extend B b)
  have hfactor (s : Set (A → Fin K)) (t : Set (B → Fin K)) :
      probability P (fun z => U z ∈ s ∧ V z ∈ t) =
        probability P (fun z => U z ∈ s) * probability P (fun z => V z ∈ t) := by
    calc
      probability P (fun z => U z ∈ s ∧ V z ∈ t) =
          ∑ a : A → Fin K, ∑ b : B → Fin K,
            if a ∈ s ∧ b ∈ t then probability P (fun z => U z = a ∧ V z = b) else 0 := by
        simpa only [Fintype.sum_prod_type, Set.mem_prod, Prod.mk.injEq] using
          probability_event_atoms P (fun z => (U z, V z)) (s ×ˢ t)
      _ = ∑ a : A → Fin K, ∑ b : B → Fin K,
          (if a ∈ s then probability P (fun z => U z = a) else 0) *
            (if b ∈ t then probability P (fun z => V z = b) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hpair a b]
        by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;> simp [ha, hb]
      _ = (∑ a : A → Fin K, if a ∈ s then probability P (fun z => U z = a) else 0) *
          (∑ b : B → Fin K, if b ∈ t then probability P (fun z => V z = b) else 0) := by
        rw [Finset.sum_mul_sum]
      _ = probability P (fun z => U z ∈ s) * probability P (fun z => V z ∈ t) := by
        rw [← probability_event_atoms P U s, ← probability_event_atoms P V t]
  have hmeasure := n1_proof P
  letI : MeasureTheory.IsProbabilityMeasure (designMeasure P) := hmeasure.1
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _hs _ht
  apply (ENNReal.toReal_eq_toReal_iff'
    (MeasureTheory.measure_ne_top _ _)
    (ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  change (designMeasure P).real {z | U z ∈ s ∧ V z ∈ t} =
    (designMeasure P).real {z | U z ∈ s} * (designMeasure P).real {z | V z ∈ t}
  rw [hmeasure.2, hmeasure.2, hmeasure.2]
  exact hfactor s t

end

end AronowAudit.P013.Wave1.CorrectedCoverage
