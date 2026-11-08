import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T19_L2

open ProbabilityTheory
open scoped BigOperators Classical
noncomputable section

theorem source_neighborhood_card (m : ℕ) (i : Fin (2*m+1)) :
    (SAP.P004b.cancellingNeighborhood m i).card ≤ 2 := by
  classical
  let f : Fin (2*m+1) → Fin 2 := fun j => ⟨j.val % 2, by omega⟩
  have hf : Set.MapsTo f (SAP.P004b.cancellingNeighborhood m i)
      (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) := by
    intro j hj
    simp
  have hinj : (SAP.P004b.cancellingNeighborhood m i : Set (Fin (2*m+1))).InjOn f := by
    intro j hj l hl h
    apply Fin.ext
    have hsource : SAP.P004b.cancellingSource m j = SAP.P004b.cancellingSource m l := by
      change j ∈ Finset.univ.filter (fun a =>
        SAP.P004b.cancellingSource m a = SAP.P004b.cancellingSource m i) at hj
      change l ∈ Finset.univ.filter (fun a =>
        SAP.P004b.cancellingSource m a = SAP.P004b.cancellingSource m i) at hl
      exact (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hl).2.symm
    have hmod : j.val % 2 = l.val % 2 := by
      exact congrArg Fin.val h
    have hdiv : (j.val + 1) / 2 = (l.val + 1) / 2 := by
      exact congrArg Fin.val hsource
    omega
  have hcard := Finset.card_le_card_of_injOn f hf hinj
  simpa using hcard

theorem cancelling_dependency (m : ℕ) :
    FiniteDependencyGraph (fun _ : Fin (2*m+1) => (1/2 : ℝ))
      (SAP.P004b.cancellingArray m) (SAP.P004b.cancellingNeighborhood m) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [SAP.P004b.cancellingNeighborhood]
  · intro i j
    simp [SAP.P004b.cancellingNeighborhood, eq_comm]
  · intro I J hsep A C
    let p : Fin (2*m+1) → ℝ := fun _ => 1/2
    let S : Set (Fin (2*m+1)) := {k | ∃ i, i ∈ I ∧ SAP.P004b.cancellingSource m i = k}
    let T : Set (Fin (2*m+1)) := {k | ∃ j, j ∈ J ∧ SAP.P004b.cancellingSource m j = k}
    have hdisj : Disjoint S T := by
      rw [Set.disjoint_left]
      intro k hkS hkT
      rcases hkS with ⟨i, hi, rfl⟩
      rcases hkT with ⟨j, hj, hsource⟩
      have hnot : j ∉ SAP.P004b.cancellingNeighborhood m i := hsep i hi j hj
      exact hnot (by simp [SAP.P004b.cancellingNeighborhood, hsource])
    let F : SAP.P004b.Assignment (2*m+1) → ℝ := fun z =>
      if A (fun i => SAP.P004b.cancellingArray m i z) then 1 else 0
    let G : SAP.P004b.Assignment (2*m+1) → ℝ := fun z =>
      if C (fun j => SAP.P004b.cancellingArray m j z) then 1 else 0
    have hF : DependsOn F S := by
      apply AronowAudit.P004.GraphCompletion.depends_of_update
      intro z k hk b
      have hcoords : ∀ i ∈ I,
          SAP.P004b.cancellingArray m i (Function.update z k b) =
            SAP.P004b.cancellingArray m i z := by
        intro i hi
        have hsource : SAP.P004b.cancellingSource m i ≠ k := by
          intro heq
          exact hk ⟨i, hi, heq⟩
        simp [SAP.P004b.cancellingArray, Function.update_of_ne hsource]
      have htuple : (fun (i : I) => SAP.P004b.cancellingArray m i (Function.update z k b)) =
          (fun (i : I) => SAP.P004b.cancellingArray m i z) := by
        funext i
        exact hcoords i i.property
      change (if A (fun i : I => SAP.P004b.cancellingArray m i (Function.update z k b))
          then 1 else 0) = (if A (fun i : I => SAP.P004b.cancellingArray m i z)
          then 1 else 0)
      exact congrArg (fun q : I → ℝ => if A q then (1 : ℝ) else 0) htuple
    have hG : DependsOn G (Sᶜ) := by
      apply AronowAudit.P004.GraphCompletion.depends_of_update
      intro z k hk b
      have hcoords : ∀ j ∈ J,
          SAP.P004b.cancellingArray m j (Function.update z k b) =
            SAP.P004b.cancellingArray m j z := by
        intro j hj
        have hjT : SAP.P004b.cancellingSource m j ∈ T := ⟨j, hj, rfl⟩
        have hjS : SAP.P004b.cancellingSource m j ∉ S := by
          intro hjS
          exact (Set.disjoint_left.mp hdisj.symm hjT) hjS
        have hsource : SAP.P004b.cancellingSource m j ≠ k := by
          intro heq
          have hkT : k ∈ T := heq ▸ hjT
          have hkS : k ∈ S := by simpa [Set.mem_compl_iff] using hk
          exact (Set.disjoint_left.mp hdisj hkS) hkT
        simp [SAP.P004b.cancellingArray, Function.update_of_ne hsource]
      have htuple : (fun (j : J) => SAP.P004b.cancellingArray m j (Function.update z k b)) =
          (fun (j : J) => SAP.P004b.cancellingArray m j z) := by
        funext j
        exact hcoords j j.property
      change (if C (fun j : J => SAP.P004b.cancellingArray m j (Function.update z k b))
          then 1 else 0) = (if C (fun j : J => SAP.P004b.cancellingArray m j z)
          then 1 else 0)
      exact congrArg (fun q : J → ℝ => if C q then (1 : ℝ) else 0) htuple
    have hfact := AronowAudit.P004.GraphCompletion.expect_mul_of_disjoint_depends
      p S F G hF hG
    change SAP.P004b.prob p
        (fun z => A (fun i => SAP.P004b.cancellingArray m i z) ∧
          C (fun j => SAP.P004b.cancellingArray m j z)) =
      SAP.P004b.prob p (fun z => A (fun i => SAP.P004b.cancellingArray m i z)) *
        SAP.P004b.prob p (fun z => C (fun j => SAP.P004b.cancellingArray m j z))
    unfold SAP.P004b.prob
    calc
      _ = SAP.P004b.expect p (fun z => F z * G z) := by
        congr 1
        funext z
        by_cases ha : A (fun i => SAP.P004b.cancellingArray m i z) <;>
          by_cases hc : C (fun j => SAP.P004b.cancellingArray m j z) <;>
          simp [F, G, ha, hc]
      _ = SAP.P004b.expect p F * SAP.P004b.expect p G := hfact
      _ = _ := rfl

end
end SAP.P004b.WH.W2.P.T19_L2

theorem SAP.P004b.WH.W2.T19_L2_proof : SAP.P004b.WH.W2.T19_L2 := by
  intro m
  constructor
  · exact SAP.P004b.WH.W2.P.T19_L2.cancelling_dependency m
  · intro i
    exact SAP.P004b.WH.W2.P.T19_L2.source_neighborhood_card m i

