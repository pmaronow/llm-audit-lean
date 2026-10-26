import AronowAudit.P045.Wave1.ClusterSamplerBlueprint

/-!
P045-T29, node N3: peel the extra initial retry at zero. The stopping
condition is unchanged, and the transition product gains one factor of 1/4.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

theorem n3_proof : N3 := by
  intro rest
  have hEmpty : marked (pathDistance (n := 4)) 3 (∅ : Finset (Fin 4)) ≠ univ := by
    rw [four_path_marking_certificate.1]
    decide
  have hZero : marked (pathDistance (n := 4)) 3 ({0} : Finset (Fin 4)) ≠ univ := by
    rw [four_path_marking_certificate.2.1]
    decide

  -- Splitting each prefix quantifier at zero leaves the same conditions:
  -- the long list has just one extra nonterminal prefix with centre set {0}.
  have hgood :
      ((∀ k : Fin (0 :: 0 :: rest).length,
          marked (pathDistance (n := 4)) 3 ((0 :: 0 :: rest).take k.val).toFinset ≠ univ) ∧
        marked (pathDistance (n := 4)) 3 (0 :: 0 :: rest).toFinset = univ) ↔
      ((∀ k : Fin (0 :: rest).length,
          marked (pathDistance (n := 4)) 3 ((0 :: rest).take k.val).toFinset ≠ univ) ∧
        marked (pathDistance (n := 4)) 3 (0 :: rest).toFinset = univ) := by
    simp [List.length_cons, Fin.forall_fin_succ, List.take_succ_cons,
      List.toFinset_cons, Finset.insert_idem, hEmpty, hZero]

  -- After deleting the very first draw, corresponding draws have equal mass.
  -- At index zero the two prefix states are {0} and ∅, both uniform;
  -- at every successor index the prefix centre sets themselves coincide.
  have hdraw : ∀ k : Fin (0 :: rest).length,
      centreDraw (pathDistance (n := 4)) 3 true
        ((0 :: 0 :: rest).take k.succ.val).toFinset ((0 :: 0 :: rest).get k.succ) =
      centreDraw (pathDistance (n := 4)) 3 true
        ((0 :: rest).take k.val).toFinset ((0 :: rest).get k) := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · change centreDraw (pathDistance (n := 4)) 3 true {0} 0 =
        centreDraw (pathDistance (n := 4)) 3 true ∅ 0
      rw [(four_path_coded_draws (0 : Fin 4)).2,
        (four_path_coded_draws (0 : Fin 4)).1]
    · simp only [Fin.val_succ, List.take_succ_cons, List.toFinset_cons,
        Finset.insert_idem, List.get_cons_succ']

  have hprod :
      (∏ k : Fin (0 :: 0 :: rest).length,
        centreDraw (pathDistance (n := 4)) 3 true
          ((0 :: 0 :: rest).take k.val).toFinset ((0 :: 0 :: rest).get k)) =
      (1/4 : ℝ) * ∏ k : Fin (0 :: rest).length,
        centreDraw (pathDistance (n := 4)) 3 true
          ((0 :: rest).take k.val).toFinset ((0 :: rest).get k) := by
    simp only [List.length_cons]
    rw [Fin.prod_univ_succ]
    change centreDraw (pathDistance (n := 4)) 3 true ∅ 0 *
        (∏ k : Fin (0 :: rest).length,
          centreDraw (pathDistance (n := 4)) 3 true
            ((0 :: 0 :: rest).take k.succ.val).toFinset ((0 :: 0 :: rest).get k.succ)) = _
    rw [(four_path_coded_draws (0 : Fin 4)).1]
    apply congrArg (fun x : ℝ => (1/4 : ℝ) * x)
    apply Finset.prod_congr rfl
    intro k _
    exact hdraw k

  -- Treat zero-mass traces as well as terminating ones: hgood identifies
  -- both branches of traceMass's conditional, independently of the product.
  unfold traceMass
  by_cases ht :
      (∀ k : Fin (0 :: rest).length,
        marked (pathDistance (n := 4)) 3 ((0 :: rest).take k.val).toFinset ≠ univ) ∧
      marked (pathDistance (n := 4)) 3 (0 :: rest).toFinset = univ
  · rw [if_pos (hgood.mpr ht), if_pos ht]
    exact hprod
  · have hlong : ¬
        ((∀ k : Fin (0 :: 0 :: rest).length,
            marked (pathDistance (n := 4)) 3 ((0 :: 0 :: rest).take k.val).toFinset ≠ univ) ∧
          marked (pathDistance (n := 4)) 3 (0 :: 0 :: rest).toFinset = univ) :=
      fun h => ht (hgood.mp h)
    rw [if_neg hlong, if_neg ht, mul_zero]

end

end AronowAudit.P045.Wave1.ClusterSampler
