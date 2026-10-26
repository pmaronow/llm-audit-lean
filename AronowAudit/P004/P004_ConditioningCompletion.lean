import AronowAudit.P004.P004_SpatialAlgebraCompletion

namespace AronowAudit.P004.ConditioningCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem join_treated_count {N : ℕ} (i : Fin N) (a : Bool)
    (u : {j : Fin N //j≠i}→Bool) :
    (Finset.univ.filter (fun j=>joinAssignment i a u j=true)).card=
      (Finset.univ.filter (fun j=>u j=true)).card+(if a then 1 else 0) := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [←Finset.sum_erase_add Finset.univ
    (fun j=>if joinAssignment i a u j=true then (1:ℕ) else 0) (Finset.mem_univ i)]
  rw [Finset.sum_subtype (p:=fun j:Fin N=>j≠i) (F:=inferInstance)
    (Finset.univ.erase i) (by intro j;simp)
    (fun j=>if joinAssignment i a u j=true then (1:ℕ) else 0)]
  have hh (j : {j:Fin N//j≠i}) : joinAssignment i a u j=u j:=by
    simp only [joinAssignment,dif_neg j.property]
  simp only [hh]
  cases a <;> simp [joinAssignment]

end
end AronowAudit.P004.ConditioningCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter ConditioningCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- T30(1), the actual conditional completely randomized law. Uniform
assignment over vectors with total n₁ gives a uniform leave-one-out law
on vectors with n₁−a treated nodes, with different arm supports. -/
theorem complete_randomization_conditioning {N : ℕ} (n1 : ℕ)
    (hlo : 1 ≤ n1) (hhi : n1 ≤ N-1) (i : Fin N) (a : Bool) :
    let S := Finset.univ.filter (fun z : Assignment N =>
      (Finset.univ.filter (fun j => z j = true)).card = n1)
    let T := Finset.univ.filter (fun u : {j : Fin N // j ≠ i} → Bool =>
      (Finset.univ.filter (fun j => u j = true)).card = n1 - (if a then 1 else 0))
    ∀ u : {j : Fin N // j ≠ i} → Bool,
      ((S.filter (fun z => z i = a ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j)).card : ℝ) /
        ((S.filter (fun z => z i = a)).card : ℝ) =
      if u ∈ T then 1/(T.card : ℝ) else 0 := by
  dsimp only
  let S:=Finset.univ.filter (fun z:Assignment N=>(Finset.univ.filter (fun j=>z j=true)).card=n1)
  let T:=Finset.univ.filter (fun (u : {j:Fin N//j≠i}→Bool)=>(Finset.univ.filter (fun j=>u j=true)).card=n1-(if a then 1 else 0))
  have hjoin (u : {j:Fin N//j≠i}→Bool) : joinAssignment i a u∈S ↔ u∈T:=by
    simp only [S,T,Finset.mem_filter,Finset.mem_univ,true_and,join_treated_count]
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.sub_zero,Nat.add_zero] <;> omega
  have heq (z : Assignment N) (hz : z i=a) : joinAssignment i a (fun j=>z j)=z:=by
    rw [←hz]
    exact (splitAssignment i).left_inv z
  have hinj : Function.Injective (joinAssignment i a):=by
    intro u v h
    funext j
    have hh:=congrFun h j
    simpa only [joinAssignment,dif_neg j.property] using hh
  have hrest (u : {j:Fin N//j≠i}→Bool) : (fun j:{j:Fin N//j≠i}=>joinAssignment i a u j)=u:=by
    funext j
    simp only [joinAssignment,dif_neg j.property]
  have hfilter (C : ({j:Fin N//j≠i}→Bool)→Prop) :
      S.filter (fun z=>z i=a ∧ C (fun j=>z j))=(T.filter C).image (joinAssignment i a):=by
    ext z
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨hz,hza,hC⟩
      have hm : (fun j:{j:Fin N//j≠i}=>z j)∈T:=(hjoin _).mp (by simpa only [heq z hza] using hz)
      exact ⟨_,⟨hm,hC⟩,heq z hza⟩
    · rintro ⟨u,⟨hu,hC⟩,rfl⟩
      refine ⟨(hjoin u).mpr hu,?_,?_⟩
      · simp [joinAssignment]
      · simpa only [hrest] using hC
  have hden : (S.filter (fun z=>z i=a)).card=T.card:=by
    have hh:=congrArg Finset.card (hfilter (fun _=>True))
    simpa only [and_true,Finset.filter_true,Finset.card_image_of_injective _ hinj] using hh
  intro u
  change ((S.filter _).card:ℝ)/(S.filter _).card=if u∈T then 1/(T.card:ℝ) else 0
  rw [hden]
  have hnum : (S.filter (fun z=>z i=a ∧ ∀j:{j:Fin N//j≠i},z j=u j)).card=
      if u∈T then 1 else 0:=by
    have hset : S.filter (fun z=>z i=a ∧ ∀j:{j:Fin N//j≠i},z j=u j)=
        (T.filter (fun v=>v=u)).image (joinAssignment i a):=by
      ext z
      have hh:=Finset.ext_iff.mp (hfilter (fun v=>v=u)) z
      simpa only [Finset.mem_filter,Finset.mem_image,funext_iff] using hh
    rw [hset,Finset.card_image_of_injective _ hinj]
    by_cases hu : u∈T <;> simp [Finset.filter_eq',hu]

  rw [hnum]
  split_ifs <;> simp


end
end AronowAudit.P004
