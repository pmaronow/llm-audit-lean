import AronowAudit.P009.P009_PairedCompletion

namespace AronowAudit.P009.ConfidenceInstances
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

/-- Split the actual subject-indexed assignment into the two members of each pair. -/
def splitAssignment (m : ℕ) : Assignment (m+m) ≃ Assignment m × Assignment m where
  toFun z := (fun i => z (finSumFinEquiv (Sum.inl i)), fun i => z (finSumFinEquiv (Sum.inr i)))
  invFun z i := Sum.elim z.1 z.2 (finSumFinEquiv.symm i)
  left_inv z := by
    funext i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  right_inv z := by
    ext i <;> simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]

def pairing (m : ℕ) : Pairing (m+m) where
  partner := (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m) (Fin m))).trans finSumFinEquiv
  involution i := by simp
  no_fixed i := by
    intro h
    have hh := congrArg finSumFinEquiv.symm h
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply] at hh
    have hswap : ∀ j : Fin m ⊕ Fin m, (Equiv.sumComm (Fin m) (Fin m)) j ≠ j := by
      intro j
      cases j <;> simp
    exact hswap _ hh

lemma partner_left (m : ℕ) (i : Fin m) :
    (pairing m).partner (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inr i) := by
  simp only [pairing,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumComm_apply,Sum.swap_inl]

lemma partner_right (m : ℕ) (i : Fin m) :
    (pairing m).partner (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inl i) := by
  simp only [pairing,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumComm_apply,Sum.swap_inr]

lemma opposite_iff (m : ℕ) (z : Assignment (m+m)) :
    (∀ i,z i ≠ z ((pairing m).partner i)) ↔
      (splitAssignment m z).2 = fun i => !(splitAssignment m z).1 i := by
  constructor
  · intro h
    funext i
    have hi := h (finSumFinEquiv (Sum.inl i))
    rw [partner_left] at hi
    change z (finSumFinEquiv (Sum.inr i)) = !(z (finSumFinEquiv (Sum.inl i)))
    cases ha : z (finSumFinEquiv (Sum.inl i)) <;> cases hb : z (finSumFinEquiv (Sum.inr i)) <;> simp_all
  · intro h i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    have hh (k : Fin m) := congrFun h k
    cases j with
    | inl k =>
      rw [partner_left]
      have hk := hh k
      change z (finSumFinEquiv (Sum.inr k)) = !(z (finSumFinEquiv (Sum.inl k))) at hk
      rw [hk]
      cases z (finSumFinEquiv (Sum.inl k)) <;> decide
    | inr k =>
      rw [partner_right]
      have hk := hh k
      change z (finSumFinEquiv (Sum.inr k)) = !(z (finSumFinEquiv (Sum.inl k))) at hk
      rw [hk]
      cases z (finSumFinEquiv (Sum.inl k)) <;> decide

/-- The normalized law of independent fair flips, one flip for each actual pair. -/
def pairedLaw (m : ℕ) : Law (Assignment (m+m)) where
  mass z := if (splitAssignment m z).2 = fun i => !(splitAssignment m z).1 i
    then 1 / (2 : ℝ)^m else 0
  nonneg z := by split_ifs <;> positivity
  total := by
    rw [←(splitAssignment m).symm.sum_comp,Fintype.sum_prod_type]
    simp [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]

def experiment (m : ℕ) : Experiment (m+m) := ⟨pairedLaw m,fun _ _ => 0⟩

lemma paired (m : ℕ) : Paired (experiment m) (pairing m) := by
  refine ⟨⟨m,rfl⟩,?_⟩
  intro z
  have hm : (m+m)/2=m := by omega
  simp only [experiment,pairedLaw,opposite_iff,hm]

lemma interferes_iff (m : ℕ) (i j : Fin (m+m)) :
    Interferes (experiment m) i j ↔ i=j := by
  simp [Interferes,experiment]

lemma dependent_iff (m : ℕ) (i j : Fin (m+m)) :
    Dependent (experiment m) i j ↔ i=j := by
  simp only [Dependent,interferes_iff]
  simp

lemma rsum_zero (m : ℕ) : rSum (experiment m) (pairing m)=0 := by
  simp [rSum,I,interferes_iff,(pairing m).no_fixed]

lemma davg_one (m : ℕ) (hm : 0 < m) : dAvg (experiment m)=1 := by
  simp [dAvg,degree,d,dependent_iff,hm.ne']

lemma eavg_one (m : ℕ) (hm : 0 < m) : eAvg (experiment m) (pairing m)=1 := by
  have he (i j : Fin (m+m)) :
      (¬i=j ∧ (pairing m).partner i=j) ↔ (pairing m).partner i=j := by
    refine ⟨And.right,fun h => ⟨?_,h⟩⟩
    intro hij
    exact (pairing m).no_fixed i (h.trans hij.symm)
  simp [eAvg,e,dependent_iff,interferes_iff,he,hm.ne']

lemma regular (m : ℕ) : Regular (experiment m) 2 2 1 := by
  refine ⟨by norm_num,by norm_num,by norm_num,?_,?_,?_⟩
  · intro i
    rw [PairedCompletion.marginal_half (experiment m) (pairing m) (paired m)]
    norm_num
  · intro i
    norm_num [experiment,mean]
  · intro i b
    norm_num [potential,experiment,mean]

/-- A genuine sequence of normalized paired designs with increasing size. -/
def study : Study where
  N t := (t+1)+(t+1)
  positive t := by omega
  grows := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with t ht
    omega
  experiment t := experiment (t+1)

/-- Every premise of the original paired-consistency theorem is inhabited.
The assignment laws have one independent fair flip per pair. Outcomes are zero;
no positive outcome variance was assumed by this consistency contract. -/
theorem paired_consistency_original_premises :
    RegularSequence study 2 2 1 ∧
    (∀ t,Paired (study.experiment t) (pairing (t+1))) ∧
    Restricted study ∧
    LittleO (fun t=>eAvg (study.experiment t) (pairing (t+1))) (size study) ∧
    LittleO (fun t=>rSum (study.experiment t) (pairing (t+1))) (size study) := by
  have hg : Tendsto (size study) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp study.grows
  have hi : Tendsto (fun t=>1/size study t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hg
  have hd (t : ℕ) : dAvg (study.experiment t)=1 := davg_one (t+1) (by omega)
  have he (t : ℕ) : eAvg (study.experiment t) (pairing (t+1))=1 :=
    eavg_one (t+1) (by omega)
  have hr (t : ℕ) : rSum (study.experiment t) (pairing (t+1))=0 := rsum_zero (t+1)
  refine ⟨fun t=>regular (t+1),fun t=>paired (t+1),?_,?_,?_⟩
  · simpa only [Restricted,hd] using hi
  · simpa only [LittleO,he] using hi
  · simp only [LittleO,hr,zero_div]
    exact tendsto_const_nhds

#print axioms paired_consistency_original_premises

/-- Direct application of the existing consistency theorem to the constructed
models. This is a confidence certificate, with no new paper-theorem credit. -/
theorem paired_consistency_application :
    EstimatorClaims study (fun t=>eate (study.experiment t))
      (fun t=>bernoulliRate study t +
        Real.sqrt (eAvg (study.experiment t) (pairing (t+1)))/Real.sqrt (size study t) +
        rSum (study.experiment t) (pairing (t+1))/size study t) := by
  obtain ⟨hreg,hpair,hrest,he,hr⟩ := paired_consistency_original_premises
  exact paired_consistency study (fun t=>pairing (t+1)) 2 2 1 hreg hpair hrest he hr

#print axioms paired_consistency_application

end
end AronowAudit.P009.ConfidenceInstances
