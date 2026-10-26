import AronowAudit.P014.P014_PrintedClaims

namespace AronowAudit.P014.Refutations
open scoped BigOperators
noncomputable section
universe u v
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Lift the same actual finite law; no scores, outcomes, or probabilities change. -/
def liftLaw {Ω : Type v} (L : FiniteLaw Ω) : FiniteLaw (ULift.{u} Ω) := L.map ULift.up

lemma lift_prob {Ω : Type v} (L : FiniteLaw Ω) (P : Ω → Prop) :
    (liftLaw.{u} L).prob (fun ω => P ω.down) = L.prob P := by
  exact prob_map L ULift.up _

lemma lift_printed_local {Ω : Type v} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N))
    (h : PrintedLocal L X b S) :
    PrintedLocal (liftLaw.{u} L) (fun ω => X ω.down) b S := by
  classical
  rcases h with ⟨hmem,⟨F,hF⟩,hprob,hNT,hcount⟩
  have hsupp : (liftLaw.{u} L).support =
      L.support.image (ULift.up : Ω → ULift.{u} Ω) := by
    ext ω
    simp only [liftLaw,FiniteLaw.map,Finset.mem_image]
  refine ⟨?_,⟨F,?_⟩,?_,?_,?_⟩
  · simpa only [hsupp,Finset.forall_mem_image,ULift.down_up] using hmem
  · simpa only [hsupp,Finset.forall_mem_image,ULift.down_up] using hF
  · intro ω hω
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp (hsupp ▸ hω)
    simpa only [liftLaw,prob_map,Function.comp_def,ULift.down_up] using hprob η hη
  · intro i hi j hj hij
    simpa only [liftLaw,prob_map,Function.comp_def,ULift.down_up] using hNT i hi j hj hij
  · simpa only [hsupp,Finset.forall_mem_image,ULift.down_up] using hcount

lemma lift_corrected_local {Ω : Type v} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ)
    (h : FiniteCorrectedLocal L X b S v) :
    FiniteCorrectedLocal (liftLaw.{u} L) (fun ω => X ω.down) b S v := by
  classical
  refine ⟨?_,?_⟩
  · simpa only [liftLaw,FiniteLaw.map,Finset.forall_mem_image,ULift.down_up] using h.1
  · intro σ
    simpa only [liftLaw,prob_map,Function.comp_def,ULift.down_up] using h.2 σ


lemma lift_threshold_law {Ω : Type v} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) :
    (liftLaw.{u} L).map (fun ω => threshold (X ω.down)) =
      L.map (fun ω => threshold (X ω)) := by
  have hext (A B : FiniteLaw (Assignment N)) (hs : A.support=B.support)
      (hm : A.mass=B.mass) : A=B := by
    cases A; cases B; cases hs; cases hm; rfl
  apply hext
  · simp only [liftLaw,FiniteLaw.map,Finset.image_image,Function.comp_def,ULift.down_up]
  · funext z
    exact lift_prob L (fun ω => threshold (X ω)=z)

/-- The three actual window subjects, identified with their three score indices. -/
def windowEquiv : threeWindow ≃ Fin 3 where
  toFun i := ⟨i.1.val, by
    have hi : i.1=0 ∨ i.1=1 ∨ i.1=2 := by simpa [threeWindow] using i.2
    rcases hi with h|h|h <;> rw [h] <;> decide⟩
  invFun j := ⟨j.castSucc, by fin_cases j <;> norm_num [threeWindow]⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl

def witnessValues : Fin 3 → ℝ := ![-2,-1,1]
def witnessScores : threeWindow → ℝ := fun i => witnessValues (windowEquiv i)

lemma witness_scores_injective : Function.Injective witnessScores := by
  have hv : Function.Injective witnessValues := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [witnessValues] at h
  exact hv.comp windowEquiv.injective

lemma witness_scores_window : ∀ i, inWindow 2 (witnessScores i) := by
  intro i
  change inWindow 2 (witnessValues (windowEquiv i))
  generalize windowEquiv i=j
  fin_cases j <;> norm_num [inWindow,witnessValues]

lemma witness_corrected_local : FiniteCorrectedLocal sixLaw witnessX 2 threeWindow witnessScores := by
  refine ⟨witness_printed_local.1,?_⟩
  intro σ
  let σ' : Equiv.Perm (Fin 3) := (windowEquiv.symm.trans σ).trans windowEquiv
  have hevent : (fun ω => ∀ i : threeWindow, witnessX ω i = witnessScores (σ i)) =
      (fun ω => ∀ j : Fin 3, witnessX ω j.castSucc = witnessValues (σ' j)) := by
    funext ω
    apply propext
    constructor
    · intro h j
      exact h (windowEquiv.symm j)
    · intro h i
      have hh := h (windowEquiv i)
      change witnessX ω (Fin.castSucc (windowEquiv i)) =
        witnessValues (windowEquiv (σ (windowEquiv.symm (windowEquiv i)))) at hh
      rw [windowEquiv.symm_apply_apply] at hh
      have hi : Fin.castSucc (windowEquiv i) = (i : Fin 4) := by apply Fin.ext; rfl
      rw [hi] at hh
      exact hh
  change sixLaw.prob (fun ω => ∀ i : threeWindow, witnessX ω i = witnessScores (σ i)) = _
  rw [hevent]
  exact all_local_permutations_equiprobable.1 σ'

/-- The full printed assertion is false at every Lean universe level. -/
theorem printed_unbiasedness_refuted : ¬ PrintedClaims.printed_unbiasedness.{u} := by
  intro h
  have hh := h (liftLaw.{u} sixLaw) (fun ω => witnessX ω.down) 2 threeWindow spilloverAll
    (by decide) (lift_printed_local sixLaw witnessX 2 threeWindow witness_printed_local)
  rw [lift_threshold_law] at hh
  apply t1_counterexample.2.2.2.2.2
  simpa only [windowContrast,Finset.sum_sub_distrib] using hh

/-- Uniform local score permutations do not repair the printed unweighted estimand. -/
theorem printed_unbiasedness_intended_local_refuted :
    ¬ PrintedClaims.printed_unbiasedness_intended_local.{u} := by
  intro h
  have hh := h (liftLaw.{u} sixLaw) (fun ω => witnessX ω.down) 2 threeWindow witnessScores
    spilloverAll (by decide) witness_scores_injective witness_scores_window
    (lift_printed_local sixLaw witnessX 2 threeWindow witness_printed_local)
    (lift_corrected_local sixLaw witnessX 2 threeWindow witnessScores witness_corrected_local)
  rw [lift_threshold_law] at hh
  exact t1_counterexample.2.2.2.2.2 hh

end
end AronowAudit.P014.Refutations
