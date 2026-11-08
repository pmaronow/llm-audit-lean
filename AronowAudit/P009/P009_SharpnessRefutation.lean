import AronowAudit.P009.P009_NormalCompletion
namespace AronowAudit.P009.SharpnessRefutation
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The overstrong former fixed-population assertion, retained as a proposition. -/
def PrintedFixedConstruction : Prop := ∀ {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s α x : ℝ) (hReg : Regular E k q s) (hBER : Bernoulli E)
    (hα : 0 < α ∧ α < 1) (hx : 0 ≤ x ∧ x < 1) (h b : ℕ)
    (hh : h = ⌈Real.rpow (n:ℝ) ((x+1)/2)⌉₊ ∧ 1 ≤ h ∧ h ≤ n)
    (hb : b ≤ h) (f : Assignment b → ℝ)
    (hf : ∀ z, f z = -1 ∨ f z = 0 ∨ f z = 1)
    (hmin : ∀ g : Assignment b → ℝ, (∀ z, g z = -1 ∨ g z = 0 ∨ g z = 1) →
      approximationError E.design α (fun z => f (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb.trans hh.2.2)⟩)) ≤
      approximationError E.design α (fun z => g (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb.trans hh.2.2)⟩))),
    let D := (h:ℝ)^2/(n:ℝ)+((n:ℝ)-h)/(n:ℝ)
    let F := fun z : Assignment n => f (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb.trans hh.2.2)⟩)
    let E' : Experiment n := {E with outcome := fun i z =>
      if i.val < h then (1/(h:ℝ))*Real.sqrt n*Real.sqrt D*
        (bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false)*F z else 0}
    (∀ i j, d E' i j = if i = j ∨ i.val < h ∧ j.val < h then 1 else 0) ∧
    dAvg E' = D ∧ dMax E' = h ∧
    (∀ i z, |(bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false)*F z| ≤ 1) ∧
    (1/(h:ℝ))*Real.sqrt n*Real.sqrt D ≤ 1+Real.sqrt n/(h:ℝ) ∧
    1+Real.sqrt n/(h:ℝ) ≤ 2 ∧ (∀ i z, |E'.outcome i z| ≤ 2) ∧
    (∀ z, ht E' z = Real.sqrt D/Real.sqrt n*F z ∧
      Real.sqrt n/Real.sqrt D*(ht E' z-mean E'.design (ht E')) =
        F z-(prob E.design (fun w => F w = 1)-prob E.design (fun w => F w = -1)))

lemma zero_minimizes :
    ∀ g : Assignment 0 → ℝ, (∀ z, g z = -1 ∨ g z = 0 ∨ g z = 1) →
      approximationError (fairLaw 4) (1/2) (fun _ : Assignment 4 => (0:ℝ)) ≤
        approximationError (fairLaw 4) (1/2) (fun z=>g (fun i : Fin 0=>z (Fin.elim0 i))) := by
  intro g hg
  let u : Assignment 0 := fun i=>Fin.elim0 i
  have he (z : Assignment 4) : (fun i : Fin 0=>z (Fin.elim0 i))=u := Subsingleton.elim _ _
  simp_rw [he]
  rcases hg u with h|h|h <;>
    simp [approximationError,h,prob,mean_const] <;> norm_num

theorem printed_fixed_construction_false : ¬ PrintedFixedConstruction := by
  intro H
  let E : Experiment 4 := fairExperiment 4 (fun _ _=>0)
  have hReg : Regular E 2 4 1 :=
    SparseCompletion.fair_regular_bounded 4 _ (by intro i z; norm_num)
  have hBER : Bernoulli E := SparseCompletion.fair_BER _ _
  have hh : 2=⌈Real.rpow (4:ℝ) (((0:ℝ)+1)/2)⌉₊ ∧ 1≤(2:ℕ) ∧ 2≤4 := by
    norm_num [Real.rpow_div_two_eq_sqrt]
  have hmin : ∀ g : Assignment 0 → ℝ, (∀ z, g z = -1 ∨ g z = 0 ∨ g z = 1) →
      approximationError E.design (1/2)
        (fun z=> (fun _ : Assignment 0=>(0:ℝ)) (fun i=>z ⟨i.val,by omega⟩)) ≤
      approximationError E.design (1/2)
        (fun z=>g (fun i=>z ⟨i.val,by omega⟩)) := by
    intro g hg
    change approximationError (fairLaw 4) (1/2) (fun _=>(0:ℝ)) ≤ _
    convert zero_minimizes g hg using 1
    congr 1
    funext z
    congr 1
    exact Subsingleton.elim _ _
  have HC := H (n:=4) (by omega) E 2 4 1 (1/2) 0 hReg hBER (by norm_num) (by norm_num)
    2 0 hh (by omega) (fun _=>0) (by intro z; simp) hmin
  let E' : Experiment 4 := {E with outcome:=fun _ _=>0}
  have hNo : NoInterference E' := by intro i z w _; rfl
  have hD := HC.2.1
  change dAvg {E with outcome := _}=(2:ℝ)^2/4+(4-2)/4 at hD
  simp only [Nat.cast_ofNat,mul_zero,ite_self] at hD
  have hactual : dAvg E'=1 := SparseCompletion.noI_dAvg (by omega) E' hNo
  change dAvg E'= _ at hD
  rw [hactual] at hD
  norm_num at hD
#print axioms printed_fixed_construction_false
end
end AronowAudit.P009.SharpnessRefutation
