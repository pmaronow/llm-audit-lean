/- Exact HT construction identity from unitwise inverse-probability cancellation and symbolic finite-prefix counting. This identity alone does not establish the sharpness construction graph or limiting theorem. -/
import AronowAudit.P009.P009_Audit
namespace AronowAudit.P009.SharpnessCompletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

lemma prefix_count {n : ℕ} (h : ℕ) (hh : h≤n) :
    (∑ i : Fin n,if i.val < h then (1:ℝ) else 0)=h := by
  have hc : (Finset.univ.filter (fun i : Fin n=>i.val < h)).card=h := by
    rw [Fin.card_filter_val_lt,Nat.min_eq_right hh]
  rw [←Finset.sum_filter]
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using congrArg (fun a : ℕ=>(a:ℝ)) hc

theorem sharpness_HT_construction_completed {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) (h : ℕ) (hh : 1 ≤ h ∧ h ≤ n)
    (f : Assignment n → ℝ) (D : ℝ) :
    let E' : Experiment n := {E with outcome := fun i z =>
      if i.val < h then (1/(h:ℝ))*Real.sqrt n*Real.sqrt D*
        (bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false)*f z else 0}
    ∀ z, ht E' z = Real.sqrt D/Real.sqrt n*f z := by
  let A : ℝ:=(1/(h:ℝ))*Real.sqrt n*Real.sqrt D
  let E' : Experiment n:={E with outcome:=fun i z=>if i.val < h then
    A*(bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false)*f z else 0}
  change ∀ z, ht E' z=Real.sqrt D/Real.sqrt n*f z
  intro z
  have hpt (i : Fin n) : 0 < marginal E i true := (hBER.1 i).1
  have hf (i : Fin n) : 0 < marginal E i false := by linarith [marginal_partition E i,(hBER.1 i).2]
  have hterm (i : Fin n) :
      (if z i=true then E'.outcome i z else 0)/marginal E' i true-
      (if z i=false then E'.outcome i z else 0)/marginal E' i false=
      A*f z*(if i.val < h then 1 else 0) := by
    have hmt : marginal E' i true=marginal E i true:=rfl
    have hmf : marginal E' i false=marginal E i false:=rfl
    rw [hmt,hmf]
    by_cases hi : i.val < h
    · cases hz : z i <;> simp [E',hi,hz,bit]
      · field_simp [(hf i).ne']
      · field_simp [(hpt i).ne']
    · simp [E',hi]
  unfold ht muHat
  rw [←sub_div,←Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [←Finset.mul_sum,prefix_count h hh.2]
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  have hh0 : (h:ℝ)≠0:=by exact_mod_cast (by omega : h≠0)
  have hs0 : Real.sqrt (n:ℝ)≠0:=Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hs : (Real.sqrt (n:ℝ))^2=n:=Real.sq_sqrt (Nat.cast_nonneg _)
  dsimp [A]
  field_simp [hn0,hh0,hs0]
  linear_combination (Real.sqrt D*f z)*hs

end
end AronowAudit.P009.SharpnessCompletion

namespace AronowAudit.P009
open scoped BigOperators
noncomputable section
/-- T51 finite identity in the construction, Supplement A pp. 36–38: under
Bernoulli assignment, choosing the printed own-treatment coefficient makes the
HT estimator exactly `Real.sqrt D / Real.sqrt n` times the supplied function `f`
whenever `1 ≤ h ≤ n`. -/
theorem sharpness_HT_construction {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) (h : ℕ) (hh : 1 ≤ h ∧ h ≤ n)
    (f : Assignment n → ℝ) (D : ℝ) :
    let E' : Experiment n := {E with outcome := fun i z =>
      if i.val < h then (1/(h:ℝ))*Real.sqrt n*Real.sqrt D*
        (bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false)*f z else 0}
    ∀ z, ht E' z = Real.sqrt D/Real.sqrt n*f z := by
  exact SharpnessCompletion.sharpness_HT_construction_completed hn E hBER h hh f D

end
end AronowAudit.P009
