import AronowAudit.P009.P009_OneSourceCompletion
namespace AronowAudit.P009.LimsupCompletion
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma limsup_interferes {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    Interferes (limsupExperiment n hn) i j ↔
      Interferes (fairExperiment n (oneSourceOutcome (limsupCluster n) (fun _=>0))) i j := by
  let o : Fin n := ⟨0,hn⟩
  let G : Finset (Fin n) := if j.val < limsupCluster n then {o} else ∅
  have hy (z : Assignment n) : (limsupExperiment n hn).outcome j z=∑ l∈G,bit (z l) := by
    dsimp [limsupExperiment,fairExperiment,G]
    split_ifs <;> simp [o]
  rw [interferes_sum_bit _ j i G hy,OneSourceCompletion.source_interferes hn]
  by_cases hj : j.val < limsupCluster n
  · rw [show G={o} by simp [G,hj]]
    simp only [Finset.mem_singleton]
    constructor
    · rintro (he|he)
      · exact Or.inl he
      · by_cases hij : i=j
        · exact Or.inl hij
        · refine Or.inr ⟨?_,?_,hj⟩
          · simpa [o] using congrArg Fin.val he
          · have hjo : j.val≠0 := by
              intro hzero
              apply hij
              exact he.trans (Fin.ext hzero.symm)
            omega
    · rintro (he|⟨he,hj0,hjb⟩)
      · exact Or.inl he
      · exact Or.inr (Fin.ext he)
  · simp [G,hj]

lemma limsup_density_exact (n : ℕ) (hn : 0 < n) :
    dAvg (limsupExperiment n hn)/(n:ℝ)=limsupDensity n := by
  have hb : 1 ≤ limsupCluster n ∧ limsupCluster n ≤ n := by
    dsimp [limsupCluster]
    omega
  have hg : dAvg (limsupExperiment n hn)=
      dAvg (fairExperiment n (oneSourceOutcome (limsupCluster n) (fun _=>0))) := by
    unfold dAvg degree d Dependent
    simp_rw [limsup_interferes hn]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl
  rw [hg]
  have h := OneSourceCompletion.source_davg hn (limsupCluster n) hb (fun _=>0)
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold limsupDensity
  field_simp [hn0]
  nlinarith [h]

lemma limsup_regular : RegularSequence limsupStudy 3 2 1 := by
  intro t
  let y := fun i : Fin (t+1) => fun z : Assignment (t+1) =>
    if i.val < limsupCluster (t+1) then bit (z 0) else 0
  have hb (i : Fin (t+1)) (z : Assignment (t+1)) : |y i z|≤1 := by
    dsimp [y]
    split_ifs <;> cases z 0 <;> norm_num [bit]
  refine ⟨by norm_num,by norm_num,by norm_num,?_,?_,?_⟩
  · intro i
    change (3:ℝ)⁻¹ ≤ marginal (fairExperiment (t+1) y) i true ∧ marginal (fairExperiment (t+1) y) i true ≤ 1-(3:ℝ)⁻¹
    rw [SparseCompletion.fair_marginal]
    norm_num
  · intro i
    apply SparseCompletion.mean_le_constant
    intro z
    change Real.rpow |y i z| 2≤Real.rpow 3 2
    simp only [Real.rpow_eq_pow,Real.rpow_two]
    nlinarith [sq_nonneg |y i z|,abs_nonneg (y i z),hb i z]
  · intro i b
    apply SparseCompletion.mean_le_constant
    intro z
    change Real.rpow |y i (Function.update z i b)| 1 ≤ Real.rpow 3 1
    simp only [Real.rpow_eq_pow,Real.rpow_one]
    exact (hb i _).trans (by norm_num)

theorem limsup_interference_counterexample_completed :
    RegularSequence limsupStudy 3 2 1 ∧
    (∀ t, Bernoulli (limsupStudy.experiment t) ∧
      dAvg (limsupStudy.experiment t)/size limsupStudy t = limsupDensity (t+1)) ∧
    Tendsto (fun t => dAvg (limsupStudy.experiment t)/size limsupStudy t)
      atTop (nhds (1/4)) ∧
    (∀ t, 1/4 ≤ dAvg (limsupStudy.experiment t)/size limsupStudy t ↔ t+1 ≤ 4) := by
  have he (t : ℕ) : dAvg (limsupStudy.experiment t)/size limsupStudy t=limsupDensity (t+1) :=
    limsup_density_exact (t+1) (by omega)
  refine ⟨limsup_regular,fun t=>⟨SparseCompletion.fair_BER _ _,he t⟩,?_,?_⟩
  · simpa only [he] using limsup_density_limit
  · intro t
    rw [he]
    exact limsup_threshold_counterexample.2.1 (t+1) (by omega)
end
end AronowAudit.P009.LimsupCompletion

namespace AronowAudit.P009
open scoped BigOperators
open Filter
noncomputable section
theorem limsup_interference_counterexample :
    RegularSequence limsupStudy 3 2 1 ∧
    (∀ t, Bernoulli (limsupStudy.experiment t) ∧
      dAvg (limsupStudy.experiment t)/size limsupStudy t = limsupDensity (t+1)) ∧
    Tendsto (fun t => dAvg (limsupStudy.experiment t)/size limsupStudy t)
      atTop (nhds (1/4)) ∧
    (∀ t, 1/4 ≤ dAvg (limsupStudy.experiment t)/size limsupStudy t ↔ t+1 ≤ 4) := by
  exact LimsupCompletion.limsup_interference_counterexample_completed
end
end AronowAudit.P009
