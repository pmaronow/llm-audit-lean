/- P011 T21: finite correlation correction, including the zero-variance convention.
All covariance and oracle identities are derived from weighted-coordinate L2
and full dependency independence. -/
import AronowAudit.P011.P011_ExpectationCompletion

namespace AronowAudit.P011.CorrelationCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma common_variance {n : ℕ} (hn : 0<n) (m : Model n) (hs : Homoskedastic m) (i : Fin n) :
    meanVariance m=covariance m i i := by
  have hC (j : Fin n) : covariance m j j=covariance m i i := hs j i
  unfold meanVariance
  simp_rw [hC]
  simp [Nat.ne_of_gt hn]

lemma covariance_abs_le_common {n : ℕ} (hn : 0<n) (m : Model n) (hs : Homoskedastic m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) (i j : Fin n) :
    |covariance m i j| ≤ meanVariance m := by
  let : IsProbabilityMeasure m.law := m.probability
  have hi : ProbabilityTheory.variance (fun y => weighted m y i) m.law=meanVariance m := by
    rw [common_variance hn m hs i,QuadraticCompletion.covariance_eq_mathlib,
      ProbabilityTheory.covariance_self (hL2 i).aemeasurable]
  have hj : ProbabilityTheory.variance (fun y => weighted m y j) m.law=meanVariance m := by
    rw [common_variance hn m hs j,QuadraticCompletion.covariance_eq_mathlib,
      ProbabilityTheory.covariance_self (hL2 j).aemeasurable]
  have hp := ProbabilityTheory.variance_nonneg (fun y => weighted m y i+weighted m y j) m.law
  have hm := ProbabilityTheory.variance_nonneg (fun y => weighted m y i-weighted m y j) m.law
  rw [ProbabilityTheory.variance_fun_add (hL2 i) (hL2 j),hi,hj] at hp
  rw [ProbabilityTheory.variance_fun_sub (hL2 i) (hL2 j),hi,hj] at hm
  rw [QuadraticCompletion.covariance_eq_mathlib]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma meanVariance_nonneg {n : ℕ} (hn : 0<n) (m : Model n) (hs : Homoskedastic m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) : 0≤meanVariance m := by
  let i : Fin n := ⟨0,hn⟩
  rw [common_variance hn m hs i,QuadraticCompletion.covariance_eq_mathlib,
    ProbabilityTheory.covariance_self (hL2 i).aemeasurable]
  exact ProbabilityTheory.variance_nonneg _ _

lemma sigma_rho {n : ℕ} (hn : 0<n) (m : Model n) (hs : Homoskedastic m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) (i j : Fin n) :
    meanVariance m*rho m i j=covariance m i j := by
  unfold rho
  by_cases h : meanVariance m=0
  · rw [if_pos h,h,zero_mul]
    have hb := covariance_abs_le_common hn m hs hL2 i j
    rw [h] at hb
    exact (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))).symm
  · rw [if_neg h]
    field_simp

lemma rho_le_one {n : ℕ} (hn : 0<n) (m : Model n) (hs : Homoskedastic m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) (i j : Fin n) : rho m i j≤1 := by
  unfold rho
  by_cases h : meanVariance m=0
  · simp [h]
  · rw [if_neg h]
    have hp : 0<meanVariance m := lt_of_le_of_ne (meanVariance_nonneg hn m hs hL2) (Ne.symm h)
    apply (div_le_one hp).mpr
    exact (le_abs_self _).trans (covariance_abs_le_common hn m hs hL2 i j)

lemma covariance_total_identity {n : ℕ} (hn : 0<n) (m : Model n) (hdep : Dependency m)
    (hs : Homoskedastic m) (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) :
    QuadraticCompletion.total (covariance m)=
      (n:ℝ)*meanVariance m+meanVariance m*(∑ i,∑ j,adjacency m.G i j*rho m i j) := by
  classical
  have hc (i j : Fin n) : covariance m i j=
      (if i=j then meanVariance m else 0)+adjacency m.G i j*covariance m i j := by
    by_cases h : i=j
    · subst j
      simp [m.G.property.2,adjacency,common_variance hn m hs i]
    · rw [if_neg h]
      by_cases hg : m.G.val i j=true
      · simp [adjacency,hg]
      · have hf : m.G.val i j=false := by cases he : m.G.val i j <;> simp_all
        rw [OracleCompletion.covariance_support m hdep hL2 i j h hf]
        simp
  have he : (∑ i,∑ j,adjacency m.G i j*covariance m i j)=
      meanVariance m*(∑ i,∑ j,adjacency m.G i j*rho m i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [←sigma_rho hn m hs hL2 i j]
    ring
  unfold QuadraticCompletion.total
  calc
    _ = ∑ i,∑ j,((if i=j then meanVariance m else 0)+adjacency m.G i j*covariance m i j) := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hc i j))
    _ = (n:ℝ)*meanVariance m+(∑ i,∑ j,adjacency m.G i j*covariance m i j) := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      simp
    _ = _ := by rw [he]

lemma pairwise_correlation_repair_completed {n : ℕ} (hn : 0 < n) (m : Model n)
    (hdep : Dependency m) (hs : Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    (n : ℝ)*var m (betaHat m) = meanVariance m*
      (1+(∑ i, ∑ j, adjacency m.G i j*rho m i j)/n) ∧
    (∀ i j, rho m i j ≤ 1) ∧ (∀ y, V2star m y ≤ V2 m.G (weighted m y)) := by
  have hnR : 0<(n:ℝ) := by positivity
  have hn0 : (n:ℝ)≠0 := ne_of_gt hnR
  have hρ := rho_le_one hn m hs hL2
  refine ⟨?_,hρ,?_⟩
  · rw [QuadraticCompletion.beta_variance _ hL2,covariance_total_identity hn m hdep hs hL2]
    field_simp <;> ring
  · intro y
    have ha (i j : Fin n) : 0≤adjacency m.G i j := by
      unfold adjacency
      split_ifs <;> norm_num
    have hsum : (∑ i,∑ j,adjacency m.G i j*rho m i j)≤∑ i,∑ j,adjacency m.G i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hρ i j) (ha i j)
    have hsample : 0≤sampleVariance (weighted m y)/(n:ℝ) :=
      div_nonneg (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hnR.le) hnR.le
    apply mul_le_mul_of_nonneg_left ?_ hsample
    simpa only [add_comm] using add_le_add_left (div_le_div_of_nonneg_right hsum hnR.le) 1

end
end AronowAudit.P011.CorrelationCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem pairwise_correlation_repair {n : ℕ} (hn : 0 < n) (m : Model n)
    (hdep : Dependency m) (hs : Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    (n : ℝ)*var m (betaHat m) = meanVariance m*
      (1+(∑ i, ∑ j, adjacency m.G i j*rho m i j)/n) ∧
    (∀ i j, rho m i j ≤ 1) ∧ (∀ y, V2star m y ≤ V2 m.G (weighted m y)) := by
  exact CorrelationCompletion.pairwise_correlation_repair_completed hn m hdep hs hL2
end AronowAudit.P011

