import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O6
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_SpatialCLTCompletion

/-! The fixed-degree CLT applied to the genuinely independent centered own-coin
summands. The dependency graph below proves full family independence directly. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

/-- Arbitrary functions of distinct own coins have a full singleton dependency graph.
This is stronger than checking just the pairwise covariances. -/
theorem own_finiteDependencyGraph {N : ℕ} (p : Fin N → ℝ) (f : Fin N → Bool → ℝ) :
    FiniteDependencyGraph p (fun i z => f i (z i)) (fun i => {i}) := by
  refine ⟨by intro i; simp, by intro i j; simp [eq_comm], ?_⟩
  intro I J hsep A C
  let S : Set (Fin N) := I
  have hF : DependsOn
      (fun z : Assignment N => if A (fun i : I => f i (z i)) then (1 : ℝ) else 0) S := by
    intro x y hxy
    have he : (fun i : I => f i (x i)) = (fun i : I => f i (y i)) := by
      funext i
      exact congrArg (f i) (hxy i i.property)
    exact congrArg (fun v : I → ℝ => if A v then (1 : ℝ) else 0) he
  have hG : DependsOn
      (fun z : Assignment N => if C (fun j : J => f j (z j)) then (1 : ℝ) else 0) (Sᶜ) := by
    intro x y hxy
    have he : (fun j : J => f j (x j)) = (fun j : J => f j (y j)) := by
      funext j
      have hj : (j : Fin N) ∈ Sᶜ := by
        change (j : Fin N) ∉ I
        intro hjI
        exact hsep (j : Fin N) hjI (j : Fin N) j.property (by simp)
      exact congrArg (f j) (hxy j hj)
    exact congrArg (fun v : J → ℝ => if C v then (1 : ℝ) else 0) he
  have hevent :
      (fun z : Assignment N =>
        if A (fun i : I => f i (z i)) ∧ C (fun j : J => f j (z j)) then (1 : ℝ) else 0) =
      (fun z : Assignment N =>
        (if A (fun i : I => f i (z i)) then (1 : ℝ) else 0) *
          (if C (fun j : J => f j (z j)) then (1 : ℝ) else 0)) := by
    funext z
    split_ifs <;> simp_all
  change expect p _ = expect p _ * expect p _
  beta_reduce
  calc
    _ = expect p (fun z : Assignment N =>
        (if A (fun i : I => f i (z i)) then (1 : ℝ) else 0) *
          (if C (fun j : J => f j (z j)) then (1 : ℝ) else 0)) := by
      congr 1
      funext z
      split_ifs <;> simp_all
    _ = _ := GraphCompletion.expect_mul_of_disjoint_depends p S _ _ hF hG

def centeredActive (N : ℕ) : CircleTable N :=
  fun i z => activeSign N i * (bit (z i) - 1/2)

theorem centeredActive_sum (N : ℕ) (z : Assignment N) :
    (∑ i, centeredActive N i z) = SAct N z - sAct N / 2 := by
  unfold centeredActive SAct sAct
  rw [show (∑ i : Fin N, activeSign N i * (bit (z i) - 1/2)) =
      (∑ i : Fin N, activeSign N i * bit (z i)) -
        (∑ i : Fin N, activeSign N i * (1/2)) by
    simp only [mul_sub, Finset.sum_sub_distrib]]
  rw [← Finset.sum_mul]
  ring

theorem centeredActive_mean (N : ℕ) (i : Fin N) :
    expect (propensities (activeO N) activeTheta) (centeredActive N i) = 0 := by
  change expect (propensities (activeO N) activeTheta)
    (fun z => activeSign N i * (bit (z i) - 1/2)) = 0
  rw [own_expect _ i (fun a => activeSign N i * (bit a - 1/2)), o4_proof N]
  by_cases hi : activeGroup N i
  · norm_num [hi, bit]
    <;> ring
  · simp [hi, activeSign_of_not_group i hi]

theorem centeredActive_variance (N : ℕ) :
    variance (propensities (activeO N) activeTheta) (fun z => ∑ i, centeredActive N i z) =
      nH N / 4 := by
  change variance (propensities (activeO N) activeTheta)
    (fun z => ∑ i : Fin N, (fun a : Bool => activeSign N i * (bit a - 1/2)) (z i)) = _
  rw [own_sum_variance _ (fun i a => activeSign N i * (bit a - 1/2))]
  calc
    _ = ∑ i : Fin N, (activeSign N i)^2 / 4 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [o4_proof N]
      by_cases hi : activeGroup N i
      · norm_num [hi, bit]
        <;> ring
      · simp [hi, bit, activeSign_of_not_group i hi]
    _ = _ := by rw [← Finset.sum_div, sum_activeSign_sq]

theorem centeredActive_second (N : ℕ) :
    expect (propensities (activeO N) activeTheta) (fun z => (∑ i, centeredActive N i z)^2) =
      nH N / 4 := by
  have hm : expect (propensities (activeO N) activeTheta)
      (fun z => ∑ i, centeredActive N i z) = 0 := by
    rw [expect_sum]
    simp only [centeredActive_mean, Finset.sum_const_zero]
  have hv := centeredActive_variance N
  rw [variance, cov, hm, mul_zero, sub_zero] at hv
  simpa only [pow_two] using hv

theorem centeredActive_abs_le (N : ℕ) (i : Fin N) (z : Assignment N) :
    |centeredActive N i z| ≤ 1 := by
  have hb : |bit (z i) - 1/2| ≤ 1 := by
    cases hz : z i <;> norm_num [bit, hz]
  calc
    _ = |activeSign N i| * |bit (z i) - 1/2| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul (activeSign_abs_le N i) hb (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem o8_proof : O8 := by
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  let μ : ∀ N, Measure (Assignment N) := fun N =>
    CLTCompletion.designMeasure (p N) (active_true_admissible N)
  have hμ (N : ℕ) : IsProbabilityMeasure (μ N) := by
    exact CLTCompletion.designMeasure_probability (p N) (active_true_admissible N)
  have hmean (N : ℕ) (i : Fin N) : (∫ z, centeredActive N i z ∂μ N) = 0 := by
    rw [CLTCompletion.designMeasure_integral]
    exact centeredActive_mean N i
  have hsecond (N : ℕ) : (∫ z, (∑ i, centeredActive N i z)^2 ∂μ N) = nH N / 4 := by
    rw [CLTCompletion.designMeasure_integral]
    exact centeredActive_second N
  have hdep (N : ℕ) : DependencyGraph (μ N) (centeredActive N) (fun i => {i}) := by
    exact CLTCompletion.finiteGraph_to_measureGraph (p N) (active_true_admissible N)
      (centeredActive N) (fun i => {i})
      (own_finiteDependencyGraph (p N) (fun i a => activeSign N i * (bit a - 1/2)))
  have hbound : ∃ M : ℝ, ∀ N i, ∀ᵐ z ∂μ N, |centeredActive N i z| ≤ M := by
    refine ⟨1, fun N i => Filter.Eventually.of_forall (centeredActive_abs_le N i)⟩
  have hdegree : ∃ D : ℕ, ∀ N (i : Fin N), ({i} : Finset (Fin N)).card ≤ D := by
    exact ⟨1, by intro N i; simp⟩
  have hvar : ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop,
      v * N ≤ (∫ z, (∑ i, centeredActive N i z)^2 ∂μ N) := by
    refine ⟨1/16, by norm_num, Filter.Eventually.of_forall fun N => ?_⟩
    rw [hsecond N]
    have hh := nH_ge_quarter N
    linarith
  have hclt := corrected_dependency_clt μ hμ centeredActive (fun N i => {i})
    (fun N i => measurable_of_finite _) hmean hbound hdep hdegree hvar
  intro x
  refine (hclt x).congr (fun N => ?_)
  rw [hsecond N]
  change ((CLTCompletion.designMeasure (p N) (active_true_admissible N))
      {z | (∑ i, centeredActive N i z) / Real.sqrt (nH N / 4) ≤ x}).toReal =
    prob (p N) (fun z => (SAct N z - sAct N / 2) / Real.sqrt (nH N / 4) ≤ x)
  rw [CLTCompletion.designMeasure_apply]
  apply prob_congr
  intro z
  simp only [Set.mem_setOf_eq, centeredActive_sum]

end
end AronowAudit.P004.Wave1.ObservationalCoverage
