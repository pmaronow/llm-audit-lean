import AronowAudit.Literature.CondP037P041

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

namespace AronowAudit.P037.Wave1

lemma CondP037P041_dirichlet_one (k : ℕ) :
    AronowAudit.Literature.dirichletFreeLaw k (fun _ => 1) =
      (k.factorial : ℝ≥0∞) • (volume.restrict (openProbabilitySimplex k)) := by
  have hd : AronowAudit.Literature.dirichletFreeDensity k (fun _ => 1) =
      fun _ => (k.factorial : ℝ≥0∞) := by
    funext p
    simp [AronowAudit.Literature.dirichletFreeDensity, Real.Gamma_one,
      Real.Gamma_nat_eq_factorial]
  rw [AronowAudit.Literature.dirichletFreeLaw, hd, withDensity_const]
  rfl

lemma CondP037P041_measurable_completion (k : ℕ) : Measurable (completeSimplex k) := by
  apply measurable_pi_lambda
  intro i
  unfold completeSimplex
  split_ifs with hi
  · exact measurable_pi_apply _
  · exact measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

lemma CondP037P041_completion_normalize {k : ℕ} (w : Fin (k+1) → ℝ)
    (ht : (∑ i, w i) ≠ 0) :
    completeSimplex k (fun i => w i.castSucc / ∑ j, w j) = normalizeWeights w := by
  funext i
  unfold completeSimplex normalizeWeights
  split_ifs with hi
  · congr 1
  · have hi' : i = Fin.last k := by
      apply Fin.ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) (Nat.le_of_not_gt hi)
    subst i
    rw [← Finset.sum_div]
    have hs := Fin.sum_univ_castSucc w
    apply (eq_div_iff ht).2
    rw [sub_mul, div_mul_cancel₀ _ ht, one_mul]
    linarith

lemma CondP037P041_exponential_positive :
    ∀ᵐ x : ℝ ∂ProbabilityTheory.expMeasure 1, 0 < x := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  rw [ae_iff]
  simp only [not_lt]
  change ProbabilityTheory.expMeasure 1 (Set.Iic 0) = 0
  rw [← ProbabilityTheory.ofReal_cdf, ProbabilityTheory.cdf_expMeasure_eq zero_lt_one]
  norm_num

/-- Normalized independent exponentials have the Bayesian bootstrap law,
conditional on the general published gamma--Dirichlet theorem. -/
theorem exponentials_give_bayesian_bootstrap_conditional :
    AronowAudit.P037.exponentials_give_bayesian_bootstrap_conditional_statement := by
  intro hDev n
  let μ : Measure (Fin (n+2) → ℝ) :=
    Measure.pi (fun _ => ProbabilityTheory.expMeasure 1)
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  have hm (i : Fin (n+2)) :
      Measure.map (fun w : Fin (n+2) → ℝ => w i) μ =
        ProbabilityTheory.gammaMeasure 1 1 :=
    (measurePreserving_eval (fun _ : Fin (n+2) => ProbabilityTheory.expMeasure 1) i).map_eq
  have hind : ProbabilityTheory.iIndepFun (fun i (w : Fin (n+2) → ℝ) => w i) μ :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ : Fin (n+2) => id)
      (fun _ => measurable_id.aemeasurable)
  have hfree := (hDev (Fin (n+2) → ℝ) μ inferInstance (n+1) (Nat.succ_pos n)
    (fun _ => 1) (fun _ => zero_lt_one)).1
    (fun i w => w i) (fun i => measurable_pi_apply i) hind hm
  dsimp only at hfree
  have hpos : ∀ᵐ w ∂μ, ∀ i, 0 < w i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
    rw [hm i]
    exact CondP037P041_exponential_positive
  have hcomp :
      (fun w : Fin (n+2) → ℝ =>
        completeSimplex (n+1) (fun i => w i.castSucc / ∑ j, w j)) =ᵐ[μ]
      normalizeWeights := by
    filter_upwards [hpos] with w hw
    apply CondP037P041_completion_normalize
    exact ne_of_gt (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty)
  have hmeas : Measurable (fun w : Fin (n+2) → ℝ =>
      fun i : Fin (n+1) => w i.castSucc / ∑ j, w j) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply _).div
      (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
  change Measure.map normalizeWeights μ = _
  rw [← Measure.map_congr hcomp]
  have hmap := Measure.map_map (μ := μ)
    (CondP037P041_measurable_completion (n+1)) hmeas
  dsimp only [Function.comp_def] at hmap
  rw [← hmap]
  rw [hfree.1, CondP037P041_dirichlet_one]
  rfl

end AronowAudit.P037.Wave1
