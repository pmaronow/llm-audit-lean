import AronowAudit.P015.P015_PaperDomains
import AronowAudit.P015.P015_InverseLinkMLCounterexample
import AronowAudit.P015.P015_PositivityRefutation
namespace AronowAudit.P015.PaperAssessments
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
noncomputable section

/-- Mathematical clauses A-C of T17: the positivity correction and
its three concrete counterexamples. -/
theorem positivity_passage_assessment : PositivityCorrection := PositivityCorrection_checked

theorem positivity_implies_variance : PositivityCorrection := PositivityCorrection_checked

/-- A valid logistic ML score, an explicit refutation of arbitrary inverse-link
substitution, and a genuine ML first-order counterexample. These address the
three mathematical assertions in the printed nonlinear-extension passage. -/
theorem nonlinear_extension_assessment :
    (∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1)
    (θ : Fin (K+2) → ℝ)
    (hmax : ∀ γ, groupedLikelihood W (fun _ => 1) Y logistic γ ≤
      groupedLikelihood W (fun _ => 1) Y logistic θ),
groupedResidual W (fun _ => 1) Y logistic θ=0) ∧
    (¬(∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i,Y i=0 ∨ Y i=1) (hW : ∀ i,W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ→ℝ)
    (hm : DifferentiableOn ℝ m I) (hinverse : Function.Injective (I.restrict m))
    (hprob : ∀ η∈I,0<m η ∧ m η<1) (θ : Fin (K+2) → ℝ)
    (hθ : ∀ i,W.mulVec θ i∈I)
    (hML : ∀ γ : Fin (K+2) → ℝ, (∀ i,W.mulVec γ i∈I) →
      groupedLikelihood W (fun _=>1) Y m γ ≤ groupedLikelihood W (fun _=>1) Y m θ),
    groupedResidual W (fun _=>1) Y m θ=0)) ∧
    RootLinkCounterexample :=
  ⟨@PaperDomains.logistic_ML_score_zero,InverseLinkMLCounterexample.printed_inverse_link_claim_false,RootLinkCounterexample_checked⟩

theorem root_link_matrix_arithmetic : RootLinkCounterexample := RootLinkCounterexample_checked

theorem root_ols_arithmetic : RootLinkCounterexample := RootLinkCounterexample_checked

theorem root_uniform_is_probability : RootLinkCounterexample := RootLinkCounterexample_checked

theorem root_unit_is_probability : RootLinkCounterexample := RootLinkCounterexample_checked

theorem log99_lower_bound : TaylorCounterexample := TaylorCounterexample_checked

theorem logistic_power_series_radius : TaylorCounterexample := TaylorCounterexample_checked

theorem extreme_grouped_data_arithmetic : TaylorCounterexample := TaylorCounterexample_checked

theorem extreme_sigmoid_arithmetic : TaylorCounterexample := TaylorCounterexample_checked

theorem binomial_probability_unique_max : TaylorCounterexample := TaylorCounterexample_checked

theorem binomial_logistic_unique_max : TaylorCounterexample := TaylorCounterexample_checked

end
end AronowAudit.P015.PaperAssessments
