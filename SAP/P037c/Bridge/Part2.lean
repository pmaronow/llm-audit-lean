import SAP.P037c.Defs
import AronowAudit.P037.P037_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.Bridge
open SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Same least-squares objective, design matrices, and inverse-form coefficient map. -/
theorem regressionMinimum_eq {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (Y : I → ℝ) (b : K → ℝ) :
    regressionMinimum w X Y b ↔ AronowAudit.P037.regressionMinimum w X Y b := Iff.rfl

theorem regressionMap_eq {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (w : I → ℝ) (X : Matrix I K ℝ) :
    regressionMap w X = AronowAudit.P037.regressionMap w X := rfl

theorem pooledExposureRow_eq {I : Type*} {p : ℕ} (D : I → Fin 4)
    (x : I → Fin p → ℝ) : pooledExposureRow D x = AronowAudit.P037.pooledExposureRow D x := rfl

theorem regression_means {I : Type*} [Fintype I] : RegressionMeanIdentities I :=
  @AronowAudit.P037.pooled_and_separate_mean_identities I _

theorem one_covariate {I : Type*} [Fintype I] : OneCovariateFormulas I :=
  @AronowAudit.P037.one_covariate_regression_formulas I _

/-- Rearrange the finite average into the usual coefficient-plus-covariate-mean form. -/
theorem prediction_mean {I : Type*} [Fintype I] : PredictionMeanIdentity I := by
  intro p hI α β x k
  have hc : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hs : (∑ i, ∑ j, x i j*β j) = ∑ j, (∑ i, x i j)*β j := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hs, add_div, mul_div_cancel_left₀ _ hc]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem regression12_design : Regression12DesignCertificate :=
  AronowAudit.P037.regression12_hierarchical_design

theorem regression12_normal : Regression12NormalCertificate :=
  AronowAudit.P037.regression12_normal_certificates

theorem regression12_fit : Regression12FitCertificate := by
  have h := AronowAudit.P037.separate_pooled_regression_counterexample
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem same_controls {Ω : Type*} [Fintype Ω] : SameControlCertificate Ω :=
  @AronowAudit.P037.same_controls_residual_imputation Ω _

/-- Expand the same fitted rows and apply the already proved constant-shift variance identity. -/
theorem same_controls_extra {Ω : Type*} [Fintype Ω] : SameControlExtra Ω := by
  intro n p hn D0 D C w0 w hw0 hw hX0 hX y prob hp ht
  intro b0 row m residual imputed L
  have h := same_controls hn D0 D C w0 w hw0 hw hX0 hX y prob hp ht
  change (∀ k l, m k-m l=b0 (k.castAdd p)-b0 (l.castAdd p)) ∧
    (∀ z, (L z*pooledExposureRow (D z) C)=1 ∧
      (L z).mulVec (imputed z)=(L z).mulVec residual+b0) ∧
    (∀ z k, dotProduct (row k) ((L z).mulVec (imputed z))=
      dotProduct (row k) ((L z).mulVec residual)+m k) ∧ _ at h
  have hi (z : Ω) (i : Fin n) :
      imputed z i=y i-b0 ((D0 i).castAdd p)+b0 ((D z i).castAdd p) := by
    dsimp only [imputed]
    linarith [h.1 (D z i) (D0 i)]
  refine ⟨hi, ?_, ?_⟩
  · intro z
    ext i
    rw [hi]
    change _=y i-(AronowAudit.P037.pooledExposureRow D0 (fun i j => C i j)).mulVec b0 i+
      (AronowAudit.P037.pooledExposureRow (D z) (fun i j => C i j)).mulVec b0 i
    rw [AronowAudit.P037.RegressionCompletion.pooled_prediction,
      AronowAudit.P037.RegressionCompletion.pooled_prediction]
    ring
  · intro k
    dsimp only
    simp_rw [h.2.2.1]
    exact AronowAudit.P037.RegressionCompletion.finite_variance_add_const prob _ ht (m k)

end SAP.P037c.Bridge
