import SAP.P037a.WH.W1.Leaves
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace SAP.P037a.WH.W1.P.T1_L2

open scoped BigOperators

noncomputable def predictionMap {B : ℕ} (w : Fin B → SAP.P037a.CompositionAssignment) :
    ((Fin B → ℝ) × (Fin 3 → ℝ)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin B × Fin 4) where
  toFun p := WithLp.toLp 2 (fun x : Fin B × Fin 4 => p.1 x.1 +
    ∑ k : Fin 3, SAP.P037a.regressionColumns (w x.1) k x.2 * p.2 k)
  map_add' p q := by
    ext x
    simp [Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm, add_comm]
  map_smul' c p := by
    ext x
    simp [Finset.mul_sum, mul_add, mul_assoc, mul_left_comm, mul_comm]

noncomputable def responseVector {B : ℕ} (w : Fin B → SAP.P037a.CompositionAssignment) :
    EuclideanSpace ℝ (Fin B × Fin 4) :=
  WithLp.toLp 2 (fun x : Fin B × Fin 4 => SAP.P037a.observedOutcome (w x.1) x.2)

lemma loss_eq_norm_sq {B : ℕ} (w : Fin B → SAP.P037a.CompositionAssignment)
    (alpha : Fin B → ℝ) (theta : Fin 3 → ℝ) :
    SAP.P037a.blockRegressionLoss w alpha theta =
      ‖responseVector w - predictionMap w (alpha, theta)‖ ^ 2 := by
  classical
  unfold SAP.P037a.blockRegressionLoss
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ b, ∑ i : Fin 4,
      (SAP.P037a.observedOutcome (w b) i - alpha b -
        ∑ k : Fin 3, SAP.P037a.regressionColumns (w b) k i * theta k) ^ 2) =
    ∑ x : Fin B × Fin 4,
      (SAP.P037a.observedOutcome (w x.1) x.2 -
        (alpha x.1 + ∑ k : Fin 3,
          SAP.P037a.regressionColumns (w x.1) k x.2 * theta k)) ^ 2
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SAP.P037a.WH.W1.P.T1_L2

theorem SAP.P037a.WH.W1.T1_L2_proof : SAP.P037a.WH.W1.T1_L2 := by
  classical
  intro B w
  let F := EuclideanSpace ℝ (Fin B × Fin 4)
  let L := SAP.P037a.WH.W1.P.T1_L2.predictionMap w
  let y : F := SAP.P037a.WH.W1.P.T1_L2.responseVector w
  let K : Submodule ℝ F := L.range
  have hcomplete : IsComplete (↑K : Set F) := by
    letI : FiniteDimensional ℝ F := inferInstance
    haveI : CompleteSpace K := inferInstance
    exact completeSpace_coe_iff_isComplete.mp inferInstance
  obtain ⟨v, hv, hmin⟩ := K.exists_norm_eq_iInf_of_complete_subspace hcomplete y
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hv
  refine ⟨p.1, p.2, ?_⟩
  intro alpha theta
  have hdist : ‖y - (v : F)‖ ≤ ‖y - L (alpha, theta)‖ := by
    let S : Set ℝ := Set.range (fun z : K => ‖y - (z : F)‖)
    have hS : BddBelow S := by
      refine ⟨0, ?_⟩
      rintro r ⟨z, rfl⟩
      exact norm_nonneg _
    calc
      ‖y - (v : F)‖ = ⨅ z : (K : Set F), ‖y - (z : F)‖ := hmin
      _ ≤ ‖y - L (alpha, theta)‖ :=
        ciInf_le hS
          ⟨L (alpha, theta), LinearMap.mem_range_self L (alpha, theta)⟩
  have hsq : ‖y - (v : F)‖ ^ 2 ≤ ‖y - L (alpha, theta)‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist
  change SAP.P037a.blockRegressionLoss w p.1 p.2 ≤
    SAP.P037a.blockRegressionLoss w alpha theta
  rw [SAP.P037a.WH.W1.P.T1_L2.loss_eq_norm_sq,
    SAP.P037a.WH.W1.P.T1_L2.loss_eq_norm_sq]
  change ‖y - L p‖ ^ 2 ≤ ‖y - L (alpha, theta)‖ ^ 2
  rw [hp]
  exact hsq
