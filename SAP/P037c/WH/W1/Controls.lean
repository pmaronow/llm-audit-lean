import SAP.P037c.Defs.WholeW1
import SAP.P037c.Bridge
import AronowAudit.P037.P037_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.WH.W1
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem indicators_prediction (D : (Fin 4 × Fin 2) → Fin 4)
    (a : Fin 4 → ℝ) (i : Fin 4 × Fin 2) :
    (whole34Indicators D).mulVec a i = a (D i) := by
  simp [whole34Indicators, Matrix.mulVec, dotProduct]

/-- The collapsed sum is a constant, and hence is absorbed by the exposure indicators. -/
theorem sum_control_space (D : (Fin 4 × Fin 2) → Fin 4) :
    wholeColumnSpace (pooledExposureRow D whole34SumControl) =
      wholeColumnSpace (whole34Indicators D) := by
  apply le_antisymm
  · rintro v ⟨a,rfl⟩
    refine ⟨fun k => a (k.castAdd 1) + a 4 / 2, ?_⟩
    ext i
    change (whole34Indicators D).mulVec (fun k => a (k.castAdd 1) + a 4 / 2) i =
      (AronowAudit.P037.pooledExposureRow D (fun i j => whole34SumControl i j)).mulVec a i
    rw [indicators_prediction]
    rw [AronowAudit.P037.RegressionCompletion.pooled_prediction]
    norm_num [whole34SumControl, controlPi, Fin.sum_univ_succ]
    ring
  · rintro v ⟨a,rfl⟩
    refine ⟨![a 0,a 1,a 2,a 3,0], ?_⟩
    ext i
    change (AronowAudit.P037.pooledExposureRow D (fun i j => whole34SumControl i j)).mulVec
      ![a 0,a 1,a 2,a 3,0] i = (whole34Indicators D).mulVec a i
    rw [AronowAudit.P037.RegressionCompletion.pooled_prediction, indicators_prediction]
    generalize D i = k
    fin_cases k <;> norm_num [Fin.sum_univ_succ]

/-- Keeping both probability controls is equivalent to keeping pi(I) and the indicators. -/
theorem two_control_space (D : (Fin 4 × Fin 2) → Fin 4) :
    wholeColumnSpace (pooledExposureRow D whole34TwoControls) =
      wholeColumnSpace (controlFullRow D) := by
  apply le_antisymm
  · rintro v ⟨a,rfl⟩
    refine ⟨![a 0+a 5/2,a 1+a 5/2,a 2+a 5/2,a 3+a 5/2,a 4-a 5], ?_⟩
    ext i
    change (controlFullRow D).mulVec
      ![a 0+a 5/2,a 1+a 5/2,a 2+a 5/2,a 3+a 5/2,a 4-a 5] i =
      (AronowAudit.P037.pooledExposureRow D (fun i j => whole34TwoControls i j)).mulVec a i
    rw [Bridge.control_prediction]
    rw [AronowAudit.P037.RegressionCompletion.pooled_prediction]
    generalize D i = k
    fin_cases k <;> norm_num [whole34TwoControls, controlPi, Fin.sum_univ_succ] <;> ring
  · rintro v ⟨a,rfl⟩
    refine ⟨![a 0,a 1,a 2,a 3,a 4,0], ?_⟩
    ext i
    change (AronowAudit.P037.pooledExposureRow D (fun i j => whole34TwoControls i j)).mulVec
      ![a 0,a 1,a 2,a 3,a 4,0] i = (controlFullRow D).mulVec a i
    rw [AronowAudit.P037.RegressionCompletion.pooled_prediction, Bridge.control_prediction]
    generalize D i = k
    fin_cases k <;> norm_num [whole34TwoControls, controlPi, Fin.sum_univ_succ]

/-- The control sum spans a proper subspace of the two separate probability controls. -/
theorem strict_control_space :
    wholeColumnSpace whole34SumControl < wholeColumnSpace whole34TwoControls := by
  apply lt_iff_le_not_ge.mpr
  constructor
  · rintro v ⟨a,rfl⟩
    refine ⟨![a 0,a 0], ?_⟩
    ext i
    norm_num [whole34SumControl, whole34TwoControls, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · intro hle
    have hm : controlPiI ∈ wholeColumnSpace whole34TwoControls := by
      refine ⟨![1,0], ?_⟩
      ext i
      norm_num [whole34TwoControls, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rcases hle hm with ⟨a,ha⟩
    have h0 := congrFun ha (0,0)
    have h1 := congrFun ha (0,1)
    norm_num [Matrix.mulVecLin_apply, whole34SumControl, Matrix.mulVec, dotProduct,
      controlPi, controlPiI, pairReferentRate, Fin.sum_univ_succ] at h0 h1
    linarith

/-- The lost fitted control contribution is not constant within the observed I group. -/
theorem omitted_outside :
    (fun i => controlPiI i * controlPoint 4) ∉
      wholeColumnSpace (whole34Indicators controlObserved) := by
  rintro ⟨a,ha⟩
  change (whole34Indicators controlObserved).mulVec a = _ at ha
  have h0 := congrFun ha (0,0)
  have h1 := congrFun ha (1,0)
  rw [indicators_prediction] at h0 h1
  rw [Bridge.collapsed_certificate.2.2.2.2.2.2.1] at h0 h1
  norm_num [controlPiI, controlObserved, pairReferentRate] at h0 h1
  linarith

/-- The general reduced-control formula and its exact range obstruction. -/
theorem reduced_controls : Whole34Reduced := by
  intro n p q D C Cc w hw hH tau gamma r Hc Lc theta omitted
  have hleft : Lc * Hc = 1 :=
    AronowAudit.P037.RegressionCompletion.weighted_left_inverse w Hc hw hH
  have ht : Hc.mulVec theta = fun i => tau (D i) := by
    ext i
    change (AronowAudit.P037.pooledExposureRow D (fun i j => Cc i j)).mulVec theta i = _
    rw [AronowAudit.P037.RegressionCompletion.pooled_prediction]
    simp [theta, Fin.castAdd]
  constructor
  · have hi : (fun i => r i + tau (D i) + omitted i) = r + Hc.mulVec theta + omitted := by
      rw [ht]
      rfl
    rw [hi, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, hleft,
      Matrix.one_mulVec]
  · constructor
    · intro he
      exact ⟨Lc.mulVec omitted,he⟩
    · rintro ⟨v,hv⟩
      change Hc.mulVec v = omitted at hv
      rw [← hv]
      have he : Lc.mulVec (Hc.mulVec v) = v := by
        rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
      rw [he]

end SAP.P037c.WH.W1
