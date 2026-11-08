import SAP.P027b.Defs
import AronowAudit.P027.P027_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b.Bridge
noncomputable section
open scoped BigOperators

variable {U Ω : Type} [Fintype U] [Fintype Ω]

/-- The adapter preserves the probability weights and selected subsets verbatim. -/
def toProject (D : Design U Ω) : AronowAudit.P027.Design U Ω where
  weight := D.weight
  nonneg := D.nonneg
  total := D.total
  selected := D.selected

theorem expect_eq (D : Design U Ω) (f : Ω → ℝ) :
    expect D f = AronowAudit.P027.expect (toProject D) f := rfl

theorem indicator_eq (D : Design U Ω) (ω : Ω) (k : U) :
    indicator D ω k = AronowAudit.P027.indicator (toProject D) ω k := rfl

theorem pi_eq (D : Design U Ω) (k : U) :
    pi D k = AronowAudit.P027.pi (toProject D) k := rfl

theorem joint_eq (D : Design U Ω) (k l : U) :
    joint D k l = AronowAudit.P027.joint (toProject D) k l := rfl

theorem positive_eq (D : Design U Ω) : Positive D = AronowAudit.P027.Positive (toProject D) := rfl

theorem variance_eq (D : Design U Ω) (f : Ω → ℝ) :
    variance D f = AronowAudit.P027.variance (toProject D) f := rfl

theorem htTotal_eq (D : Design U Ω) (y : U → ℝ) :
    htTotal D y = AronowAudit.P027.htTotal (toProject D) y := rfl

theorem htMean_eq (D : Design U Ω) (y : U → ℝ) :
    htMean D y = AronowAudit.P027.htMean (toProject D) y := rfl

theorem htVarianceEstimator_eq (D : Design U Ω) (y : U → ℝ) :
    htVarianceEstimator D y = AronowAudit.P027.htVarianceEstimator (toProject D) y := rfl

theorem biasA_eq (D : Design U Ω) (y : U → ℝ) :
    biasA D y = AronowAudit.P027.biasA (toProject D) y := rfl

theorem youngA_eq (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ) :
    youngA D y a b = AronowAudit.P027.youngA (toProject D) y a b := rfl

theorem youngCorrection_eq (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ) :
    youngCorrection D y a b = AronowAudit.P027.youngCorrection (toProject D) y a b := rfl

theorem conservativeEstimator_eq (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ) :
    conservativeEstimator D y a b = AronowAudit.P027.conservativeEstimator (toProject D) y a b := rfl

theorem c2Estimator_eq (D : Design U Ω) (y : U → ℝ) :
    c2Estimator D y = AronowAudit.P027.c2Estimator (toProject D) y := rfl

theorem wrEstimator_eq (D : Design U Ω) (y : U → ℝ) (m : ℕ) :
    wrEstimator D y m = AronowAudit.P027.wrEstimator (toProject D) y m := rfl

theorem strataDesign_eq (M : ℕ) (hM : 0 < M) :
    toProject (strataDesign M hM) = AronowAudit.P027.strataDesign M hM := rfl

theorem pairLaw_eq : toProject pairLaw = AronowAudit.P027.pairLaw := rfl

theorem cluster3_eq : toProject cluster3 = AronowAudit.P027.cluster3 := rfl

theorem T14_proof : T14Statement := by
  have h := AronowAudit.P027.strata5_counterexample
  change
    variance (strataDesign 5 (by norm_num)) (htMean (strataDesign 5 (by norm_num)) (fixedStrata5 0)) = 1/2 ∧
    variance (strataDesign 5 (by norm_num)) (htMean (strataDesign 5 (by norm_num)) (fixedStrata5 2)) = 1/2 ∧
    expect (strataDesign 5 (by norm_num)) (fun ω => htVarianceEstimator (strataDesign 5 (by norm_num)) (fixedStrata5 0) ω/100) = 2/5 ∧
    expect (strataDesign 5 (by norm_num)) (fun ω => c2Estimator (strataDesign 5 (by norm_num)) (fixedStrata5 0) ω/100) = 4/5 ∧
    expect (strataDesign 5 (by norm_num)) (collapsedEstimator (fixedStrata5 0)) = 1/2 ∧
    expect (strataDesign 5 (by norm_num)) (fun ω => htVarianceEstimator (strataDesign 5 (by norm_num)) (fixedStrata5 2) ω/100) = 2 ∧
    expect (strataDesign 5 (by norm_num)) (fun ω => c2Estimator (strataDesign 5 (by norm_num)) (fixedStrata5 2) ω/100) = 4 ∧
    expect (strataDesign 5 (by norm_num)) (collapsedEstimator (fixedStrata5 2)) = 9/2 at h
  rcases h with ⟨v0,v2,h0,c0,s0,h2,c2,s2⟩
  dsimp only [T14Statement]
  refine ⟨v0,v2,h0,c0,s0,h2,c2,s2,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [v0,v2,c0,s0,c2,s2] <;> norm_num

theorem T16_proof : T16Statement := by
  exact AronowAudit.P027.icc_counterexample

theorem T18_proof : T18Statement := by
  constructor
  · intro M hM
    have h := AronowAudit.P027.strata_inclusion_correction M hM
    refine ⟨h.1,h.2.1,h.2.2,?_⟩
    intro k
    let D := strataDesign M hM
    have hv : variance D (fun ω => indicator D ω k) =
        expect D (fun ω => (indicator D ω k)^2)-(pi D k)^2 :=
      AronowAudit.P027.variance_second_moment (toProject D) (fun ω => indicator D ω k)
    have hsq : expect D (fun ω => (indicator D ω k)^2) = pi D k := by
      have hj : joint D k k = pi D k := AronowAudit.P027.joint_self (toProject D) k
      simpa only [joint,pow_two] using hj
    rw [hv,hsq,show pi D k = 1/(M:ℝ) from h.1 k]
    ring
  · have h := AronowAudit.P027.strata_joint_value 2 (by norm_num)
      ((0:Fin 2),(0:Fin 2)) (0,0)
    have hSap : joint (strataDesign 2 (by norm_num)) ((0:Fin 2),(0:Fin 2)) (0,0) =
        if ((0:Fin 2),(0:Fin 2)) = (0,0) then 1/(2:ℝ) else
          if (0:Fin 2) = 0 then 0 else 1/(2:ℝ)^2 := h
    simpa using hSap

theorem T20_proof : T20Statement := by
  constructor
  · intro U Ω _ _ D hD y
    have hp : expect D (htVarianceEstimator D y) = variance D (htTotal D y) + biasA D y :=
      AronowAudit.P027.proposition1 (toProject D) hD y
    refine ⟨hp,?_⟩
    intro hs
    have hb : 0 ≤ biasA D y := AronowAudit.P027.biasA_same_sign (toProject D) hD y hs
    exact ⟨hb, by linarith⟩
  · have hp := AronowAudit.P027.aggregation_counterexample_positive
    have hm := AronowAudit.P027.aggregation_counterexample_mixed
    have hD : Positive cluster3 := hp.1
    have hbPos : biasA cluster3 allOnes3 = 4 := hp.2.2.2.2.2.1
    have hbNeg : biasA cluster3 mixed3 = -1 := hm.2.2.1
    have hePos : expect cluster3 (htVarianceEstimator cluster3 allOnes3) =
        variance cluster3 (htTotal cluster3 allOnes3) + biasA cluster3 allOnes3 :=
      AronowAudit.P027.proposition1 (toProject cluster3) hD allOnes3
    have heNeg : expect cluster3 (htVarianceEstimator cluster3 mixed3) =
        variance cluster3 (htTotal cluster3 mixed3) + biasA cluster3 mixed3 :=
      AronowAudit.P027.proposition1 (toProject cluster3) hD mixed3
    refine ⟨cluster3, allOnes3, mixed3, hD, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem T21_proof : T21Statement := by
  intro U Ω _ _ D hD y a b hab
  have hy := AronowAudit.P027.young_bounds (toProject D) hD y a b hab
  exact ⟨hy.1, hy.2, AronowAudit.P027.expected_young_correction (toProject D) hD y a b hab,
    AronowAudit.P027.conservative_expectation (toProject D) hD y a b hab,
    AronowAudit.P027.proposition2 (toProject D) hD y a b hab⟩

theorem T22_proof : T22Statement := by
  intro U Ω _ _ D hD y a b hab heq hopp
  exact AronowAudit.P027.corollary1 (toProject D) hD y a b hab heq hopp

theorem T23_proof : T23Statement := by
  intro U Ω _ _ D hD y
  exact ⟨AronowAudit.P027.c2_is_young_two (toProject D) y,
    AronowAudit.P027.corollary2 (toProject D) hD y⟩

theorem T24_proof : T24Statement := by
  intro U Ω _ _ D hD y ω
  exact AronowAudit.P027.corollary3 (toProject D) hD y ω

end
end SAP.P027b.Bridge
