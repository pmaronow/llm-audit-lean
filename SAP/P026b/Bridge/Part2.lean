import SAP.P026b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b.Bridge
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

/-- The closed numerical designs retain every allocation and weight. -/
theorem tableDesign_eq : toDesign tableDesign = AronowAudit.P026.tableDesign := rfl
theorem realTableDesign_eq : toDesign realTableDesign = AronowAudit.P026.realTableDesign := rfl
theorem oneOfThree_eq : toDesign oneOfThree = AronowAudit.P026.oneOfThree := rfl
theorem packageFit_eq : packageFit = AronowAudit.P026.packageFit := rfl
theorem logitCoefficients_eq : logitCoefficients = AronowAudit.P026.logitCoefficients := rfl
theorem logitResidual_eq : tableLogitResidual = AronowAudit.P026.tableLogitResidual := rfl
theorem realAsymmetricTwo_eq : toDesign realAsymmetricTwo =
    AronowAudit.P026.Refutations.realAsymmetricTwo := rfl
theorem realXorThree_eq : toDesign realXorThree = AronowAudit.P026.Refutations.realXorThree := rfl

/-- Expand the square and use the exported finite-expectation identities. -/
theorem mse_of_unbiased {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ) (hD : probabilityDesign D) (f : Ω → ℝ) (c : ℝ)
    (hc : expectation D f = c) :
    expectation D (fun w => (f w-c)^2) = variance D f := by
  have hpoly : (fun w => (f w-c)^2) = (fun w => f w*f w-f w*(2*c)+c*c) := by
    funext w
    ring
  change AronowAudit.P026.expectation (toDesign D) (fun w => (f w-c)^2) =
    AronowAudit.P026.variance (toDesign D) f
  rw [hpoly, AronowAudit.P026.expectation_add, AronowAudit.P026.expectation_sub,
    AronowAudit.P026.expectation_mul_const, AronowAudit.P026.expectation_const (toDesign D) hD]
  change expectation D (fun w => f w*f w) - expectation D f*(2*c)+c*c =
    expectation D (fun w => f w*f w) - expectation D f*expectation D f
  rw [hc]
  ring

/-- Rounding and the two RMSE equalities are arithmetic on the exported moments. -/
theorem logit_column_glue (h : logitCoreFacts) :
    (∀ j, roundsTo (logitColumn j) (correctedLogitColumn j)) ∧
    (∀ j : Fin 10, j ∈ ({3,4,5,6,8,9} : Finset (Fin 10)) →
      ¬ roundsTo (logitColumn j) (printedLogitColumn j)) := by
  rcases h with ⟨_, _, _, _, _, _, hm, hslo, hshi, hvlo, hvhi, he, htlo, hthi⟩
  have hp : probabilityDesign realTableDesign := AronowAudit.P026.LogitCompletion.real_table_probability
  have hΔ : ate 16 (fun i : Fin 16 => (tableY i : ℝ)) (fun i => (tableY i : ℝ)) = 0 := by
    simp only [ate, sub_self, zero_div]
  have hms := mse_of_unbiased realTableDesign hp logitEstimate 0 hm
  have hmv := mse_of_unbiased realTableDesign hp logitVarianceEstimate
    (variance realTableDesign logitEstimate) he
  have hcol : logitColumn =
      ![0,0,0,Real.sqrt (variance realTableDesign logitEstimate),
        Real.sqrt (variance realTableDesign logitEstimate),
        variance realTableDesign logitEstimate, variance realTableDesign logitEstimate,0,
        Real.sqrt (variance realTableDesign logitVarianceEstimate),
        Real.sqrt (variance realTableDesign logitVarianceEstimate)] := by
    simp only [logitColumn, hΔ, hm, he, sub_self, hms, hmv]
  constructor
  · intro j
    rw [hcol]
    fin_cases j <;> norm_num [correctedLogitColumn, roundsTo] <;> constructor <;> linarith
  · intro j hj hh
    rw [hcol] at hh
    fin_cases j <;> norm_num at hj
    all_goals
      rcases hh with ⟨ha, hb⟩
      norm_num [printedLogitColumn] at ha hb
      linarith

/-- Instantiate the existing inverse-Gram OLS theorem and evaluate its 2 by 2 matrix. -/
theorem package_fit_eq_projection (w : Fin 3) :
    olsFitted 2 (designWithIntercept 1 (fun (i : Fin 3) (_ : Fin 1) => (i.val : ℝ)))
      (fun i => ((observed oneOfThree (fun _ => 1) (fun _ => 0) w i : ℚ) : ℝ)) =
        (fun i => (packageFit w i : ℝ)) := by
  let V : Matrix (Fin 3) (Fin 2) ℝ :=
    designWithIntercept 1 (fun (i : Fin 3) (_ : Fin 1) => (i.val : ℝ))
  have hV : V = !![1,0;1,1;1,2] := by
    ext i j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [V, designWithIntercept, Fin.cases_zero]
      fin_cases i <;> norm_num
    · simp only [V, designWithIntercept, Fin.cases_succ]
      fin_cases k
      fin_cases i <;> norm_num
  have hG : V.transpose * V = !![3,3;3,5] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hV, Matrix.mul_apply, Fin.sum_univ_succ]
  have hd : (V.transpose * V).det ≠ 0 := by rw [hG]; norm_num [Matrix.det_fin_two]
  have h := AronowAudit.P026.Wave1.olsFitted_eq_inverse 2 V hd
    (fun i => ((observed oneOfThree (fun _ => 1) (fun _ => 0) w i : ℚ) : ℝ))
  change olsFitted 2 V _ = _
  rw [← Bridge.olsFitted_eq, h, hG]
  ext i
  fin_cases w <;> fin_cases i <;>
    norm_num [hV, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.cases, Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
      packageFit, observed, oneOfThree]


end
end SAP.P026b.Bridge
