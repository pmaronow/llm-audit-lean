import SAP.P001f.WH.W2.Leaves
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

namespace SAP.P001f.WH.W2.P.T113_L3

end SAP.P001f.WH.W2.P.T113_L3

theorem SAP.P001f.WH.W2.T113_L3_proof : SAP.P001f.WH.W2.T113_L3 := by
  intro Ω mΩ μ hμ G hG M W B hM hW hB hWcond hS
  let U : Ω → ℝ := fun ω => 1 - W ω
  let T : Ω → ℝ := M * U
  have hU : Integrable U μ := by
    dsimp [U]
    exact (integrable_const (1 : ℝ)).sub hW
  have hScore : Integrable (fun ω => B ω + T ω) μ := by
    simpa [T, U, Pi.mul_apply] using hS
  have hT : Integrable T μ := by
    have hsub : Integrable (fun ω => (B ω + T ω) - B ω) μ := hScore.sub hB
    have heq : (fun ω => (B ω + T ω) - B ω) = T := by
      funext ω
      dsimp [T, U]
      ring
    rw [heq] at hsub
    exact hsub
  have hUce : μ[U | G] =ᵐ[μ] (fun _ => 0) := by
    have hsub := condExp_sub (integrable_const (1 : ℝ)) hW G
    have hUeq : U =ᵐ[μ] ((fun _ : Ω => (1 : ℝ)) - W) := by
      filter_upwards with ω
      rfl
    calc
      μ[U | G] =ᵐ[μ] μ[(fun _ : Ω => (1 : ℝ)) - W | G] := condExp_congr_ae hUeq
      _ =ᵐ[μ] μ[(fun _ : Ω => (1 : ℝ)) | G] - μ[W | G] := hsub
      _ =ᵐ[μ] (fun _ => 0) := by
        filter_upwards [hWcond] with ω hw
        have hc : μ[(fun _ : Ω => (1 : ℝ)) | G] ω = 1 :=
          congrFun (condExp_const hG (1 : ℝ)) ω
        change μ[(fun _ : Ω => (1 : ℝ)) | G] ω - μ[W | G] ω = 0
        rw [hc, hw]
        norm_num
  have hTce : μ[T | G] =ᵐ[μ] (fun _ => 0) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left hM hT hU
    calc
      μ[T | G] =ᵐ[μ] M * μ[U | G] := by
        simpa only [T] using hpull
      _ =ᵐ[μ] (fun _ => 0) := by
        filter_upwards [hUce] with ω hω
        simp [hω]
  have hTint : (∫ ω, T ω ∂μ) = 0 := by
    calc
      (∫ ω, T ω ∂μ) = ∫ ω, μ[T | G] ω ∂μ := (integral_condExp hG).symm
      _ = 0 := by
        rw [integral_congr_ae hTce]
        simp
  calc
    (∫ ω, B ω + M ω * (1 - W ω) ∂μ) =
        (∫ ω, B ω ∂μ) + (∫ ω, T ω ∂μ) := by
      simpa [T, U, Pi.mul_apply] using (integral_add hB hT)
    _ = ∫ ω, B ω ∂μ := by rw [hTint, add_zero]
