import SAP.P017.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017.WH.W1.P.T2_L1

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

end
end SAP.P017.WH.W1.P.T2_L1

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal NNReal Classical

theorem SAP.P017.WH.W1.T2_L1_proof : SAP.P017.WH.W1.T2_L1 := by
  intro Ω mΩ G hG τ hτm hτi t hl hu
  let L : Set Ω := {ω | τ ω < t}
  let U : Set Ω := {ω | t < τ ω}
  have hmL : MeasurableSet L := measurableSet_lt hτm measurable_const
  have hmU : MeasurableSet U := measurableSet_lt measurable_const hτm
  let fL : Ω → ℝ := L.indicator (fun ω => t - τ ω)
  let fU : Ω → ℝ := U.indicator (fun ω => τ ω - t)
  have hiL : Integrable fL G := ((integrable_const t).sub hτi).indicator hmL
  have hiU : Integrable fU G := (hτi.sub (integrable_const t)).indicator hmU
  have hnL : 0 ≤ fL := by
    intro ω
    by_cases hω : τ ω < t
    · simp [fL, L, hω]
      linarith
    · simp [fL, L, hω]
  have hnU : 0 ≤ fU := by
    intro ω
    by_cases hω : t < τ ω
    · simp [fU, U, hω]
      linarith
    · simp [fU, U, hω]
  have hsL : Function.support fL = L := by
    ext ω
    by_cases hω : τ ω < t
    · simp [Function.support, fL, L, hω, sub_ne_zero.mpr hω.ne']
    · simp [Function.support, fL, L, hω]
  have hsU : Function.support fU = U := by
    ext ω
    by_cases hω : t < τ ω
    · simp [Function.support, fU, U, hω, sub_ne_zero.mpr hω.ne']
    · simp [Function.support, fU, U, hω]
  have hlL : 0 < pr G L := by simpa [L] using hl
  have huU : 0 < pr G U := by simpa [U] using hu
  have hposL : 0 < ∫ ω, fL ω ∂G := by
    apply (integral_pos_iff_support_of_nonneg hnL hiL).mpr
    rw [hsL]
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hlL.ne')
  have hposU : 0 < ∫ ω, fU ω ∂G := by
    apply (integral_pos_iff_support_of_nonneg hnU hiU).mpr
    rw [hsU]
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp huU.ne')
  have hLfun : fL = L.indicator (fun _ : Ω => t) - L.indicator τ := by
    funext ω
    by_cases hω : τ ω < t <;> simp [fL, L, hω] <;> ring
  have hUfun : fU = U.indicator τ - U.indicator (fun _ : Ω => t) := by
    funext ω
    by_cases hω : t < τ ω <;> simp [fU, U, hω] <;> ring
  have hLexpr : (∫ ω, fL ω ∂G) = t * pr G L - (∫ ω, L.indicator τ ω ∂G) := by
    calc
      (∫ ω, fL ω ∂G) = ∫ ω, L.indicator (fun _ : Ω => t) ω - L.indicator τ ω ∂G := by
        simp only [hLfun, Pi.sub_apply]
      _ = (∫ ω, L.indicator (fun _ : Ω => t) ω ∂G) - ∫ ω, L.indicator τ ω ∂G := by
        exact integral_sub ((integrable_const t).indicator hmL) (hτi.indicator hmL)
      _ = t * pr G L - ∫ ω, L.indicator τ ω ∂G := by
        rw [integral_indicator_const t hmL]
        simp only [smul_eq_mul, pr]
        ring
  have hUexpr : (∫ ω, fU ω ∂G) = (∫ ω, U.indicator τ ω ∂G) - t * pr G U := by
    calc
      (∫ ω, fU ω ∂G) = ∫ ω, U.indicator τ ω - U.indicator (fun _ : Ω => t) ω ∂G := by
        simp only [hUfun, Pi.sub_apply]
      _ = (∫ ω, U.indicator τ ω ∂G) - ∫ ω, U.indicator (fun _ : Ω => t) ω ∂G := by
        exact integral_sub (hτi.indicator hmU) ((integrable_const t).indicator hmU)
      _ = (∫ ω, U.indicator τ ω ∂G) - t * pr G U := by
        rw [integral_indicator_const t hmU]
        simp only [smul_eq_mul, pr]
        ring
  constructor
  · dsimp [SAP.P017.lowerMean]
    apply (div_lt_iff₀ hl).2
    have := hposL
    rw [hLexpr] at this
    linarith
  · dsimp [SAP.P017.upperMean]
    apply (lt_div_iff₀ hu).2
    have := hposU
    rw [hUexpr] at this
    linarith
