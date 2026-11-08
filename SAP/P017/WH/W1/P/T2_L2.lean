import SAP.P017.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace SAP.P017.WH.W1.P.T2_L2

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

theorem certificate : SAP.P017.WH.W1.T2_L2 := by
  intro Ω mΩ G hG τ hτm hτi t hl hu a ha ha1
  let L : Set Ω := {ω | τ ω < t}
  let U : Set Ω := {ω | t < τ ω}
  let pL : ℝ := pr G L
  let pU : ℝ := pr G U
  let cL : ℝ := a / pL
  let cU : ℝ := (1 - a) / pU
  let W : Ω → ℝ := twoRegionWeight G τ t a
  have hpL : 0 < pL := by simpa [pL, L] using hl
  have hpU : 0 < pU := by simpa [pU, U] using hu
  have hmL : MeasurableSet L := by
    exact measurableSet_lt hτm measurable_const
  have hmU : MeasurableSet U := by
    exact measurableSet_lt measurable_const hτm
  have hcL : 0 ≤ cL := (div_pos ha hpL).le
  have hcU : 0 ≤ cU := (div_pos (by linarith : 0 < 1 - a) hpU).le
  have hmeas : Measurable W := by
    change Measurable (fun ω =>
      cL * L.indicator (fun _ => (1 : ℝ)) ω +
        cU * U.indicator (fun _ => (1 : ℝ)) ω)
    exact (measurable_const.mul (measurable_const.indicator hmL)).add
      (measurable_const.mul (measurable_const.indicator hmU))
  have hconstL : Integrable (L.indicator (fun _ => (1 : ℝ))) G :=
    (integrable_const 1).indicator hmL
  have hconstU : Integrable (U.indicator (fun _ => (1 : ℝ))) G :=
    (integrable_const 1).indicator hmU
  have hwi : Integrable W G := by
    change Integrable (fun ω =>
      cL * L.indicator (fun _ => (1 : ℝ)) ω +
        cU * U.indicator (fun _ => (1 : ℝ)) ω) G
    exact (hconstL.const_mul cL).add (hconstU.const_mul cU)
  have hτL : Integrable (L.indicator τ) G := hτi.indicator hmL
  have hτU : Integrable (U.indicator τ) G := hτi.indicator hmU
  have hprod : (fun ω => W ω * τ ω) = fun ω =>
      cL * L.indicator τ ω + cU * U.indicator τ ω := by
    funext ω
    change (cL * L.indicator (fun _ => (1 : ℝ)) ω +
      cU * U.indicator (fun _ => (1 : ℝ)) ω) * τ ω =
        cL * L.indicator τ ω + cU * U.indicator τ ω
    simp only [Set.indicator]
    split_ifs <;> ring
  have hwτ : Integrable (fun ω => W ω * τ ω) G := by
    rw [hprod]
    exact (hτL.const_mul cL).add (hτU.const_mul cU)
  have hprobL : (∫ ω, L.indicator (fun _ => (1 : ℝ)) ω ∂G) = pL := by
    rw [integral_indicator_const (1 : ℝ) hmL]
    simp [pL, pr]
  have hprobU : (∫ ω, U.indicator (fun _ => (1 : ℝ)) ω ∂G) = pU := by
    rw [integral_indicator_const (1 : ℝ) hmU]
    simp [pU, pr]
  have hweight : (∫ ω, W ω ∂G) = 1 := by
    change (∫ ω, cL * L.indicator (fun _ => (1 : ℝ)) ω +
      cU * U.indicator (fun _ => (1 : ℝ)) ω ∂G) = 1
    rw [integral_add (hconstL.const_mul cL) (hconstU.const_mul cU),
      integral_const_mul, integral_const_mul, hprobL, hprobU]
    change cL * pL + cU * pU = 1
    dsimp [cL, cU]
    field_simp [hpL.ne', hpU.ne']
    ring
  have hmeanL : (∫ ω, L.indicator τ ω ∂G) =
      pL * lowerMean G τ t := by
    have hrealL : 0 < G.real {ω | τ ω < t} := by simpa [pr] using hl
    unfold lowerMean
    dsimp [pL, L, pr]
    field_simp [ne_of_gt hrealL]
  have hmeanU : (∫ ω, U.indicator τ ω ∂G) =
      pU * upperMean G τ t := by
    have hrealU : 0 < G.real {ω | t < τ ω} := by simpa [pr] using hu
    unfold upperMean
    dsimp [pU, U, pr]
    field_simp [ne_of_gt hrealU]
  have hmoment : (∫ ω, W ω * τ ω ∂G) =
      a * lowerMean G τ t + (1 - a) * upperMean G τ t := by
    rw [hprod, integral_add (hτL.const_mul cL) (hτU.const_mul cU),
      integral_const_mul, integral_const_mul, hmeanL, hmeanU]
    change cL * (pL * lowerMean G τ t) +
      cU * (pU * upperMean G τ t) =
        a * lowerMean G τ t + (1 - a) * upperMean G τ t
    dsimp [cL, cU]
    field_simp [hpL.ne', hpU.ne']
  have hvalue (ω : Ω) : W ω =
      (if ω ∈ L then cL else 0) + (if ω ∈ U then cU else 0) := by
    simp [W, twoRegionWeight, L, U, pL, pU, cL, cU, Set.indicator]
  have hbound : ∀ ω, 0 ≤ W ω ∧ W ω ≤
      a / pr G {ω | τ ω < t} + (1 - a) / pr G {ω | t < τ ω} := by
    intro ω
    change 0 ≤ W ω ∧ W ω ≤ cL + cU
    rw [hvalue ω]
    by_cases hLmem : ω ∈ L <;> by_cases hUmem : ω ∈ U
    · have hLt : τ ω < t := hLmem
      have hUt : t < τ ω := hUmem
      linarith
    · simp only [if_pos hLmem, if_neg hUmem]
      constructor
      · simpa using hcL
      · linarith
    · simp only [if_neg hLmem, if_pos hUmem]
      constructor
      · simpa using hcU
      · linarith
    · simp only [if_neg hLmem, if_neg hUmem]
      constructor
      · norm_num
      · linarith
  refine ⟨⟨hmeas, (fun ω => (hbound ω).1), hwi, ?_, hwτ⟩,
    hbound, hweight, ?_⟩
  · rw [hweight]
    norm_num
  · exact hmoment

end
end SAP.P017.WH.W1.P.T2_L2

theorem SAP.P017.WH.W1.T2_L2_proof : SAP.P017.WH.W1.T2_L2 :=
  SAP.P017.WH.W1.P.T2_L2.certificate
