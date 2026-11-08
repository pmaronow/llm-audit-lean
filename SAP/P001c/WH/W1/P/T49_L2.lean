import SAP.P001c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W1.P.T49_L2

open MeasureTheory

lemma expectation_sq_sub_mul_expand {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R D : Ω → ℝ)
    (hR : MemLp R 2 μ) (hD : MemLp D 2 μ) (t : ℝ) :
    SAP.P001c.expectation μ (fun ω => (R ω - t * D ω)^2) =
      SAP.P001c.expectation μ (fun ω => R ω^2) -
        (2 * t) * SAP.P001c.expectation μ (fun ω => D ω * R ω) +
        t^2 * SAP.P001c.expectation μ (fun ω => D ω^2) := by
  have hR2 : Integrable (fun ω => R ω^2) μ := hR.integrable_sq
  have hD2 : Integrable (fun ω => D ω^2) μ := hD.integrable_sq
  have hDR : Integrable (fun ω => D ω * R ω) μ := hD.integrable_mul hR
  unfold SAP.P001c.expectation
  calc
    (∫ ω, (R ω - t * D ω)^2 ∂μ) =
        ∫ ω, (R ω^2 - (2 * t) * (D ω * R ω) + t^2 * D ω^2) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by ring
    _ = (∫ ω, R ω^2 ∂μ) -
          (2 * t) * (∫ ω, D ω * R ω ∂μ) +
          t^2 * (∫ ω, D ω^2 ∂μ) := by
      calc
        (∫ ω, R ω^2 - (2 * t) * (D ω * R ω) + t^2 * D ω^2 ∂μ) =
            (∫ ω, R ω^2 - (2 * t) * (D ω * R ω) ∂μ) +
              ∫ ω, t^2 * D ω^2 ∂μ :=
          integral_add (hR2.sub (hDR.const_mul (2 * t))) (hD2.const_mul (t^2))
        _ = ((∫ ω, R ω^2 ∂μ) - ∫ ω, (2 * t) * (D ω * R ω) ∂μ) +
              ∫ ω, t^2 * D ω^2 ∂μ := by
          rw [integral_sub hR2 (hDR.const_mul (2 * t))]
        _ = (∫ ω, R ω^2 ∂μ) -
              (2 * t) * (∫ ω, D ω * R ω ∂μ) +
              t^2 * (∫ ω, D ω^2 ∂μ) := by
          rw [integral_const_mul (2 * t), integral_const_mul (t^2)]

end SAP.P001c.WH.W1.P.T49_L2

theorem SAP.P001c.WH.W1.T49_L2_proof : SAP.P001c.WH.W1.T49_L2 := by
  intro Ω hΩ μ hμ R D hR hD hmin
  let a : ℝ := SAP.P001c.expectation μ (fun ω => R ω^2)
  let b : ℝ := SAP.P001c.expectation μ (fun ω => D ω * R ω)
  let c : ℝ := SAP.P001c.expectation μ (fun ω => D ω^2)
  let q : ℝ → ℝ := fun t => SAP.P001c.expectation μ (fun ω => (R ω - t * D ω)^2)
  have hq (t : ℝ) : q t = a - 2 * t * b + t^2 * c := by
    simpa [q, a, b, c] using
      SAP.P001c.WH.W1.P.T49_L2.expectation_sq_sub_mul_expand μ R D hR hD t
  have hglobal : IsLocalMin q 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simpa [q] using hmin t
  have hmul : HasDerivAt (fun t : ℝ => 2 * t * b) (2 * b) 0 := by
    simpa using (hasDerivAt_const_mul (2 : ℝ)).mul_const b
  have hlinear : HasDerivAt (fun t : ℝ => a - 2 * t * b) (-2 * b) 0 := by
    convert (hasDerivAt_const 0 a).sub hmul using 1
    simp
  have hsquare : HasDerivAt (fun t : ℝ => t^2 * c) 0 0 := by
    convert ((hasDerivAt_id 0).pow 2).mul_const c using 1 <;> simp
  have hpoly : HasDerivAt (fun t : ℝ => a - 2 * t * b + t^2 * c) (-2 * b) 0 := by
    convert hlinear.add hsquare using 1
    simp
  have hqderiv : HasDerivAt q (-2 * b) 0 := by
    rw [show q = (fun t => a - 2 * t * b + t^2 * c) from funext hq]
    exact hpoly
  have hderiv_zero : -2 * b = 0 := hglobal.hasDerivAt_eq_zero hqderiv
  have hb : b = 0 := by nlinarith
  simpa [b] using hb
