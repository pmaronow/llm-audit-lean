import SAP.P001c.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2.P.T43_L1

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology Classical ContDiff

universe u
noncomputable section

private theorem risk_form {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    SAP.P001c.affineRisk μ X Y a b =
      variance Y μ - 2*b*covariance X Y μ + b^2*variance X μ +
        (expectation μ Y-a-b*expectation μ X)^2 := by
  simpa [SAP.P001c.affineRisk, SAP.P001c.expectation, AronowAudit.P001.linearRisk,
    AronowAudit.P001.mean, AronowAudit.P001.var] using
      (AronowAudit.P001.linearRisk_mean_covariance_form μ X Y hX hY a b)

private theorem residual_mean {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    expectation μ (fun z => Y z-a-b*X z) =
      expectation μ Y-a-b*expectation μ X := by
  have hYi : Integrable Y μ := hY.integrable one_le_two
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hBX : Integrable (fun z => b*X z) μ := hXi.const_mul b
  have hYa : Integrable (fun z => Y z-a) μ := hYi.sub (integrable_const a)
  unfold SAP.P001c.expectation
  rw [show (fun z => Y z-a-b*X z) = (fun z => (Y z-a)-b*X z) by
    funext z; ring]
  rw [integral_sub hYa hBX, integral_sub hYi (integrable_const a), integral_const_mul]
  simp

private theorem residual_cross {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    expectation μ (fun z => (Y z-a-b*X z)*X z) =
      covariance X Y μ-b*variance X μ+
        expectation μ X*(expectation μ Y-a-b*expectation μ X) := by
  have hYi : Integrable Y μ := hY.integrable one_le_two
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hYX : Integrable (fun z => Y z*X z) μ := hY.integrable_mul hX
  have hAX : Integrable (fun z => a*X z) μ := hXi.const_mul a
  have hBXsq : Integrable (fun z => b*(X z)^2) μ := hX.integrable_sq.const_mul b
  have hfun : (fun z => (Y z-a-b*X z)*X z) =
      (fun z => (Y z*X z-a*X z)-b*(X z)^2) := by
    funext z
    ring
  rw [hfun]
  unfold SAP.P001c.expectation
  change (∫ z, ((fun z => Y z*X z)-(fun z => a*X z)) z -
      (fun z => b*(X z)^2) z ∂μ) = _
  rw [integral_sub (hYX.sub hAX) hBXsq]
  change (∫ z, Y z*X z-a*X z ∂μ) - (∫ z, b*(X z)^2 ∂μ) = _
  rw [integral_sub hYX hAX, integral_const_mul, integral_const_mul]
  change expectation μ (fun z => Y z*X z)-a*expectation μ X-
      b*expectation μ (fun z => (X z)^2) = _
  have hCov : expectation μ (fun z => Y z*X z) =
      covariance X Y μ+expectation μ Y*expectation μ X := by
    have hc := covariance_eq_sub hY hX
    rw [covariance_comm Y X] at hc
    change covariance X Y μ = expectation μ (fun z => Y z*X z)-
      expectation μ Y*expectation μ X at hc
    linarith
  have hVar : expectation μ (fun z => (X z)^2) =
      variance X μ+(expectation μ X)^2 := by
    have hv := variance_eq_sub hX
    change variance X μ = expectation μ (fun z => (X z)^2)-
      (expectation μ X)^2 at hv
    linarith
  rw [hCov, hVar]
  simp only [SAP.P001c.expectation]
  ring

private theorem second_moment {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) :
    expectation μ (fun z => (X z)^2) = variance X μ+(expectation μ X)^2 := by
  have hv := variance_eq_sub hX
  change variance X μ = expectation μ (fun z => (X z)^2)-(expectation μ X)^2 at hv
  linarith

private theorem first_a {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    HasDerivAt (fun t => SAP.P001c.affineRisk μ X Y t b)
      (-2*expectation μ (fun z => Y z-a-b*X z)) a := by
  let mX := expectation μ X
  let mY := expectation μ Y
  let vX := variance X μ
  let vY := variance Y μ
  let cXY := covariance X Y μ
  have hpoly : (fun t : ℝ => SAP.P001c.affineRisk μ X Y t b) =
      (fun t => vY-2*b*cXY+b^2*vX+(mY-t-b*mX)^2) := by
    funext t
    simpa [mX, mY, vX, vY, cXY] using risk_form μ X Y hX hY t b
  have hlin : HasDerivAt (fun t : ℝ => mY-t-b*mX) (-1) a := by
    convert ((hasDerivAt_const a mY).sub (hasDerivAt_id a)).sub
      (hasDerivAt_const a (b*mX)) using 1
    ext t
    simp only [Pi.sub_apply, id_eq]
    ring
  have hd : HasDerivAt
      (fun t : ℝ => vY-2*b*cXY+b^2*vX+(mY-t-b*mX)^2)
      (-2*(mY-a-b*mX)) a := by
    convert (hasDerivAt_const a (vY-2*b*cXY+b^2*vX)).add (hlin.pow 2) using 1
    all_goals ring
  have hval : -2*(mY-a-b*mX) =
      -2*expectation μ (fun z => Y z-a-b*X z) := by
    rw [residual_mean μ X Y hX hY a b]
  exact (hd.congr_deriv hval).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hpoly t)

private theorem first_b {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    HasDerivAt (fun t => SAP.P001c.affineRisk μ X Y a t)
      (-2*expectation μ (fun z => (Y z-a-b*X z)*X z)) b := by
  let mX := expectation μ X
  let mY := expectation μ Y
  let vX := variance X μ
  let vY := variance Y μ
  let cXY := covariance X Y μ
  have hpoly : (fun t : ℝ => SAP.P001c.affineRisk μ X Y a t) =
      (fun t => vY-2*t*cXY+t^2*vX+(mY-a-t*mX)^2) := by
    funext t
    simpa [mX, mY, vX, vY, cXY] using risk_form μ X Y hX hY a t
  have hl := ((hasDerivAt_id b).const_mul (-2*cXY)).const_add vY
  have hq := ((hasDerivAt_id b).pow 2).mul_const vX
  have hb := ((hasDerivAt_const b (mY-a)).sub
    ((hasDerivAt_id b).mul_const mX)).pow 2
  have hd := (hl.add hq).add hb
  have hpoly' : HasDerivAt
      (fun t : ℝ => vY-2*t*cXY+t^2*vX+(mY-a-t*mX)^2)
      (-2*cXY+2*b*vX-2*mX*(mY-a-b*mX)) b := by
    convert hd using 1
    · ext t
      dsimp [id_eq]
      ring
    · simp only [id_eq]
      dsimp [Pi.sub_apply]
      norm_num
      ring
  have hval : -2*cXY+2*b*vX-2*mX*(mY-a-b*mX) =
      -2*expectation μ (fun z => (Y z-a-b*X z)*X z) := by
    rw [residual_cross μ X Y hX hY a b]
    simp [mX, mY, vX, cXY]
    ring
  exact (hpoly'.congr_deriv hval).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hpoly t)

end
end SAP.P001c.WH.W2.P.T43_L1

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology Classical ContDiff
open SAP.P001c.WH.W2.P.T43_L1

theorem SAP.P001c.WH.W2.T43_L1_proof : SAP.P001c.WH.W2.T43_L1 := by
  intro Ω hΩ μ hμ X Y hX hY
  letI := hΩ
  letI := hμ
  let mX := expectation μ X
  let mY := expectation μ Y
  let vX := variance X μ
  let vY := variance Y μ
  let cXY := covariance X Y μ
  have hform (a b : ℝ) : SAP.P001c.affineRisk μ X Y a b =
      vY-2*b*cXY+b^2*vX+(mY-a-b*mX)^2 := by
    simpa [mX, mY, vX, vY, cXY] using risk_form μ X Y hX hY a b
  have hsmooth : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => SAP.P001c.affineRisk μ X Y p.1 p.2) := by
    have hpoly : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => vY-2*p.2*cXY+p.2^2*vX+(mY-p.1-p.2*mX)^2) := by
      fun_prop
    have heq : (fun p : ℝ × ℝ => SAP.P001c.affineRisk μ X Y p.1 p.2) =
        (fun p => vY-2*p.2*cXY+p.2^2*vX+(mY-p.1-p.2*mX)^2) := by
      funext p
      exact hform p.1 p.2
    rw [heq]
    exact hpoly
  have hpartials : ∀ a b : ℝ,
      HasDerivAt (fun t => SAP.P001c.affineRisk μ X Y t b)
        (-2*expectation μ (fun z => Y z-a-b*X z)) a ∧
      HasDerivAt (fun t => SAP.P001c.affineRisk μ X Y a t)
        (-2*expectation μ (fun z => (Y z-a-b*X z)*X z)) b ∧
      HasDerivAt (fun t => deriv (fun u => SAP.P001c.affineRisk μ X Y u b) t) 2 a ∧
      HasDerivAt (fun t => deriv (fun u => SAP.P001c.affineRisk μ X Y a u) t)
        (2*expectation μ (fun z => (X z)^2)) b ∧
      HasDerivAt (fun t => deriv (fun u => SAP.P001c.affineRisk μ X Y u t) a)
        (2*expectation μ X) b ∧
      HasDerivAt (fun t => deriv (fun u => SAP.P001c.affineRisk μ X Y t u) b)
        (2*expectation μ X) a := by
    intro a b
    have ha := first_a μ X Y hX hY a b
    have hb := first_b μ X Y hX hY a b
    have hasec (t : ℝ) : deriv (fun u => SAP.P001c.affineRisk μ X Y u b) t =
        -2*(mY-t-b*mX) := by
      rw [(first_a μ X Y hX hY t b).deriv]
      rw [residual_mean μ X Y hX hY t b]
    have hbsec (t : ℝ) : deriv (fun u => SAP.P001c.affineRisk μ X Y a u) t =
        -2*cXY+2*t*vX-2*mX*(mY-a-t*mX) := by
      rw [(first_b μ X Y hX hY a t).deriv]
      rw [residual_cross μ X Y hX hY a t]
      ring
    have hmixab (t : ℝ) : deriv (fun u => SAP.P001c.affineRisk μ X Y u t) a =
        -2*(mY-a-t*mX) := by
      rw [(first_a μ X Y hX hY a t).deriv]
      rw [residual_mean μ X Y hX hY a t]
    have hmixba (t : ℝ) : deriv (fun u => SAP.P001c.affineRisk μ X Y t u) b =
        -2*cXY+2*b*vX-2*mX*(mY-t-b*mX) := by
      rw [(first_b μ X Y hX hY t b).deriv]
      rw [residual_cross μ X Y hX hY t b]
      ring
    refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
    · have hsec : (fun t : ℝ => deriv (fun u => SAP.P001c.affineRisk μ X Y u b) t) =
          (fun t => -2*(mY-t-b*mX)) := by funext t; exact hasec t
      rw [hsec]
      convert ((hasDerivAt_const a (-2*(mY-b*mX))).add
        ((hasDerivAt_id a).const_mul 2)) using 1 <;>
        all_goals try ext t
      all_goals try dsimp [id_eq]
      all_goals ring
    · have hsec : (fun t : ℝ => deriv (fun u => SAP.P001c.affineRisk μ X Y a u) t) =
          (fun t => -2*cXY+2*t*vX-2*mX*(mY-a-t*mX)) := by funext t; exact hbsec t
      have hmoment := second_moment μ X hX
      rw [hsec]
      have hlin := (hasDerivAt_const b (mY-a)).sub
        ((hasDerivAt_id b).const_mul mX)
      have hcalc : HasDerivAt
          (fun t : ℝ => -2*cXY+2*t*vX-2*mX*(mY-a-t*mX))
          (2*vX+2*mX^2) b := by
        convert ((hasDerivAt_const b (-2*cXY)).add
          ((hasDerivAt_id b).const_mul (2*vX))).sub (hlin.const_mul (2*mX)) using 1
        all_goals try ext t
        all_goals try dsimp [id_eq]
        all_goals ring
      have hval : 2*vX+2*mX^2 = 2*expectation μ (fun z => (X z)^2) := by
        rw [hmoment]
        simp [mX, vX]
        ring
      exact hcalc.congr_deriv hval
    · have hsec : (fun t : ℝ => deriv (fun u => SAP.P001c.affineRisk μ X Y u t) a) =
          (fun t => -2*(mY-a-t*mX)) := by funext t; exact hmixab t
      rw [hsec]
      convert ((hasDerivAt_const b (-2*(mY-a))).add
        ((hasDerivAt_id b).const_mul (2*mX))) using 1
      all_goals try ext t
      all_goals try dsimp [id_eq]
      all_goals ring
    · have hsec : (fun t : ℝ => deriv (fun u => SAP.P001c.affineRisk μ X Y t u) b) =
          (fun t => -2*cXY+2*b*vX-2*mX*(mY-t-b*mX)) := by funext t; exact hmixba t
      rw [hsec]
      convert ((hasDerivAt_const a (-2*cXY+2*b*vX-2*mX*(mY-b*mX))).add
        ((hasDerivAt_id a).const_mul (2*mX))) using 1
      all_goals try ext t
      all_goals try dsimp [id_eq]
      all_goals ring
  have hdet : 2*(2*expectation μ (fun z => (X z)^2))-
      (2*expectation μ X)^2 = 4*variance X μ := by
    rw [second_moment μ X hX]
    ring
  exact ⟨hsmooth, hpartials, hdet⟩

