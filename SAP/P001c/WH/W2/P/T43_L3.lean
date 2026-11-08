import SAP.P001c.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter AronowAudit.P001
open scoped Classical

theorem SAP.P001c.WH.W2.T43_L3_proof : SAP.P001c.WH.W2.T43_L3 := by
  intro Ω hΩ μ hμ X Y hX hY hvar
  let mX : ℝ := expectation μ X
  let mY : ℝ := expectation μ Y
  have hXconst : X =ᵐ[μ] fun _ => mX := by
    change X =ᵐ[μ] fun _ => expectation μ X
    exact ae_eq_integral_of_variance_eq_zero hX hvar
  refine ⟨?_, ?_, ?_⟩
  · simpa [mX] using hXconst
  · intro g h hg hh hgm
    have hgconst : (g ∘ X) =ᵐ[μ] fun _ => g mX := by
      filter_upwards [hXconst] with z hz
      simp [Function.comp_apply, hz]
    have hhconst : (h ∘ X) =ᵐ[μ] fun _ => h mX := by
      filter_upwards [hXconst] with z hz
      simp [Function.comp_apply, hz]
    have hgrisk : (fun z => (Y z - g (X z)) ^ 2) =ᵐ[μ]
        fun z => (Y z - g mX) ^ 2 := by
      filter_upwards [hgconst] with z hz
      simpa [Function.comp_apply] using congrArg (fun t : ℝ => (Y z - t) ^ 2) hz
    have hhrisk : (fun z => (Y z - h (X z)) ^ 2) =ᵐ[μ]
        fun z => (Y z - h mX) ^ 2 := by
      filter_upwards [hhconst] with z hz
      simpa [Function.comp_apply] using congrArg (fun t : ℝ => (Y z - t) ^ 2) hz
    have hmse := AronowAudit.P001.mse_general_identity_and_unique_minimum μ Y hY
    have hgm' : g mX = mY := by simpa [mX, mY] using hgm
    constructor
    · calc
        expectation μ (fun z => (Y z - g (X z)) ^ 2) = mse μ Y (g mX) := by
          change (∫ z, (Y z - g (X z)) ^ 2 ∂μ) = ∫ z, (Y z - g mX) ^ 2 ∂μ
          exact integral_congr_ae hgrisk
        _ = variance Y μ := by
          rw [hgm']
          simpa [mY, AronowAudit.P001.mean, AronowAudit.P001.var, expectation] using hmse.1 mY
    · calc
        expectation μ (fun z => (Y z - g (X z)) ^ 2) = mse μ Y (g mX) := by
          change (∫ z, (Y z - g (X z)) ^ 2 ∂μ) = ∫ z, (Y z - g mX) ^ 2 ∂μ
          exact integral_congr_ae hgrisk
        _ = mse μ Y (mean μ Y) := by simp [hgm', mY, AronowAudit.P001.mean, expectation]
        _ ≤ mse μ Y (h mX) := (hmse.2 (h mX)).1
        _ = expectation μ (fun z => (Y z - h (X z)) ^ 2) := by
          change (∫ z, (Y z - h mX) ^ 2 ∂μ) = ∫ z, (Y z - h (X z)) ^ 2 ∂μ
          exact (integral_congr_ae hhrisk).symm
  · intro a b
    let c : ℝ := a + b * mX
    let R : Ω → ℝ := fun z => Y z - (a + b * X z)
    have hRconst : R =ᵐ[μ] fun z => Y z - c := by
      filter_upwards [hXconst] with z hz
      simp [R, c, hz]
    have hRmem : MemLp R 2 μ := by
      apply (memLp_congr_ae hRconst).mpr
      have hs : MemLp (Y - fun _ : Ω => c) 2 μ := by
        exact hY.sub (memLp_const c)
      have heq : (Y - fun _ : Ω => c) =ᵐ[μ] fun z => Y z - c :=
        Filter.Eventually.of_forall (fun _ => rfl)
      exact (memLp_congr_ae heq).mp hs
    have hRiskAffine : affineRisk μ X Y a b = mse μ Y c := by
      change (∫ z, (Y z - a - b * X z) ^ 2 ∂μ) = ∫ z, (Y z - c) ^ 2 ∂μ
      apply integral_congr_ae
      filter_upwards [hXconst] with z hz
      rw [hz]
      dsimp [c]
      ring
    have hmse := AronowAudit.P001.mse_general_identity_and_unique_minimum μ Y hY
    have hmeanMse : mse μ Y mY = variance Y μ := by
      have hh := hmse.1 mY
      simpa [mY, AronowAudit.P001.mean, AronowAudit.P001.var, expectation] using hh
    constructor
    · rw [hRiskAffine, ← hmeanMse]
      simpa [c, mX, mY, expectation, AronowAudit.P001.mean] using (hmse.2 c).2
    · intro hline
      have hEq : c = mY := by
        simpa [c, mX, mY] using hline
      have hMeanR : expectation μ R = 0 := by
        calc
          expectation μ R = ∫ z, Y z - c ∂μ := integral_congr_ae hRconst
          _ = expectation μ Y - c := by
            rw [integral_sub (hY.integrable one_le_two) (integrable_const c)]
            simp [expectation, integral_const]
          _ = 0 := by
            rw [show expectation μ Y = mY by rfl, hEq]
            simp
      have hProd : (fun z => X z * R z) =ᵐ[μ]
          fun z => mX * (Y z - c) := by
        filter_upwards [hXconst, hRconst] with z hx hr
        simp [hx, hr]
      have hProdZero : expectation μ (fun z => X z * R z) = 0 := by
        calc
          expectation μ (fun z => X z * R z) = ∫ z, mX * (Y z - c) ∂μ :=
            integral_congr_ae hProd
          _ = mX * (expectation μ Y - c) := by
            rw [integral_const_mul, integral_sub (hY.integrable one_le_two)
              (integrable_const c)]
            simp [expectation, integral_const]
          _ = 0 := by
            rw [show expectation μ Y = mY by rfl, hEq]
            simp
      refine ⟨hMeanR, hProdZero, ?_⟩
      have hCov := covariance_eq_sub hX hRmem
      have hCov' : covariance X R μ =
          expectation μ (fun z => X z * R z) - expectation μ X * expectation μ R := by
        simpa [AronowAudit.P001.mean, SAP.P001c.expectation] using hCov
      rw [hCov', hProdZero, hMeanR]
      simp
