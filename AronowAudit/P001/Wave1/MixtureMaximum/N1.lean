import AronowAudit.P001.Wave1.MixtureMaximumBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MixtureMaximum

open AronowAudit.P001
open scoped BigOperators

noncomputable section

theorem n1_proof : N1 := by
  intro σ hσ
  have hc : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hnormal (m y : ℝ) (s : ℝ) (hs : 0 < s) : 0 ≤ normalDensity m s y := by
    unfold normalDensity
    exact div_nonneg (Real.exp_pos _).le (mul_pos hs hc).le
  have hlog (y : ℝ) : 0 ≤ lognormalDensity 0 1 y := by
    unfold lognormalDensity
    split_ifs with hy
    · exact div_nonneg (hnormal 0 (Real.log y) 1 (by norm_num)) hy.le
    · exact le_rfl
  have hexp (y : ℝ) : 0 ≤ exponentialDensity 1 y := by
    unfold exponentialDensity
    split_ifs <;> positivity
  have hdensity (y : ℝ) : mixtureDensity (collapse σ) y =
      (1/2 : ℝ) * normalDensity 1 σ y +
      (1/4 : ℝ) * lognormalDensity 0 1 y +
      (1/4 : ℝ) * exponentialDensity 1 y := by
    norm_num [mixtureDensity, collapse]
  have hn1 : normalDensity 1 σ 1 = 1 / (σ * Real.sqrt (2 * Real.pi)) := by
    simp [normalDensity]
  have he2 : exponentialDensity 1 2 = Real.exp (-2) := by
    norm_num [exponentialDensity]
  have he3 : exponentialDensity 1 3 = Real.exp (-3) := by
    norm_num [exponentialDensity]
  have h1 : (1/2 : ℝ) / (σ * Real.sqrt (2 * Real.pi)) ≤
      mixtureDensity (collapse σ) 1 := by
    rw [hdensity, hn1]
    have := hlog 1
    have := hexp 1
    have e : (1/2 : ℝ) / (σ * Real.sqrt (2 * Real.pi)) =
        1/2 * (1 / (σ * Real.sqrt (2 * Real.pi))) := by ring
    linarith
  have h2 : Real.exp (-2) / 4 ≤ mixtureDensity (collapse σ) 2 := by
    rw [hdensity, he2]
    have := hnormal 1 2 σ hσ
    have := hlog 2
    linarith
  have h3 : Real.exp (-3) / 4 ≤ mixtureDensity (collapse σ) 3 := by
    rw [hdensity, he3]
    have := hnormal 1 3 σ hσ
    have := hlog 3
    linarith
  have hlow1 : 0 ≤ (1/2 : ℝ) / (σ * Real.sqrt (2 * Real.pi)) := by positivity
  have hlow2 : 0 ≤ Real.exp (-2) / 4 := by positivity
  have hlow3 : 0 ≤ Real.exp (-3) / 4 := by positivity
  have hprod := mul_le_mul (mul_le_mul h1 h2 hlow2 (hlow1.trans h1)) h3
    hlow3 (mul_nonneg (hlow1.trans h1) (hlow2.trans h2))
  have hexps : Real.exp (-5 : ℝ) = Real.exp (-2) * Real.exp (-3) := by
    rw [← Real.exp_add]
    norm_num
  have hconst : lowerConst / σ =
      ((1/2 : ℝ) / (σ * Real.sqrt (2 * Real.pi))) *
        (Real.exp (-2) / 4) * (Real.exp (-3) / 4) := by
    unfold lowerConst
    rw [hexps]
    field_simp [hσ.ne', hc.ne']
    <;> ring
  refine ⟨?_, ?_⟩
  · norm_num [MixtureAdmissible, collapse, hσ]
  · rw [hconst]
    simpa [mixtureLikelihood, Fin.prod_univ_three, sample] using hprod

end

end AronowAudit.P001.Wave1.MixtureMaximum
