import AronowAudit.P004.Wave1.DesignLimits.DL7
import Mathlib.Analysis.Real.Sqrt

/-!
Coverage with a random radius converging in probability to a positive constant.
Continuous mapping applies to the square-root radius, followed by a fixed-radius
event sandwich. The argument requires neither joint convergence nor independence
of the numerator and the radius.
-/

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

namespace DLbSupport

theorem normalCDF_mono : Monotone normalCDF := by
  intro a b hab
  simpa only [normalCDF_eq_cdf] using
    (ProbabilityTheory.monotone_cdf (μ := ProbabilityTheory.gaussianReal 0 1) hab)

/-- Closed intervals are a difference of a weak upper CDF and a strict lower
CDF, even when the finite design distribution has atoms at an endpoint. -/
theorem prob_closed_interval {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    prob p (fun z => a ≤ X z ∧ X z ≤ b) =
      prob p (fun z => X z ≤ b) - prob p (fun z => X z < a) := by
  classical
  unfold prob
  rw [← expect_sub]
  apply congrArg (expect p)
  funext z
  by_cases hlo : X z < a
  · have hnot : ¬ a ≤ X z := not_le.mpr hlo
    have hhi : X z ≤ b := le_trans hlo.le hab
    simp [hlo, hnot, hhi]
  · have ha : a ≤ X z := le_of_not_gt hlo
    by_cases hhi : X z ≤ b <;> simp [hlo, ha, hhi]

/-- Fixed symmetric closed intervals have their usual normal limiting mass. -/
theorem normalLimit_abs (p : ∀ N, Fin N → ℝ) (hp : AdmissibleSeq p)
    (Z : ∀ N, Assignment N → ℝ) (hZ : NormalLimit p Z) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun N => prob (p N) (fun z => |Z N z| ≤ r)) atTop
      (nhds (2 * normalCDF r - 1)) := by
  classical
  have hid (N : ℕ) :
      prob (p N) (fun z => |Z N z| ≤ r) =
        prob (p N) (fun z => Z N z ≤ r) - prob (p N) (fun z => Z N z < -r) := by
    calc
      _ = prob (p N) (fun z => -r ≤ Z N z ∧ Z N z ≤ r) :=
        prob_congr (p N) _ _ (fun z => abs_le)
      _ = _ := prob_closed_interval (p N) (Z N) (-r) r (by linarith)
  have hlim : Tendsto
      (fun N => prob (p N) (fun z => Z N z ≤ r) -
        prob (p N) (fun z => Z N z < -r))
      atTop (nhds (normalCDF r - normalCDF (-r))) :=
    (hZ r).sub (normalLimit_lt p hp Z hZ (-r))
  have he : normalCDF r - normalCDF (-r) = 2 * normalCDF r - 1 := by
    rw [normalCDF_neg]
    ring
  rw [he] at hlim
  exact Filter.Tendsto.congr (fun N => (hid N).symm) hlim

end DLbSupport

/-- The limiting coverage of a CLT statistic with a consistent random radius. -/
theorem dl8_proof : DL8 := by
  classical
  intro p hp T W σ w c hσ hw hc hT hW
  let Z : ∀ N, Assignment N → ℝ := fun N z => T N z / σ
  let R : ∀ N, Assignment N → ℝ := fun N z => c * Real.sqrt (W N z) / σ
  let r₀ : ℝ := c * Real.sqrt w / σ
  have hZ : NormalLimit p Z := hT
  have hr₀ : 0 < r₀ := div_pos (mul_pos hc (Real.sqrt_pos.mpr hw)) hσ
  have hR : InProb p (fun N z => R N z - r₀) := by
    have hF : ContinuousAt
        (fun v : Fin 1 → ℝ => c * Real.sqrt (v 0) / σ) (fun _ => w) := by
      have hproj : Continuous (fun v : Fin 1 → ℝ => v 0) := continuous_apply 0
      have hroot : Continuous (fun v : Fin 1 → ℝ => Real.sqrt (v 0)) :=
        Real.continuous_sqrt.comp hproj
      have hscaled : Continuous (fun v : Fin 1 → ℝ => c * Real.sqrt (v 0)) :=
        continuous_const.mul hroot
      have hcont : Continuous (fun v : Fin 1 → ℝ => c * Real.sqrt (v 0) / σ) :=
        hscaled.div_const σ
      exact hcont.continuousAt
    exact dl9_proof p hp (m := 1) (fun _ N z => W N z) (fun _ => w)
      (fun v => c * Real.sqrt (v 0) / σ) hF (fun _ => hW)
  have hsand (ε : ℝ) (N : ℕ) :
      prob (p N) (fun z => |Z N z| ≤ r₀ - ε) -
          prob (p N) (fun z => ε < |R N z - r₀|) ≤
            prob (p N) (fun z => |Z N z| ≤ R N z) ∧
      prob (p N) (fun z => |Z N z| ≤ R N z) ≤
        prob (p N) (fun z => |Z N z| ≤ r₀ + ε) +
          prob (p N) (fun z => ε < |R N z - r₀|) := by
    have hlo : prob (p N) (fun z => |Z N z| ≤ r₀ - ε) ≤
        prob (p N) (fun z => |Z N z| ≤ R N z) +
          prob (p N) (fun z => ε < |R N z - r₀|) := by
      apply DLbSupport.prob_le_add (p N) (hp N)
      intro z hz
      by_cases hbad : ε < |R N z - r₀|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        linarith
    have hhi : prob (p N) (fun z => |Z N z| ≤ R N z) ≤
        prob (p N) (fun z => |Z N z| ≤ r₀ + ε) +
          prob (p N) (fun z => ε < |R N z - r₀|) := by
      apply DLbSupport.prob_le_add (p N) (hp N)
      intro z hz
      by_cases hbad : ε < |R N z - r₀|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        linarith
    constructor <;> linarith
  have hcov : Tendsto (fun N => prob (p N) (fun z => |Z N z| ≤ R N z))
      atTop (nhds (2 * normalCDF r₀ - 1)) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have hb' : (b + 1) / 2 < normalCDF r₀ := by linarith
      obtain ⟨y, hy, hby⟩ := DLbSupport.cdf_left r₀ ((b + 1) / 2) hb'
      -- Taking the maximum with zero keeps the lower fixed radius admissible.
      let l : ℝ := max y 0
      have hl0 : 0 ≤ l := le_max_right y 0
      have hlr : l < r₀ := max_lt_iff.mpr ⟨hy, hr₀⟩
      have hyl : normalCDF y ≤ normalCDF l :=
        DLbSupport.normalCDF_mono (le_max_left y 0)
      have hgap : b < 2 * normalCDF l - 1 := by linarith
      let ε : ℝ := r₀ - l
      have hε : 0 < ε := sub_pos.mpr hlr
      have hcut : r₀ - ε = l := by dsimp [ε]; ring
      have hfixed := DLbSupport.normalLimit_abs p hp Z hZ l hl0
      have hlim : Tendsto
          (fun N => prob (p N) (fun z => |Z N z| ≤ l) -
            prob (p N) (fun z => ε < |R N z - r₀|))
          atTop (nhds (2 * normalCDF l - 1)) := by
        simpa only [sub_zero] using hfixed.sub (hR ε hε)
      filter_upwards [(tendsto_order.mp hlim).1 b hgap] with N hclose
      have hlower := (hsand ε N).1
      rw [hcut] at hlower
      exact lt_of_lt_of_le hclose hlower
    · intro b hb
      have hb' : normalCDF r₀ < (b + 1) / 2 := by linarith
      obtain ⟨y, hy, hyb⟩ := DLbSupport.cdf_right r₀ ((b + 1) / 2) hb'
      have hy0 : 0 ≤ y := (lt_trans hr₀ hy).le
      have hgap : 2 * normalCDF y - 1 < b := by linarith
      let ε : ℝ := y - r₀
      have hε : 0 < ε := sub_pos.mpr hy
      have hcut : r₀ + ε = y := by dsimp [ε]; ring
      have hfixed := DLbSupport.normalLimit_abs p hp Z hZ y hy0
      have hlim : Tendsto
          (fun N => prob (p N) (fun z => |Z N z| ≤ y) +
            prob (p N) (fun z => ε < |R N z - r₀|))
          atTop (nhds (2 * normalCDF y - 1)) := by
        simpa only [add_zero] using hfixed.add (hR ε hε)
      filter_upwards [(tendsto_order.mp hlim).2 b hgap] with N hclose
      have hupper := (hsand ε N).2
      rw [hcut] at hupper
      exact lt_of_le_of_lt hupper hclose
  have heq (N : ℕ) :
      prob (p N) (fun z => |Z N z| ≤ R N z) =
        prob (p N) (fun z => |T N z| ≤ c * Real.sqrt (W N z)) := by
    apply DLbSupport.prob_congr
    intro z
    dsimp only [Z, R]
    rw [abs_div, abs_of_pos hσ]
    exact div_le_div_iff_of_pos_right hσ
  exact Filter.Tendsto.congr heq hcov

end
end AronowAudit.P004.Wave1.DesignLimits
