import AronowAudit.P004.Wave1.DesignLimits.DL7
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Real.Sqrt

/-!
Normal approximation by fixed-radius arrays. The radius is chosen only after
the CDF tolerance, and the eventual sample-size bound is then taken for that
single radius. No uniform-in-radius sample-size threshold is assumed.
-/

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

namespace DLbSupport

/-- The squared-error probability bound, directly from finite expectation. -/
theorem prob_sq_tail_le {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (U : Assignment N → ℝ) (ε : ℝ) (hε : 0 < ε) :
    prob p (fun z => ε < |U z|) ≤ expect p (fun z => (U z)^2) / ε^2 := by
  classical
  have hden : 0 < ε^2 := sq_pos_of_pos hε
  calc
    prob p (fun z => ε < |U z|) ≤ expect p (fun z => (U z)^2 / ε^2) := by
      apply expect_mono p hp
      intro z
      by_cases hz : ε < |U z|
      · rw [if_pos hz]
        apply (le_div_iff₀ hden).mpr
        have hs : ε^2 ≤ |U z|^2 := (sq_le_sq₀ hε.le (abs_nonneg _)).mpr hz.le
        simpa only [one_mul, sq_abs] using hs
      · rw [if_neg hz]
        exact div_nonneg (sq_nonneg _) hden.le
    _ = expect p (fun z => (U z)^2) / ε^2 := expect_div p _ _

end DLbSupport

/-- The standard-normal limit passes from fixed-radius L² approximants. -/
theorem dl6_proof : DL6 := by
  classical
  intro p hp T Tr η hη hTr herror x
  have herrlim (ε : ℝ) :
      Tendsto (fun r => (η r)^2 / ε^2) atTop (nhds (0 : ℝ)) := by
    simpa using (hη.pow 2).div_const (ε^2)
  have hsand (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ N in atTop,
        prob (p N) (fun z => Tr r N z ≤ x - ε) - (η r)^2 / ε^2 ≤
            prob (p N) (fun z => T N z ≤ x) ∧
        prob (p N) (fun z => T N z ≤ x) ≤
            prob (p N) (fun z => Tr r N z ≤ x + ε) + (η r)^2 / ε^2 := by
    filter_upwards [herror r] with N hN
    change Real.sqrt (expect (p N) (fun z => (T N z - Tr r N z)^2)) ≤ η r at hN
    have hmoment : expect (p N) (fun z => (T N z - Tr r N z)^2) ≤ (η r)^2 :=
      (Real.sqrt_le_iff.mp hN).2
    have htail : prob (p N) (fun z => ε < |T N z - Tr r N z|) ≤
        (η r)^2 / ε^2 := by
      calc
        _ ≤ expect (p N) (fun z => (T N z - Tr r N z)^2) / ε^2 :=
          DLbSupport.prob_sq_tail_le (p N) (hp N) _ ε hε
        _ ≤ (η r)^2 / ε^2 := div_le_div_of_nonneg_right hmoment (sq_nonneg ε)
    have hlo : prob (p N) (fun z => Tr r N z ≤ x - ε) ≤
        prob (p N) (fun z => T N z ≤ x) +
          prob (p N) (fun z => ε < |T N z - Tr r N z|) := by
      apply DLbSupport.prob_le_add (p N) (hp N)
      intro z hz
      by_cases hbad : ε < |T N z - Tr r N z|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        linarith
    have hhi : prob (p N) (fun z => T N z ≤ x) ≤
        prob (p N) (fun z => Tr r N z ≤ x + ε) +
          prob (p N) (fun z => ε < |T N z - Tr r N z|) := by
      apply DLbSupport.prob_le_add (p N) (hp N)
      intro z hz
      by_cases hbad : ε < |T N z - Tr r N z|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        linarith
    constructor <;> linarith
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨y, hy, hby⟩ := DLbSupport.cdf_left x b hb
    let ε : ℝ := x - y
    have hε : 0 < ε := sub_pos.mpr hy
    have hcut : x - ε = y := by dsimp [ε]; ring
    have hr_event : ∀ᶠ r in atTop,
        (η r)^2 / ε^2 < (normalCDF y - b) / 2 :=
      (tendsto_order.mp (herrlim ε)).2 _ (by linarith)
    obtain ⟨r, hr⟩ := hr_event.exists
    have hgap : b < normalCDF y - (η r)^2 / ε^2 := by linarith
    have hlim : Tendsto
        (fun N => prob (p N) (fun z => Tr r N z ≤ y) - (η r)^2 / ε^2)
        atTop (nhds (normalCDF y - (η r)^2 / ε^2)) :=
      (hTr r y).sub tendsto_const_nhds
    filter_upwards [hsand r ε hε, (tendsto_order.mp hlim).1 b hgap]
      with N hbounds hclose
    have hlower : prob (p N) (fun z => Tr r N z ≤ y) - (η r)^2 / ε^2 ≤
        prob (p N) (fun z => T N z ≤ x) := by
      simpa only [hcut] using hbounds.1
    exact lt_of_lt_of_le hclose hlower
  · intro b hb
    obtain ⟨y, hy, hyb⟩ := DLbSupport.cdf_right x b hb
    let ε : ℝ := y - x
    have hε : 0 < ε := sub_pos.mpr hy
    have hcut : x + ε = y := by dsimp [ε]; ring
    have hr_event : ∀ᶠ r in atTop,
        (η r)^2 / ε^2 < (b - normalCDF y) / 2 :=
      (tendsto_order.mp (herrlim ε)).2 _ (by linarith)
    obtain ⟨r, hr⟩ := hr_event.exists
    have hgap : normalCDF y + (η r)^2 / ε^2 < b := by linarith
    have hlim : Tendsto
        (fun N => prob (p N) (fun z => Tr r N z ≤ y) + (η r)^2 / ε^2)
        atTop (nhds (normalCDF y + (η r)^2 / ε^2)) :=
      (hTr r y).add tendsto_const_nhds
    filter_upwards [hsand r ε hε, (tendsto_order.mp hlim).2 b hgap]
      with N hbounds hclose
    have hupper : prob (p N) (fun z => T N z ≤ x) ≤
        prob (p N) (fun z => Tr r N z ≤ y) + (η r)^2 / ε^2 := by
      simpa only [hcut] using hbounds.2
    exact lt_of_le_of_lt hupper hclose

end
end AronowAudit.P004.Wave1.DesignLimits
