import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.DesignLimits.DL8
import AronowAudit.P004.Wave1.DesignLimits.NF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T1_L6

open MeasureTheory ProbabilityTheory Filter Set
open AronowAudit.P004
open scoped BigOperators Classical

theorem normalLimit_lt_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ)
    (hp : ∀ k i, 0 < p k i ∧ p k i < 1)
    (Z : ∀ k, Assignment (n k) → ℝ)
    (hZ : SAP.P004a.W1NormalLimit n p Z) (x : ℝ) :
    Tendsto (fun k => prob (p k) (fun z => Z k z < x)) atTop
      (nhds (AronowAudit.P004.normalCDF x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨y, hy, hby⟩ :=
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_left x b hb
    filter_upwards [(tendsto_order.mp (hZ y)).1 b hby] with k hk
    have hmono := AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
      (p k) (hp k) (fun z => Z k z ≤ y) (fun z => Z k z < x)
      (fun z hz => lt_of_le_of_lt hz hy)
    exact lt_of_lt_of_le hk hmono
  · intro b hb
    obtain ⟨y, hy, hyb⟩ :=
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_right x b hb
    filter_upwards [(tendsto_order.mp (hZ y)).2 b hyb] with k hk
    have hmono := AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
      (p k) (hp k) (fun z => Z k z < x) (fun z => Z k z ≤ y)
      (fun z hz => (lt_trans hz hy).le)
    exact lt_of_le_of_lt hmono hk

theorem normalLimit_abs_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ)
    (hp : ∀ k i, 0 < p k i ∧ p k i < 1)
    (Z : ∀ k, Assignment (n k) → ℝ)
    (hZ : SAP.P004a.W1NormalLimit n p Z) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun k => prob (p k) (fun z => |Z k z| ≤ r)) atTop
      (nhds (2 * AronowAudit.P004.normalCDF r - 1)) := by
  have hid (k : ℕ) :
      prob (p k) (fun z => |Z k z| ≤ r) =
        prob (p k) (fun z => Z k z ≤ r) -
          prob (p k) (fun z => Z k z < -r) := by
    calc
      _ = prob (p k) (fun z => -r ≤ Z k z ∧ Z k z ≤ r) := by
        apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr
        intro z
        exact abs_le
      _ = _ :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_closed_interval
          (p k) (Z k) (-r) r (by linarith)
  have hlim := (hZ r).sub (normalLimit_lt_reindexed p hp Z hZ (-r))
  have hcdfEq (x : ℝ) : AronowAudit.P004.normalCDF x = SAP.P004a.normalCDF x := rfl
  rw [← hcdfEq r] at hlim
  obtain ⟨_, _, _, hneg, _, _, _⟩ :=
    AronowAudit.P004.Wave1.DesignLimits.nf_proof
  have he : AronowAudit.P004.normalCDF r - AronowAudit.P004.normalCDF (-r) = 2 * AronowAudit.P004.normalCDF r - 1 := by
    rw [hneg r]
    ring
  rw [he] at hlim
  exact Filter.Tendsto.congr (fun k => (hid k).symm) hlim

/-- Random-radius coverage for an arbitrary sequence of finite assignment spaces. -/
theorem random_radius_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ)
    (hp : ∀ k i, 0 < p k i ∧ p k i < 1)
    (T W : ∀ k, Assignment (n k) → ℝ) (σ w c : ℝ)
    (hσ : 0 < σ) (hw : 0 < w) (hc : 0 < c)
    (hT : SAP.P004a.W1NormalLimit n p (fun k z => T k z / σ))
    (hW : SAP.P004a.W1InProb n p (fun k z => W k z - w)) :
    Tendsto (fun k => prob (p k) (fun z => |T k z| ≤ c * Real.sqrt (W k z))) atTop
      (nhds (2 * AronowAudit.P004.normalCDF (c * Real.sqrt w / σ) - 1)) := by
  classical
  let R : ∀ k, Assignment (n k) → ℝ := fun k z => c * Real.sqrt (W k z) / σ
  let r₀ : ℝ := c * Real.sqrt w / σ
  have hr₀ : 0 < r₀ := div_pos (mul_pos hc (Real.sqrt_pos.mpr hw)) hσ
  have hF : ContinuousAt (fun v : ℝ => c * Real.sqrt v / σ) w := by
    have hroot : ContinuousAt (fun v : ℝ => Real.sqrt v) w :=
      Real.continuous_sqrt.continuousAt
    have hscaled : ContinuousAt (fun v : ℝ => c * Real.sqrt v) w :=
      continuousAt_const.mul hroot
    exact hscaled.div_const σ
  have hR : SAP.P004a.W1InProb n p (fun k z => R k z - r₀) := by
    intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp hF) ε hε
    have hbad (k : ℕ) (z : Assignment (n k))
        (hz : ε < |R k z - r₀|) : δ / 2 < |W k z - w| := by
      by_contra hnot
      have hin : dist (W k z) w < δ := by
        rw [Real.dist_eq]
        have hh : |W k z - w| ≤ δ / 2 := le_of_not_gt hnot
        linarith
      have hout := hnear hin
      rw [Real.dist_eq] at hout
      dsimp [R, r₀] at hz hout
      exact (not_lt_of_ge hz.le) hout
    have hbound (k : ℕ) :
        prob (p k) (fun z => ε < |R k z - r₀|) ≤
          prob (p k) (fun z => δ / 2 < |W k z - w|) :=
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (p k) (hp k) (fun z => ε < |R k z - r₀|)
        (fun z => δ / 2 < |W k z - w|) (hbad k)
    have htail := hW (δ / 2) (by linarith)
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have hnonneg (k : ℕ) :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_nonneg
          (p k) (hp k) (fun z => ε < |R k z - r₀|)
      filter_upwards [Filter.Eventually.of_forall hnonneg] with k hk
      exact lt_of_lt_of_le hb hk
    · intro b hb
      filter_upwards [(tendsto_order.mp htail).2 b hb] with k hk
      exact lt_of_le_of_lt (hbound k) hk
  have hsand (ε : ℝ) (k : ℕ) :
      prob (p k) (fun z => |T k z / σ| ≤ r₀ - ε) -
          prob (p k) (fun z => ε < |R k z - r₀|) ≤
            prob (p k) (fun z => |T k z / σ| ≤ R k z) ∧
      prob (p k) (fun z => |T k z / σ| ≤ R k z) ≤
        prob (p k) (fun z => |T k z / σ| ≤ r₀ + ε) +
          prob (p k) (fun z => ε < |R k z - r₀|) := by
    have hlo : prob (p k) (fun z => |T k z / σ| ≤ r₀ - ε) ≤
        prob (p k) (fun z => |T k z / σ| ≤ R k z) +
          prob (p k) (fun z => ε < |R k z - r₀|) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_le_add
        (p k) (hp k)
      intro z hz
      by_cases hbad : ε < |R k z - r₀|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        exact le_trans hz (by dsimp [R, r₀] at hd ⊢; linarith)
    have hhi : prob (p k) (fun z => |T k z / σ| ≤ R k z) ≤
        prob (p k) (fun z => |T k z / σ| ≤ r₀ + ε) +
          prob (p k) (fun z => ε < |R k z - r₀|) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_le_add
        (p k) (hp k)
      intro z hz
      by_cases hbad : ε < |R k z - r₀|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        exact le_trans hz (by dsimp [R, r₀] at hd ⊢; linarith)
    constructor <;> linarith
  have hcov : Tendsto
      (fun k => prob (p k) (fun z => |T k z / σ| ≤ R k z)) atTop
      (nhds (2 * AronowAudit.P004.normalCDF r₀ - 1)) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have hb' : (b + 1) / 2 < AronowAudit.P004.normalCDF r₀ := by linarith
      obtain ⟨y, hy, hby⟩ :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_left
          r₀ ((b + 1) / 2) hb'
      let l : ℝ := max y 0
      have hl0 : 0 ≤ l := le_max_right y 0
      have hlr : l < r₀ := max_lt_iff.mpr ⟨hy, hr₀⟩
      have hyl : AronowAudit.P004.normalCDF y ≤ AronowAudit.P004.normalCDF l :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.normalCDF_mono
          (le_max_left y 0)
      have hgap : b < 2 * AronowAudit.P004.normalCDF l - 1 := by nlinarith [hby, hyl]
      let ε : ℝ := r₀ - l
      have hε : 0 < ε := sub_pos.mpr hlr
      have hcut : r₀ - ε = l := by dsimp [ε]; ring
      have hfixed := normalLimit_abs_reindexed p hp (fun k z => T k z / σ)
        hT l hl0
      have hlim : Tendsto
          (fun k => prob (p k) (fun z => |T k z / σ| ≤ l) -
            prob (p k) (fun z => ε < |R k z - r₀|)) atTop
          (nhds (2 * AronowAudit.P004.normalCDF l - 1)) := by
        simpa only [sub_zero] using hfixed.sub (hR ε hε)
      filter_upwards [(tendsto_order.mp hlim).1 b hgap] with k hk
      have hlower := (hsand ε k).1
      rw [hcut] at hlower
      exact lt_of_lt_of_le hk hlower
    · intro b hb
      have hb' : AronowAudit.P004.normalCDF r₀ < (b + 1) / 2 := by linarith
      obtain ⟨y, hy, hyb⟩ :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_right
          r₀ ((b + 1) / 2) hb'
      have hy0 : 0 ≤ y := (lt_trans hr₀ hy).le
      have hgap : 2 * AronowAudit.P004.normalCDF y - 1 < b := by nlinarith [hyb]
      let ε : ℝ := y - r₀
      have hε : 0 < ε := sub_pos.mpr hy
      have hcut : r₀ + ε = y := by dsimp [ε]; ring
      have hfixed := normalLimit_abs_reindexed p hp (fun k z => T k z / σ)
        hT y hy0
      have hlim : Tendsto
          (fun k => prob (p k) (fun z => |T k z / σ| ≤ y) +
            prob (p k) (fun z => ε < |R k z - r₀|)) atTop
          (nhds (2 * AronowAudit.P004.normalCDF y - 1)) := by
        simpa only [add_zero] using hfixed.add (hR ε hε)
      filter_upwards [(tendsto_order.mp hlim).2 b hgap] with k hk
      have hupper := (hsand ε k).2
      rw [hcut] at hupper
      exact lt_of_le_of_lt hupper hk
  have heq (k : ℕ) :
      prob (p k) (fun z => |T k z / σ| ≤ R k z) =
        prob (p k) (fun z => |T k z| ≤ c * Real.sqrt (W k z)) := by
    apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr
    intro z
    dsimp [R, r₀]
    rw [abs_div, abs_of_pos hσ]
    exact div_le_div_iff_of_pos_right hσ
  exact Filter.Tendsto.congr heq hcov

end SAP.P004a.WH.W1.P.T1_L6

open SAP.P004a.WH.W1
open SAP.P004a.WH.W1.P.T1_L6
open MeasureTheory ProbabilityTheory Filter Set AronowAudit.P004
open scoped BigOperators Classical

theorem SAP.P004a.WH.W1.T1_L6_proof : SAP.P004a.WH.W1.T1_L6 := by
  intro θhat hG Vhat hVnonneg hV α hα0 hα1
  let p : ∀ k, Fin (3 * k) → ℝ := fun k => w1ThreeP (3 * k)
  let T : ∀ k, Assignment (3 * k) → ℝ := fun k z =>
    Real.sqrt (3 * k : ℕ) * w1ThreeIPW θhat (3 * k) z
  let W : ∀ k, Assignment (3 * k) → ℝ := fun k z =>
    (3 * k : ℕ) * Vhat k z
  let σ : ℝ := Real.sqrt (3 / 625)
  let w : ℝ := 1753 / 750000
  have hp (k : ℕ) (i : Fin (3 * k)) : 0 < p k i ∧ p k i < 1 := by
    have hh := three_spatial.2.2.2.2.2.2.1 (3 * k) i
    constructor <;> dsimp [p] at * <;> linarith
  have hσ : 0 < σ := by norm_num [σ]
  have hw : 0 < w := by norm_num [w]
  have hZ : SAP.P004a.W1NormalLimit (fun k => 3 * k) p
      (fun k z => T k z / σ) := by
    simpa [T, σ] using hG.1
  have hWin : SAP.P004a.W1InProb (fun k => 3 * k) p
      (fun k z => W k z - w) := by
    simpa [W, w] using hV
  let a : ℝ := 1 - α / 2
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hc : 0 < AronowAudit.P004.normalQuantile a := by
    obtain ⟨_, hmono, hzero, _, hquant, _, _⟩ :=
      AronowAudit.P004.Wave1.DesignLimits.nf_proof
    have hqa := hquant a ha0 ha1
    apply hmono.lt_iff_lt.mp
    have hcdf : AronowAudit.P004.normalCDF 0 < AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a) := by
      rw [hzero]
      calc
        (1 / 2 : ℝ) < a := by dsimp [a]; linarith
        _ = AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a) := hqa.symm
    exact hcdf
  let c : ℝ := AronowAudit.P004.normalQuantile a
  have hcl : 0 < c := by simpa [c] using hc
  have hrad := random_radius_reindexed p hp T W σ w c hσ hw hcl hZ hWin
  have hratio : Real.sqrt w / Real.sqrt (3 / 625) = Real.sqrt (1753 / 3600) := by
    have hdiv : Real.sqrt (w / (3 / 625)) =
        Real.sqrt w / Real.sqrt (3 / 625) :=
      Real.sqrt_div (by norm_num [w] : (0 : ℝ) ≤ w) (3 / 625 : ℝ)
    calc
      _ = Real.sqrt (w / (3 / 625)) := hdiv.symm
      _ = Real.sqrt (1753 / 3600) := by norm_num [w]
  have harg : c * Real.sqrt w / σ =
      AronowAudit.P004.normalQuantile a * Real.sqrt (1753 / 3600) := by
    dsimp [c, σ]
    rw [← hratio]
    ring
  have hcoverage : Tendsto
      (fun k => prob (p k) (fun z =>
        |w1ThreeIPW θhat (3 * k) z -
          ame (w1ThreeP (3 * k)) (circleAverage (threeTypePopulation (3 * k)) 0)| ≤
          c * Real.sqrt (Vhat k z))) atTop
      (nhds (2 * AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a * Real.sqrt (1753 / 3600)) - 1)) := by
    have hevent (k : ℕ) (hk : 0 < k) (z : Assignment (3 * k)) :
        (|w1ThreeIPW θhat (3 * k) z -
          ame (w1ThreeP (3 * k)) (circleAverage (threeTypePopulation (3 * k)) 0)| ≤
            c * Real.sqrt (Vhat k z)) ↔
        (|T k z| ≤ c * Real.sqrt (W k z)) := by
      obtain ⟨_, _, _, _, _, _, hame, _, _⟩ := three_population k hk
      rw [hame, sub_zero]
      have hn : (0 : ℝ) < (3 * k : ℕ) := by exact_mod_cast (by omega : 0 < 3 * k)
      have hroot : 0 < Real.sqrt (3 * k : ℕ) := Real.sqrt_pos.mpr hn
      have hrootW : Real.sqrt (((3 * k : ℕ) : ℝ) * Vhat k z) =
          Real.sqrt (3 * k : ℕ) * Real.sqrt (Vhat k z) :=
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (3 * k : ℕ)) (Vhat k z)
      dsimp [T, W]
      rw [hrootW, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [show c * (Real.sqrt (3 * k : ℕ) * Real.sqrt (Vhat k z)) =
        Real.sqrt (3 * k : ℕ) * (c * Real.sqrt (Vhat k z)) by ring]
      exact (mul_le_mul_iff_of_pos_left hroot).symm
    have heq : ∀ᶠ k in atTop,
        prob (p k) (fun z =>
          |w1ThreeIPW θhat (3 * k) z -
            ame (w1ThreeP (3 * k)) (circleAverage (threeTypePopulation (3 * k)) 0)| ≤
            c * Real.sqrt (Vhat k z)) =
        prob (p k) (fun z => |T k z| ≤ c * Real.sqrt (W k z)) := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr
      intro z
      exact hevent k hk z
    have heq' : (fun k => prob (p k) (fun z => |T k z| ≤ c * Real.sqrt (W k z))) =ᶠ[atTop]
        (fun k => prob (p k) (fun z =>
          |w1ThreeIPW θhat (3 * k) z -
            ame (w1ThreeP (3 * k)) (circleAverage (threeTypePopulation (3 * k)) 0)| ≤
            c * Real.sqrt (Vhat k z))) := heq.mono (fun k hk => hk.symm)
    have hrad' := Filter.Tendsto.congr' heq' hrad
    rw [harg] at hrad'
    exact hrad'
  obtain ⟨_, hmono, hzero, _, hquant, _, _⟩ :=
    AronowAudit.P004.Wave1.DesignLimits.nf_proof
  have hqa : AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a) = a := hquant a ha0 ha1
  have hsqrt : Real.sqrt (1753 / 3600) < 1 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num)
  have hscaled : AronowAudit.P004.normalQuantile a * Real.sqrt (1753 / 3600) < AronowAudit.P004.normalQuantile a :=
    mul_lt_of_lt_one_right hc hsqrt
  have hcdf : AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a * Real.sqrt (1753 / 3600)) < a := by
    calc
      _ < AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a) := hmono hscaled
      _ = a := hqa
  have hdeficit :
      2 * AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile a * Real.sqrt (1753 / 3600)) - 1 < 1 - α := by
    have heq : 2 * a - 1 = 1 - α := by dsimp [a]; ring
    rw [← heq]
    linarith
  have hdeficit' :
      2 * SAP.P004a.normalCDF
        (SAP.P004a.normalQuantile (1 - α / 2) * Real.sqrt (1753 / 3600)) - 1 < 1 - α := by
    simpa [SAP.P004a.normalCDF, AronowAudit.P004.normalCDF,
      SAP.P004a.normalQuantile, AronowAudit.P004.normalQuantile, a] using hdeficit
  refine ⟨?_, hdeficit'⟩
  simpa [a, c, SAP.P004a.normalCDF, AronowAudit.P004.normalCDF,
    SAP.P004a.normalQuantile, AronowAudit.P004.normalQuantile] using hcoverage
