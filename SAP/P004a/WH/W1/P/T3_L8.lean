import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.DesignLimits.DL8
import AronowAudit.P004.Wave1.DesignLimits.NF

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P004a.WH.W1.P.T3_L8

open SAP.P004a MeasureTheory ProbabilityTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical Topology

noncomputable section

lemma normalCDF_eq : SAP.P004a.normalCDF = AronowAudit.P004.normalCDF := by
  funext x
  rfl

lemma normalQuantile_eq : SAP.P004a.normalQuantile = AronowAudit.P004.normalQuantile := by
  funext x
  rfl

lemma normal_sandwich_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ)
    (Z : ∀ k, Assignment (n k) → ℝ)
    (hZ : ∀ x, Tendsto (fun k => prob (p k) (fun z => Z k z ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x))) (x : ℝ) (q : ℕ → ℝ)
    (hlo : ∀ y, y < x → ∀ᶠ k in atTop,
      prob (p k) (fun z => Z k z ≤ y) ≤ q k)
    (hhi : ∀ y, x < y → ∀ᶠ k in atTop,
      q k ≤ prob (p k) (fun z => Z k z ≤ y)) :
    Tendsto q atTop (nhds (AronowAudit.P004.normalCDF x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨y,hy,hby⟩ :=
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_left x b hb
    filter_upwards [hlo y hy,(tendsto_order.mp (hZ y)).1 b hby] with k hk hbk
    exact lt_of_lt_of_le hbk hk
  · intro b hb
    obtain ⟨y,hy,hyb⟩ :=
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_right x b hb
    filter_upwards [hhi y hy,(tendsto_order.mp (hZ y)).2 b hyb] with k hk hbk
    exact lt_of_le_of_lt hk hbk

lemma normal_lt_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ) (hp : ∀ k i, 0 < p k i ∧ p k i < 1)
    (Z : ∀ k, Assignment (n k) → ℝ)
    (hZ : ∀ x, Tendsto (fun k => prob (p k) (fun z => Z k z ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x))) (x : ℝ) :
    Tendsto (fun k => prob (p k) (fun z => Z k z < x)) atTop
      (nhds (AronowAudit.P004.normalCDF x)) := by
  apply normal_sandwich_reindexed p Z hZ x
  · intro y hy
    exact Eventually.of_forall fun k =>
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (p k) (hp k) _ _ (fun z hz => lt_of_le_of_lt hz hy)
  · intro y hy
    exact Eventually.of_forall fun k =>
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (p k) (hp k) _ _ (fun z hz => (lt_trans hz hy).le)

lemma normal_abs_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ) (hp : ∀ k i, 0 < p k i ∧ p k i < 1)
    (Z : ∀ k, Assignment (n k) → ℝ)
    (hZ : ∀ x, Tendsto (fun k => prob (p k) (fun z => Z k z ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x))) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun k => prob (p k) (fun z => |Z k z| ≤ r)) atTop
      (nhds (2*AronowAudit.P004.normalCDF r-1)) := by
  have hid (k : ℕ) : prob (p k) (fun z => |Z k z| ≤ r) =
      prob (p k) (fun z => Z k z ≤ r)-prob (p k) (fun z => Z k z < -r) := by
    calc
      _ = prob (p k) (fun z => -r ≤ Z k z ∧ Z k z ≤ r) :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr (p k) _ _
          (fun z => abs_le)
      _ = _ := AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_closed_interval
        (p k) (Z k) (-r) r (by linarith)
  have hlim := (hZ r).sub (normal_lt_reindexed p hp Z hZ (-r))
  have he : AronowAudit.P004.normalCDF r-AronowAudit.P004.normalCDF (-r)=
      2*AronowAudit.P004.normalCDF r-1 := by
    rw [AronowAudit.P004.Wave1.DesignLimits.DLbSupport.normalCDF_neg]
    ring
  rw [he] at hlim
  exact Filter.Tendsto.congr (fun k => (hid k).symm) hlim

theorem random_radius_reindexed {n : ℕ → ℕ}
    (p : ∀ k, Fin (n k) → ℝ) (hp : ∀ k i, 0 < p k i ∧ p k i < 1)
    (T W : ∀ k, Assignment (n k) → ℝ) (σ w c : ℝ)
    (hσ : 0 < σ) (hw : 0 < w) (hc : 0 < c)
    (hT : ∀ x, Tendsto (fun k => prob (p k) (fun z => T k z/σ ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x)))
    (hW : ∀ ε, 0 < ε → Tendsto (fun k => prob (p k)
      (fun z => ε < |W k z-w|)) atTop (nhds 0)) :
    Tendsto (fun k => prob (p k) (fun z => |T k z| ≤ c*Real.sqrt (W k z))) atTop
      (nhds (2*AronowAudit.P004.normalCDF (c*Real.sqrt w/σ)-1)) := by
  classical
  let Z : ∀ k, Assignment (n k) → ℝ := fun k z => T k z/σ
  let R : ∀ k, Assignment (n k) → ℝ := fun k z => c*Real.sqrt (W k z)/σ
  let r₀ : ℝ := c*Real.sqrt w/σ
  have hr₀ : 0 < r₀ := div_pos (mul_pos hc (Real.sqrt_pos.mpr hw)) hσ
  have hZ : ∀ x, Tendsto (fun k => prob (p k) (fun z => Z k z ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x)) := hT
  have hR : ∀ ε, 0 < ε → Tendsto (fun k => prob (p k)
      (fun z => ε < |R k z-r₀|)) atTop (nhds 0) := by
    intro ε hε
    let f : ℝ → ℝ := fun v => c*Real.sqrt v/σ
    have hf : ContinuousAt f w := by
      have hsqrt : Continuous (fun v : ℝ => Real.sqrt v) := Real.continuous_sqrt
      exact ((continuous_const.mul hsqrt).div_const σ).continuousAt
    have hmap : Tendsto f (nhds w) (nhds (f w)) := hf.tendsto
    have hnear : ∀ᶠ v in nhds w, |f v-f w| < ε := by
      have hm := (Metric.tendsto_nhds.mp hmap) ε hε
      filter_upwards [hm] with v hv
      simpa [Real.dist_eq] using hv
    obtain ⟨δ,hδ,hclose⟩ := Metric.eventually_nhds_iff.mp hnear
    let d : ℝ := δ/2
    have hd : 0 < d := by dsimp [d]; linarith
    have hbound : ∀ k, prob (p k) (fun z => ε < |R k z-r₀|) ≤
        prob (p k) (fun z => d < |W k z-w|) := by
      intro k
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (p k) (hp k) _ _
      intro z hz
      by_contra hn
      have hdist : dist (W k z) w < δ := by
        rw [Real.dist_eq]
        have habs : |W k z-w| ≤ d := le_of_not_gt hn
        dsimp [d] at habs
        linarith
      have hout := hclose hdist
      have heq : R k z-r₀ = f (W k z)-f w := by rfl
      rw [heq] at hz
      exact (not_lt_of_ge (le_of_lt hout)) hz
    have hupper := hW d hd
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall (fun k =>
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_nonneg (p k) (hp k) _))
      (Eventually.of_forall hbound)
  have hsand (ε : ℝ) (k : ℕ) :
      prob (p k) (fun z => |Z k z| ≤ r₀-ε)-
        prob (p k) (fun z => ε < |R k z-r₀|) ≤
          prob (p k) (fun z => |Z k z| ≤ R k z) ∧
      prob (p k) (fun z => |Z k z| ≤ R k z) ≤
        prob (p k) (fun z => |Z k z| ≤ r₀+ε)+
          prob (p k) (fun z => ε < |R k z-r₀|) := by
    have hlo : prob (p k) (fun z => |Z k z| ≤ r₀-ε) ≤
        prob (p k) (fun z => |Z k z| ≤ R k z)+
          prob (p k) (fun z => ε < |R k z-r₀|) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_le_add
        (p k) (hp k) _ _ _
      intro z hz
      by_cases hbad : ε < |R k z-r₀|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        linarith
    have hhi : prob (p k) (fun z => |Z k z| ≤ R k z) ≤
        prob (p k) (fun z => |Z k z| ≤ r₀+ε)+
          prob (p k) (fun z => ε < |R k z-r₀|) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_le_add
        (p k) (hp k) _ _ _
      intro z hz
      by_cases hbad : ε < |R k z-r₀|
      · exact Or.inr hbad
      · left
        have hd := abs_le.mp (le_of_not_gt hbad)
        linarith
    constructor <;> linarith
  have hcov : Tendsto (fun k => prob (p k) (fun z => |Z k z| ≤ R k z)) atTop
      (nhds (2*AronowAudit.P004.normalCDF r₀-1)) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have hb' : (b+1)/2 < AronowAudit.P004.normalCDF r₀ := by linarith
      obtain ⟨y,hy,hby⟩ :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_left r₀ ((b+1)/2) hb'
      let l : ℝ := max y 0
      have hl0 : 0 ≤ l := le_max_right y 0
      have hlr : l < r₀ := max_lt_iff.mpr ⟨hy,hr₀⟩
      have hyl : AronowAudit.P004.normalCDF y ≤ AronowAudit.P004.normalCDF l :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.normalCDF_mono (le_max_left y 0)
      have hgap : b < 2*AronowAudit.P004.normalCDF l-1 := by linarith [hby,hyl]
      let ε : ℝ := r₀-l
      have hε : 0 < ε := sub_pos.mpr hlr
      have hcut : r₀-ε=l := by dsimp [ε]; ring
      have hfixed := normal_abs_reindexed p hp Z hZ l hl0
      have hlim : Tendsto (fun k => prob (p k) (fun z => |Z k z|≤l)-
          prob (p k) (fun z => ε < |R k z-r₀|)) atTop
          (nhds (2*AronowAudit.P004.normalCDF l-1)) := by
        simpa only [sub_zero] using hfixed.sub (hR ε hε)
      filter_upwards [(tendsto_order.mp hlim).1 b hgap] with k hk
      have hlow := (hsand ε k).1
      rw [hcut] at hlow
      exact lt_of_lt_of_le hk hlow
    · intro b hb
      have hb' : AronowAudit.P004.normalCDF r₀ < (b+1)/2 := by linarith
      obtain ⟨y,hy,hyb⟩ :=
        AronowAudit.P004.Wave1.DesignLimits.DLbSupport.cdf_right r₀ ((b+1)/2) hb'
      have hy0 : 0 ≤ y := (lt_trans hr₀ hy).le
      have hgap : 2*AronowAudit.P004.normalCDF y-1 < b := by linarith [hyb]
      let ε : ℝ := y-r₀
      have hε : 0 < ε := sub_pos.mpr hy
      have hcut : r₀+ε=y := by dsimp [ε]; ring
      have hfixed := normal_abs_reindexed p hp Z hZ y hy0
      have hlim : Tendsto (fun k => prob (p k) (fun z => |Z k z|≤y)+
          prob (p k) (fun z => ε < |R k z-r₀|)) atTop
          (nhds (2*AronowAudit.P004.normalCDF y-1)) := by
        simpa only [add_zero] using hfixed.add (hR ε hε)
      filter_upwards [(tendsto_order.mp hlim).2 b hgap] with k hk
      have hupper := (hsand ε k).2
      rw [hcut] at hupper
      exact lt_of_le_of_lt hupper hk
  have heq (k : ℕ) : prob (p k) (fun z => |Z k z|≤R k z) =
      prob (p k) (fun z => |T k z|≤c*Real.sqrt (W k z)) := by
    apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr
    intro z
    dsimp [Z,R]
    rw [abs_div,abs_of_pos hσ]
    exact div_le_div_iff_of_pos_right hσ
  have hresult := Filter.Tendsto.congr heq hcov
  simpa only [r₀] using hresult

end
end SAP.P004a.WH.W1.P.T3_L8

open SAP.P004a MeasureTheory ProbabilityTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical Topology

theorem SAP.P004a.WH.W1.T3_L8_proof : SAP.P004a.WH.W1.T3_L8 := by
  intro hAsym
  rcases hAsym with ⟨_hrem,hNormal,hVariance,_hcount,_hR,hVprinted,_hRatio,hBad⟩
  intro α hα hαhalf
  let p : ∀ r, Fin (8*r) → ℝ := fun r => w1ActiveP (8*r)
  let Z : ∀ r, Assignment (8*r) → ℝ := fun r z =>
    Real.sqrt (8*r : ℕ) * w1ActiveIPW (8*r) z / (1/2)
  let W : ∀ r, Assignment (8*r) → ℝ := fun r z =>
    4 * ((8*r : ℕ) * w1ActiveVPrinted (8*r) z)
  let c : ℝ := AronowAudit.P004.normalQuantile (1-α/2)
  have hp : ∀ r i, 0 < p r i ∧ p r i < 1 := by
    intro r i
    exact AronowAudit.P004.Wave1.ObservationalCoverage.active_true_admissible (8*r) i
  have hZ : ∀ x, Tendsto (fun r => prob (p r) (fun z => Z r z ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x)) := by
    intro x
    simpa only [p,Z,SAP.P004a.WH.W1.P.T3_L8.normalCDF_eq] using hNormal x
  have hW : ∀ ε, 0 < ε → Tendsto (fun r => prob (p r)
      (fun z => ε < |W r z-8/25|)) atTop (nhds 0) := by
    intro ε hε
    have hscaled := hVprinted (ε/4) (by positivity)
    have hevent (r : ℕ) :
      prob (p r) (fun z => ε < |W r z-8/25|) =
          prob (p r) (fun z => ε/4 < |(8*r : ℕ)*w1ActiveVPrinted (8*r) z-2/25|) := by
      apply AronowAudit.P004.Wave1.ObservationalCoverage.prob_congr
      intro z
      have he : W r z-8/25 =
          4*((8*r : ℕ)*w1ActiveVPrinted (8*r) z-2/25) := by
        dsimp [W]
        ring
      rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
      constructor <;> intro hh <;> nlinarith
    exact Filter.Tendsto.congr (fun r => (hevent r).symm) hscaled
  have hcoverageZ :
      Tendsto (fun r => prob (p r) (fun z => |Z r z| ≤ c*Real.sqrt (W r z))) atTop
        (nhds (2*AronowAudit.P004.normalCDF (c*Real.sqrt (8/25))-1)) := by
    have hZ' : ∀ x, Tendsto (fun r => prob (p r) (fun z => Z r z/1 ≤ x)) atTop
        (nhds (AronowAudit.P004.normalCDF x)) := by
      simpa only [div_one] using hZ
    obtain ⟨_,hmono,hzero,_,hquant,_,_⟩ :=
      AronowAudit.P004.Wave1.DesignLimits.nf_proof
    have hq := hquant (1-α/2) (by linarith) (by linarith)
    have hqpos : 0 < AronowAudit.P004.normalQuantile (1-α/2) := by
      apply hmono.lt_iff_lt.mp
      rw [hzero,hq]
      linarith
    have h := SAP.P004a.WH.W1.P.T3_L8.random_radius_reindexed
      p hp Z W 1 (8/25) c (by norm_num) (by norm_num) hqpos hZ' hW
    simpa only [div_one] using h
  have hintervalP :
      Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z =>
        |w1ActiveIPW (8*r) z| ≤ normalQuantile (1-α/2) *
          Real.sqrt (w1ActiveVPrinted (8*r) z))) atTop
        (nhds (2*AronowAudit.P004.normalCDF (c*Real.sqrt (8/25))-1)) := by
    apply hcoverageZ.congr'
    filter_upwards [eventually_gt_atTop 0] with r hr
    apply AronowAudit.P004.Wave1.ObservationalCoverage.prob_congr
    intro z
    have hn : 0 < ((8*r : ℕ) : ℝ) := by exact_mod_cast (show 0 < 8*r by omega)
    have hs : 0 < Real.sqrt ((8*r : ℕ) : ℝ) := Real.sqrt_pos.mpr hn
    have hroot : Real.sqrt (4*((8*r : ℕ) : ℝ)*w1ActiveVPrinted (8*r) z) =
        2*Real.sqrt ((8*r : ℕ) : ℝ)*Real.sqrt (w1ActiveVPrinted (8*r) z) := by
      rw [show 4*((8*r : ℕ) : ℝ)*w1ActiveVPrinted (8*r) z =
        4*(((8*r : ℕ) : ℝ)*w1ActiveVPrinted (8*r) z) by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
        Real.sqrt_mul hn.le]
      norm_num
      ring
    have hleft : |Z r z| = 2*Real.sqrt ((8*r : ℕ) : ℝ)*|w1ActiveIPW (8*r) z| := by
      dsimp [Z]
      rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_pos hs]
      norm_num
      ring
    change (|Z r z| ≤ c*Real.sqrt (W r z)) ↔
      (|w1ActiveIPW (8*r) z| ≤ normalQuantile (1-α/2)*
        Real.sqrt (w1ActiveVPrinted (8*r) z))
    have hrootW : Real.sqrt (W r z) =
        2*Real.sqrt ((8*r : ℕ) : ℝ)*Real.sqrt (w1ActiveVPrinted (8*r) z) := by
      dsimp [W]
      calc
        Real.sqrt (4*(((8*r : ℕ) : ℝ)*w1ActiveVPrinted (8*r) z)) =
            Real.sqrt (4*((8*r : ℕ) : ℝ)*w1ActiveVPrinted (8*r) z) := by
          congr 1
          ring
        _ = _ := hroot
    rw [hleft, hrootW]
    rw [SAP.P004a.WH.W1.P.T3_L8.normalQuantile_eq]
    dsimp [c]
    have hA : 0 < 2*Real.sqrt ((8*r : ℕ) : ℝ) := by positivity
    constructor
    · intro hh
      apply (mul_le_mul_iff_of_pos_left hA).mp
      calc
        2*Real.sqrt ((8*r : ℕ) : ℝ)*|w1ActiveIPW (8*r) z| ≤
            AronowAudit.P004.normalQuantile (1-α/2)*
              (2*Real.sqrt ((8*r : ℕ) : ℝ)*Real.sqrt (w1ActiveVPrinted (8*r) z)) := hh
        _ = 2*Real.sqrt ((8*r : ℕ) : ℝ)*
            (AronowAudit.P004.normalQuantile (1-α/2)*
              Real.sqrt (w1ActiveVPrinted (8*r) z)) := by ring
    · intro hh
      have hm := (mul_le_mul_iff_of_pos_left hA).mpr hh
      calc
        2*Real.sqrt ((8*r : ℕ) : ℝ)*|w1ActiveIPW (8*r) z| ≤
            2*Real.sqrt ((8*r : ℕ) : ℝ)*
              (AronowAudit.P004.normalQuantile (1-α/2)*
                Real.sqrt (w1ActiveVPrinted (8*r) z)) := hm
        _ = AronowAudit.P004.normalQuantile (1-α/2)*
            (2*Real.sqrt ((8*r : ℕ) : ℝ)*Real.sqrt (w1ActiveVPrinted (8*r) z)) := by ring
  have hinterval :
      Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z =>
        |w1ActiveIPW (8*r) z| ≤ normalQuantile (1-α/2) *
          Real.sqrt (w1ActiveVPrinted (8*r) z))) atTop
        (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1)) := by
    simpa only [SAP.P004a.WH.W1.P.T3_L8.normalCDF_eq,
      SAP.P004a.WH.W1.P.T3_L8.normalQuantile_eq,c] using hintervalP
  have hbad : Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z =>
      w1ActiveVPrinted (8*r) z ≤ 0)) atTop (nhds 0) := hBad
  have hstandard :
      Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z =>
        0 < w1ActiveVPrinted (8*r) z ∧
        |w1ActiveIPW (8*r) z/Real.sqrt (w1ActiveVPrinted (8*r) z)| ≤
          normalQuantile (1-α/2))) atTop
        (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1)) := by
    let A : ∀ r, Assignment (8*r) → Prop := fun r z =>
      0 < w1ActiveVPrinted (8*r) z ∧
        |w1ActiveIPW (8*r) z/Real.sqrt (w1ActiveVPrinted (8*r) z)| ≤ c
    let B : ∀ r, Assignment (8*r) → Prop := fun r z =>
      |w1ActiveIPW (8*r) z| ≤ c*Real.sqrt (w1ActiveVPrinted (8*r) z)
    have hmono (r : ℕ) : prob (w1ActiveP (8*r)) (A r) ≤ prob (w1ActiveP (8*r)) (B r) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (w1ActiveP (8*r)) (hp r)
      intro z hz
      have hv := hz.1
      have hsV : 0 < Real.sqrt (w1ActiveVPrinted (8*r) z) := Real.sqrt_pos.mpr hv
      have hdiv := hz.2
      rw [abs_div, abs_of_pos hsV] at hdiv
      exact (div_le_iff₀ hsV).mp hdiv
    have hupper (r : ℕ) : prob (w1ActiveP (8*r)) (B r) ≤
        prob (w1ActiveP (8*r)) (A r) +
          prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_le_add
        (w1ActiveP (8*r)) (hp r) (B r) (A r)
        (fun z => w1ActiveVPrinted (8*r) z ≤ 0)
      intro z hz
      by_cases hv : 0 < w1ActiveVPrinted (8*r) z
      · left
        refine ⟨hv, ?_⟩
        have hsV : 0 < Real.sqrt (w1ActiveVPrinted (8*r) z) := Real.sqrt_pos.mpr hv
        rw [abs_div, abs_of_pos hsV]
        exact (div_le_iff₀ hsV).2 hz
      · exact Or.inr (le_of_not_gt hv)
    have hlowLim : Tendsto (fun r => prob (w1ActiveP (8*r)) (B r) -
        prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0)) atTop
        (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1)) := by
      simpa only [B,c,SAP.P004a.WH.W1.P.T3_L8.normalQuantile_eq,sub_zero]
        using hinterval.sub hbad
    have hhighLim : Tendsto (fun r => prob (w1ActiveP (8*r)) (B r) +
        prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0)) atTop
        (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1)) := by
      simpa only [B,c,SAP.P004a.WH.W1.P.T3_L8.normalQuantile_eq,add_zero]
        using hinterval.add hbad
    have hlow : ∀ r, prob (w1ActiveP (8*r)) (B r) -
        prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0) ≤
          prob (w1ActiveP (8*r)) (A r) := by
      intro r
      linarith [hupper r]
    have hhigh : ∀ r, prob (w1ActiveP (8*r)) (A r) ≤
        prob (w1ActiveP (8*r)) (B r) +
          prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0) := by
      intro r
      calc
        prob (w1ActiveP (8*r)) (A r) ≤ prob (w1ActiveP (8*r)) (B r) := hmono r
        _ ≤ prob (w1ActiveP (8*r)) (B r) +
            prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0) :=
          le_add_of_nonneg_right
            (AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_nonneg
              (w1ActiveP (8*r)) (hp r) _)
    have hlimA := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowLim hhighLim
      (Eventually.of_forall hlow) (Eventually.of_forall hhigh)
    simpa only [A,c,SAP.P004a.WH.W1.P.T3_L8.normalQuantile_eq] using hlimA
  obtain ⟨_,hmono,hzero,_,hquant,_,_⟩ :=
    AronowAudit.P004.Wave1.DesignLimits.nf_proof
  have hq := hquant (1-α/2) (by linarith) (by linarith)
  have hqpos : 0 < AronowAudit.P004.normalQuantile (1-α/2) := by
    apply hmono.lt_iff_lt.mp
    rw [hzero,hq]
    linarith
  have hrootlt : Real.sqrt (8/25 : ℝ) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hcrit : AronowAudit.P004.normalQuantile (1-α/2)*Real.sqrt (8/25) <
      AronowAudit.P004.normalQuantile (1-α/2) := by
    nlinarith
  have hcdf : AronowAudit.P004.normalCDF
      (AronowAudit.P004.normalQuantile (1-α/2)*Real.sqrt (8/25)) <
      AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile (1-α/2)) := hmono hcrit
  rw [hq] at hcdf
  have hcdf' : normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25)) < 1-α/2 := by
    simpa only [SAP.P004a.WH.W1.P.T3_L8.normalCDF_eq,
      SAP.P004a.WH.W1.P.T3_L8.normalQuantile_eq] using hcdf
  refine ⟨hinterval,hstandard,?_⟩
  linarith [hcdf']

