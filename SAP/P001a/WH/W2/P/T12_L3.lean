import SAP.P001a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics
open AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Core
open AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Core.Hilbert
open AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Core.NondominatedQMDPath
open scoped BigOperators ENNReal NNReal Topology Classical InnerProductSpace RealInnerProductSpace

noncomputable section

namespace SAP.P001a.WH.W2.P.T12_L3

private lemma coordinate_dist {τ : ℕ} (θ : Fin τ → ℝ) (k : Fin τ) (t : ℝ) :
    dist (GLP0011B3_coordinate θ k t) θ = |t| :=
  GLP0011B3_coordinate_dist θ k t

private lemma coordinate_sum {τ : ℕ} (θ : Fin τ → ℝ) (k : Fin τ) (t : ℝ)
    (s : Fin τ → ℝ) :
    (∑ j, (GLP0011B3_coordinate θ k t j - θ j) * s j) = t * s k :=
  GLP0011B3_coordinate_sum θ k t s

end SAP.P001a.WH.W2.P.T12_L3

open SAP.P001a.WH.W2.P.T12_L3

theorem SAP.P001a.WH.W2.T12_L3_proof : SAP.P001a.WH.W2.T12_L3 := by
  intro E hE τ ρ f s θ δ hδ hf hnonneg hprob hbase hs2 hs0 hqmd T ψ hreg j k
  let ν : (Fin τ → ℝ) → Measure E := fun a =>
    ρ.withDensity (fun z => ENNReal.ofReal (f a z))
  let P : Measure E := ν θ
  let : IsProbabilityMeasure P := hbase
  have hθball : θ ∈ Metric.ball θ δ := by
    simp [Metric.mem_ball, dist_self, hδ]
  have hνprob (a : Fin τ → ℝ) (ha : a ∈ Metric.ball θ δ) :
      IsProbabilityMeasure (ν a) := by
    simpa only [ν] using hprob a ha

  -- Replace the score by its measurable L² representative in L²₀(P).
  let c : CandidateIF P := ⟨fun z => s z k, hs2 k, hs0 k⟩
  let sc : ↥(L2ZeroMean P) := c.toL2ZeroMean
  have hscmeas : Measurable (sc : E → ℝ) :=
    (Lp.stronglyMeasurable (sc : Lp ℝ 2 P)).measurable
  have hscae : (sc : E → ℝ) =ᵐ[P] fun z => s z k :=
    c.coeFn_toL2ZeroMean
  have hweighted :
      (fun z => (sc : E → ℝ) z * Real.sqrt (f θ z)) =ᵐ[ρ]
        fun z => s z k * Real.sqrt (f θ z) := by
    have hon := (ae_withDensity_iff (hf θ hθball).ennreal_ofReal).1 hscae
    filter_upwards [hon] with z hz
    by_cases hzero : f θ z = 0
    · simp [hzero]
    · have hpositive : 0 < f θ z := lt_of_le_of_ne
        (hnonneg θ hθball z) (Ne.symm hzero)
      rw [hz ((ENNReal.ofReal_pos.2 hpositive).ne')]

  -- Truncate the coordinate path outside the ball where densities are laws.
  let v : ℝ → Fin τ → ℝ := fun t =>
    if |t| < δ then GLP0011B3_coordinate θ k t else θ
  let fp : ℝ → E → ℝ := fun t z => f (v t) z
  have hv0 : v 0 = θ := by simp [v, hδ, GLP0011B3_coordinate]
  have hvball (t : ℝ) : v t ∈ Metric.ball θ δ := by
    by_cases ht : |t| < δ
    · simpa [v, ht, Metric.mem_ball, coordinate_dist] using ht
    · simp [v, ht, Metric.mem_ball, dist_self, hδ]
  have hfpath (t : ℝ) : Measurable (fp t) := hf (v t) (hvball t)
  have hnonnegpath (t : ℝ) (z : E) : 0 ≤ fp t z :=
    hnonneg (v t) (hvball t) z
  have hprobpath (t : ℝ) :
      IsProbabilityMeasure (ρ.withDensity (fun z => ENNReal.ofReal (fp t z))) := by
    simpa only [fp] using hprob (v t) (hvball t)
  have hnormpath (t : ℝ) :
      (∫⁻ z, ENNReal.ofReal (fp t z) ∂ρ) = 1 := by
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
      (hprobpath t).measure_univ
  have hbasePath : fp 0 = f θ := by
    funext z
    simp [fp, hv0]
  have hsc2 : MemLp (sc : E → ℝ) 2
      (ρ.withDensity (fun z => ENNReal.ofReal (fp 0 z))) := by
    simpa only [hbasePath, P, ν] using
      (Lp.memLp (sc : Lp ℝ 2 P))

  -- The normalization of each density puts its square root in L²(ρ).
  have hres (t : ℝ) : MemLp
      (fun z => Real.sqrt (fp t z) - Real.sqrt (fp 0 z) -
        (t / 2) * (sc : E → ℝ) z * Real.sqrt (fp 0 z)) 2 ρ := by
    have hroot0 := GLP0011B3_sqrt_memLp ρ (fp 0) (hfpath 0)
      (hnonnegpath 0) (hnormpath 0)
    have hrootT := GLP0011B3_sqrt_memLp ρ (fp t) (hfpath t)
      (hnonnegpath t) (hnormpath t)
    have hscore := GLP0011B3_weighted_score_memLp ρ (fp 0) (sc : E → ℝ)
      (hfpath 0) hscmeas (hnonnegpath 0) hsc2
    convert (hrootT.sub hroot0).sub (hscore.const_mul (t / 2)) using 1
    funext z
    simp only [Pi.sub_apply]
    ring

  -- Restrict QMD to the local coordinate path and change to the L² representative.
  have hint : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ,
      |t| < r → (∫ z, (Real.sqrt (fp t z) - Real.sqrt (fp 0 z) -
        (t / 2) * (sc : E → ℝ) z * Real.sqrt (fp 0 z)) ^ 2 ∂ρ) ≤ ε * t ^ 2 := by
    intro ε hε
    obtain ⟨r, hr, hbound⟩ := hqmd.2 ε hε
    refine ⟨min δ r, lt_min hδ hr, ?_⟩
    intro t ht
    have htδ : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
    have htr : |t| < r := lt_of_lt_of_le ht (min_le_right _ _)
    have hcoord : dist (GLP0011B3_coordinate θ k t) θ < r := by
      simpa only [coordinate_dist] using htr
    have hft : fp t = fun z => f (GLP0011B3_coordinate θ k t) z := by
      funext z
      simp [fp, v, htδ]
    rw [hft, hbasePath]
    calc
      (∫ z, (Real.sqrt (f (GLP0011B3_coordinate θ k t) z) - Real.sqrt (f θ z) -
          (t / 2) * (sc : E → ℝ) z * Real.sqrt (f θ z)) ^ 2 ∂ρ) =
        ∫ z, (Real.sqrt (f (GLP0011B3_coordinate θ k t) z) - Real.sqrt (f θ z) -
          (∑ l, (GLP0011B3_coordinate θ k t l - θ l) * s z l) *
            Real.sqrt (f θ z) / 2) ^ 2 ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hweighted] with z hweight
        have hcoeff : (t / 2) * (sc : E → ℝ) z * Real.sqrt (f θ z) =
            (∑ l, (GLP0011B3_coordinate θ k t l - θ l) * s z l) *
              Real.sqrt (f θ z) / 2 := by
          calc
            _ = t * ((sc : E → ℝ) z * Real.sqrt (f θ z)) / 2 := by ring
            _ = t * (s z k * Real.sqrt (f θ z)) / 2 := by rw [hweight]
            _ = (∑ l, (GLP0011B3_coordinate θ k t l - θ l) * s z l) *
                  Real.sqrt (f θ z) / 2 := by
                rw [coordinate_sum]
                ring
        rw [hcoeff]
      _ ≤ ε * t ^ 2 := by
        have hb := hbound (GLP0011B3_coordinate θ k t) hcoord
        simpa only [coordinate_dist, sq_abs] using hb

  have hright := GLP0011B3_qmd_of_integral ρ fp (sc : E → ℝ)
    hfpath hnonnegpath hprobpath hres hint
  let γ : NondominatedQMDPath P := {
    curve := fun t => ρ.withDensity (fun z => ENNReal.ofReal (fp t z))
    curve_at_zero := by
      simpa only [hbasePath, P, ν] using rfl
    curve_isProbability := fun t ht => hprobpath t
    score := sc
    qmd_limit := by
      simpa only [hbasePath, P, ν] using hright
  }

  have hpath : ∀ᶠ n : ℕ in atTop,
      γ.curve ((Real.sqrt n)⁻¹) =
        ν (θ + (Real.sqrt n)⁻¹ • (Pi.single k (1 : ℝ) : Fin τ → ℝ)) := by
    have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hsmall := hinv.abs.eventually (Iio_mem_nhds (by simpa using hδ))
    filter_upwards [hsmall] with n hn
    simp only [γ, fp, v, if_pos hn, ν, GLP0011B3_coordinate]

  exact GLP0011B3_regularity_forces_coordinate ν θ T ψ hreg j k
    (fun z => s z k) γ hscae hpath

