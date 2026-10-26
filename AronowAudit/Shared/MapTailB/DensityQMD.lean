import AronowAudit.Shared.MapTailB.StatLeanSmoke
import AronowAudit.P001.Wave1.Gap.GLP0011B3
import AronowAudit.Literature.CondP001g14

/-!
Scalar density QMD with an S-finite reference measure. Normalization and the
score L² assumption first give genuine L² residuals. The finite pairwise
reference is handled by a direct withDensity calculation; no sigma-finiteness
assumption on the original reference is used.
The final replacement of an L² representative uses contiguity of the actual
local experiments, rather than equality under every alternative law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology InnerProductSpace RealInnerProductSpace
open AsymptoticStatistics
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option linter.style.haveILetI false

/-- Normalized square-root densities and an L² score give an L² residual,
independently of the totalized real integral in the QMD hypothesis. -/
theorem TailB_density_residual_memLp
    {E : Type*} [MeasurableSpace E] (ρ : Measure E)
    (p : ℝ → E → ℝ) (s : E → ℝ)
    (hpmeas : ∀ t, Measurable (p t)) (hpnonneg : ∀ t x, 0 ≤ p t x)
    (hpnorm : ∀ t, (∫⁻ x, ENNReal.ofReal (p t x) ∂ρ) = 1)
    (hsmeas : Measurable s)
    (hs2 : MemLp s 2 (ρ.withDensity (fun x => ENNReal.ofReal (p 0 x))))
    (t : ℝ) :
    MemLp (fun x => Real.sqrt (p t x) - Real.sqrt (p 0 x) -
      t * s x * Real.sqrt (p 0 x) / 2) 2 ρ := by
  have h0 := AronowAudit.P001.Wave1.GLP0011B3_sqrt_memLp
    ρ (p 0) (hpmeas 0) (hpnonneg 0) (hpnorm 0)
  have ht := AronowAudit.P001.Wave1.GLP0011B3_sqrt_memLp
    ρ (p t) (hpmeas t) (hpnonneg t) (hpnorm t)
  have hs := AronowAudit.P001.Wave1.GLP0011B3_weighted_score_memLp
    ρ (p 0) s (hpmeas 0) hsmeas (hpnonneg 0) hs2
  convert (ht.sub h0).sub (hs.const_mul (t / 2)) using 1
  funext x
  simp only [Pi.sub_apply]
  ring

/-- Direct pairwise-dominator identity. The original reference need not be
sigma-finite: the two weighted measures themselves are finite. -/
theorem TailB_density_pairwise_residual_norm
    {E : Type*} [MeasurableSpace E] (ρ : Measure E)
    (f q s : E → ℝ) (hf : Measurable f) (hq : Measurable q)
    (hf0 : ∀ x, 0 ≤ f x) (hq0 : ∀ x, 0 ≤ q x)
    [IsFiniteMeasure (ρ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsFiniteMeasure (ρ.withDensity (fun x => ENNReal.ofReal (q x)))] (t : ℝ) :
    let P := ρ.withDensity (fun x => ENNReal.ofReal (f x))
    let Q := ρ.withDensity (fun x => ENNReal.ofReal (q x))
    eLpNorm' (residualAgainst P Q (P + Q) s t) 2 (P + Q) =
      eLpNorm' (fun x => Real.sqrt (q x) - Real.sqrt (f x) -
        (t / 2) * s x * Real.sqrt (f x)) 2 ρ := by
  exact AronowAudit.P001.Wave1.GLP0011B3_pairwise_residual_norm
    ρ f q s hf hq hf0 hq0 t

/-- Real-density QMD implies the canonical pairwise QMD condition. -/
theorem TailB_density_isRightQMD
    {E : Type*} [MeasurableSpace E] (ρ : Measure E)
    (p : ℝ → E → ℝ) (s : E → ℝ)
    (hpmeas : ∀ t, Measurable (p t)) (hpnonneg : ∀ t x, 0 ≤ p t x)
    (hpnorm : ∀ t, (∫⁻ x, ENNReal.ofReal (p t x) ∂ρ) = 1)
    (hsmeas : Measurable s)
    (hs2 : MemLp s 2 (ρ.withDensity (fun x => ENNReal.ofReal (p 0 x))))
    (hqm : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      (∫ x, (Real.sqrt (p t x) - Real.sqrt (p 0 x) -
        t * s x * Real.sqrt (p 0 x) / 2)^2 ∂ρ) ≤ ε * t^2) :
    IsRightQMD (ρ.withDensity (fun x => ENNReal.ofReal (p 0 x)))
      (fun t => ρ.withDensity (fun x => ENNReal.ofReal (p t x))) s := by
  have hprob (t : ℝ) : IsProbabilityMeasure
      (ρ.withDensity (fun x => ENNReal.ofReal (p t x))) := by
    constructor
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using hpnorm t
  apply AronowAudit.P001.Wave1.GLP0011B3_qmd_of_integral
    ρ p s hpmeas hpnonneg hprob
  · intro t
    convert TailB_density_residual_memLp ρ p s hpmeas hpnonneg hpnorm hsmeas hs2 t using 1
    funext x
    ring
  · intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hqm ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    convert hb t ht using 1
    congr 1
    funext x
    ring

/-- Scalar density score-shift and contiguity. -/
theorem TailB_density_qmd_score_shift
    {E : Type*} [MeasurableSpace E] (ρ : Measure E) [SFinite ρ]
    (p : ℝ → E → ℝ) (s u : E → ℝ)
    (hpmeas : ∀ t, Measurable (p t))
    (hpnonneg : ∀ t x, 0 ≤ p t x)
    (hpnorm : ∀ t, (∫⁻ x, ENNReal.ofReal (p t x) ∂ρ) = 1)
    (hsmeas : Measurable s) (humeas : Measurable u)
    (hs2 : MemLp s 2 (ρ.withDensity (fun x => ENNReal.ofReal (p 0 x))))
    (hu2 : MemLp u 2 (ρ.withDensity (fun x => ENNReal.ofReal (p 0 x))))
    (hs0 : (∫ x, s x ∂(ρ.withDensity (fun x => ENNReal.ofReal (p 0 x)))) = 0)
    (hu0 : (∫ x, u x ∂(ρ.withDensity (fun x => ENNReal.ofReal (p 0 x)))) = 0)
    (hqm : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      (∫ x, (Real.sqrt (p t x) - Real.sqrt (p 0 x) -
        t * s x * Real.sqrt (p 0 x) / 2)^2 ∂ρ) ≤ ε * t^2) :
    let P := ρ.withDensity (fun x => ENNReal.ofReal (p 0 x))
    let Q := fun n => ρ.withDensity (fun x => ENNReal.ofReal (p ((Real.sqrt n)⁻¹) x))
    AronowAudit.Literature.Contiguous
      (fun n => AronowAudit.Literature.ProductLaw P n)
      (fun n => AronowAudit.Literature.ProductLaw (Q n) n) ∧
    AronowAudit.Literature.RowWeak
      (fun n => AronowAudit.Literature.ProductLaw (Q n) n)
      (fun n z => (Real.sqrt n)⁻¹ * ∑ i, u (z i))
      (gaussianReal (∫ x, u x * s x ∂P) (∫ x, (u x)^2 ∂P).toNNReal) := by
  let P := ρ.withDensity (fun x => ENNReal.ofReal (p 0 x))
  let curve := fun t => ρ.withDensity (fun x => ENNReal.ofReal (p t x))
  have hprob (t : ℝ) : IsProbabilityMeasure (curve t) := by
    constructor
    simpa only [curve, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using hpnorm t
  letI instTailBDensityBase : IsProbabilityMeasure P := hprob 0
  obtain ⟨γ, hcurve, hscore⟩ := exists_nondominatedQMDPath_of_bare_qmd
    P curve (fun t _ => hprob t) rfl s hsmeas
    (TailB_density_isRightQMD ρ p s hpmeas hpnonneg hpnorm hsmeas hs2 hqm)
  let c : CandidateIF P := ⟨u, hu2, hu0⟩
  let v : ↥(L2ZeroMean P) := c.toL2ZeroMean
  have hvae : (v : E → ℝ) =ᵐ[P] u := c.coeFn_toL2ZeroMean
  let Pn : (n : ℕ) → Measure (Fin n → E) := fun n => Measure.pi (fun _ => P)
  let Qn : (n : ℕ) → Measure (Fin n → E) := fun n =>
    Measure.pi (fun _ => curve ((Real.sqrt n)⁻¹))
  let A : (n : ℕ) → (Fin n → E) → ℝ := normalizedScoreSum v
  let B : (n : ℕ) → (Fin n → E) → ℝ := fun n z => (Real.sqrt n)⁻¹ * ∑ i, u (z i)
  letI instTailBDensityPn (n : ℕ) : IsProbabilityMeasure (Pn n) := by
    dsimp [Pn]
    infer_instance
  letI instTailBDensityQn (n : ℕ) : IsProbabilityMeasure (Qn n) := by
    letI instTailBDensityCurve : IsProbabilityMeasure (curve ((Real.sqrt n)⁻¹)) := hprob _
    dsimp [Qn]
    infer_instance
  have hA (n : ℕ) : Measurable (A n) :=
    measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
      (Lp.stronglyMeasurable (v : Lp ℝ 2 P)).measurable.comp (measurable_pi_apply i)))
  have hB (n : ℕ) : Measurable (B n) :=
    measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
      humeas.comp (measurable_pi_apply i)))
  have hcont : AsymptoticStatistics.Contiguity.Contiguous atTop Pn Qn := by
    simpa only [one_mul, hcurve, Pn, Qn] using TailB_qmd_local_contiguous γ 1 (by norm_num)
  have hclt : WeakConverges (fun n => (Qn n).map (A n))
      (gaussianReal ⟪v, γ.score⟫_ℝ (NNReal.mk (‖v‖^2) (sq_nonneg _))) := by
    simpa only [one_mul, hcurve, Qn, A] using TailB_qmd_local_score_clt γ 1 (by norm_num) v
  have hraw (n : ℕ) : A n =ᵐ[Pn n] B n := by
    have hpi := Measure.ae_eq_pi (μ := fun _ : Fin n => P) (fun _ => hvae)
    filter_upwards [hpi] with z hz
    change (Real.sqrt n)⁻¹ * ∑ i, (v : E → ℝ) (z i) = _
    congr 1
    exact Finset.sum_congr rfl (fun i _ => congrFun hz i)
  have hdist (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (Qn n).real {z | ε ≤ dist (A n z) (B n z)}) atTop (nhds 0) := by
    have hz (n : ℕ) : (Pn n) {z | ε ≤ dist (A n z) (B n z)} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.2
      filter_upwards [hraw n] with z hz
      simpa only [Set.mem_setOf_eq, hz, dist_self] using (not_le_of_gt hε)
    have hb : Tendsto (fun n => (Pn n) {z | ε ≤ dist (A n z) (B n z)})
        atTop (nhds 0) := by simp only [hz]; exact tendsto_const_nhds
    exact (ENNReal.tendsto_toReal_zero_iff (fun n => by finiteness)).2
      (hcont (fun n => {z | ε ≤ dist (A n z) (B n z)})
        (fun n => measurableSet_le measurable_const ((hA n).dist (hB n))) hb)
  have hBclt := WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => (hA n).aemeasurable) (fun n => (hB n).aemeasurable) hclt hdist
  have hinner : ⟪v, γ.score⟫_ℝ = ∫ x, u x * s x ∂P := by
    change ⟪(v : Lp ℝ 2 P), (γ.score : Lp ℝ 2 P)⟫_ℝ = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hvae, hscore] with x hx hsx
    change (γ.score : E → ℝ) x * (v : E → ℝ) x = _
    rw [hx, ← hsx, mul_comm]
  have hnorm : ‖v‖^2 = ∫ x, (u x)^2 ∂P := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪(v : Lp ℝ 2 P), (v : Lp ℝ 2 P)⟫_ℝ = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hvae] with x hx
    change (v : E → ℝ) x * (v : E → ℝ) x = _
    rw [hx, pow_two]
  have hvar : NNReal.mk (‖v‖^2) (sq_nonneg _) = (∫ x, (u x)^2 ∂P).toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (integral_nonneg (fun _ => sq_nonneg _))]
    exact hnorm
  rw [hinner, hvar] at hBclt
  refine ⟨?_, ?_⟩
  · change AronowAudit.Literature.Contiguous Pn Qn
    intro D hD hDlim
    exact (ENNReal.tendsto_toReal_zero_iff (fun n => by finiteness)).2
      (hcont D hD ((ENNReal.tendsto_toReal_zero_iff (fun n => by finiteness)).1 hDlim))
  · change AronowAudit.Literature.RowWeak Qn B
      (gaussianReal (∫ x, u x * s x ∂P) (∫ x, (u x)^2 ∂P).toNNReal)
    intro f hf hb
    let F : BoundedContinuousFunction ℝ ℝ := ⟨⟨f, hf⟩, by
      obtain ⟨C, hC⟩ := hb
      exact ⟨2 * C, fun x y => (dist_le_norm_add_norm _ _).trans (by
        simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hC x) (hC y))⟩⟩
    have hl := hBclt F
    simp only [integral_map (hB _).aemeasurable F.continuous.aestronglyMeasurable] at hl
    exact hl
