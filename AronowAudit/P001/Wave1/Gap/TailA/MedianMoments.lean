import AronowAudit.P001.Wave1.Lib.TailA.MedianSquareTails
import AronowAudit.P001.Wave1.Gap.GLP0014B2

/-! Moment transfer for the actual finite bootstrap kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace AronowAudit.P001.Wave1.TailA

open AronowAudit.P001.TailA

local instance instDecidableMedianMoments (p : Prop) : Decidable p := Classical.propDecidable p

/-- The general moment correction specialized to finite resampling, with arbitrary sizes
and a measurable statistic. Every conditional moment exists without a population moment. -/
theorem medianMoments_finite_kernel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (sizes : ℕ → ℕ)
    (T : {n : ℕ} → (Fin n → ℝ) → ℝ) (hT : ∀ n, Measurable (@T n))
    (φ : ℝ) (hφ : 0 < φ)
    (hweak : BootstrapWeakCP μ X sizes T (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩)) :
    ((∀ ε : ℝ, 0 < ε → Tendsto
      (fun K : ℕ => Filter.limsup (fun n => prob μ {ω | ε <
        bootstrapTestMean T (firstSample X (sizes n) ω)
          (fun z => if (K : ℝ) < |z| then z^2 else 0)}) atTop)
      atTop (nhds 0)) ↔
      CP μ (fun n ω => (sizes n : ℝ) * bootVar T (firstSample X (sizes n) ω)) (φ^2)) ∧
    (CP μ (fun n ω => (sizes n : ℝ) * bootVar T (firstSample X (sizes n) ω)) (φ^2) →
      CP μ (fun n ω => Real.sqrt (sizes n) *
        Real.sqrt (bootVar T (firstSample X (sizes n) ω))) φ) := by
  let ν := fun n ω => CenteredBootstrapLaw T (firstSample X (sizes n) ω)
  have hk : ∀ n (A : Set ℝ), MeasurableSet A → Measurable (fun ω => ν n ω A) := by
    intro n A hA
    exact ((centeredBootstrapKernel (hT (sizes n))).measurable_coe hA).comp
      (measurable_pi_iff.mpr fun i => hX i)
  have hw : ∀ g : ℝ → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      CP μ (fun n ω => mean (ν n ω) g) (mean (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩) g) := by
    intro g hg hb
    simpa only [ν, centered_bootstrap_test T _ hg.measurable] using hweak g hg hb
  have hc := bootstrap_moments_correction_proof μ ν
    (fun _ _ => inferInstance) hk
    (fun _ _ => centered_bootstrap_memLp T _ measurable_id 2) φ hφ hw
  have ht (K : ℕ) : Measurable (fun z : ℝ => if (K : ℝ) < |z| then z^2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
      (measurable_id.pow_const 2) measurable_const
  have htest (n : ℕ) (ω : Ω) (K : ℕ) :
      (∫ x, if (K : ℝ) < |x| then x^2 else 0 ∂ν n ω) =
        bootstrapTestMean T (firstSample X (sizes n) ω)
          (fun z => if (K : ℝ) < |z| then z^2 else 0) :=
    centered_bootstrap_test T _ (ht K)
  simpa only [htest, ν, centered_bootstrap_variance,
    Real.sqrt_mul (Nat.cast_nonneg _)] using hc

/-- Once the square tails are controlled, the local weak theorem gives both moment limits. -/
theorem medianMoments_of_square_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f)
    (htails : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun K : ℕ => Filter.limsup (fun n => prob μ {ω | ε <
        bootstrapTestMean sampleMedian (firstSample X n ω)
          (fun z => if (K : ℝ) < |z| then z^2 else 0)}) atTop)
      atTop (nhds 0)) :
    CP μ (fun n ω => (n : ℝ)*bootVar sampleMedian (firstSample X n ω)) (1/(4*(f m)^2)) ∧
    CP μ (fun n ω => Real.sqrt n*Real.sqrt (bootVar sampleMedian (firstSample X n ω)))
      (1/(2*f m)) := by
  have hp : 0 < f m := by obtain ⟨δ, hδ, hf, hn, hm, hc, hp, _⟩ := hlocal; exact hp
  have he : (1/(2*f m))^2 = 1/(4*(f m)^2) := by ring
  have hw := (local_median_weak μ X hiid m f hlocal).2
  have hww : BootstrapWeakCP μ X (fun n => n) (fun {n} => @sampleMedian n)
      (gaussianReal 0 ⟨(1/(2*f m))^2, sq_nonneg _⟩) := by
    convert hw using 1
    congr 1
    exact NNReal.eq he
  have hh := medianMoments_finite_kernel μ X hiid.1 (fun n => n)
    (fun {n} => @sampleMedian n) upper_median_measurable (1/(2*f m)) (by positivity) hww
  have hv := hh.1.mp htails
  exact ⟨by simpa only [he] using hv, hh.2 hv⟩

/-- The all-size local-density moment condition. -/
theorem bootstrap_median_primitive_moment_condition_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (hiid : IID μ X)
      (m : ℝ)
      (f : ℝ → ℝ)
      (δ : ℝ)
      (hδ : 0 < δ)
      (hf : (μ.map (X 0)).restrict (Metric.ball m δ) = (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)))
      (hfn : ∀ x ∈ Metric.ball m δ, 0 ≤ f x)
      (hfm : AEMeasurable f (volume.restrict (Metric.ball m δ)))
      (hcont : ContinuousAt f m)
      (hpos : 0 < f m)
      (hmed : cdf μ (X 0) m=1/2 ∧ (∀ x, x < m → cdf μ (X 0) x < 1/2) ∧ (∀ x, m < x → 1/2 < cdf μ (X 0) x))
      (η : ℝ)
      (hη : 0 < η)
      (hmoment : Integrable (fun ω => |X 0 ω|^η) μ),
      CP μ (fun n ω => (n : ℝ)*bootVar sampleMedian (firstSample X n ω)) (1/(4*(f m)^2)) ∧
  CP μ (fun n ω => Real.sqrt n*Real.sqrt (bootVar sampleMedian (firstSample X n ω)))
    (1/(2*f m))) := by
  intro Ω mΩ μ hμ X hiid m f δ hδ hf hfn hfm hcont hpos hmed η hη hmoment
  let hlocal : LocalMedianData μ X m f :=
    ⟨δ, hδ, hf, hfn, hfm, hcont, hpos, hmed.1, hmed.2⟩
  exact medianMoments_of_square_tails μ X hiid m f hlocal
    (local_median_square_tails μ X hiid m f hlocal η hη hmoment)

/-- The global density supplies the required local data on any positive ball. -/
theorem medianMoments_local_of_pdf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℝ) (f : ℝ → ℝ)
    (hf : HasPDF (μ.map (X 0)) f) (hcont : ContinuousAt f m) (hpos : 0 < f m)
    (hmed : cdf μ (X 0) m=1/2 ∧
      (∀ x, x < m → cdf μ (X 0) x < 1/2) ∧
      (∀ x, m < x → 1/2 < cdf μ (X 0) x)) : LocalMedianData μ X m f := by
  refine ⟨1, by norm_num, ?_, fun x _ => hf.2.1 x, hf.1.restrict,
    hcont, hpos, hmed.1, hmed.2⟩
  rw [hf.2.2.2, restrict_withDensity measurableSet_ball]

/-- The odd-size global-density moment condition. -/
theorem bootstrap_median_primitive_moment_condition_supporting_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (hiid : IID μ X)
      (m : ℝ)
      (f : ℝ → ℝ)
      (hf : HasPDF (μ.map (X 0)) f)
      (hcont : ContinuousAt f m)
      (hpos : 0 < f m)
      (hmed : cdf μ (X 0) m=1/2 ∧ (∀ x,x < m → cdf μ (X 0) x < 1/2) ∧ (∀ x,m < x → 1/2 < cdf μ (X 0) x))
      (η : ℝ)
      (hη : 0 < η)
      (hmoment : Integrable (fun ω => |X 0 ω|^η) μ),
      CP μ (fun k ω => ((2*k+1 : ℕ) : ℝ)*bootVar sampleMedian (firstSample X (2*k+1) ω))
     (1/(4*(f m)^2)) ∧
   CP μ (fun k ω => Real.sqrt (2*k+1)*Real.sqrt (bootVar sampleMedian (firstSample X (2*k+1) ω)))
     (1/(2*f m))) := by
  intro Ω mΩ μ hμ X hiid m f hf hcont hpos hmed η hη hmoment
  have hlocal := medianMoments_local_of_pdf μ X m f hf hcont hpos hmed
  have hh := medianMoments_of_square_tails μ X hiid m f hlocal
    (local_median_square_tails μ X hiid m f hlocal η hη hmoment)
  have hs : Tendsto (fun k : ℕ => 2*k+1) atTop atTop := by
    apply tendsto_atTop_mono (fun k => by change k ≤ 2*k+1; omega) tendsto_id
  constructor
  · intro ε hε
    exact (hh.1 ε hε).comp hs
  · intro ε hε
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using (hh.2 ε hε).comp hs

end AronowAudit.P001.Wave1.TailA
