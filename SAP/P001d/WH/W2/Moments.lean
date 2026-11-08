import SAP.P001d.Defs.WholeW2
import SAP.P001d.Bridge
import AronowAudit.P001.Wave1.Gap.TailA.MedianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2

local instance instDecidableMoments (p : Prop) : Decidable p := Classical.propDecidable p

open AronowAudit.P001.TailA

/-- The finite conditional law only uses measurability on the actual sample images. -/
theorem composite_kernel {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (T : {n : ℕ} → (Fin n → ℝ) → ℝ)
    (hT : WholeResampleMeasurable X T) (n : ℕ) :
    Measurable (fun ω => CenteredBootstrapLaw T (firstSample X (n+1) ω)) := by
  have hj : Measurable (fun p : Ω × (Fin (n+1) → Fin (n+1)) =>
      Real.sqrt (n+1 : ℕ) *
        (T (firstSample X (n+1) p.1 ∘ p.2) - T (firstSample X (n+1) p.1))) := by
    apply measurable_from_prod_countable_left
    intro a
    exact ((hT n a).sub (by simpa using hT n id)).const_mul _
  have hm := (Measure.measurable_map _ hj).comp
    (Measurable.map_prodMk_left (ν := UniformResampling (n+1)) (α := Ω))
  convert hm using 1
  funext ω
  change _ = ((UniformResampling (n+1)).map (Prod.mk ω)).map _
  rw [Measure.map_map hj measurable_prodMk_left]
  rfl

/-- A nonnegative decreasing function has the same zero limit on real and natural cutoffs. -/
theorem cutoff_cofinal (f : ℝ → ℝ) (hpos : ∀ K, 0 ≤ f K) (hanti : Antitone f) :
    Tendsto (fun K : ℕ => f K) atTop (nhds 0) ↔ Tendsto f atTop (nhds 0) := by
  constructor
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun K => ha.trans_le (hpos K))
    · intro b hb
      obtain ⟨K, hK⟩ := ((tendsto_order.mp h).2 b hb).exists
      filter_upwards [eventually_ge_atTop (K : ℝ)] with x hx
      exact (hanti hx).trans_lt hK
  · intro h
    exact h.comp tendsto_natCast_atTop_atTop

/-- All probabilities in the cutoff limsup lie in [0,1]; no extended-real junk occurs. -/
theorem square_tails_cofinal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (T : {n : ℕ} → (Fin n → ℝ) → ℝ) :
    WholeSquareTails μ X T ↔
      (∀ ε : ℝ, 0 < ε → Tendsto
        (fun K : ℕ => Filter.limsup (fun n => prob μ {ω | ε <
          bootstrapTestMean T (firstSample X (n+1) ω)
            (fun z => if (K : ℝ) < |z| then z^2 else 0)}) atTop) atTop (nhds 0)) := by
  have hcut (ε : ℝ) :
      let p := fun K : ℝ => fun n => prob μ {ω | ε <
        bootstrapTestMean T (firstSample X (n+1) ω)
          (fun z => if K < |z| then z^2 else 0)}
      Tendsto (fun K : ℕ => Filter.limsup (p K) atTop) atTop (nhds 0) ↔
        Tendsto (fun K : ℝ => Filter.limsup (p K) atTop) atTop (nhds 0) := by
    dsimp only
    let p := fun K : ℝ => fun n => prob μ {ω | ε <
      bootstrapTestMean T (firstSample X (n+1) ω)
        (fun z => if K < |z| then z^2 else 0)}
    have hp0 (K : ℝ) (n : ℕ) : 0 ≤ p K n := ENNReal.toReal_nonneg
    have hp1 (K : ℝ) (n : ℕ) : p K n ≤ 1 := measureReal_le_one
    have hb (K : ℝ) : IsBoundedUnder (· ≤ ·) atTop (p K) :=
      isBoundedUnder_of ⟨1, hp1 K⟩
    have hc (K : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (p K) :=
      isCoboundedUnder_le_of_le atTop (hp0 K)
    have hm : ∀ K L : ℝ, K ≤ L → ∀ n, p L n ≤ p K n := by
      intro K L hKL n
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      apply measure_mono
      intro ω hω
      change ε < _ at hω ⊢
      apply lt_of_lt_of_le hω
      unfold bootstrapTestMean
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro a _
      dsimp only
      split_ifs <;> nlinarith [sq_nonneg
        (Real.sqrt (n+1 : ℕ) *
          (T (fun i => firstSample X (n+1) ω (a i))-T (firstSample X (n+1) ω)))]
    apply cutoff_cofinal (fun K => limsup (p K) atTop)
    · intro K
      have hh := limsup_le_limsup (Eventually.of_forall (hp0 K))
        (isCoboundedUnder_le_of_le atTop (fun _ => le_refl (0 : ℝ))) (hb K)
      simpa only [limsup_const] using hh
    · intro K L hKL
      exact limsup_le_limsup (Eventually.of_forall (hm K L hKL)) (hc L) (hb K)
  exact ⟨fun h ε hε => (hcut ε).mpr (h ε hε),
    fun h ε hε => (hcut ε).mp (h ε hε)⟩

/-- The corrected general moment criterion, with composite rather than global measurability. -/
theorem composite_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (T : {n : ℕ} → (Fin n → ℝ) → ℝ) (hT : WholeResampleMeasurable X T)
    (φ : ℝ) (hφ : 0 < φ)
    (hw : BootstrapWeakCP μ X (fun n => n+1) T (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩)) :
    (WholeSquareTails μ X T ↔
      CP μ (fun n ω => (n+1 : ℕ)*bootVar T (firstSample X (n+1) ω)) (φ^2)) ∧
    (CP μ (fun n ω => (n+1 : ℕ)*bootVar T (firstSample X (n+1) ω)) (φ^2) →
      CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt
        (bootVar T (firstSample X (n+1) ω))) φ) := by
  let ν := fun n ω => CenteredBootstrapLaw T (firstSample X (n+1) ω)
  have hk : ∀ n (A : Set ℝ), MeasurableSet A → Measurable (fun ω => ν n ω A) := by
    intro n A hA
    exact (Measure.measurable_coe hA).comp (composite_kernel X T hT n)
  have hw' : ∀ g : ℝ → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.mean (ν n ω) g)
        (AronowAudit.P001.mean (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩) g) := by
    intro g hg hb
    have h := hw g hg hb
    change AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.bootstrapTestMean T
      (firstSample X (n+1) ω) g) (AronowAudit.P001.mean _ g) at h
    simpa only [ν, centered_bootstrap_test T _ hg.measurable] using h
  have hc := AronowAudit.P001.Wave1.bootstrap_moments_correction_proof μ ν
    (fun _ _ => inferInstance) hk
    (fun _ _ => centered_bootstrap_memLp T _ measurable_id 2) φ hφ hw'
  have ht (K : ℕ) : Measurable (fun z : ℝ => if (K : ℝ) < |z| then z^2 else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
      (measurable_id.pow_const 2) measurable_const
  have htest (n : ℕ) (ω : Ω) (K : ℕ) :
      (∫ z, if (K : ℝ) < |z| then z^2 else 0 ∂ν n ω) =
        bootstrapTestMean T (firstSample X (n+1) ω)
          (fun z => if (K : ℝ) < |z| then z^2 else 0) :=
    centered_bootstrap_test T _ (ht K)
  rw [square_tails_cofinal]
  simpa only [htest, ν, centered_bootstrap_variance,
    Real.sqrt_mul (Nat.cast_nonneg _), Bridge.cp_iff, Bridge.bootVar_eq,
    Bridge.prob_eq] using hc

end SAP.P001d.WH.W2
