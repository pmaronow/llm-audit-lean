import AronowAudit.P001.Wave1.Cond.CondP001cdProofs
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterMapping
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterSlutsky

/-! Real majorant outer expectations and shifted nonnegative outer expectations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology

namespace AronowAudit.P001.Wave1.TailA

universe u

set_option maxHeartbeats 800000

/-- Both infima describe the same bounded, possibly nonmeasurable, readout. -/
theorem outer_readout_eq {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hZ : ∀ ω, |Z ω| ≤ C) :
    outerMean μ Z =
      (MeasureTheory.outerExpectation μ (fun ω => ENNReal.ofReal (Z ω + C))).toReal - C := by
  classical
  let S : Set ℝ := {r | ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
    (∀ ω, Z ω ≤ g ω) ∧ mean μ g = r}
  have hlo (ω) : -C ≤ Z ω := (abs_le.mp (hZ ω)).1
  have hhi (ω) : Z ω ≤ C := (abs_le.mp (hZ ω)).2
  have hSne : S.Nonempty := by
    refine ⟨C, (fun _ => C), measurable_const, integrable_const C, hhi, ?_⟩
    simp [mean]
  have hSlower : ∀ r ∈ S, -C ≤ r := by
    rintro r ⟨g, hgm, hgi, hg, rfl⟩
    have hi := integral_mono (integrable_const (-C) : Integrable (fun _ : Ω => -C) μ)
      hgi (fun ω => (hlo ω).trans (hg ω))
    simpa [mean] using hi
  have hSbdd : BddBelow S := ⟨-C, hSlower⟩
  have hlower : -C ≤ outerMean μ Z := le_csInf hSne hSlower
  have hOE : outerExpectation μ (fun ω => ENNReal.ofReal (Z ω + C))
      ≤ ENNReal.ofReal (2 * C) := by
    calc
      _ ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * C)) :=
        outerExpectation_mono fun ω => ENNReal.ofReal_le_ofReal (by linarith [hhi ω])
      _ = _ := by simp [outerExpectation_const]
  have hOEfin : outerExpectation μ (fun ω => ENNReal.ofReal (Z ω + C)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hOE
  apply le_antisymm
  · have hle : ENNReal.ofReal (outerMean μ Z + C) ≤
        outerExpectation μ (fun ω => ENNReal.ofReal (Z ω + C)) := by
      apply le_iInf
      intro U
      let V : Ω → ℝ≥0∞ := fun ω => min (U.val ω) (ENNReal.ofReal (2 * C))
      have hVm : Measurable V := U.property.1.min measurable_const
      have hVfin (ω) : V ω ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
      have hVbound (ω) : (V ω).toReal ≤ 2 * C := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (show V ω ≤ ENNReal.ofReal (2 * C) from min_le_right _ _)
        simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * C)] using this
      have hVi : Integrable (fun ω => (V ω).toReal) μ :=
        Integrable.of_bound hVm.ennreal_toReal.aestronglyMeasurable (2 * C)
          (ae_of_all μ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
            exact hVbound ω)
      have hmaj (ω) : Z ω + C ≤ (V ω).toReal := by
        apply (ENNReal.ofReal_le_iff_le_toReal (hVfin ω)).mp
        exact le_min (U.property.2 ω)
          (ENNReal.ofReal_le_ofReal (by linarith [hhi ω]))
      have hs : outerMean μ Z ≤ ∫ ω, ((V ω).toReal - C) ∂μ := by
        exact csInf_le hSbdd ⟨_, hVm.ennreal_toReal.sub measurable_const,
          hVi.sub (integrable_const C), (fun ω => by
            change Z ω ≤ (V ω).toReal - C
            linarith [hmaj ω]), rfl⟩
      have hint : (∫ ω, ((V ω).toReal - C) ∂μ) + C =
          ∫ ω, (V ω).toReal ∂μ := by
        rw [integral_sub hVi (integrable_const C)]
        simp
      calc
        ENNReal.ofReal (outerMean μ Z + C)
            ≤ ENNReal.ofReal (∫ ω, (V ω).toReal ∂μ) :=
          ENNReal.ofReal_le_ofReal (by linarith)
        _ = ∫⁻ ω, V ω ∂μ := by
          rw [integral_toReal hVm.aemeasurable
            (ae_of_all μ fun ω => (hVfin ω).lt_top), ENNReal.ofReal_toReal]
          exact ne_top_of_le_ne_top (by
            simpa only [lintegral_const, measure_univ, mul_one] using
              (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * C) ≠ ⊤))
            (lintegral_mono fun ω => min_le_right _ _)
        _ ≤ ∫⁻ ω, U.val ω ∂μ := lintegral_mono fun ω => min_le_left _ _
    have ht := ENNReal.toReal_mono hOEfin hle
    rw [ENNReal.toReal_ofReal (by linarith)] at ht
    linarith
  · apply le_csInf hSne
    rintro r ⟨g, hgm, hgi, hg, rfl⟩
    have hnon (ω) : 0 ≤ g ω + C := by linarith [hlo ω, hg ω]
    have hshift : Integrable (fun ω => g ω + C) μ := hgi.add (integrable_const C)
    have heq : (∫⁻ ω, ENNReal.ofReal (g ω + C) ∂μ) =
        ENNReal.ofReal (mean μ g + C) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hshift (ae_of_all μ hnon),
        integral_add hgi (integrable_const C)]
      simp [mean]
    have hmajor : outerExpectation μ (fun ω => ENNReal.ofReal (Z ω + C)) ≤
        ENNReal.ofReal (mean μ g + C) := by
      rw [← heq]
      exact iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧
        (fun ω => ENNReal.ofReal (Z ω + C)) ≤ U} => ∫⁻ ω, U.val ω ∂μ)
        ⟨(fun ω => ENNReal.ofReal (g ω + C)),
          (hgm.add_const C).ennreal_ofReal,
          fun ω => ENNReal.ofReal_le_ofReal (by linarith [hg ω])⟩
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmajor
    rw [ENNReal.toReal_ofReal (by
      have := MeasureTheory.integral_nonneg (μ := μ) (f := fun ω => g ω + C) hnon
      simpa [integral_add hgi (integrable_const C), mean] using this)] at ht
    linarith

/-- Shifting by the norm identifies the nonnegative outer expectation with the real outer mean. -/
theorem outer_bcf_readout {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : E →ᵇ ℝ) (X : Ω → E) :
    outerMean μ (fun ω => f (X ω)) =
      (outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal -
        ‖f‖ * (μ Set.univ).toReal := by
  simpa using outer_readout_eq μ (fun ω => f (X ω)) ‖f‖ (norm_nonneg f)
    (fun ω => f.norm_coe_le_norm (X ω))

/-- Testing both signs is equivalent to testing all bounded continuous functions. -/
theorem outer_weak_donor_iff {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    OuterWeakLimit μ Z ν ↔
      AsymptoticStatistics.WeakConvergesOuter (fun _ => μ) Z ν := by
  constructor
  · intro h f
    have ht := (h f f.continuous ⟨‖f‖, f.norm_coe_le_norm⟩).1
    simpa only [outer_bcf_readout, mean] using ht
  · intro h f hf hb
    obtain ⟨C, hC⟩ := hb
    let g : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) (by
      intro x y
      calc
        dist (f x) (f y) = |f x - f y| := Real.dist_eq _ _
        _ ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC x, hC y])
    have ht := h g
    have hn := h (-g)
    simp only [← outer_bcf_readout] at ht hn
    constructor
    · exact ht
    · change Tendsto (fun n => outerMean μ (fun ω => -f (Z n ω))) atTop
        (nhds (∫ y, -f y ∂ν)) at hn
      simpa only [integral_neg, neg_neg, mean] using hn.neg


/-- A scalar ramp argument gives CDF convergence from the outer weak limit. -/
theorem outer_weak_real_CD {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : OuterWeakLimit μ Z ν) :
    CD μ Z ν := by
  apply AronowAudit.P001.Wave1.CondP001cd_outer_CD μ Z ν
  intro f hf hb
  exact (h f hf hb).1

end AronowAudit.P001.Wave1.TailA
