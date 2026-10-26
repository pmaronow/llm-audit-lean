import AronowAudit.Literature.CondP001g14
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.DKWUniform

/-!
# Expected empirical CDF deviation and root-n tightness

The expected bound has the distribution-free constant 4. The measurable
root-n deviation consequently has tail probability at most `4 / C`.
The rational-supremum argument follows the private right-continuity helpers
in the vendored StatLean DKWUniform module.
Modified for llm-audit-lean: renamed the right-continuity helpers and
adapted the rational-supremum proof to a bounded supremum.
Upstream license: Apache-2.0; see NOTICE at the repository root.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace AronowAudit.P001.Wave1.TailA

universe u

open AronowAudit.Literature

theorem taila09_finiteCDF_eq_empCDF {Ω : Type u} {n : ℕ}
    (X : Fin n → Ω → ℝ) (ω : Ω) (t : ℝ) :
    FiniteCDF (fun i => X i ω) t = StatLean.HypothesisTesting.empCDF X ω t := by
  classical
  simp only [FiniteCDF, StatLean.HypothesisTesting.empCDF, div_eq_mul_inv, mul_comm]

theorem taila09_cdfDeviation_eq_ksDist {Ω : Type u} {n : ℕ}
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ) (ω : Ω) :
    CDFDeviation P (fun i => X i ω) = StatLean.HypothesisTesting.ksDist X P ω := by
  have heq : (fun t : ℝ => |FiniteCDF (fun i => X i ω) t - (P (Set.Iic t)).toReal|) =
      (fun t : ℝ => |StatLean.HypothesisTesting.empCDF X ω t - ProbabilityTheory.cdf P t|) := by
    funext t
    rw [taila09_finiteCDF_eq_empCDF, cdf_eq_real, measureReal_def]
  exact congrArg (fun f : ℝ → ℝ => sSup (Set.range f)) heq

theorem taila09_finiteCDF_bounds {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    0 ≤ FiniteCDF x t ∧ FiniteCDF x t ≤ 1 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum0 : (0 : ℝ) ≤ ∑ i, if x i ≤ t then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hsum1 : (∑ i, if x i ≤ t then (1 : ℝ) else 0) ≤ n := by
    calc
      (∑ i, if x i ≤ t then (1 : ℝ) else 0) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = n := by simp
  exact ⟨div_nonneg hsum0 hnR.le, (div_le_iff₀ hnR).2 (by simpa using hsum1)⟩

theorem taila09_pointwise_deviation_le {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : Fin n → ℝ) (t : ℝ) :
    |FiniteCDF x t - (P (Set.Iic t)).toReal| ≤ 1 := by
  have hx := taila09_finiteCDF_bounds hn x t
  have hP0 : 0 ≤ (P (Set.Iic t)).toReal := ENNReal.toReal_nonneg
  have hP1 : (P (Set.Iic t)).toReal ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith

theorem taila09_cdfDeviation_bounds {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : Fin n → ℝ) :
    0 ≤ CDFDeviation P x ∧ CDFDeviation P x ≤ 1 := by
  have hbdd : BddAbove (Set.range fun t : ℝ =>
      |FiniteCDF x t - (P (Set.Iic t)).toReal|) :=
    ⟨1, by rintro _ ⟨t, rfl⟩; exact taila09_pointwise_deviation_le hn P x t⟩
  exact ⟨(abs_nonneg _).trans (le_csSup hbdd (Set.mem_range_self (0 : ℝ))),
    csSup_le (Set.range_nonempty _) (by
      rintro _ ⟨t, rfl⟩
      exact taila09_pointwise_deviation_le hn P x t)⟩

theorem taila09_rightCont_step (a s : ℝ) :
    Tendsto (fun t => if a ≤ t then (1 : ℝ) else 0)
      (nhdsWithin s (Set.Ioi s)) (nhds (if a ≤ s then (1 : ℝ) else 0)) := by
  classical
  have heq : (fun _ : ℝ => if a ≤ s then (1 : ℝ) else 0)
      =ᶠ[nhdsWithin s (Set.Ioi s)] (fun t => if a ≤ t then (1 : ℝ) else 0) := by
    by_cases h : a ≤ s
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [ite_eq_left h, ite_eq_left (h.trans ht.le)]
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp h))] with t ht
      rw [ite_eq_right h, ite_eq_right (not_le.mpr ht)]
  exact Tendsto.congr' heq tendsto_const_nhds

theorem taila09_iSup_eq_rat (g : ℝ → ℝ) (hbdd : BddAbove (Set.range g))
    (hrc : ∀ s, Tendsto g (nhdsWithin s (Set.Ioi s)) (nhds (g s))) :
    (⨆ t : ℝ, g t) = ⨆ q : ℚ, g (q : ℝ) := by
  have hbddQ : BddAbove (Set.range fun q : ℚ => g (q : ℝ)) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, by rintro _ ⟨q, rfl⟩; exact hM (Set.mem_range_self _)⟩
  have hle : ∀ t : ℝ, g t ≤ ⨆ q : ℚ, g (q : ℝ) := by
    intro t
    obtain ⟨v, hvgt, hvlt⟩ : ∃ v : ℕ → ℚ,
        (∀ k, t < (v k : ℝ)) ∧ (∀ k, (v k : ℝ) < t + 1 / ((k : ℝ) + 1)) := by
      choose v hv using fun k : ℕ =>
        exists_rat_btwn (show t < t + 1 / ((k : ℝ) + 1) from
          lt_add_of_pos_right t (by positivity))
      exact ⟨v, fun k => (hv k).1, fun k => (hv k).2⟩
    have hupper : Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) atTop (nhds t) := by
      simpa using (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hnhds : Tendsto (fun k => (v k : ℝ)) atTop (nhds t) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
        (Eventually.of_forall fun k => (hvgt k).le)
        (Eventually.of_forall fun k => (hvlt k).le)
    have htend : Tendsto (fun k => (v k : ℝ)) atTop (nhdsWithin t (Set.Ioi t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hnhds, Eventually.of_forall hvgt⟩
    exact le_of_tendsto ((hrc t).comp htend)
      (Eventually.of_forall fun k => le_ciSup hbddQ (v k))
  exact le_antisymm (ciSup_le hle) (ciSup_le fun q => le_ciSup hbdd (q : ℝ))

theorem taila09_cdfDeviation_eq_rat {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : Fin n → ℝ) :
    CDFDeviation P x = ⨆ q : ℚ, |FiniteCDF x (q : ℝ) - ProbabilityTheory.cdf P (q : ℝ)| := by
  classical
  have heq := taila09_cdfDeviation_eq_ksDist P (fun i (_ : Unit) => x i) ()
  rw [heq]
  simp only [StatLean.HypothesisTesting.ksDist, ← taila09_finiteCDF_eq_empCDF]
  refine taila09_iSup_eq_rat _ ⟨1, ?_⟩ ?_
  · rintro _ ⟨t, rfl⟩
    simpa only [cdf_eq_real, measureReal_def] using taila09_pointwise_deviation_le hn P x t
  · intro s
    have hemp : Tendsto (fun t => FiniteCDF x t) (nhdsWithin s (Set.Ioi s))
        (nhds (FiniteCDF x s)) := by
      simp only [FiniteCDF]
      exact (tendsto_finsetSum Finset.univ
        fun i _ => taila09_rightCont_step (x i) s).div_const _
    exact (hemp.sub (((ProbabilityTheory.cdf P).right_continuous s).mono Set.Ioi_subset_Ici_self)).abs

/-- Measurability needs only measurable observations, without independence. -/
theorem cdf_deviation_measurable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (P : Measure ℝ) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ω => CDFDeviation P (fun i => X i ω)) := by
  classical
  have heq : (fun ω => CDFDeviation P (fun i => X i ω)) =
      (fun ω => ⨆ q : ℚ, |FiniteCDF (fun i => X i ω) (q : ℝ) - ProbabilityTheory.cdf P (q : ℝ)|) :=
    funext fun ω => taila09_cdfDeviation_eq_rat hn P _
  rw [heq]
  refine Measurable.iSup fun q => Measurable.abs (Measurable.sub ?_ measurable_const)
  exact (Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_le (hmeas i) measurable_const)
      measurable_const measurable_const).div_const _

/-- The deviation is integrable because its measurable values lie in `[0,1]`. -/
theorem cdf_deviation_integrable {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) :
    Integrable (fun ω => CDFDeviation P (fun i => X i ω)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (cdf_deviation_measurable hn P X hmeas).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (taila09_cdfDeviation_bounds hn P _).1]
    exact (taila09_cdfDeviation_bounds hn P _).2


/-- A measurable root-n deviation and its distribution-free Markov bound. -/
theorem cdf_deviation_root_n_tail {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = P) (C : ℝ) (hC : 0 < C) :
    Measurable (fun ω => Real.sqrt n * CDFDeviation P (fun i => X i ω)) ∧
    (μ {ω | C < Real.sqrt n * CDFDeviation P (fun i => X i ω)}).toReal ≤ 4 / C := by
  refine ⟨(cdf_deviation_measurable hn P X hmeas).const_mul _, ?_⟩
  have hint := (cdf_deviation_integrable μ hn P X hmeas).const_mul (Real.sqrt n)
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => Real.sqrt n * CDFDeviation P (fun i => X i ω)) :=
    Eventually.of_forall fun ω => mul_nonneg (Real.sqrt_nonneg _) (taila09_cdfDeviation_bounds hn P _).1
  have hmean : (∫ ω, Real.sqrt n * CDFDeviation P (fun i => X i ω) ∂μ) ≤ 4 := by
    rw [integral_const_mul]
    have hbound : (∫ ω, CDFDeviation P (fun i => X i ω) ∂μ) ≤ 4 / Real.sqrt n := by
      simpa only [taila09_cdfDeviation_eq_ksDist] using
        StatLean.HypothesisTesting.integral_ksDist_le hn P X hmeas hindep hlaw
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    calc
      Real.sqrt n * (∫ ω, CDFDeviation P (fun i => X i ω) ∂μ)
          ≤ Real.sqrt n * (4 / Real.sqrt n) := mul_le_mul_of_nonneg_left hbound hsqrt.le
      _ = 4 := by field_simp
  have hmarkov := (mul_meas_ge_le_integral_of_nonneg hnonneg hint C).trans hmean
  have hsub : μ.real {ω | C < Real.sqrt n * CDFDeviation P (fun i => X i ω)} ≤
      μ.real {ω | C ≤ Real.sqrt n * CDFDeviation P (fun i => X i ω)} :=
    measureReal_mono (by
      intro ω hω
      change C < Real.sqrt n * CDFDeviation P (fun i => X i ω) at hω
      change C ≤ Real.sqrt n * CDFDeviation P (fun i => X i ω)
      exact hω.le)
  apply (le_div_iff₀ hC).2
  calc
    (μ {ω | C < Real.sqrt n * CDFDeviation P (fun i => X i ω)}).toReal * C
        ≤ μ.real {ω | C ≤ Real.sqrt n * CDFDeviation P (fun i => X i ω)} * C :=
      mul_le_mul_of_nonneg_right hsub hC.le
    _ ≤ 4 := by simpa only [mul_comm] using hmarkov


end AronowAudit.P001.Wave1.TailA
