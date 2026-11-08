import SAP.P053.Defs.WholeW1
import SAP.P053.Bridge
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P053.WH.W1
open Filter
open scoped BigOperators Topology
noncomputable section

/-- The only new T2 calculation: exact mean, variance and fourth moments
of the repeated binary population, for every positive block count. Transport finite sums
by `repeatedEquivW1` using `Equiv.sum_comp`, expand the four entries, and use
`Fintype.sum_prod_type` and `Finset.sum_const`. The outcome sum and square sum are 2m,
the centered sum of squares is m, and the combined fourth-power sum is 4m.
Use `change` to expose the fixed Fin carrier before unfolding dependent population fields.
This is finite algebra (including transport), with no asymptotic or probability step. -/
def T2_L1 : Prop :=
  ∀ m : ℕ, 0 < m →
    let P := repeatedPopulationW1 m
    populationMean P P.Y0 = 1/2 ∧
    populationVariance P P.Y0 = (m : ℝ)/(4*(m : ℝ)-1) ∧
    (∑ i : Fin P.size, ((P.Y1 i)^4 + (P.Y0 i)^4))/(P.size : ℝ) = 1

/-- Exact population moments of the one-success balanced family. For N=2(k+2),
the outcome sum and square sum are one, so its variance is 1/N. The combined fourth
sum is two. Prove the single nonzero-entry sums with
`Finset.sum_eq_single`, then expand `sampleMean`/`sampleVariance` (or use
`AronowAudit.P053.centeredSS_raw`). The guard k+2>=2 makes every divisor valid.
Use `change` to fix the Fin carrier before unfolding population fields and their instances. -/
def T6_L1 : Prop :=
  ∀ k : ℕ,
    let P := sparsePopulationW1 k
    populationVariance P P.Y0 = 1/(2*((k : ℝ)+2)) ∧
    (∑ i : Fin P.size, ((P.Y1 i)^4 + (P.Y0 i)^4))/(P.size : ℝ) = 1/((k : ℝ)+2)

/-- Exact supported-assignment formulas for the sparse family. Put n=k+2.
If the unique success is treated the arm means are 1/n and zero; otherwise they are
zero and 1/n. In either case SSR=(n-1)/n, giving OLS variance 1/n^2. The combined
sample has variance 1/(2n), giving the same Fisher variance. Split on membership of
unit zero, use `AronowAudit.P053.arm_cards` and `centeredSS_raw`, and evaluate the
indicator sums with `Finset.sum_eq_single`. This is independent of T6_L1. -/
def T6_L2 : Prop :=
  ∀ k : ℕ, ∀ z ∈ support (ι := Fin (sparsePopulationW1 k).size) (sparsePopulationW1 k).n1,
    |estimate (sparsePopulationW1 k) z| = 1/((k : ℝ)+2) ∧
    olsVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 ∧
    fisherVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2

private theorem add_tendstoW1 (a : ℕ) :
    Tendsto (fun k : ℕ => k+a) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, by intro k hk; omega⟩

private theorem sharp_momentsW1 (P : Population) (hs : SharpNull P) :
    populationVariance P (unitEffects P) = 0 ∧ averageEffect P = 0 := by
  have hy : P.Y1 = P.Y0 := funext hs
  constructor
  · simp [populationVariance, unitEffects, hy, sampleVariance, centeredSS, sampleMean]
  · simp [averageEffect, hy]

private theorem inverse_limitW1 (a : ℕ) (_ha : 0 < a) :
    Tendsto (fun k : ℕ => 1/((k+a : ℕ) : ℝ)) atTop (nhds 0) := by
  simpa only [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (add_tendstoW1 a)))

private theorem repeated_variance_limitW1 :
    Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)/(4*((k+1 : ℕ) : ℝ)-1))
      atTop (nhds (1/4)) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).div
    (tendsto_const_nhds.sub (inverse_limitW1 1 (by decide)))
    (by norm_num : (4 : ℝ)-0 ≠ 0))
  change Tendsto (fun k : ℕ => 1/(4-1/((k+1 : ℕ) : ℝ)))
    atTop (nhds (1/(4-0))) at h
  have h' : Tendsto (fun k : ℕ => 1/(4-1/((k+1 : ℕ) : ℝ)))
      atTop (nhds (1/4)) := by simpa only [sub_zero] using h
  apply h'.congr'
  apply Eventually.of_forall
  intro k
  have hm : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k+1)
  have hd : 4*((k+1 : ℕ) : ℝ)-1 ≠ 0 := by nlinarith
  field_simp [hm.ne', hd]

private theorem probability_trueW1 (P : Population)
    (A : Finset (Fin P.size) → Prop) (h : ∀ z ∈ support P.n1, A z) :
    randomizationProbability P A = 1 := by
  classical
  unfold randomizationProbability
  rw [Finset.filter_eq_self.mpr h]
  exact div_self (by exact_mod_cast
    (AronowAudit.P053.support_positive (Bridge.toPopulation P)).ne')

private theorem probability_falseW1 (P : Population)
    (A : Finset (Fin P.size) → Prop) (h : ∀ z ∈ support P.n1, ¬ A z) :
    randomizationProbability P A = 0 := by
  classical
  unfold randomizationProbability
  have he : (support (ι := Fin P.size) P.n1).filter A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact h z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
  rw [he]
  simp

private theorem sparse_alphaW1 :
    0 < sparseAlphaW1 ∧ sparseAlphaW1 < 1 ∧ normalCritical sparseAlphaW1 = 1/2 := by
  have hm : StrictMono standardNormalCDF := by
    intro a b hab
    change AronowAudit.P053.standardNormalCDF a < AronowAudit.P053.standardNormalCDF b
    rw [AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf,
      AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
    exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hab
  have hz : standardNormalCDF 0 = 1/2 := by
    change AronowAudit.P053.standardNormalCDF 0 = 1/2
    rw [AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
    exact AronowAudit.P053.NormalCompletion.normal_cdf_zero
  have hl : 1/2 < standardNormalCDF (1/2) := by
    calc
      1/2 = standardNormalCDF 0 := hz.symm
      _ < standardNormalCDF (1/2) := hm (by norm_num)
  have hu : standardNormalCDF (1/2) < 1 := by
    have hle : standardNormalCDF 1 ≤ 1 := by
      change AronowAudit.P053.standardNormalCDF 1 ≤ 1
      rw [AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
      exact ProbabilityTheory.cdf_le_one (μ := ProbabilityTheory.gaussianReal 0 1) 1
    exact (hm (by norm_num : (1/2 : ℝ) < 1)).trans_le hle
  have ha : 0 < sparseAlphaW1 := by dsimp [sparseAlphaW1]; linarith
  have hb : sparseAlphaW1 < 1 := by dsimp [sparseAlphaW1]; linarith
  refine ⟨ha, hb, hm.injective ?_⟩
  have hc : standardNormalCDF (normalCritical sparseAlphaW1) = 1-sparseAlphaW1/2 :=
    AronowAudit.P053.NormalCompletion.normalCritical_cdf sparseAlphaW1 ha hb
  rw [hc]
  dsimp [sparseAlphaW1]
  ring

/-- Assemble all existing counterexample facts and the new moment calculation;
the only new analytic step is the elementary limit m/(4m-1) -> 1/4. -/
theorem T2_assembly (h1 : T2_L1) : T2WholeStatement := by
  have hmom : ∀ m : ℕ, 0 < m → RepeatedMomentsW1 m := by
    intro m hm
    obtain ⟨hmean, hvar, hfour⟩ := h1 m hm
    have hs : SharpNull (repeatedPopulationW1 m) := by intro i; rfl
    obtain ⟨heff, htau⟩ := sharp_momentsW1 _ hs
    exact ⟨hs, hmean, hmean, hvar, hvar, heff, htau, hfour⟩
  have hold : T2Statement :=
    ⟨AronowAudit.P053.four_counterexample_values,
      AronowAudit.P053.unrestricted_counterexample,
      fun m hm => ⟨AronowAudit.P053.repeated_counterexample_values m hm,
        AronowAudit.P053.unrestricted_repeated_counterexample m hm⟩,
      AronowAudit.P053.repeated_counterexample_scaling⟩
  refine ⟨hold, ?_, hmom, ?_⟩
  · intro z hz
    simp [uniformMassW1, hz, hold.1.1]
  · rcases hold.2.2.2 with ⟨hsize, halloc, _hq, _hfourth⟩
    have hsize' : ∀ k, (repeatedFamilyW1 k).size = 4*(k+1) := by
      intro k
      dsimp [repeatedFamilyW1, repeatedPopulationW1, Population.size]
      omega
    refine {
      size_diverges := ?_
      arm_sizes := ?_
      p_positive := by norm_num
      p_less_one := by norm_num
      allocation := ?_
      variance1 := ?_
      variance0 := ?_
      varianceEffect := ?_
      average_effect := ?_
      fourth_moments := ?_
    }
    · simpa only [hsize'] using hsize
    · exact Eventually.of_forall (fun k => by
        dsimp [repeatedFamilyW1, repeatedPopulationW1]; omega)
    · change Tendsto (fun k : ℕ => ((2*(k+1) : ℕ) : ℝ)/(repeatedFamilyW1 k).size)
        atTop (nhds (1/2))
      simpa only [hsize'] using halloc
    · apply repeated_variance_limitW1.congr'
      exact Eventually.of_forall (fun k => (hmom (k+1) (by omega)).2.2.2.1.symm)
    · apply repeated_variance_limitW1.congr'
      exact Eventually.of_forall (fun k => (hmom (k+1) (by omega)).2.2.2.2.1.symm)
    · apply tendsto_const_nhds.congr'
      exact Eventually.of_forall (fun k => (hmom (k+1) (by omega)).2.2.2.2.2.1.symm)
    · apply tendsto_const_nhds.congr'
      exact Eventually.of_forall (fun k => (hmom (k+1) (by omega)).2.2.2.2.2.2.1.symm)
    · exact ⟨1, by norm_num, fun k => (hmom (k+1) (by omega)).2.2.2.2.2.2.2.le⟩

/-- Assemble a genuine local S5 counterexample to test equivalence. No CLT is used:
the conditional Fisher p-value is identically one, while the absolute Wald statistic
is identically one. Quantile inversion and all event/probability glue are proved here. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6WholeStatement := by
  have hs : ∀ k, SharpNull (sparsePopulationW1 k) := by intro k i; rfl
  have hmom : ∀ k, SparseMomentsW1 k := by
    intro k
    obtain ⟨hvar, hfour⟩ := h1 k
    obtain ⟨heff, htau⟩ := sharp_momentsW1 _ (hs k)
    exact ⟨hvar, hvar, heff, htau, hfour⟩
  have ht : ∀ k, averageEffect (sparsePopulationW1 k) = 0 :=
    fun k => (hmom k).2.2.2.1
  have hlocal : Tendsto (fun k => averageEffect (sparsePopulationW1 k)) atTop (nhds 0) := by
    simpa only [ht] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hinv : Tendsto (fun k : ℕ => 1/((k : ℝ)+2)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using inverse_limitW1 2 (by decide)
  have hvar : Tendsto (fun k : ℕ => 1/(2*((k : ℝ)+2))) atTop (nhds 0) := by
    simpa only [Pi.mul_apply, zero_mul, one_div, mul_inv_rev] using hinv.mul_const (2 : ℝ)⁻¹
  have hreg : Regularity sparsePopulationW1 (1/2) 0 0 0 0 := by
    refine {
      size_diverges := ?_
      arm_sizes := ?_
      p_positive := by norm_num
      p_less_one := by norm_num
      allocation := ?_
      variance1 := ?_
      variance0 := ?_
      varianceEffect := ?_
      average_effect := hlocal
      fourth_moments := ?_
    }
    · apply tendsto_atTop.2
      intro b
      exact eventually_atTop.2 ⟨b, by
        intro k hk; dsimp [sparsePopulationW1, Population.size]; omega⟩
    · exact Eventually.of_forall (fun k => by dsimp [sparsePopulationW1]; omega)
    · have he : ∀ k : ℕ, ((sparsePopulationW1 k).n1 : ℝ)/(sparsePopulationW1 k).size = 1/2 := by
        intro k
        dsimp [sparsePopulationW1, Population.size]
        push_cast
        field_simp
        ring
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (nhds (1/2)))
    · exact hvar.congr' (Eventually.of_forall (fun k => (hmom k).1.symm))
    · exact hvar.congr' (Eventually.of_forall (fun k => (hmom k).2.1.symm))
    · apply tendsto_const_nhds.congr'
      exact Eventually.of_forall (fun k => (hmom k).2.2.1.symm)
    · refine ⟨1, by norm_num, ?_⟩
      intro k
      rw [(hmom k).2.2.2.2]
      apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ)+2)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨ha, hb, hc⟩ := sparse_alphaW1
  have hpoint : ∀ k, ∀ z ∈ support (ι := Fin (sparsePopulationW1 k).size) (sparsePopulationW1 k).n1,
      |estimate (sparsePopulationW1 k) z| = 1/((k : ℝ)+2) ∧
      olsVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 ∧
      fisherVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 ∧
      0 < olsVariance (sparsePopulationW1 k) z ∧
      0 < fisherVariance (sparsePopulationW1 k) z ∧
      frtPValueW1 (sparsePopulationW1 k) z = 1 ∧
      waldRejectW1 (sparsePopulationW1 k) sparseAlphaW1 z ∧
      ¬ frtRejectW1 (sparsePopulationW1 k) sparseAlphaW1 z := by
    intro k z hz
    obtain ⟨he, ho, hf⟩ := h2 k z hz
    have hp : (0 : ℝ) < (k : ℝ)+2 := by positivity
    have ho' : 0 < olsVariance (sparsePopulationW1 k) z := by rw [ho]; positivity
    have hf' : 0 < fisherVariance (sparsePopulationW1 k) z := by rw [hf]; positivity
    have hobs : ∀ w, observed (sparsePopulationW1 k) w = (sparsePopulationW1 k).Y0 := by
      intro w
      funext i
      simp [observed, sparsePopulationW1]
    have hfrt : frtPValueW1 (sparsePopulationW1 k) z = 1 := by
      apply probability_trueW1
      intro w hw
      rw [hobs z, ← hobs w]
      change |estimate (sparsePopulationW1 k) z| ≤ |estimate (sparsePopulationW1 k) w|
      rw [he, (h2 k w hw).1]
    have hwald : waldRejectW1 (sparsePopulationW1 k) sparseAlphaW1 z := by
      unfold waldRejectW1
      rw [hc, he, ho]
      have hsq : Real.sqrt (1/((k : ℝ)+2)^2) = 1/((k : ℝ)+2) := by
        rw [← one_div_pow, Real.sqrt_sq (by positivity)]
      rw [hsq, div_self (by positivity)]
      norm_num
    exact ⟨he, ho, hf, ho', hf', hfrt, hwald, by unfold frtRejectW1; rw [hfrt]; exact not_le.mpr hb⟩
  have hprob : ∀ k, randomizationProbability (sparsePopulationW1 k)
        (waldRejectW1 (sparsePopulationW1 k) sparseAlphaW1) = 1 ∧
      randomizationProbability (sparsePopulationW1 k)
        (frtRejectW1 (sparsePopulationW1 k) sparseAlphaW1) = 0 ∧
      testDisagreementW1 (sparsePopulationW1 k) sparseAlphaW1 = 1 := by
    intro k
    refine ⟨probability_trueW1 _ _ (fun z hz => (hpoint k z hz).2.2.2.2.2.2.1),
      probability_falseW1 _ _ (fun z hz => (hpoint k z hz).2.2.2.2.2.2.2), ?_⟩
    apply probability_trueW1
    intro z hz heq
    exact (hpoint k z hz).2.2.2.2.2.2.2 (heq.mp (hpoint k z hz).2.2.2.2.2.2.1)
  refine ⟨hreg, fun k => ⟨hs k, ht k⟩, ha, hb, hc, hpoint, hprob, ?_⟩
  intro hall
  have hlim := hall sparsePopulationW1 (1/2) 0 0 0 0 hreg hlocal
    (fun k z hz => (hpoint k z hz).2.2.2.1) sparseAlphaW1 ha hb
  have heq : (fun k => randomizationProbability (sparsePopulationW1 k)
        (waldRejectW1 (sparsePopulationW1 k) sparseAlphaW1) -
      randomizationProbability (sparsePopulationW1 k)
        (frtRejectW1 (sparsePopulationW1 k) sparseAlphaW1)) = (fun _ : ℕ => (1 : ℝ)) := by
    funext k
    rw [(hprob k).1, (hprob k).2.1]
    norm_num
  rw [heq] at hlim
  have hbad : (1 : ℝ) = 0 := tendsto_const_nhds_iff.mp hlim
  norm_num at hbad

end
end SAP.P053.WH.W1
