import SAP.P001d.WH.W2.Leaves
import AronowAudit.P001.Wave1.Gap.GP0014B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2.P.T61_L4

lemma sign_normal_limit_all_sizes {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (hq : cdf μ (X 0) 0 = 1/2) :
    CD μ (fun n ω => Real.sqrt (n+1 : ℕ) *
      (AronowAudit.P001.sampleMean
        (fun i ω => if X i ω ≤ 0 then (1 : ℝ) else 0) (n+1) ω - 1/2))
      (gaussianReal 0 (1/4)) := by
  let g : ℝ → ℝ := fun x => if x ≤ 0 then 1 else 0
  let Z : ℕ → Ω → ℝ := fun i ω => g (X i ω)
  let p : ℕ → Ω → ℝ := AronowAudit.P001.sampleMean Z
  have hg : Measurable g := measurable_const.piecewise measurableSet_Iic measurable_const
  have hZ : IID μ Z := ⟨fun i => hg.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => g) (fun _ => hg), fun i => (hiid.2.2 i).comp hg⟩
  have h2 : MemLp (Z 0) 2 μ := MemLp.of_bound (hZ.1 0).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω => by
      by_cases hω : X 0 ω ≤ 0 <;> simp [Z, g, hω]))
  have hA : MeasurableSet {ω | X 0 ω ≤ 0} := measurableSet_le (hiid.1 0) measurable_const
  have hm : AronowAudit.P001.mean μ (Z 0) = 1/2 := by
    have he : AronowAudit.P001.mean μ (Z 0) = cdf μ (X 0) 0 := by
      change (∫ ω, {ω | X 0 ω ≤ 0}.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
      rw [integral_indicator hA]
      simp [cdf, prob, Measure.real]
    exact he.trans hq
  have hsq : (∫ ω, (Z 0 ω)^2 ∂μ) = AronowAudit.P001.mean μ (Z 0) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by
      by_cases hω : X 0 ω ≤ 0 <;> simp [Z, g, hω])
  have hv : AronowAudit.P001.var μ (Z 0) = 1/4 := by
    rw [AronowAudit.P001.var, variance_eq_sub h2]
    change (∫ ω, (Z 0 ω)^2 ∂μ) - (AronowAudit.P001.mean μ (Z 0))^2 = _
    rw [hsq, hm]
    norm_num
  have hpos : 0 < AronowAudit.P001.var μ (Z 0) := by rw [hv]; norm_num
  have hclt := AronowAudit.P001.central_limit_finite_variance μ Z hZ h2 hpos
  have hnn : (⟨AronowAudit.P001.var μ (Z 0), hpos.le⟩ : ℝ≥0) = (1/4 : ℝ≥0) := by
    apply Subtype.ext
    exact hv
  rw [hm, hnn] at hclt
  have hsucc : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  intro x hx
  have hh := (hclt x hx).comp hsucc
  convert hh using 1
  · funext n
    congr 1
  · rfl

end SAP.P001d.WH.W2.P.T61_L4

theorem SAP.P001d.WH.W2.T61_L4_proof : SAP.P001d.WH.W2.T61_L4 := by
  intro Ω mΩ μ hμ X hiid hq
  let p : ℕ → Ω → ℝ := fun n =>
    AronowAudit.P001.sampleMean
      (fun i ω => if X i ω ≤ 0 then (1 : ℝ) else 0) n
  have hW : CD μ (fun n ω => Real.sqrt (n+1 : ℕ) * (p (n+1) ω - 1/2))
      (gaussianReal 0 (1/4)) := by
    simpa only [p] using SAP.P001d.WH.W2.P.T61_L4.sign_normal_limit_all_sizes μ X hiid hq
  have hq' : AronowAudit.P001.cdf μ (X 0) 0 = 1/2 := hq
  have hpDonor : AronowAudit.P001.CP μ p (1/2) := by
    have hh := AronowAudit.P001.empirical_cdf_consistency μ X hiid 0
    rw [hq'] at hh
    exact hh
  have hp : CP μ p (1/2) := (Bridge.cp_iff μ p (1/2)).2 hpDonor
  let B : ℕ → Set Ω := fun n => {ω | p (n+1) ω ∉ Set.Icc (1/4 : ℝ) (3/4)}
  have hsucc : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hB : Tendsto (fun n => prob μ (B n)) atTop (nhds 0) := by
    have hlim := (hp (1/4) (by norm_num)).comp hsucc
    have hbound (n : ℕ) : prob μ (B n) ≤
        prob μ {ω | (1/4 : ℝ) ≤ dist (p (n+1) ω) (1/2)} := by
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      apply measure_mono
      intro ω hω
      change (1/4 : ℝ) ≤ dist (p (n+1) ω) (1/2)
      rw [Real.dist_eq]
      by_contra h
      have hh := abs_lt.mp (lt_of_not_ge h)
      apply hω
      exact ⟨by linarith, by linarith⟩
    exact squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (Eventually.of_forall hbound) hlim
  apply AronowAudit.P001.Wave1.regular_cd_agree_off μ _ _ B _ ?_ hB hW
  intro n ω hω
  have hg : p (n+1) ω ∈ Set.Icc (1/4 : ℝ) (3/4) := Classical.not_not.mp hω
  have hc : ((Finset.univ.filter
      (fun i : Fin (n+1) => firstSample X (n+1) ω i ≤ 0)).card : ℝ)/((n+1 : ℕ) : ℝ) =
      p (n+1) ω := by
    exact AronowAudit.P001.Wave1.regular_sign_count X (n+1) ω
  have he : wholeEmpiricalCDF (firstSample X (n+1) ω) 0 = p (n+1) ω := by
    simpa only [wholeEmpiricalCDF] using hc
  change Real.sqrt (n+1 : ℕ) *
      wholeRegularStatistic (firstSample X (n+1) ω) =
    Real.sqrt (n+1 : ℕ) * (p (n+1) ω - 1/2)
  simp only [wholeRegularStatistic, regularHeavyFunctional, he, if_pos hg]

end
