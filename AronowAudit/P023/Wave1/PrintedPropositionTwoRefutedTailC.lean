import AronowAudit.P023.Wave1.Lib.ContinuousBadMeanTailC
import Mathlib.Probability.Independence.InfinitePi

/-! Refutation of the complete printed universal proposition, with every sampling premise supplied. -/
namespace AronowAudit.P023.Wave1
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology
local instance tc10_refutation_decidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance tc10_refutation_uniform_probability : IsProbabilityMeasure uniformMargins :=
  ⟨uniform_law_normalized.1⟩

/-- Both outcome branches have finite second moments under the actual witness law. -/
theorem tc10_witness_second_moment (h : ℝ → ℝ) (hc : Continuous h) :
    Integrable (fun z => z.2^2) (witnessLaw uniformMargins h) := by
  apply (GP023B1b_integrable_witness_iff uniformMargins hc.measurable (measurable_snd.pow_const 2)).mpr
  constructor <;>
    exact tc04_supported_continuous_integrable uniformMargins uniform_law_normalized.2 _
      (((continuous_const.add hc).add continuous_const).pow 2).continuousOn

/-- Independent symmetric noise has zero conditional mean for every bounded measurable test. -/
theorem tc10_witness_conditional_mean (h : ℝ → ℝ) (hc : Continuous h) :
    ConditionalMean (witnessLaw uniformMargins h) (fun x => 1/2+h x) := by
  let m : ℝ → ℝ := fun x => 1/2+h x
  have hm : Continuous m := continuous_const.add hc
  have hbranch (u : ℝ) : Integrable (fun x => m x+u) uniformMargins :=
    tc04_supported_continuous_integrable uniformMargins uniform_law_normalized.2 _
      (hm.add continuous_const).continuousOn
  have hiY : Integrable (fun z : ℝ × ℝ => z.2) (witnessLaw uniformMargins h) :=
    (GP023B1b_integrable_witness_iff uniformMargins hc.measurable measurable_snd).mpr
      ⟨hbranch _,hbranch _⟩
  have hiM : Integrable (fun z : ℝ × ℝ => m z.1) (witnessLaw uniformMargins h) := by
    apply (GP023B1b_integrable_witness_iff uniformMargins hc.measurable
      (hm.measurable.comp measurable_fst)).mpr
    constructor <;> exact tc04_supported_continuous_integrable uniformMargins uniform_law_normalized.2 _ hm.continuousOn
  refine ⟨hiY,hiM,?_⟩
  rintro t ht ⟨B,hB⟩
  have hiTY := hiY.bdd_mul (ht.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.1))
  have hiTM := hiM.bdd_mul (ht.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.1))
  have hbminus := (hbranch (-1/10)).bdd_mul ht.aestronglyMeasurable (ae_of_all _ hB)
  have hbplus := (hbranch (1/10)).bdd_mul ht.aestronglyMeasurable (ae_of_all _ hB)
  change (∫ z : ℝ × ℝ, t z.1*z.2 ∂witnessLaw uniformMargins h) =
    ∫ z : ℝ × ℝ, t z.1*m z.1 ∂witnessLaw uniformMargins h
  rw [GP023B1b_integral_witness uniformMargins hc.measurable
    (g := fun z : ℝ × ℝ => t z.1*z.2) ((ht.comp measurable_fst).mul measurable_snd) hiTY,
    GP023B1b_integral_witness uniformMargins hc.measurable
      (g := fun z : ℝ × ℝ => t z.1*m z.1) ((ht.comp measurable_fst).mul (hm.measurable.comp measurable_fst)) hiTM]
  change (1/2:ℝ)*(∫ x, t x*(m x+(-1/10)) ∂uniformMargins) +
    (1/2:ℝ)*(∫ x, t x*(m x+(1/10)) ∂uniformMargins) =
    (1/2:ℝ)*(∫ x, t x*m x ∂uniformMargins)+(1/2:ℝ)*(∫ x, t x*m x ∂uniformMargins)
  rw [← mul_add, ← integral_add hbminus hbplus]
  rw [show (fun x => t x*(m x+(-1/10))+t x*(m x+(1/10))) =
    (fun x => 2*(t x*m x)) from funext (fun x => by ring), integral_const_mul]
  ring

/-- The local conditional variance is exactly 1/100, for every Borel margin set. -/
theorem tc10_witness_variance (h : ℝ → ℝ) (hc : Continuous h)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ z in {z : ℝ × ℝ | z.1 ∈ A}, (z.2-(1/2+h z.1))^2 ∂witnessLaw uniformMargins h) =
      (1/100:ℝ)*(uniformMargins A).toReal := by
  let S : Set (ℝ × ℝ) := {z | z.1 ∈ A}
  have hS : MeasurableSet S := hA.preimage measurable_fst
  let F : ℝ × ℝ → ℝ := S.indicator (fun z => (z.2-(1/2+h z.1))^2)
  have hF : Measurable F :=
    ((measurable_snd.sub (measurable_const.add (hc.measurable.comp measurable_fst))).pow_const 2).indicator hS
  have he (u : ℝ) : (fun x => F (x,1/2+h x+u)) = A.indicator (fun _ => u^2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [F,S,hx]
  have hi : Integrable F (witnessLaw uniformMargins h) := by
    apply (GP023B1b_integrable_witness_iff uniformMargins hc.measurable hF).mpr
    constructor <;> rw [he] <;> exact (integrable_const _).indicator hA
  rw [← integral_indicator hS]
  change (∫ z, F z ∂witnessLaw uniformMargins h) = _
  rw [GP023B1b_integral_witness uniformMargins hc.measurable hF hi, he, he,
    integral_indicator hA, integral_indicator hA]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  ring

universe u

/-- A countable iid sample in any universe, using lifted outcome coordinates. -/
theorem tc10_iid_exists (ν : Measure (ℝ × ℝ)) (hp : ProbabilityLaw ν) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ sample : ℕ → Ω → ℝ × ℝ, IIDSample P ν sample := by
  letI tc10_nu_probability : IsProbabilityMeasure ν := ⟨hp⟩
  let νu : Measure (ULift.{u} (ℝ × ℝ)) := ν.map ULift.up
  letI tc10_nuu_probability : IsProbabilityMeasure νu := by dsimp [νu]; infer_instance
  let P : Measure (ℕ → ULift.{u} (ℝ × ℝ)) := Measure.infinitePi (fun _ : ℕ => νu)
  let sample : ℕ → (ℕ → ULift.{u} (ℝ × ℝ)) → ℝ × ℝ := fun i ω => (ω i).down
  refine ⟨_,inferInstance,P,sample,?_,?_,?_,?_⟩
  · exact measure_univ
  · intro i
    exact measurable_down.comp (measurable_pi_apply i)
  · intro i
    change P.map (ULift.down ∘ Function.eval i) = ν
    rw [← Measure.map_map measurable_down (measurable_pi_apply i), Measure.infinitePi_map_eval]
    change (ν.map ULift.up).map ULift.down = ν
    rw [Measure.map_map measurable_down measurable_up]
    exact Measure.map_id
  · exact iIndepFun_infinitePi (fun _ : ℕ => measurable_down)

/-- The concrete positive bandwidth 1/sqrt(N+1). -/
def tc10_bandwidth (N : ℕ) : ℝ := 1 / Real.sqrt ((N:ℝ)+1)

theorem tc10_bandwidth_pos (N : ℕ) : 0 < tc10_bandwidth N := by
  dsimp [tc10_bandwidth]
  positivity

theorem tc10_bandwidth_le_one (N : ℕ) : tc10_bandwidth N ≤ 1 := by
  dsimp [tc10_bandwidth]
  have hs : (1:ℝ) ≤ Real.sqrt ((N:ℝ)+1) :=
    Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hs

theorem tc10_sqrt_top : Tendsto (fun N : ℕ => Real.sqrt ((N:ℝ)+1)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

theorem tc10_bandwidth_zero : Tendsto tc10_bandwidth atTop (nhds 0) := by
  change Tendsto (fun N : ℕ => 1 / Real.sqrt ((N:ℝ)+1)) atTop (nhds 0)
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tc10_sqrt_top

theorem tc10_bandwidth_counts : Tendsto (fun N : ℕ => (N:ℝ)*tc10_bandwidth N) atTop atTop := by
  have hlow := tc10_sqrt_top.atTop_mul_const (by norm_num : (0:ℝ) < 1/2)
  apply tendsto_atTop_mono' atTop _ hlow
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs := Real.sq_sqrt (show 0 ≤ (N:ℝ)+1 by positivity)
  have hp : 0 < Real.sqrt ((N:ℝ)+1) := by positivity
  change Real.sqrt ((N:ℝ)+1)*(1/2) ≤ (N:ℝ)*(1 / Real.sqrt ((N:ℝ)+1))
  simp only [mul_one_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith [hs]

/-- All of the printed RD assumptions, including both divergent expected window counts. -/
theorem tc10_witness_rd (h : ℝ → ℝ) (hc : Continuous h) :
    UsualRDRegularity (witnessLaw uniformMargins h) (fun x => 1/2+h x) tc10_bandwidth := by
  have hm := GP023B1b_witness_margin uniformMargins hc.measurable
  refine ⟨?_,?_,?_,1,1/100,by norm_num,by norm_num,?_⟩
  · rw [hm]
    simp [uniformMargins, Measure.smul_apply]
  · simp_rw [hm, (GP023B1b_uniform_window _ (tc10_bandwidth_pos _) (tc10_bandwidth_le_one _)).1]
    have he : (fun N : ℕ => (N:ℝ)*(tc10_bandwidth N/2)) =
        (fun N : ℕ => ((N:ℝ)*tc10_bandwidth N)*(1/2)) := funext (fun N => by ring)
    rw [he]
    exact tc10_bandwidth_counts.atTop_mul_const (by norm_num : (0:ℝ) < 1/2)
  · simp_rw [hm, (GP023B1b_uniform_window _ (tc10_bandwidth_pos _) (tc10_bandwidth_le_one _)).2]
    have he : (fun N : ℕ => (N:ℝ)*(tc10_bandwidth N/2)) =
        (fun N : ℕ => ((N:ℝ)*tc10_bandwidth N)*(1/2)) := funext (fun N => by ring)
    rw [he]
    exact tc10_bandwidth_counts.atTop_mul_const (by norm_num : (0:ℝ) < 1/2)
  · intro A hA _
    rw [tc10_witness_variance h hc A hA,hm]

/-- Every open subinterval of the full margin support has positive mass. -/
theorem tc10_uniform_open_positive (a b : ℝ) (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < uniformMargins (Ioo a b) := by
  have hs : Ioo a b ⊆ Icc (-1:ℝ) 1 := fun x hx => ⟨ha.trans hx.1.le,hx.2.le.trans hb⟩
  rw [uniformMargins, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr hs, Real.volume_Ioo, smul_eq_mul]
  exact ENNReal.mul_pos_iff.mpr ⟨by norm_num, ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)⟩

/-- Negation of printed Proposition 2, with the same universe parameter. -/
theorem printed_proposition2_refuted : ¬ ((∀ {Ω : Type u}
      [MeasurableSpace Ω]
      (P : Measure Ω)
      (ν : Measure (ℝ × ℝ))
      (sample : ℕ → Ω → ℝ × ℝ)
      (g f : ℝ → ℝ)
      (α : ℝ)
      (hprob : ProbabilityLaw ν)
      (hsupport : MarginSupport (marginLaw ν))
      (hsq : Integrable (fun z => z.2^2) ν)
      (hg : ContinuousOn g (Set.Ico (-1) 0))
      (hf : ContinuousOn f (Set.Icc 0 1))
      (hleft : Tendsto g (nhdsWithin 0 (Set.Iio 0)) (nhds α))
      (hmean : ConditionalMean ν (appendixMean g f))
      (hiid : IIDSample P ν sample)
      (hpd : ∀ J, 1 ≤ J → MomentPositiveDefinite (marginLaw ν) J)
      (k : ℕ → ℝ)
      (hkpos : ∀ N, 0 < k N)
      (hk0 : Tendsto k atTop (nhds 0))
      (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop)
      (hsup : ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ a b : ℝ, -k₀ ≤ a → a < b → b ≤ k₀ → 0 < marginLaw ν (Set.Ioo a b))
      (hRD : UsualRDRegularity ν (appendixMean g f) k),
      ConvergesInProbability P (sampleRD sample k) (f 0 - α) ∧
    ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω)
        (populationCoefficient (marginLaw ν) J (appendixMean g f) - (f 0 - α)) ∧
      |populationCoefficient (marginLaw ν) J (appendixMean g f) - (f 0 - α)| < ε)) := by
  intro H
  obtain ⟨h,degrees,hc,h0,hb,hmono,hgrow,hfwl⟩ := fixed_bad_mean_unconditional
  let ν := witnessLaw uniformMargins h
  have hp : ProbabilityLaw ν := GP023B1b_witness_probability uniformMargins uniform_law_normalized.1 hc.measurable
  have hm : marginLaw ν = uniformMargins := GP023B1b_witness_margin uniformMargins hc.measurable
  obtain ⟨Ω,mΩ,P,sample,hiid⟩ := tc10_iid_exists.{u} ν hp
  letI tc10_sample_measurableSpace : MeasurableSpace Ω := mΩ
  let m : ℝ → ℝ := fun x => 1/2+h x
  have hcM : Continuous m := continuous_const.add hc
  have happ : appendixMean m m = m := by funext x; simp [appendixMean]
  have hleft : Tendsto m (nhdsWithin 0 (Iio 0)) (nhds (1/2)) := by
    simpa [m,h0] using (hcM.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsupport : MarginSupport (marginLaw ν) := by rw [hm]; exact uniform_law_normalized.2
  have hmean : ConditionalMean ν (appendixMean m m) := by
    rw [happ]
    exact tc10_witness_conditional_mean h hc
  have hpd : ∀ J, 1 ≤ J → MomentPositiveDefinite (marginLaw ν) J := by
    intro J _
    rw [hm]
    exact uniform_full_rank J
  have hsup : ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ a b : ℝ, -k₀ ≤ a → a < b → b ≤ k₀ →
      0 < marginLaw ν (Ioo a b) := by
    refine ⟨1,by norm_num,?_⟩
    intro a b ha hab hb
    rw [hm]
    exact tc10_uniform_open_positive a b ha hab hb
  have hRD : UsualRDRegularity ν (appendixMean m m) tc10_bandwidth := by
    rw [happ]
    exact tc10_witness_rd h hc
  have hcon := @H Ω mΩ P ν sample m m (1/2) hp hsupport (tc10_witness_second_moment h hc)
    hcM.continuousOn hcM.continuousOn hleft hmean hiid hpd tc10_bandwidth tc10_bandwidth_pos
    tc10_bandwidth_zero tc10_bandwidth_counts hsup hRD
  obtain ⟨J₀,hJ₀⟩ := hcon.2 1 (by norm_num)
  let index : ℕ := max (J₀+1) 8
  have hi : 1 ≤ index := by dsimp [index]; omega
  have hd : index ≤ degrees index := hmono.id_le index
  have hdeg : 1 ≤ degrees index := hi.trans hd
  have hge : J₀ ≤ degrees index := (Nat.le_succ J₀).trans ((le_max_left (J₀+1) 8).trans hd)
  have hsmall := (hJ₀ (degrees index) hge hdeg).2
  rw [hm,happ] at hsmall
  have hm0 : m 0-(1/2:ℝ)=0 := by dsimp [m]; rw [h0]; ring
  rw [hm0,sub_zero,hfwl _ hdeg] at hsmall
  have hlarge := hgrow index hi
  have hi8 : 8 ≤ index := le_max_right _ _
  have hi8r : (8:ℝ) ≤ index := by exact_mod_cast hi8
  have habs := le_abs_self (biasFunctional uniformMargins (degrees index) h)
  linarith

end
end AronowAudit.P023.Wave1
