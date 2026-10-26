import AronowAudit.P018.Wave1.Gap.TailBSignPopulation

/-! Tight sign sums and the second-order remainder in probability. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
local instance tb05_probability_unit : IsProbabilityMeasure signPairKernel.μ := tb05_standing.1

theorem tb05_sum_second (f : Bool × Bool → ℝ)
    (hf0 : (∫ u,f u ∂signPairKernel.μ)=0) (hf2 : (∫ u,f u^2 ∂signPairKernel.μ)=1) (N : ℕ) :
    (∫ ω : Fin N → Bool × Bool,(∑ i,f (ω i))^2 ∂unitSampleLaw signPairKernel N)=(N:ℝ) := by
  have hvar : variance f signPairKernel.μ=1 := by
    rw [variance_eq_sub (printed_finite_L2 _ f)]
    simpa only [Pi.pow_apply,hf0,hf2,zero_pow (by decide : 2 ≠ 0),sub_zero]
  have hm : (∫ ω : Fin N → Bool × Bool,(∑ i,f (ω i)) ∂unitSampleLaw signPairKernel N)=0 := by
    rw [integral_finsetSum _ (fun i _ => printed_finite_integrable _ _)]
    have hi (i : Fin N) : (∫ ω : Fin N → Bool × Bool,f (ω i) ∂unitSampleLaw signPairKernel N)=0 := by
      exact (GP0182B2b_integral_comp_measurePreserving _
        (measurePreserving_eval (fun _ : Fin N => signPairKernel.μ) i) f
        (measurable_of_countable _)).trans hf0
    simp only [hi,Finset.sum_const_zero]
  have hv := variance_sum_pi (μ := fun _ : Fin N => signPairKernel.μ)
    (X := fun _ => f) (fun _ => printed_finite_L2 _ f)
  have he : (∑ i : Fin N,(fun ω : Fin N → Bool × Bool => f (ω i))) =
      fun ω => ∑ i,f (ω i) := by ext ω; simp only [Finset.sum_apply]
  rw [he] at hv
  change variance (fun ω : Fin N → Bool × Bool => ∑ i,f (ω i))
    (unitSampleLaw signPairKernel N)=_ at hv
  rw [variance_eq_sub (printed_finite_L2 _ _)] at hv
  simpa only [Pi.pow_apply,hm,hvar,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,zero_pow (by decide : 2 ≠ 0),sub_zero] using hv

theorem tb05_normalized_sum_second (f : Bool × Bool → ℝ)
    (hf0 : (∫ u,f u ∂signPairKernel.μ)=0) (hf2 : (∫ u,f u^2 ∂signPairKernel.μ)=1)
    {N : ℕ} (hN : 0 < N) :
    (∫ ω : Fin N → Bool × Bool,((∑ i,f (ω i))/Real.sqrt N)^2
      ∂unitSampleLaw signPairKernel N)=1 := by
  have he : (fun ω : Fin N → Bool × Bool => ((∑ i,f (ω i))/Real.sqrt N)^2) =
      fun ω => (Real.sqrt N)⁻¹^2*(∑ i,f (ω i))^2 := by ext ω; ring
  rw [he,integral_const_mul,tb05_sum_second f hf0 hf2 N,inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N)]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [hn]

theorem tb05_scalar_sign_tail (f : Bool × Bool → ℝ)
    (hf0 : (∫ u,f u ∂signPairKernel.μ)=0) (hf2 : (∫ u,f u^2 ∂signPairKernel.μ)=1)
    {N : ℕ} (hN : 0 < N) (R : ℝ) (hR : 0 < R) :
    (unitSampleLaw signPairKernel N {ω | R < |(∑ i,f (ω i))/Real.sqrt N|}).toReal ≤ 1/R^2 := by
  have h := GP0182B2b_square_probability (unitSampleLaw signPairKernel N)
    (fun ω => (∑ i,f (ω i))/Real.sqrt N) (printed_finite_L2 _ _) R hR
  rw [tb05_normalized_sum_second f hf0 hf2 hN] at h
  apply le_trans _ h
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  change R < |(∑ i,f (ω i))/Real.sqrt N| at hω
  simpa only [Real.norm_eq_abs,Set.mem_setOf_eq] using hω.le

def tb05_badBox (N : ℕ) (R : ℝ) : Set (Fin N → Bool × Bool) :=
  {ω | R < |(∑ i,tb05_z ω i)/Real.sqrt N| ∨
    R < |(∑ i,tb05_w ω i)/Real.sqrt N| ∨
    R < |(∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N|}

theorem tb05_box_probability {N : ℕ} (hN : 0 < N) (R : ℝ) (hR : 0 < R) :
    (unitSampleLaw signPairKernel N (tb05_badBox N R)).toReal ≤ 3/R^2 := by
  have hm0 (f : Bool × Bool → ℝ) : (∫ u,f u ∂signPairKernel.μ)=tb05_average f := tb05_unit_integral f
  have hz := tb05_scalar_sign_tail (fun u => signValue u.1)
    (by rw [hm0]; norm_num [tb05_average,signValue])
    (by rw [hm0]; norm_num [tb05_average,signValue]) hN R hR
  have hw := tb05_scalar_sign_tail (fun u => signValue u.2)
    (by rw [hm0]; norm_num [tb05_average,signValue])
    (by rw [hm0]; norm_num [tb05_average,signValue]) hN R hR
  have hzw := tb05_scalar_sign_tail (fun u => signValue u.1*signValue u.2)
    (by rw [hm0]; norm_num [tb05_average,signValue])
    (by rw [hm0]; norm_num [tb05_average,signValue]) hN R hR
  let A : Set (Fin N → Bool × Bool) := {ω | R < |(∑ i,tb05_z ω i)/Real.sqrt N|}
  let B : Set (Fin N → Bool × Bool) := {ω | R < |(∑ i,tb05_w ω i)/Real.sqrt N|}
  let C : Set (Fin N → Bool × Bool) := {ω | R < |(∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N|}
  change (unitSampleLaw signPairKernel N (A ∪ (B ∪ C))).toReal ≤ _
  have hu := WeightedConsistency.probability_union_bound (unitSampleLaw signPairKernel) N A (B ∪ C)
  have hv := WeightedConsistency.probability_union_bound (unitSampleLaw signPairKernel) N B C
  change (unitSampleLaw signPairKernel N A).toReal ≤ 1/R^2 at hz
  change (unitSampleLaw signPairKernel N B).toReal ≤ 1/R^2 at hw
  change (unitSampleLaw signPairKernel N C).toReal ≤ 1/R^2 at hzw
  calc
    _ ≤ (unitSampleLaw signPairKernel N A).toReal+
        (unitSampleLaw signPairKernel N B).toReal+(unitSampleLaw signPairKernel N C).toReal := by linarith
    _ ≤ 1/R^2+1/R^2+1/R^2 := by linarith
    _ = 3/R^2 := by ring

def tb05_secondOrderError (N : ℕ) (ω : Fin N → Bool × Bool) : ℝ :=
  (N:ℝ)^2*sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1-
    4*(((∑ i,tb05_z ω i)/Real.sqrt N)^2+((∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N)^2-1)

theorem tb05_second_order_in_probability :
    inProbability (unitSampleLaw signPairKernel) tb05_secondOrderError := by
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let R := 3/δ+1
  have hR1 : 1 < R := by
    have hp : (0:ℝ) < 3/δ := by positivity
    dsimp [R]
    linarith
  have hR : 0 < R := by linarith
  have hδR : δ*R=3+δ := by dsimp [R]; field_simp <;> ring
  have htail : 3/R^2 < δ := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).2
    have hp := mul_pos (mul_pos hδ hR) (sub_pos.2 hR1)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := tb05_model_second_order_eventual R hR.le
  have hi : Tendsto (fun N : ℕ => C/Real.sqrt N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
  filter_upwards [hbound,hi.eventually (gt_mem_nhds hε),eventually_ge_atTop 1] with N hb hs hN
  have hsub : {ω | ε ≤ ‖tb05_secondOrderError N ω‖} ⊆ tb05_badBox N R := by
    intro ω hω
    by_contra hn
    have hg : |(∑ i,tb05_z ω i)/Real.sqrt N| ≤ R ∧
        |(∑ i,tb05_w ω i)/Real.sqrt N| ≤ R ∧
        |(∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N| ≤ R := by
      simpa only [tb05_badBox,Set.mem_setOf_eq,not_or,not_lt] using hn
    have he := hb ω hg.1 hg.2.1 hg.2.2
    change ε ≤ |tb05_secondOrderError N ω| at hω
    dsimp [tb05_secondOrderError] at hω
    linarith
  have hp : (unitSampleLaw signPairKernel N {ω | ε ≤ ‖tb05_secondOrderError N ω‖}).toReal < δ := by
    calc
      _ ≤ (unitSampleLaw signPairKernel N (tb05_badBox N R)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ 3/R^2 := tb05_box_probability (by omega) R hR
      _ < δ := htail
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg] using hp

end AronowAudit.P018.Wave1.TailBSign
