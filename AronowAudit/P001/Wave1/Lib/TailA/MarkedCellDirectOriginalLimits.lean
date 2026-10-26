import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectTruncated

/-! Limits of the original, unresampled donor-avoidance kernels, including
one-recipient queries in scaled coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectOriginalLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Original donor avoidance is the zero-count test of the actual rare law. -/
theorem marked_direct_original_category_limit
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (E : ℕ → Set MatchUnit) (hE : ∀ n, MeasurableSet (E n)) (rate : ℝ≥0)
    (hrate : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n)) atTop
      (𝓝 (rate : ℝ))) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      if markedWindowCount (E n) z = 0 then 1 else 0)) atTop
      (𝓝 (Real.exp (-(rate : ℝ)))) := by
  let X : (n : ℕ) → (Fin (m n) → MatchUnit) → Fin 1 → ℕ :=
    fun n z _ => markedWindowCount (E n) z
  let rates : Fin 1 → ℝ≥0 := fun _ => rate
  have hw := rare_partition_counts 1 m hm (fun _ => matchingUnitLaw)
    (fun _ => inferInstance) (fun n _ => E n) (fun n _ => hE n)
    (fun n i j hij => False.elim (hij (Subsingleton.elim i j))) rates (fun _ => hrate)
  have hpow (c : ℕ) : (0 : ℝ)^c = if c = 0 then 1 else 0 := by
    by_cases hc : c = 0 <;> simp [hc]
  have hb (v : Fin 1 → ℕ) : |(0 : ℝ)^(v 0)| ≤ 1 := by
    rw [hpow]
    split_ifs <;> norm_num
  have ht := hw (fun v => (0 : ℝ)^(v 0)) continuous_of_discreteTopology ⟨1,hb⟩
  have he : (∫ v : Fin 1 → ℕ, (0 : ℝ)^(v 0)
      ∂Measure.pi (fun i => poissonMeasure (rates i))) = Real.exp (-(rate : ℝ)) := by
    simpa only [Fin.prod_univ_one,Fin.sum_univ_one,rates,zero_sub,mul_neg_one]
      using marked_poisson_product_power_integral 1 rates (fun _ => 0)
  rw [he] at ht
  convert ht using 1
  funext n
  apply integral_congr_ae
  apply ae_of_all
  intro z
  beta_reduce
  rw [hpow]
  congr! 2

/-- The original one-recipient void limit at an actual scaled query. -/
theorem marked_direct_original_recipient_kernel_limit (p t : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      if markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ))) z = 0 then 1 else 0))
      atTop (𝓝 (Real.exp (-4*p*|t|))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  let rate : ℝ≥0 := ⟨4*p*|t|,by positivity⟩
  have hh := marked_direct_original_category_limit m hm
    (fun n => markedCloserDonors p (p+t/(m n : ℝ)))
    (fun _ => marked_closer_donors_measurable _ _) rate
    (marked_closer_donors_rate p t hp m hm)
  have he : -(rate : ℝ) = -4*p*|t| := by change -(4*p*|t|) = _; ring
  simpa only [he] using hh


end AronowAudit.P001.TailA
