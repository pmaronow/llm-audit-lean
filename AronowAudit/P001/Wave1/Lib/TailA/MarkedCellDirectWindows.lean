import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectGeometry
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectPairLimits

/-! Pointwise direct-kernel limits for the actual closer-donor intervals. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectWindows (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem marked_unit_score_ne (q : ℝ) :
    ∀ᵐ u ∂matchingUnitLaw, u.1 ≠ q := by
  have h := MatchingScoreLaw.ae_ne q
  have hmap : ∀ᵐ x ∂matchingUnitLaw.map (fun u : MatchUnit => u.1), x ≠ q := by
    rw [matching_score_marginal.map_eq]
    exact h
  exact ae_of_ae_map measurable_fst.aemeasurable hmap

/-- The right closer-donor interval differs from the half-open interval at
only its upper comparison boundary, which has zero actual score mass. -/
theorem marked_closer_donors_measure_right (p x : ℝ) (hpx : p ≤ x) :
    matchingUnitLaw (markedCloserDonors p x) =
      matchingUnitLaw (markedTypeInterval true p (2*x-p)) := by
  apply measure_congr
  filter_upwards [marked_unit_score_ne (2*x-p)] with u hu
  apply propext
  change (u.2.1 = true ∧ |u.1-x| < |p-x|) ↔
    (p < u.1 ∧ u.1 ≤ 2*x-p) ∧ u.2.1 = true
  rw [marked_closer_right hpx]
  constructor
  · rintro ⟨hr,hlo,hhi⟩
    exact ⟨⟨hlo,hhi.le⟩,hr⟩
  · rintro ⟨⟨hlo,hhi⟩,hr⟩
    exact ⟨hr,hlo,lt_of_le_of_ne hhi hu⟩

theorem marked_closer_donors_measure_left (p x : ℝ) (hxp : x ≤ p) :
    matchingUnitLaw (markedCloserDonors p x) =
      matchingUnitLaw (markedTypeInterval true (2*x-p) p) := by
  apply measure_congr
  filter_upwards [marked_unit_score_ne p] with u hu
  apply propext
  change (u.2.1 = true ∧ |u.1-x| < |p-x|) ↔
    (2*x-p < u.1 ∧ u.1 ≤ p) ∧ u.2.1 = true
  rw [marked_closer_left hxp]
  constructor
  · rintro ⟨hr,hlo,hhi⟩
    exact ⟨⟨hlo,hhi.le⟩,hr⟩
  · rintro ⟨⟨hlo,hhi⟩,hr⟩
    exact ⟨hr,hlo,lt_of_le_of_ne hhi hu⟩

/-- Actual closer-donor mass at a rescaled recipient location.  Both sides
of the pin have the same local rate, with no continuity assertion at ties. -/
theorem marked_closer_donors_rate (p t : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p+t/(m n : ℝ)))) atTop (𝓝 (4*p*|t|)) := by
  by_cases ht : 0 ≤ t
  · have he (n : ℕ) : matchingUnitLaw.real (markedCloserDonors p (p+t/(m n : ℝ))) =
        matchingUnitLaw.real (markedTypeInterval true p (p+(2*t)/(m n : ℝ))) := by
      rw [Measure.real,marked_closer_donors_measure_right p _
        (le_add_of_nonneg_right (div_nonneg ht (Nat.cast_nonneg _)))]
      congr 2
      ring
    have hh := marked_type_interval_rate true p hp m hm 0 (2*t) (by positivity)
    simpa only [he,zero_div,add_zero,sub_zero,markedTypeDensity,ite_true,
      abs_of_nonneg ht,mul_assoc,show (2*t)*(2*p) = 4*p*t by ring] using hh
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have he (n : ℕ) : matchingUnitLaw.real (markedCloserDonors p (p+t/(m n : ℝ))) =
        matchingUnitLaw.real (markedTypeInterval true (p+(2*t)/(m n : ℝ)) p) := by
      rw [Measure.real,marked_closer_donors_measure_left p _
        (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht' (Nat.cast_nonneg _)))]
      congr 2
      ring
    have hh := marked_type_interval_rate true p hp m hm (2*t) 0 (by linarith)
    simpa only [he,zero_div,add_zero,zero_sub,markedTypeDensity,ite_true,
      abs_of_nonpos ht',show -(2*t)*(2*p) = 4*p*(-t) by ring] using hh

/-- Pointwise limits of actual one-recipient kernels, after the recipient's
position and response have been fixed.  The remaining `m n` units are iid. -/
theorem marked_direct_recipient_kernel_limits (p t : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ))) z) k)) atTop
      (𝓝 (Real.exp (-4*p*matchS*|t|))) ∧
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ))) z) k)) atTop
      (𝓝 (matchS*Real.exp (-4*p*matchS*|t|))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  let rate : ℝ≥0 := ⟨4*p*|t|,by positivity⟩
  have hh := marked_direct_single_category_limits m N hm hN
    (fun n => markedCloserDonors p (p+t/(m n : ℝ)))
    (fun n => marked_closer_donors_measurable _ _) rate
    (marked_closer_donors_rate p t hp m hm) k
  have he : -matchS*(rate : ℝ) = -4*p*matchS*|t| := by
    change -matchS*(4*p*|t|) = _
    ring
  simpa only [he] using hh

end AronowAudit.P001.TailA
