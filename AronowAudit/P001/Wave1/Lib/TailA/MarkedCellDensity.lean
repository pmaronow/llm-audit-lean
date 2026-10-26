import AronowAudit.P001.Wave1.Lib.TailA.MatchingLaw
import AronowAudit.P001.Wave1.Lib.TailA.RareCounts

/-! Donor and recipient interval rates of the actual matching design. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDensity (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000

def markedTypeInterval (r : Bool) (a b : ℝ) : Set MatchUnit :=
  {u | u.1 ∈ Set.Ioc a b ∧ u.2.1 = r}

def markedTypeDensity (r : Bool) (p : ℝ) : ℝ := if r then 2*p else 2*(1-p)

theorem marked_type_density_continuous (r : Bool) : Continuous (markedTypeDensity r) := by
  cases r <;> unfold markedTypeDensity <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    <;> fun_prop

theorem marked_type_interval_measurable (r : Bool) (a b : ℝ) :
    MeasurableSet (markedTypeInterval r a b) :=
  (measurableSet_Ioc.preimage measurable_fst).inter
    (measurableSet_eq_fun measurable_snd.fst measurable_const)

theorem marked_type_interval_lintegral (r : Bool) (a b : ℝ)
    (ha : (1/4 : ℝ) ≤ a) (hb : b ≤ (3/4 : ℝ)) :
    matchingUnitLaw (markedTypeInterval r a b) =
      ∫⁻ p in Set.Ioc a b, ENNReal.ofReal (markedTypeDensity r p) := by
  rw [← lintegral_indicator_one (marked_type_interval_measurable r a b)]
  change (∫⁻ u, (markedTypeInterval r a b).indicator
    (fun _ => (1 : ℝ≥0∞)) u ∂matchingUnitLaw) = _
  rw [matching_lintegral _
      (measurable_const.indicator (marked_type_interval_measurable r a b))]
  have heq : (fun p : ℝ =>
      ENNReal.ofReal p *
        ((markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,true,true)+
         (markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,true,false)) +
      ENNReal.ofReal (1-p) *
        ((markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,false,true)+
         (markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,false,false))) =
      (Set.Ioc a b).indicator (fun p => ENNReal.ofReal (markedTypeDensity r p)) := by
    funext p
    by_cases hp : p ∈ Set.Ioc a b
    · simp only [Set.mem_Ioc] at hp
      cases r <;> simp [markedTypeInterval,markedTypeDensity,Set.indicator,hp,
        ENNReal.ofReal_mul] <;> ring
    · simp only [Set.mem_Ioc] at hp
      cases r <;> simp [markedTypeInterval,markedTypeDensity,Set.indicator,hp]
  change (∫⁻ p in Set.Icc (1/4 : ℝ) (3/4),
    (fun p => ENNReal.ofReal p *
        ((markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,true,true)+
         (markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,true,false)) +
      ENNReal.ofReal (1-p) *
        ((markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,false,true)+
         (markedTypeInterval r a b).indicator (fun _ => (1 : ℝ≥0∞)) (p,false,false))) p) = _
  rw [heq,lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  have hsub : Set.Ioc a b ⊆ Set.Icc (1/4 : ℝ) (3/4) := by
    intro p hp
    exact ⟨ha.trans hp.1.le,hp.2.trans hb⟩
  rw [Set.inter_eq_left.mpr hsub]

theorem marked_type_interval_probability (r : Bool) (a b : ℝ)
    (hab : a ≤ b) (ha : (1/4 : ℝ) ≤ a) (hb : b ≤ (3/4 : ℝ)) :
    matchingUnitLaw.real (markedTypeInterval r a b) =
      ∫ p : ℝ in a..b, markedTypeDensity r p := by
  rw [Measure.real,marked_type_interval_lintegral r a b ha hb]
  have hi : IntegrableOn (markedTypeDensity r) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((marked_type_density_continuous r).intervalIntegrable a b)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] markedTypeDensity r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
    have hp0 : 0 ≤ p := by linarith [hp.1]
    have hp1 : p ≤ 1 := by linarith [hp.2]
    cases r <;> simp only [markedTypeDensity,Bool.false_eq_true,ite_false,ite_true]
      <;> positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg),
    intervalIntegral.integral_of_le hab]

/-- The donor mass is exactly `b²-a²` inside the score support. -/
theorem marked_donor_interval_probability (a b : ℝ)
    (hab : a ≤ b) (ha : (1/4 : ℝ) ≤ a) (hb : b ≤ (3/4 : ℝ)) :
    matchingUnitLaw.real (markedTypeInterval true a b) = b^2-a^2 := by
  rw [marked_type_interval_probability true a b hab ha hb]
  simp only [markedTypeDensity,ite_true]
  rw [intervalIntegral.integral_const_mul,integral_id]
  ring


/-- Lower bound used to convert a shrinking interval into an exponential window bound. -/
theorem marked_donor_interval_lower (a b : ℝ)
    (hab : a ≤ b) (ha : (1/4 : ℝ) ≤ a) (hb : b ≤ (3/4 : ℝ)) :
    (b-a)/2 ≤ matchingUnitLaw.real (markedTypeInterval true a b) := by
  rw [marked_donor_interval_probability a b hab ha hb]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a+b-1/2 by linarith)]

/-- Both actual local intensities, at every interior pin. -/
theorem marked_type_interval_rate (r : Bool) (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedTypeInterval r (p+a/(m n : ℝ)) (p+b/(m n : ℝ))))
      atTop (𝓝 ((b-a)*markedTypeDensity r p)) := by
  let δ : ℝ := min (p-1/4) (3/4-p)
  have hδ : 0 < δ := lt_min (by linarith [hp.1]) (by linarith [hp.2])
  let P : Measure ℝ := (matchingUnitLaw.restrict {u : MatchUnit | u.2.1 = r}).map Prod.fst
  have hP : ∀ x y : ℝ, x ∈ Metric.ball p δ → y ∈ Metric.ball p δ → x ≤ y →
      P.real (Set.Ioc x y) = ∫ t in x..y, markedTypeDensity r t := by
    intro x y hx hy hxy
    rw [Metric.mem_ball,Real.dist_eq] at hx hy
    have hxlo : (1/4 : ℝ) ≤ x := by
      have := (abs_lt.mp hx).1
      have := min_le_left (p-1/4) (3/4-p)
      dsimp [δ] at hx
      dsimp [δ] at *
      linarith
    have hyhi : y ≤ (3/4 : ℝ) := by
      have := (abs_lt.mp hy).2
      have := min_le_right (p-1/4) (3/4-p)
      dsimp [δ] at *
      linarith
    have heq : P (Set.Ioc x y) = matchingUnitLaw (markedTypeInterval r x y) := by
      dsimp only [P]
      rw [Measure.map_apply measurable_fst measurableSet_Ioc,
        Measure.restrict_apply (measurableSet_Ioc.preimage measurable_fst)]
      rfl
    simpa only [Measure.real,heq] using
      marked_type_interval_probability r x y hxy hxlo hyhi
  have h := rare_counts_scaled_interval_probability_local m hm P (markedTypeDensity r)
    (marked_type_density_continuous r) p δ hδ hP a b hab
  have heq : ∀ n, P.real (Set.Ioc (p+a/(m n : ℝ)) (p+b/(m n : ℝ))) =
      matchingUnitLaw.real
        (markedTypeInterval r (p+a/(m n : ℝ)) (p+b/(m n : ℝ))) := by
    intro n
    dsimp only [P,Measure.real]
    rw [Measure.map_apply measurable_fst measurableSet_Ioc,
      Measure.restrict_apply (measurableSet_Ioc.preimage measurable_fst)]
    rfl
  change Tendsto (fun n => (m n : ℝ)*P.real
    (Set.Ioc (p+a/(m n : ℝ)) (p+b/(m n : ℝ)))) _ _ at h
  simpa only [heq] using h


end AronowAudit.P001.TailA
