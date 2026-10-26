import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectUnionLimits
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellIntegrals

/-! Uniform exponential position envelopes for the actual finite count kernels.
These estimates permit removal of the whole bounded position window. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectDomination (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- A fixed positive rate that works for both bootstrap sizes `m+2` and `m+3`. -/
def markedDirectDecay : ℝ := (1-Real.exp (-(1/4 : ℝ)))/2

theorem marked_direct_decay_pos : 0 < markedDirectDecay := by
  unfold markedDirectDecay
  have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1/4 : ℝ) < 0)
  linarith

/-- Removing at most three specified draws still gives a uniform exponential
bound at every possible donor count. -/
theorem marked_draw_power_exp_bound (m d c k : ℕ) (hm : 0 < m) (hd : d ≤ 3)
    (hk : k ≤ d) (hc : c ≤ m) :
    markedDrawPower (m+d) c k ≤ Real.exp (-(c : ℝ)/4) := by
  have hN : 0 < m+d := by omega
  have hNR : (0 : ℝ) < m+d := by exact_mod_cast hN
  have hNk : m+d ≤ 4*(m+d-k) := by omega
  have hratio : (1/4 : ℝ) ≤ ((m+d-k : ℕ) : ℝ)/((m+d : ℕ) : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have hh : ((m+d : ℕ) : ℝ) ≤ 4*((m+d-k : ℕ) : ℝ) := by exact_mod_cast hNk
    linarith
  rw [marked_draw_power_of_le hN (by omega) k]
  have hbase : 0 ≤ 1-(c : ℝ)/((m+d : ℕ) : ℝ) :=
    sub_nonneg.mpr ((div_le_one (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast (show c ≤ m+d by omega)))
  have hexp : 1-(c : ℝ)/((m+d : ℕ) : ℝ) ≤ Real.exp (-(c : ℝ)/((m+d : ℕ) : ℝ)) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using
      Real.add_one_le_exp (-(c : ℝ)/((m+d : ℕ) : ℝ))
  calc
    _ ≤ (Real.exp (-(c : ℝ)/((m+d : ℕ) : ℝ)))^(m+d-k) :=
      pow_le_pow_left₀ hbase hexp _
    _ = Real.exp (-(c : ℝ)*(((m+d-k : ℕ) : ℝ)/((m+d : ℕ) : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
      nlinarith)

theorem marked_retained_power_le_draw (N c k : ℕ) :
    markedRetainedDrawPower N c k ≤ markedDrawPower N c k := by
  unfold markedRetainedDrawPower
  linarith [(marked_draw_power_bounds N (c+1) k).1]

/-- A direct iid generating-function bound, with no point-process replacement. -/
theorem marked_exponential_count_bound (m : ℕ) (E : Set MatchUnit)
    (hE : MeasurableSet E) (a : ℝ) (ha : 0 < a) :
    mean (MatchProduct m) (fun z => Real.exp (-a*(markedWindowCount E z : ℝ))) ≤
      Real.exp (-(1-Real.exp (-a))*matchingUnitLaw.real E*(m : ℝ)) := by
  let f : MatchUnit → ℝ := fun u => if u ∈ E then Real.exp (-a) else 1
  have hf : Measurable f := Measurable.ite hE measurable_const measurable_const
  have he (z : Fin m → MatchUnit) : Real.exp (-a*(markedWindowCount E z : ℝ)) =
      ∏ i, f (z i) := by
    calc
      _ = (Real.exp (-a))^(markedWindowCount E z) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ = _ := marked_exp_count_product E z (Real.exp (-a))
  have hpoint : f = fun u => 1-(1-Real.exp (-a))*E.indicator (fun _ => (1 : ℝ)) u := by
    funext u
    by_cases hu : u ∈ E <;> simp [f,hu] <;> ring
  have hi : (∫ u, f u ∂matchingUnitLaw) = 1-(1-Real.exp (-a))*matchingUnitLaw.real E := by
    rw [hpoint,integral_sub (integrable_const _)
      (((integrable_const (1 : ℝ)).indicator hE).const_mul _),
      integral_const_mul,integral_indicator_const _ hE]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,mul_one]
  simp_rw [he]
  change (∫ z : Fin m → MatchUnit, ∏ i, f (z i) ∂Measure.pi (fun _ => matchingUnitLaw)) ≤ _
  rw [integral_fintype_prod_eq_pow,Fintype.card_fin,hi]
  have hbase : 0 ≤ 1-(1-Real.exp (-a))*matchingUnitLaw.real E := by
    rw [← hi]
    exact integral_nonneg (fun u => by dsimp [f]; split_ifs <;> positivity)
  have hexp : 1-(1-Real.exp (-a))*matchingUnitLaw.real E ≤
      Real.exp (-((1-Real.exp (-a))*matchingUnitLaw.real E)) := by
    have hh := Real.add_one_le_exp (-((1-Real.exp (-a))*matchingUnitLaw.real E))
    linarith
  calc
    _ ≤ (Real.exp (-((1-Real.exp (-a))*matchingUnitLaw.real E)))^m :=
      pow_le_pow_left₀ hbase hexp _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Every query on the score support excludes at least the donor interval
between the pin and the query. Its mass is at least half their distance. -/
theorem marked_closer_mass_lower (p x : ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)) (hx : x ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    |x-p|/2 ≤ matchingUnitLaw.real (markedCloserDonors p x) := by
  rcases le_total p x with hpx | hxp
  · rw [abs_of_nonneg (sub_nonneg.mpr hpx)]
    apply (marked_donor_interval_lower p x hpx hp.1 hx.2).trans
    simp only [Measure.real,marked_closer_donors_measure_right p x hpx]
    refine measureReal_mono ?_ (by finiteness)
    intro u hu
    exact ⟨⟨hu.1.1,by linarith [hu.1.2]⟩,hu.2⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr hxp)]
    have hh := marked_donor_interval_lower x p hxp hx.1 hp.2
    have hb : (p-x)/2 ≤ matchingUnitLaw.real (markedCloserDonors p x) := by
      apply hh.trans
      simp only [Measure.real,marked_closer_donors_measure_left p x hxp]
      refine measureReal_mono ?_ (by finiteness)
      intro u hu
      exact ⟨⟨by linarith [hu.1.1],hu.1.2⟩,hu.2⟩
    linarith

/-- The count-generating-function envelope in scaled recipient coordinates. -/
theorem marked_scaled_exponential_count_bound (m : ℕ) (hm : 0 < m) (p t : ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4))
    (ht : p+t/(m : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    mean (MatchProduct m) (fun z => Real.exp
      (-(markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z : ℝ)/4)) ≤
        Real.exp (-markedDirectDecay*|t|) := by
  have hh := marked_exponential_count_bound m (markedCloserDonors p (p+t/(m : ℝ)))
    (marked_closer_donors_measurable _ _) (1/4) (by norm_num)
  have he (z : Fin m → MatchUnit) : -(1/4 : ℝ)*
      (markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z : ℝ) =
        -(markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z : ℝ)/4 := by ring
  simp only [he] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hmass := marked_closer_mass_lower p (p+t/(m : ℝ)) hp ht
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  simp only [add_sub_cancel_left,abs_div,abs_of_pos hmR] at hmass
  have hmass' : |t|/2 ≤ matchingUnitLaw.real (markedCloserDonors p (p+t/(m : ℝ)))*(m : ℝ) := by
    have heq : |t|/(m : ℝ)/2 = (|t|/2)/(m : ℝ) := by ring
    rw [heq] at hmass
    exact (div_le_iff₀ hmR).mp hmass
  have hs : 0 ≤ 1-Real.exp (-(1/4 : ℝ)) := by
    have := marked_direct_decay_pos
    dsimp [markedDirectDecay] at this
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmass' hs
  dsimp [markedDirectDecay]
  nlinarith

/-- The actual finite score density is nonnegative. -/
theorem marked_scaled_recipient_density_nonneg (m : ℕ) (p t : ℝ) :
    0 ≤ markedScaledRecipientDensity m p t := by
  unfold markedScaledRecipientDensity
  split_ifs with h
  · linarith [h.2]
  · exact le_rfl

/-- An integrable envelope on the whole position line. -/
theorem marked_integrable_exp_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-c*|t|)) := by
  have hleft : IntegrableOn (fun t : ℝ => Real.exp (-c*|t|)) (Set.Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro t ht
    change Real.exp (c*t) = Real.exp (-c*|t|)
    rw [abs_of_nonpos ht]
    congr 1
    ring
  have hright : IntegrableOn (fun t : ℝ => Real.exp (-c*|t|)) (Set.Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0).congr_fun _ measurableSet_Ioi
    intro t ht
    change Real.exp (-c*t) = Real.exp (-c*|t|)
    rw [abs_of_nonneg ht.le]
  rw [← integrableOn_univ,← (Set.Iic_union_Ioi (a := (0 : ℝ)))]
  exact hleft.union hright

end AronowAudit.P001.TailA
