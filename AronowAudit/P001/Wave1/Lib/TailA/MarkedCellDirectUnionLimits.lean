import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectDisintegration
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectOriginalLimits
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectTwoWindows

/-! Actual union forbidden-set kernels for two recipients in one cell. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectUnionLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- The signed length of the union in one-recipient coordinates. -/
def markedDirectionalSpan (t u : ℝ) : ℝ := |t|+|u|-markedDirectionalOverlap t u

theorem marked_directional_span_nonneg (t u : ℝ) : 0 ≤ markedDirectionalSpan t u := by
  by_cases ht : 0 ≤ t <;> by_cases hu : 0 ≤ u
  · simp only [markedDirectionalSpan,markedDirectionalOverlap,max_eq_left ht,max_eq_left hu,
      max_eq_right (neg_nonpos.mpr ht),max_eq_right (neg_nonpos.mpr hu),min_self,add_zero,
      abs_of_nonneg ht,abs_of_nonneg hu]
    linarith [min_le_left t u]
  · have hu' := le_of_not_ge hu
    simp only [markedDirectionalSpan,markedDirectionalOverlap,max_eq_left ht,max_eq_right hu',
      max_eq_right (neg_nonpos.mpr ht),max_eq_left (neg_nonneg.mpr hu'),
      min_eq_right ht,min_eq_left (neg_nonneg.mpr hu'),add_zero,sub_zero,
      abs_of_nonneg ht,abs_of_nonpos hu']
    linarith
  · have ht' := le_of_not_ge ht
    simp only [markedDirectionalSpan,markedDirectionalOverlap,max_eq_right ht',max_eq_left hu,
      max_eq_left (neg_nonneg.mpr ht'),max_eq_right (neg_nonpos.mpr hu),
      min_eq_left hu,min_eq_right (neg_nonneg.mpr ht'),add_zero,sub_zero,
      abs_of_nonpos ht',abs_of_nonneg hu]
    linarith
  · have ht' := le_of_not_ge ht
    have hu' := le_of_not_ge hu
    simp only [markedDirectionalSpan,markedDirectionalOverlap,max_eq_right ht',max_eq_right hu',
      max_eq_left (neg_nonneg.mpr ht'),max_eq_left (neg_nonneg.mpr hu'),min_self,zero_add,
      abs_of_nonpos ht',abs_of_nonpos hu']
    linarith [min_le_left (-t) (-u)]

/-- The union mass has the rate of the larger window on each side of the pin.
Opposite sides are disjoint; same-side windows are nested. -/
theorem marked_closer_union_rate (p t u : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p+t/(m n : ℝ)) ∪ markedCloserDonors p (p+u/(m n : ℝ))))
      atTop (𝓝 (4*p*markedDirectionalSpan t u)) := by
  let E : ℝ → ℕ → Set MatchUnit := fun a n => markedCloserDonors p (p+a/(m n : ℝ))
  have hright (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E a n ∪ E b n)) atTop
        (𝓝 (4*p*(a+b-min a b))) := by
    rcases le_total a b with hab | hba
    · have he (n : ℕ) : E a n ∪ E b n = E b n := Set.union_eq_right.mpr
        (marked_closer_donors_nested_right
          (le_add_of_nonneg_right (div_nonneg ha (Nat.cast_nonneg _)))
          (add_le_add (le_refl p) (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))))
      simpa only [he,abs_of_nonneg hb,min_eq_left hab,show a+b-a = b by ring,E] using
        marked_closer_donors_rate p b hp m hm
    · have he (n : ℕ) : E a n ∪ E b n = E a n := Set.union_eq_left.mpr
        (marked_closer_donors_nested_right
          (le_add_of_nonneg_right (div_nonneg hb (Nat.cast_nonneg _)))
          (add_le_add (le_refl p) (div_le_div_of_nonneg_right hba (Nat.cast_nonneg _))))
      simpa only [he,abs_of_nonneg ha,min_eq_right hba,add_sub_cancel_right,E] using
        marked_closer_donors_rate p a hp m hm
  have hleft (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E (-a) n ∪ E (-b) n)) atTop
        (𝓝 (4*p*(a+b-min a b))) := by
    rcases le_total a b with hab | hba
    · have he (n : ℕ) : E (-a) n ∪ E (-b) n = E (-b) n := Set.union_eq_right.mpr
        (marked_closer_donors_nested_left
          (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _)))
          (add_le_add (le_refl p) (div_le_div_of_nonneg_right (neg_le_neg hab) (Nat.cast_nonneg _))))
      simpa only [he,abs_neg,abs_of_nonneg hb,min_eq_left hab,show a+b-a = b by ring,E] using
        marked_closer_donors_rate p (-b) hp m hm
    · have he (n : ℕ) : E (-a) n ∪ E (-b) n = E (-a) n := Set.union_eq_left.mpr
        (marked_closer_donors_nested_left
          (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (Nat.cast_nonneg _)))
          (add_le_add (le_refl p) (div_le_div_of_nonneg_right (neg_le_neg hba) (Nat.cast_nonneg _))))
      simpa only [he,abs_neg,abs_of_nonneg ha,min_eq_right hba,add_sub_cancel_right,E] using
        marked_closer_donors_rate p (-a) hp m hm
  have hopp (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b) :
      Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E a n ∪ E b n)) atTop
        (𝓝 (4*p*(-a+b))) := by
    have hd (n : ℕ) : Disjoint (E a n) (E b n) :=
      marked_closer_donors_opposite
        (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)))
        (le_add_of_nonneg_right (div_nonneg hb (Nat.cast_nonneg _)))
    have he (n : ℕ) : matchingUnitLaw.real (E a n ∪ E b n) =
        matchingUnitLaw.real (E a n)+matchingUnitLaw.real (E b n) :=
      measureReal_union (hd n) (marked_closer_donors_measurable _ _)
    simpa only [he,mul_add,abs_of_nonpos ha,abs_of_nonneg hb,E] using
      (marked_closer_donors_rate p a hp m hm).add (marked_closer_donors_rate p b hp m hm)
  by_cases ht : 0 ≤ t
  · by_cases hu : 0 ≤ u
    · simpa only [markedDirectionalSpan,markedDirectionalOverlap,max_eq_left ht,max_eq_left hu,
        max_eq_right (neg_nonpos.mpr ht),max_eq_right (neg_nonpos.mpr hu),min_self,add_zero,
        abs_of_nonneg ht,abs_of_nonneg hu] using hright t u ht hu
    · have hu' := le_of_not_ge hu
      have hh := hopp u t hu' ht
      simpa only [E,Set.union_comm,markedDirectionalSpan,markedDirectionalOverlap,max_eq_left ht,
        max_eq_right hu',max_eq_right (neg_nonpos.mpr ht),max_eq_left (neg_nonneg.mpr hu'),
        min_eq_right ht,min_eq_left (neg_nonneg.mpr hu'),add_zero,sub_zero,
        abs_of_nonneg ht,abs_of_nonpos hu',add_comm t (-u)] using hh
  · have ht' := le_of_not_ge ht
    by_cases hu : 0 ≤ u
    · simpa only [markedDirectionalSpan,markedDirectionalOverlap,max_eq_right ht',max_eq_left hu,
        max_eq_left (neg_nonneg.mpr ht'),max_eq_right (neg_nonpos.mpr hu),
        min_eq_left hu,min_eq_right (neg_nonneg.mpr ht'),add_zero,sub_zero,
        abs_of_nonpos ht',abs_of_nonneg hu] using hopp t u ht' hu
    · have hu' := le_of_not_ge hu
      simpa only [neg_neg,markedDirectionalSpan,markedDirectionalOverlap,max_eq_right ht',
        max_eq_right hu',max_eq_left (neg_nonneg.mpr ht'),max_eq_left (neg_nonneg.mpr hu'),
        min_self,zero_add,abs_of_nonpos ht',abs_of_nonpos hu'] using
          hleft (-t) (-u) (neg_nonneg.mpr ht') (neg_nonneg.mpr hu')

/-- Original two-recipient avoidance, with the actual union of forbidden sets. -/
theorem marked_direct_original_union_kernel_limit (p t u : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      if markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ)) ∪
        markedCloserDonors p (p+u/(m n : ℝ))) z = 0 then 1 else 0)) atTop
      (𝓝 (Real.exp (-4*p*markedDirectionalSpan t u))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  let rate : ℝ≥0 := ⟨4*p*markedDirectionalSpan t u,
    mul_nonneg (by positivity) (marked_directional_span_nonneg t u)⟩
  have hh := marked_direct_original_category_limit m hm
    (fun n => markedCloserDonors p (p+t/(m n : ℝ)) ∪ markedCloserDonors p (p+u/(m n : ℝ)))
    (fun _ => (marked_closer_donors_measurable _ _).union (marked_closer_donors_measurable _ _))
    rate (marked_closer_union_rate p t u hp m hm)
  have he : -(rate : ℝ) = -4*p*markedDirectionalSpan t u := by
    change -(4*p*markedDirectionalSpan t u) = _
    ring
  simpa only [he] using hh

/-- Both marked one-replica union kernels, including the central retention. -/
theorem marked_direct_union_kernel_limits (p t u : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop) (k : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedDrawPower (N n) (markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ)) ∪
        markedCloserDonors p (p+u/(m n : ℝ))) z) k)) atTop
      (𝓝 (Real.exp (-4*p*matchS*markedDirectionalSpan t u))) ∧
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n) (markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ)) ∪
        markedCloserDonors p (p+u/(m n : ℝ))) z) k)) atTop
      (𝓝 (matchS*Real.exp (-4*p*matchS*markedDirectionalSpan t u))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  let rate : ℝ≥0 := ⟨4*p*markedDirectionalSpan t u,
    mul_nonneg (by positivity) (marked_directional_span_nonneg t u)⟩
  have hh := marked_direct_single_category_limits m N hm hN
    (fun n => markedCloserDonors p (p+t/(m n : ℝ)) ∪ markedCloserDonors p (p+u/(m n : ℝ)))
    (fun _ => (marked_closer_donors_measurable _ _).union (marked_closer_donors_measurable _ _))
    rate (marked_closer_union_rate p t u hp m hm) k
  have he : -matchS*(rate : ℝ) = -4*p*matchS*markedDirectionalSpan t u := by
    change -matchS*(4*p*markedDirectionalSpan t u) = _
    ring
  simpa only [he] using hh

end AronowAudit.P001.TailA
