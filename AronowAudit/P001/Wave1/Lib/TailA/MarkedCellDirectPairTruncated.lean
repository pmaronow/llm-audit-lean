import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectTwoWindows
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectTruncated

/-! Bounded two-recipient integrals in the actual finite shared-site experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectPairTruncated (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Two query-dependent counts are jointly measurable before averaging the
same original sample in both coordinates. -/
theorem marked_direct_pair_count_kernel_measurable (n : ℕ) (p : ℝ)
    (f : ℕ × ℕ → ℝ) :
    Measurable (fun q : ℝ × ℝ => mean (MatchProduct n) (fun z =>
      f (markedWindowCount (markedCloserDonors p (p+q.1/(n : ℝ))) z,
        markedWindowCount (markedCloserDonors p (p+q.2/(n : ℝ))) z))) := by
  let C : ℝ × (Fin n → MatchUnit) → ℕ := fun y =>
    markedWindowCount (markedCloserDonors p (p+y.1/(n : ℝ))) y.2
  have hC : Measurable C := marked_scaled_closer_count_measurable n p
  have hproj1 : Measurable (fun y : (ℝ × ℝ) × (Fin n → MatchUnit) => (y.1.1,y.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hproj2 : Measurable (fun y : (ℝ × ℝ) × (Fin n → MatchUnit) => (y.1.2,y.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hfirst := hC.comp hproj1
  have hsecond := hC.comp hproj2
  have hj := (measurable_of_countable f).comp (hfirst.prodMk hsecond)
  have hav := hj.stronglyMeasurable.integral_prod_right' (ν := MatchProduct n)
  simpa only [C,Function.comp_def,mean] using hav.measurable

theorem marked_direct_pair_count_kernel_bound (n : ℕ) (p : ℝ) (q : ℝ × ℝ)
    (f : ℕ × ℕ → ℝ) {C : ℝ} (hf : ∀ c, |f c| ≤ C) :
    |mean (MatchProduct n) (fun z =>
      f (markedWindowCount (markedCloserDonors p (p+q.1/(n : ℝ))) z,
        markedWindowCount (markedCloserDonors p (p+q.2/(n : ℝ))) z))| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := MatchProduct n)
    (f := fun z => f (markedWindowCount (markedCloserDonors p (p+q.1/(n : ℝ))) z,
      markedWindowCount (markedCloserDonors p (p+q.2/(n : ℝ))) z))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hf _))
  simpa only [mean,Real.norm_eq_abs,probReal_univ,mul_one] using h

/-- The bounded two-recipient integral converges with both actual recipient
densities and both finite support cutoffs.  Shared original donors are averaged
jointly, before either limiting integration. -/
theorem marked_direct_truncated_pair_integral (p R : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (k l : ℕ) :
    Tendsto (fun n => ∫ q : ℝ × ℝ,
      (markedScaledRecipientDensity (m n) p q.1*markedScaledRecipientDensity (m n) p q.2) *
      mean (MatchProduct (m n)) (fun z =>
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+q.1/(m n : ℝ))) z) k *
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+q.2/(m n : ℝ))) z) l)
      ∂(volume.restrict (Set.Icc (-R) R)).prod (volume.restrict (Set.Icc (-R) R))) atTop
      (𝓝 (∫ q : ℝ × ℝ,
        ((2*(1-p))*(2*(1-p))) *
          (matchS^2*Real.exp (-(4*p)*(matchS*(|q.1|+|q.2|)-
            matchS^2*markedDirectionalOverlap q.1 q.2)))
        ∂(volume.restrict (Set.Icc (-R) R)).prod (volume.restrict (Set.Icc (-R) R)))) := by
  have hf (n : ℕ) (c : ℕ × ℕ) :
      |markedRetainedDrawPower (N n) c.1 k*markedRetainedDrawPower (N n) c.2 l| ≤ 1 := by
    obtain ⟨h0,h1⟩ := marked_retained_draw_power_bounds (N n) c.1 k
    obtain ⟨h2,h3⟩ := marked_retained_draw_power_bounds (N n) c.2 l
    rw [abs_of_nonneg (mul_nonneg h0 h2)]
    exact mul_le_one₀ h1 h2 h3
  have hmeas (n : ℕ) : Measurable (fun q : ℝ × ℝ =>
      (markedScaledRecipientDensity (m n) p q.1*markedScaledRecipientDensity (m n) p q.2) *
      mean (MatchProduct (m n)) (fun z =>
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+q.1/(m n : ℝ))) z) k *
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+q.2/(m n : ℝ))) z) l)) :=
    (((marked_scaled_recipient_density_measurable (m n) p).comp measurable_fst).mul
      ((marked_scaled_recipient_density_measurable (m n) p).comp measurable_snd)).mul
      (marked_direct_pair_count_kernel_measurable (m n) p
        (fun c => markedRetainedDrawPower (N n) c.1 k*markedRetainedDrawPower (N n) c.2 l))
  have hb (n : ℕ) (q : ℝ × ℝ) :
      |(markedScaledRecipientDensity (m n) p q.1*markedScaledRecipientDensity (m n) p q.2) *
      mean (MatchProduct (m n)) (fun z =>
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+q.1/(m n : ℝ))) z) k *
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+q.2/(m n : ℝ))) z) l)| ≤ 4 := by
    rw [abs_mul]
    have hd : |markedScaledRecipientDensity (m n) p q.1*
        markedScaledRecipientDensity (m n) p q.2| ≤ 4 := by
      rw [abs_mul]
      have hh := mul_le_mul (marked_scaled_recipient_density_bound (m n) p q.1)
        (marked_scaled_recipient_density_bound (m n) p q.2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at hh ⊢
      exact hh
    have hk := marked_direct_pair_count_kernel_bound (m n) p q
      (fun c => markedRetainedDrawPower (N n) c.1 k*markedRetainedDrawPower (N n) c.2 l) (hf n)
    have hh := mul_le_mul hd hk (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    simpa only [mul_one] using hh
  apply tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
  · intro n
    exact (hmeas n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (hb n)
  · exact ae_of_all _ (fun q =>
      ((marked_scaled_recipient_density_limit p q.1 hp m hm).mul
        (marked_scaled_recipient_density_limit p q.2 hp m hm)).mul
          (marked_direct_recipient_pair_kernel_limit p q.1 q.2 hp m N hm hN k l))

end AronowAudit.P001.TailA
