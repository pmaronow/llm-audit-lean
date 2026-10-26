import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectDomination

/-! Removal of the full position cutoff by direct finite-experiment envelopes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectFullIntegrals (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def markedCountKernel (m : ℕ) (p : ℝ) (K : ℕ → ℝ) (t : ℝ) : ℝ :=
  mean (MatchProduct m) (fun z => K (markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z))

def markedPairKernel (m : ℕ) (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ) (q : ℝ × ℝ) : ℝ :=
  mean (MatchProduct m) (fun z =>
    K (markedWindowCount (markedCloserDonors p (p+q.1/(m : ℝ))) z)
      (markedWindowCount (markedCloserDonors p (p+q.2/(m : ℝ))) z)
      (markedWindowCount (markedCloserDonors p (p+q.1/(m : ℝ)) ∪
        markedCloserDonors p (p+q.2/(m : ℝ))) z))

theorem marked_pair_kernel_measurable (m : ℕ) (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ) :
    Measurable (markedPairKernel m p K) := by
  have hq : Measurable (fun q : ℝ × ℝ => (p+q.1/(m : ℝ),p+q.2/(m : ℝ))) := by fun_prop
  have hh := (marked_unscaled_pair_kernel_measurable m p K).comp hq
  convert hh using 1
  funext q
  dsimp only [Function.comp_def,markedPairKernel]

theorem marked_window_count_mono {m : ℕ} {E F : Set MatchUnit} (hEF : E ⊆ F)
    (z : Fin m → MatchUnit) : markedWindowCount E z ≤ markedWindowCount F z := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hEF (Finset.mem_filter.mp hi).2⟩

/-- Any nonnegative finite test below the exponential count test inherits its
uniform position envelope. -/
theorem marked_query_test_envelope (m : ℕ) (hm : 0 < m) (p t : ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4))
    (ht : p+t/(m : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4))
    (F : (Fin m → MatchUnit) → ℝ) (hF0 : ∀ z, 0 ≤ F z)
    (hF : ∀ z, F z ≤ Real.exp
      (-(markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z : ℝ)/4)) :
    0 ≤ mean (MatchProduct m) F ∧ mean (MatchProduct m) F ≤ Real.exp (-markedDirectDecay*|t|) := by
  have hi : Integrable (fun z : Fin m → MatchUnit => Real.exp
      (-(markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z : ℝ)/4)) (MatchProduct m) := by
    apply Integrable.of_bound
      (((measurable_of_countable (fun c : ℕ => Real.exp (-(c : ℝ)/4))).comp
        (marked_window_count_measurable m _ (marked_closer_donors_measurable _ _))).aestronglyMeasurable) 1
    apply ae_of_all
    intro z
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have hnon : (0 : ℝ) ≤ markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z := Nat.cast_nonneg _
    linarith
  refine ⟨integral_nonneg hF0,?_⟩
  exact (integral_mono_of_nonneg (ae_of_all _ hF0) hi (ae_of_all _ hF)).trans
    (marked_scaled_exponential_count_bound m hm p t hp ht)

/-- An envelope for every one-recipient count test satisfying the direct
finite exponential bound. -/
theorem marked_single_density_kernel_bound (m : ℕ) (hm : 0 < m) (p t : ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)) (K : ℕ → ℝ)
    (hK : ∀ c, c ≤ m → 0 ≤ K c ∧ K c ≤ Real.exp (-(c : ℝ)/4)) :
    |markedScaledRecipientDensity m p t*markedCountKernel m p K t| ≤
      2*Real.exp (-markedDirectDecay*|t|) := by
  by_cases ht : p+t/(m : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4)
  · have hh := marked_query_test_envelope m hm p t hp ht _
      (fun z => (hK _ (marked_window_count_le _ _ z)).1)
      (fun z => (hK _ (marked_window_count_le _ _ z)).2)
    have hd := marked_scaled_recipient_density_nonneg m p t
    change 0 ≤ markedCountKernel m p K t ∧ markedCountKernel m p K t ≤ _ at hh
    rw [abs_of_nonneg (mul_nonneg hd hh.1)]
    apply mul_le_mul _ hh.2 hh.1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [abs_of_nonneg hd] using marked_scaled_recipient_density_bound m p t
  · simp only [markedScaledRecipientDensity,if_neg ht,zero_mul,abs_zero]
    positivity

/-- Permitted two-recipient kernels are dominated in both query counts. -/
def MarkedPairKernelBound (m : ℕ) (K : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ a b c, a ≤ m → b ≤ m → c ≤ m → a ≤ c → b ≤ c →
    0 ≤ K a b c ∧ K a b c ≤ Real.exp (-(a : ℝ)/4) ∧ K a b c ≤ Real.exp (-(b : ℝ)/4)

theorem marked_pair_density_kernel_bound (m : ℕ) (hm : 0 < m) (p : ℝ) (q : ℝ × ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℕ → ℝ)
    (hK : MarkedPairKernelBound m K) :
    |(markedScaledRecipientDensity m p q.1*markedScaledRecipientDensity m p q.2)*
      markedPairKernel m p K q| ≤ 4*Real.exp (-(markedDirectDecay/2)*(|q.1|+|q.2|)) := by
  have hKz (z : Fin m → MatchUnit) := hK
    (markedWindowCount (markedCloserDonors p (p+q.1/(m : ℝ))) z)
    (markedWindowCount (markedCloserDonors p (p+q.2/(m : ℝ))) z)
    (markedWindowCount (markedCloserDonors p (p+q.1/(m : ℝ)) ∪
      markedCloserDonors p (p+q.2/(m : ℝ))) z)
    (marked_window_count_le _ _ z) (marked_window_count_le _ _ z) (marked_window_count_le _ _ z)
    (marked_window_count_mono Set.subset_union_left z)
    (marked_window_count_mono Set.subset_union_right z)
  have hmean0 : 0 ≤ markedPairKernel m p K q := integral_nonneg (fun z => (hKz z).1)
  by_cases ht : p+q.1/(m : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4)
  · by_cases hu : p+q.2/(m : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4)
    · have h1 := (marked_query_test_envelope m hm p q.1 hp ht _
        (fun z => (hKz z).1) (fun z => (hKz z).2.1)).2
      have h2 := (marked_query_test_envelope m hm p q.2 hp hu _
        (fun z => (hKz z).1) (fun z => (hKz z).2.2)).2
      have hh : markedPairKernel m p K q ≤ Real.exp (-(markedDirectDecay/2)*(|q.1|+|q.2|)) := by
        rcases le_total |q.1| |q.2| with h | h
        · apply h2.trans
          apply Real.exp_le_exp.mpr
          nlinarith [marked_direct_decay_pos]
        · apply h1.trans
          apply Real.exp_le_exp.mpr
          nlinarith [marked_direct_decay_pos]
      have hd0 := mul_nonneg (marked_scaled_recipient_density_nonneg m p q.1)
        (marked_scaled_recipient_density_nonneg m p q.2)
      have hd : markedScaledRecipientDensity m p q.1*markedScaledRecipientDensity m p q.2 ≤ 4 := by
        have hb := mul_le_mul (marked_scaled_recipient_density_bound m p q.1)
          (marked_scaled_recipient_density_bound m p q.2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
        rw [← abs_mul,abs_of_nonneg hd0] at hb
        norm_num at hb ⊢
        exact hb
      rw [abs_of_nonneg (mul_nonneg hd0 hmean0)]
      exact mul_le_mul hd hh hmean0 (by norm_num : (0 : ℝ) ≤ 4)
    · simp only [markedScaledRecipientDensity,if_neg hu,mul_zero,zero_mul,abs_zero]
      positivity
  · simp only [markedScaledRecipientDensity,if_neg ht,zero_mul,abs_zero]
    positivity

theorem marked_pair_exponential_envelope_integrable :
    Integrable (fun q : ℝ × ℝ => 4*Real.exp (-(markedDirectDecay/2)*(|q.1|+|q.2|))) := by
  have hh := (marked_integrable_exp_abs (half_pos marked_direct_decay_pos)).mul_prod
    (marked_integrable_exp_abs (half_pos marked_direct_decay_pos))
  convert hh.const_mul 4 using 1
  funext q
  rw [← Real.exp_add]
  congr 2
  ring

theorem marked_pair_density_kernel_measurable (m : ℕ) (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ) :
    Measurable (fun q : ℝ × ℝ =>
      (markedScaledRecipientDensity m p q.1*markedScaledRecipientDensity m p q.2)*
        markedPairKernel m p K q) :=
  (((marked_scaled_recipient_density_measurable m p).comp measurable_fst).mul
    ((marked_scaled_recipient_density_measurable m p).comp measurable_snd)).mul
    (marked_pair_kernel_measurable m p K)

theorem marked_pair_density_kernel_integrable (m : ℕ) (hm : 0 < m) (p : ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℕ → ℝ)
    (hK : MarkedPairKernelBound m K) :
    Integrable (fun q : ℝ × ℝ =>
      (markedScaledRecipientDensity m p q.1*markedScaledRecipientDensity m p q.2)*
        markedPairKernel m p K q) := by
  apply marked_pair_exponential_envelope_integrable.mono'
    (marked_pair_density_kernel_measurable m p K).aestronglyMeasurable
  exact ae_of_all _ (fun q => by
    simpa only [Real.norm_eq_abs] using marked_pair_density_kernel_bound m hm p q hp K hK)

/-- Full one-query integral convergence: no position, count or weight cutoff
remains in this endpoint. -/
theorem marked_full_single_integral_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℝ)
    (hK : ∀ m, 0 < m → ∀ c, c ≤ m → 0 ≤ K m c ∧ K m c ≤ Real.exp (-(c : ℝ)/4))
    (L : ℝ → ℝ) (hlim : ∀ t, Tendsto (fun m => markedCountKernel m p (K m) t) atTop (𝓝 (L t))) :
    Tendsto (fun m => ∫ t : ℝ, markedScaledRecipientDensity m p t*markedCountKernel m p (K m) t)
      atTop (𝓝 (∫ t : ℝ, 2*(1-p)*L t)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun t => 2*Real.exp (-markedDirectDecay*|t|))
  · exact Eventually.of_forall (fun m => ((marked_scaled_recipient_density_measurable m p).mul
      (marked_direct_count_kernel_measurable m p (K m))).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact ae_of_all _ (fun t => by
      simpa only [Real.norm_eq_abs] using
        marked_single_density_kernel_bound m (by omega) p t ⟨hp.1.le,hp.2.le⟩ (K m) (hK m (by omega)))
  · exact (marked_integrable_exp_abs marked_direct_decay_pos).const_mul 2
  · exact ae_of_all _ (fun t => (marked_scaled_recipient_density_limit p t hp id tendsto_id).mul (hlim t))

/-- Full two-query convergence in the same original donor environment. -/
theorem marked_full_pair_integral_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hK : ∀ m, 0 < m → MarkedPairKernelBound m (K m))
    (L : ℝ × ℝ → ℝ)
    (hlim : ∀ q, Tendsto (fun m => markedPairKernel m p (K m) q) atTop (𝓝 (L q))) :
    Tendsto (fun m => ∫ q : ℝ × ℝ,
      (markedScaledRecipientDensity m p q.1*markedScaledRecipientDensity m p q.2)*
        markedPairKernel m p (K m) q) atTop
      (𝓝 (∫ q : ℝ × ℝ, (2*(1-p))^2*L q)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q : ℝ × ℝ => 4*Real.exp (-(markedDirectDecay/2)*(|q.1|+|q.2|)))
  · exact Eventually.of_forall (fun m => (marked_pair_density_kernel_measurable m p (K m)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact ae_of_all _ (fun q => by
      simpa only [Real.norm_eq_abs] using
        marked_pair_density_kernel_bound m (by omega) p q ⟨hp.1.le,hp.2.le⟩ (K m) (hK m (by omega)))
  · exact marked_pair_exponential_envelope_integrable
  · apply ae_of_all
    intro q
    have hh := ((marked_scaled_recipient_density_limit p q.1 hp id tendsto_id).mul
      (marked_scaled_recipient_density_limit p q.2 hp id tendsto_id)).mul (hlim q)
    simpa only [pow_two,id_eq] using hh

/-- The full product integral is the exact iterated integral in the sampling
identity; its integrability has been proved from the finite envelope. -/
theorem marked_pair_density_integral_iterated (m : ℕ) (hm : 0 < m) (p : ℝ)
    (hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℕ → ℝ)
    (hK : MarkedPairKernelBound m K) :
    (∫ q : ℝ × ℝ,
      (markedScaledRecipientDensity m p q.1*markedScaledRecipientDensity m p q.2)*
        markedPairKernel m p K q) =
      ∫ t : ℝ, markedScaledRecipientDensity m p t *
        (∫ u : ℝ, markedScaledRecipientDensity m p u*markedPairKernel m p K (t,u)) := by
  rw [Measure.volume_eq_prod,integral_prod _ (marked_pair_density_kernel_integrable m hm p hp K hK)]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  beta_reduce
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by ring)

end AronowAudit.P001.TailA
