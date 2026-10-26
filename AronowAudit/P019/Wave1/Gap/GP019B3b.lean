import AronowAudit.P019.Wave1.Gap.GLP019B2
import AronowAudit.P019.Wave1.Gap.GP019B1

/-!
Propositions 3 and 4 for the actual completed cell statistics. Positive cell
probabilities make all exceptional completion branches disappear eventually
almost surely on the common IID product.
-/

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

def GP019B3b_count (D : Ω → Prop) [DecidablePred D] {n : ℕ} (s : Fin n → Ω) : ℕ :=
  ∑ i, if D (s i) then 1 else 0

def GP019B3b_sampleMean (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D]
    {n : ℕ} (s : Fin n → Ω) (c : ℝ) : ℝ :=
  if GP019B3b_count D s = 0 then c else
    (∑ i, if D (s i) then f (s i) else 0) /
      (GP019B3b_count D s : ℝ)

def GP019B3b_sampleVariance (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D]
    {n : ℕ} (s : Fin n → Ω) : ℝ :=
  if GP019B3b_count D s < 2 then 0 else
    (∑ i, if D (s i) then
      (f (s i) - GP019B3b_sampleMean f D s 0)^2 else 0) /
        ((GP019B3b_count D s : ℝ) - 1)

theorem GP019B3b_count_cast (D : Ω → Prop) [DecidablePred D] {n : ℕ} (s : Fin n → Ω) :
    (GP019B3b_count D s : ℝ) =
      ∑ i, if D (s i) then (1 : ℝ) else 0 := by
  simp only [GP019B3b_count, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]


theorem GP019B3b_sampleMean_eq (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D]
    {n : ℕ} (s : Fin n → Ω) (c : ℝ)
    (hN : GP019B3b_count D s ≠ 0) :
    GP019B3b_sampleMean f D s c =
      (∑ i, if D (s i) then f (s i) else 0) /
        (GP019B3b_count D s : ℝ) := by
  rw [GP019B3b_sampleMean, if_neg hN]

/-- The exact centered numerator identity used in ratio linearization. -/
theorem GP019B3b_masked_residual_sum (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D]
    {n : ℕ} (s : Fin n → Ω) (m : ℝ) :
    (∑ i, if D (s i) then f (s i) - m else 0) =
      (∑ i, if D (s i) then f (s i) else 0) -
        (GP019B3b_count D s : ℝ) * m := by
  rw [GP019B3b_count_cast, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : D (s i) <;> simp [hi]

theorem GP019B3b_sampleMean_residual (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D] {n : ℕ} (s : Fin n → Ω) (c : ℝ)
    (hN : GP019B3b_count D s ≠ 0) :
    GP019B3b_sampleMean f D s c - P.ce f D =
      (∑ i, if D (s i) then f (s i) - P.ce f D else 0) /
        (GP019B3b_count D s : ℝ) := by
  have hNR : (GP019B3b_count D s : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [GP019B3b_sampleMean_eq f D s c hN,
    GP019B3b_masked_residual_sum]
  field_simp [hNR]


theorem GP019B3b_sampleVariance_eq (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D]
    {n : ℕ} (s : Fin n → Ω) (hN : 2 ≤ GP019B3b_count D s) :
    GP019B3b_sampleVariance f D s =
      (GP019B3b_count D s : ℝ) /
          ((GP019B3b_count D s : ℝ) - 1) *
        ((∑ i, if D (s i) then (f (s i))^2 else 0) /
          (GP019B3b_count D s : ℝ) -
            (GP019B3b_sampleMean f D s 0)^2) := by
  have hN0 : GP019B3b_count D s ≠ 0 := by omega
  have hNR : (GP019B3b_count D s : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hNR1 : (GP019B3b_count D s : ℝ) - 1 ≠ 0 := by
    have hN' : (2 : ℝ) ≤ GP019B3b_count D s := by exact_mod_cast hN
    linarith
  have he : (∑ i, if D (s i) then
        (f (s i) - GP019B3b_sampleMean f D s 0)^2 else 0) =
      (∑ i, if D (s i) then (f (s i))^2 else 0) -
        (∑ i, if D (s i) then f (s i) else 0) *
          (2 * GP019B3b_sampleMean f D s 0) +
        (GP019B3b_count D s : ℝ) *
          (GP019B3b_sampleMean f D s 0)^2 := by
    rw [GP019B3b_count_cast, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : D (s i) <;> simp [hi] <;> ring
  rw [GP019B3b_sampleVariance, if_neg (not_lt.mpr hN), he]
  simp only [GP019B3b_sampleMean_eq f D s 0 hN0]
  field_simp [hNR, hNR1]
  <;> ring


variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

lemma GP019B3b_cell_ae (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] (c : ℝ)
    (hp : 0 < P.prob (D)) :
    ∀ᵐ ω ∂t19_product P,
      Tendsto (fun (n : ℕ) => (GP019B3b_count D (t19_sample n ω) : ℝ)/(n : ℝ))
        atTop (nhds (P.prob (D))) ∧
      (∀ᶠ n in atTop, 2 ≤ GP019B3b_count D (t19_sample n ω)) ∧
      Tendsto (fun (n : ℕ) => GP019B3b_sampleMean f D (t19_sample n ω) c)
        atTop (nhds (P.ce f D)) ∧
      Tendsto (fun (n : ℕ) => GP019B3b_sampleVariance f D (t19_sample n ω))
        atTop (nhds (P.cv (fun t => f t) (D))) := by
  filter_upwards [t19_average_ae P (fun t => if D t then 1 else 0),
    t19_average_ae P (fun t => if D t then f t else 0),
    t19_average_ae P (fun t => if D t then f t^2 else 0)] with ω hI hV hV2
  let C := fun (n : ℕ) => (GP019B3b_count D (t19_sample n ω) : ℝ)
  let A := fun (n : ℕ) => ∑ i : Fin n, if D (ω i) then f (ω i) else 0
  let B := fun (n : ℕ) => ∑ i : Fin n, if D (ω i) then f (ω i)^2 else 0
  have hc : Tendsto (fun (n : ℕ) => C n/(n : ℝ)) atTop (nhds (P.prob (D))) := by
    simpa only [C, GP019B3b_count_cast, t19_sample, FiniteLaw.prob] using hI
  have hN : Tendsto C atTop atTop := by
    have h := hc.pos_mul_atTop hp tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hn)
  have h2 : ∀ᶠ n in atTop, 2 ≤ GP019B3b_count D (t19_sample n ω) := by
    filter_upwards [hN.eventually_ge_atTop 2] with n hn
    change (2 : ℝ) ≤ (GP019B3b_count D (t19_sample n ω) : ℝ) at hn
    exact_mod_cast hn
  have hm : Tendsto (fun (n : ℕ) => GP019B3b_sampleMean f D (t19_sample n ω) c)
      atTop (nhds (P.ce f D)) := by
    have h := hV.div hc (ne_of_gt hp)
    change Tendsto _ atTop (nhds (_/_)) at h
    apply h.congr'
    filter_upwards [h2, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
    have hcnt : GP019B3b_count D (t19_sample n ω) ≠ 0 := by omega
    simp only [GP019B3b_sampleMean, if_neg hcnt, t19_sample]
    dsimp only [C]
    exact div_div_div_cancel_right₀ hn' _ _
  have hm0 : Tendsto (fun (n : ℕ) => GP019B3b_sampleMean f D (t19_sample n ω) 0)
      atTop (nhds (P.ce f D)) := by
    apply hm.congr'
    filter_upwards [h2] with n hn
    have hcnt : GP019B3b_count D (t19_sample n ω) ≠ 0 := by omega
    simp [GP019B3b_sampleMean, hcnt]
  have hInv : Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hfac := hc.div (hc.sub hInv) (by simpa using ne_of_gt hp)
  have hsecond := hV2.div hc (ne_of_gt hp)
  have hv := ((hsecond.sub (hm0.pow 2)).mul hfac)
  have hv' : Tendsto (fun (n : ℕ) => GP019B3b_sampleVariance f D (t19_sample n ω)) atTop
      (nhds (P.cv (fun t => f t) (D))) := by
    change Tendsto _ atTop (nhds ((_/_-_^2)*(_/(_-0)))) at hv
    rw [sub_zero, div_self (ne_of_gt hp), mul_one] at hv
    apply hv.congr'
    filter_upwards [h2, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
    rw [GP019B3b_sampleVariance_eq f D _ hn]
    have hcn : (GP019B3b_count D (t19_sample n ω) : ℝ) ≠ 0 := by
      exact_mod_cast (show GP019B3b_count D (t19_sample n ω) ≠ 0 by omega)
    have hcm : (GP019B3b_count D (t19_sample n ω) : ℝ)-1 ≠ 0 := by
      have : (2 : ℝ) ≤ (GP019B3b_count D (t19_sample n ω) : ℝ) := by exact_mod_cast hn
      linarith
    dsimp only [Pi.div_apply, Pi.sub_apply, C, t19_sample]
    field_simp
    <;> ring_nf <;> congr!
  exact ⟨hc, h2, hm, hv'⟩


/-- The root-n remainder of one completed cell mean vanishes in probability. -/
lemma GP019B3b_ratio_remainder (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D] (hp : 0 < P.prob D) (c : ℝ) :
    TendstoInMeasure (t19_product P) (fun (n : ℕ) ω =>
      Real.sqrt n * (GP019B3b_sampleMean f D (t19_sample n ω) c - P.ce f D) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n,
          (if D (ω i) then f (ω i) - P.ce f D else 0) / P.prob D)
      atTop (fun _ => 0) := by
  let u : Ω → ℝ := fun t => if D t then f t - P.ce f D else 0
  let b : ℕ → (ℕ → Ω) → ℝ := fun n ω =>
    1 / ((GP019B3b_count D (t19_sample n ω) : ℝ) / (n : ℝ)) - 1 / P.prob D
  have hb : ∀ᵐ ω ∂t19_product P, Tendsto (fun n => b n ω) atTop (nhds 0) := by
    filter_upwards [GP019B3b_cell_ae P f D c hp] with ω h
    simpa only [b, sub_self, Pi.div_apply] using
      ((tendsto_const_nhds (x := (1 : ℝ))).div h.1 hp.ne').sub
        (tendsto_const_nhds (x := 1 / P.prob D))
  have hR := t19_small_product P u (masked_central_moments P f D hp.ne').1 b
    (fun n => t19_stat_measurable n (fun s =>
      1 / ((GP019B3b_count D s : ℝ)/(n : ℝ)) - 1 / P.prob D)) hb
  apply t19_transfer_inMeasure (t19_product P)
    (fun n => t19_stat_measurable n (fun s =>
      ((Real.sqrt n)⁻¹ * ∑ i, u (s i)) *
        (1 / ((GP019B3b_count D s : ℝ)/(n : ℝ)) - 1 / P.prob D)))
    (fun n => t19_stat_measurable n (fun s =>
      Real.sqrt n * (GP019B3b_sampleMean f D s c - P.ce f D) -
        (Real.sqrt n)⁻¹ * ∑ i, u (s i) / P.prob D)) hR
  filter_upwards [GP019B3b_cell_ae P f D c hp] with ω h
  filter_upwards [h.2.1, eventually_gt_atTop (0 : ℕ)] with n hN hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hNR : (GP019B3b_count D (t19_sample n ω) : ℝ) ≠ 0 := by
    exact_mod_cast (show GP019B3b_count D (t19_sample n ω) ≠ 0 by omega)
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  rw [GP019B3b_sampleMean_residual P f D _ c (by omega)]
  simp only [← Finset.sum_div]
  dsimp only [u, b, t19_sample]
  field_simp [hnR, hsqrt, hNR, hp.ne']
  rw [hsquare]

def GP019B3b_contrast (f : Ω → ℝ) (D1 D0 : Ω → Prop)
    [DecidablePred D1] [DecidablePred D0] {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  GP019B3b_sampleMean f D1 s c1 - GP019B3b_sampleMean f D0 s c0

def GP019B3b_varianceHat (f : Ω → ℝ) (D1 D0 : Ω → Prop)
    [DecidablePred D1] [DecidablePred D0] {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ GP019B3b_count D1 s ∧ 2 ≤ GP019B3b_count D0 s then
    GP019B3b_sampleVariance f D1 s / (GP019B3b_count D1 s : ℝ) +
      GP019B3b_sampleVariance f D0 s / (GP019B3b_count D0 s : ℝ)
  else cV

lemma GP019B3b_contrast_clt (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D1 D0 : Ω → Prop) [DecidablePred D1] [DecidablePred D0]
    (hp1 : 0 < P.prob D1) (hp0 : 0 < P.prob D0)
    (hd : ∀ ω, D1 ω → ¬ D0 ω) (c1 c0 : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
      (GP019B3b_contrast f D1 D0 (t19_sample n ω) c1 c0 - (P.ce f D1 - P.ce f D0)))
      atTop id (fun _ => t19_product P)
        (gaussianReal 0 (P.cv f D1 / P.prob D1 + P.cv f D0 / P.prob D0).toNNReal) := by
  have hm := contrast_influence_moments P f D1 D0 hp1.ne' hp0.ne' hd
  have hCLT := t19_average_clt P (P.contrastInfluence f D1 D0) hm.1
  rw [hm.2] at hCLT
  have hR := AronowAudit.P015.ConvergenceCompletion.sub_limit _
    (GP019B3b_ratio_remainder P f D1 hp1 c1)
    (GP019B3b_ratio_remainder P f D0 hp0 c0)
  have hdiff : TendstoInMeasure (t19_product P) (fun (n : ℕ) ω =>
      Real.sqrt n * (GP019B3b_contrast f D1 D0 (t19_sample n ω) c1 c0 -
        (P.ce f D1 - P.ce f D0)) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, P.contrastInfluence f D1 D0 (ω i))
      atTop (fun _ => 0) := by
    convert hR using 1
    · funext n ω
      simp only [GP019B3b_contrast, FiniteLaw.contrastInfluence, Finset.sum_sub_distrib]
      ring
    · simp only [sub_zero]
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hCLT hdiff
    (fun n => (t19_stat_measurable n (fun s => Real.sqrt n *
      (GP019B3b_contrast f D1 D0 s c1 c0 - (P.ce f D1 - P.ce f D0)))).aemeasurable)

lemma GP019B3b_varianceHat_ae (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D1 D0 : Ω → Prop) [DecidablePred D1] [DecidablePred D0]
    (hp1 : 0 < P.prob D1) (hp0 : 0 < P.prob D0) (cV : ℝ) :
    ∀ᵐ ω ∂t19_product P, Tendsto (fun (n : ℕ) =>
      (n : ℝ) * GP019B3b_varianceHat f D1 D0 (t19_sample n ω) cV) atTop
      (nhds (P.cv f D1 / P.prob D1 + P.cv f D0 / P.prob D0)) := by
  filter_upwards [GP019B3b_cell_ae P f D1 0 hp1,
    GP019B3b_cell_ae P f D0 0 hp0] with ω h1 h0
  have h := (h1.2.2.2.div h1.1 hp1.ne').add (h0.2.2.2.div h0.1 hp0.ne')
  apply h.congr'
  filter_upwards [h1.2.1, h0.2.1, eventually_gt_atTop (0 : ℕ)] with n hn1 hn0 hn
  rw [GP019B3b_varianceHat, if_pos ⟨hn1, hn0⟩]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Pi.div_apply]
  field_simp
  <;> ring

/-- Studentization and the finite-sample normalization agree eventually, even
when a prescribed variance completion is nonpositive. -/
lemma GP019B3b_studentize (P : FiniteLaw Ω)
    (a v : (n : ℕ) → (Fin n → Ω) → ℝ) (θ V : ℝ) (hV : 0 < V)
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * (a n (t19_sample n ω) - θ))
      atTop id (fun _ => t19_product P) (gaussianReal 0 V.toNNReal))
    (hv : ∀ᵐ ω ∂t19_product P, Tendsto
      (fun (n : ℕ) => (n : ℝ) * v n (t19_sample n ω)) atTop (nhds V)) :
    TendstoInDistribution (fun (n : ℕ) ω =>
      (a n (t19_sample n ω) - θ) / Real.sqrt (v n (t19_sample n ω)))
      atTop id (fun _ => t19_product P) (gaussianReal 0 1) := by
  have hsqrt : Real.sqrt V ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hV)
  have ha : ∀ᵐ ω ∂t19_product P, Tendsto
      (fun (n : ℕ) => (Real.sqrt ((n : ℝ) * v n (t19_sample n ω)))⁻¹)
      atTop (nhds (Real.sqrt V)⁻¹) := by
    filter_upwards [hv] with ω hω
    exact hω.sqrt.inv₀ hsqrt
  have hi := tendstoInMeasure_of_tendsto_ae (μ := t19_product P)
    (fun n => (t19_stat_measurable n (fun s =>
      (Real.sqrt ((n : ℝ) * v n s))⁻¹)).aestronglyMeasurable) ha
  have hh := hCLT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hi
    (fun n => (t19_stat_measurable n (fun s =>
      (Real.sqrt ((n : ℝ) * v n s))⁻¹)).aemeasurable)
  have hd : NNReal.mk ((Real.sqrt V)^2) (sq_nonneg _) = V.toNNReal := by
    apply NNReal.eq
    change (Real.sqrt V)^2 = (V.toNNReal : ℝ)
    rw [Real.sq_sqrt hV.le]
    exact (Real.coe_toNNReal V hV.le).symm
  have hVnn : V.toNNReal ≠ 0 := by
    simpa only [ne_eq, Real.toNNReal_eq_zero, not_le] using hV
  have hl := gaussianReal_div_const
    (HasLaw.id : HasLaw id (gaussianReal 0 V.toNNReal) (gaussianReal 0 V.toNNReal)) (Real.sqrt V)
  rw [zero_div, hd, div_self hVnn] at hl
  have hnorm := t19_distribution_hasLaw (ν := gaussianReal 0 V.toNNReal)
    (by simpa only [div_eq_mul_inv] using hh) (by simpa only [div_eq_mul_inv] using hl)
  have heq : ∀ᶠ n : ℕ in atTop, (fun ω =>
      Real.sqrt n * (a n (t19_sample n ω) - θ) *
        (Real.sqrt ((n : ℝ) * v n (t19_sample n ω)))⁻¹) =
      (fun ω => (a n (t19_sample n ω) - θ) / Real.sqrt (v n (t19_sample n ω))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    funext ω
    have hnS : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    simp only [Real.sqrt_mul (Nat.cast_nonneg n), mul_inv_rev, div_eq_mul_inv]
    field_simp
  exact ⟨fun n => (t19_stat_measurable n (fun s => (a n s - θ) / Real.sqrt (v n s))).aemeasurable,
    hnorm.aemeasurable_limit, hnorm.tendsto.congr' (heq.mono (fun n hn => by rw [hn]))⟩


lemma GP019B3b_pvalue_limit (P : FiniteLaw Ω)
    (a v : (n : ℕ) → (Fin n → Ω) → ℝ) (θ : ℝ)
    (hZ : TendstoInDistribution (fun (n : ℕ) ω =>
      (a n (t19_sample n ω) - θ) / Real.sqrt (v n (t19_sample n ω)))
      atTop id (fun _ => t19_product P) (gaussianReal 0 1))
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    Tendsto (fun n => (P.iid n).prob (fun s => normalPValue (a n s) θ (v n s) ≤ u))
      atTop (nhds u) := by
  let D : Set ℝ := {g | 2 * normalCDF (-|g|) ≤ u}
  have hD : D = (Set.Ioo (-normalQuantile (1-u/2)) (normalQuantile (1-u/2)))ᶜ := by
    rw [show D = _ from npu_tail_event u hu0 hu1]
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_compl_iff,
      Set.mem_Ioo, not_and_or, not_lt]
  have hmeas : MeasurableSet D := by rw [hD]; exact measurableSet_Ioo.compl
  haveI GP019B3b_normal_atomless : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hbd : (gaussianReal 0 1).map id (frontier D) = 0 := by
    rw [Measure.map_id, hD, frontier_compl, frontier_Ioo (by
      have h := npu_quantile_pos u hu0 hu1
      linarith)]
    exact measure_union_null (measure_singleton _) (measure_singleton _)
  have ht := t19_event_limit hZ D hmeas hbd
  change Tendsto _ atTop (nhds ((gaussianReal 0 1 D).toReal)) at ht
  rw [show (gaussianReal 0 1 D).toReal = u from normal_pvalue_uniform_proof u hu0 hu1] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n => by
    calc
      _ = (t19_product P).real {ω | normalPValue (a n (t19_sample n ω)) θ
          (v n (t19_sample n ω)) ≤ u} := by
        apply congrArg (fun E : Set (ℕ → Ω) => (t19_product P).real E)
        ext ω
        simp only [D, Set.mem_setOf_eq, normalPValue, abs_div,
          abs_of_nonneg (Real.sqrt_nonneg _), neg_div]
      _ = _ := by
        convert t19_sample_prob P n (fun s => normalPValue (a n s) θ (v n s) ≤ u) using 1 <;> congr!)


end
noncomputable section
variable {Ω : Type*} [Fintype Ω]

theorem proposition_three_proof (S : Study Ω) (hs : S.standing) (c1 c0 cV : ℝ) :
    S.beta = 1 ∧
    WeakLimit S.law (fun _ s => (S.betaHat s c1 c0-1) /
      Real.sqrt (S.betaVarianceHat s cV)) (gaussianReal 0 1) ∧
    (∀ u : ℝ, 0 < u → u < 1 →
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        normalPValue (S.betaHat s c1 c0) 1 (S.betaVarianceHat s cV) ≤ u))
          atTop (nhds u)) := by
  classical
  letI GP019B3b_measurable_three : MeasurableSpace Ω := ⊤
  haveI GP019B3b_singleton_three : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  have hβ : S.beta = 1 := placebo_one_identity S hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.1 false true).1.ne' (hs.2.2.2.1 true true).1.ne'
  have hp1 := (hs.2.2.2.1 true true).1
  have hp0 := (hs.2.2.2.1 false true).1
  have hCLT := GP019B3b_contrast_clt S.law (fun ω => (S.V ω : ℝ))
    (S.cell true true) (S.cell false true) hp1 hp0
    (by intro ω ht hf; exact Bool.false_ne_true (hf.1.symm.trans ht.1)) c1 c0
  have hv := GP019B3b_varianceHat_ae S.law (fun ω => (S.V ω : ℝ))
    (S.cell true true) (S.cell false true) hp1 hp0 cV
  have hpos : 0 < S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true true) / S.law.prob (S.cell true true) +
      S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false true) / S.law.prob (S.cell false true) :=
    add_pos (div_pos (hs.2.2.2.1 true true).2 hp1) (div_pos (hs.2.2.2.1 false true).2 hp0)
  change TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
    (S.betaHat (t19_sample n ω) c1 c0 - S.beta)) _ _ _ _ at hCLT
  rw [hβ] at hCLT
  have hZ := GP019B3b_studentize S.law (fun _ s => S.betaHat s c1 c0)
    (fun _ s => S.betaVarianceHat s cV) 1 _ hpos hCLT hv
  exact ⟨hβ, t19_weakLimit _ _ _ hZ, GP019B3b_pvalue_limit _ _ _ _ hZ⟩

theorem proposition_four_proof (S : Study Ω) (h3 : S.treatmentIndependent)
    (h4 : S.nondegenerate) (c1 c0 cV : ℝ) :
    S.delta = 0 ∧
    WeakLimit S.law (fun _ s => S.deltaHat s c1 c0 /
      Real.sqrt (S.deltaVarianceHat s cV)) (gaussianReal 0 1) ∧
    (∀ u : ℝ, 0 < u → u < 1 →
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        normalPValue (S.deltaHat s c1 c0) 0 (S.deltaVarianceHat s cV) ≤ u))
          atTop (nhds u)) := by
  letI GP019B3b_measurable_four : MeasurableSpace Ω := ⊤
  haveI GP019B3b_singleton_four : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  have hp := regularity_probabilities S h4
  have hδ : S.delta = 0 := placebo_two_identity S h3 (hp.1 false).ne' (hp.1 true).ne'
  have hcv (z : Bool) : S.law.cv (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = z) =
      S.law.variance (fun ω => bitVal (S.Y ω)) := by
    unfold FiniteLaw.cv FiniteLaw.variance
    rw [ce_arm_independent S h3 (fun _ _ y => (bitVal y)^2) z (hp.1 z).ne',
      ce_arm_independent S h3 (fun _ _ y => bitVal y) z (hp.1 z).ne']
  have hpos : 0 < S.law.cv (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) /
      S.law.prob (fun ω => S.Z ω = true) +
      S.law.cv (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false) /
      S.law.prob (fun ω => S.Z ω = false) := by
    rw [hcv, hcv]
    exact add_pos (div_pos h4.2.2 (hp.1 true)) (div_pos h4.2.2 (hp.1 false))
  have hCLT := GP019B3b_contrast_clt S.law (fun ω => bitVal (S.Y ω))
    (fun ω => S.Z ω = true) (fun ω => S.Z ω = false) (hp.1 true) (hp.1 false)
    (by intro ω ht hf; exact Bool.false_ne_true (hf.symm.trans ht)) c1 c0
  have hv := GP019B3b_varianceHat_ae S.law (fun ω => bitVal (S.Y ω))
    (fun ω => S.Z ω = true) (fun ω => S.Z ω = false) (hp.1 true) (hp.1 false) cV
  change TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
    (S.deltaHat (t19_sample n ω) c1 c0 - S.delta)) _ _ _ _ at hCLT
  rw [hδ] at hCLT
  have hZ := GP019B3b_studentize S.law (fun _ s => S.deltaHat s c1 c0)
    (fun _ s => S.deltaVarianceHat s cV) 0 _ hpos hCLT hv
  simp only [sub_zero] at hZ
  refine ⟨hδ, t19_weakLimit _ _ _ hZ, ?_⟩
  apply GP019B3b_pvalue_limit _ _ _ _
  simpa only [sub_zero] using hZ

end
end AronowAudit.P019.Wave1
