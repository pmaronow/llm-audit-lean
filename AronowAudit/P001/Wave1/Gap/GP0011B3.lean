import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

/-! The finite two-bootstrap-draw identity. -/

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-! Regrouping the pointwise hot-deck statistic does not require donor existence:
an empty donor option contributes the constant 50 and hence zero centered noise. -/

private theorem t14b3_donor_responds {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (i j : Fin n)
    (h : nearestDonor p r i = some j) : r j = true := by
  classical
  unfold nearestDonor at h
  split_ifs at h with hex
  · have hj : Classical.choose hex = j := Option.some.inj h
    simpa only [hj] using (Classical.choose_spec hex).1

private def t14b3_incidence {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (i j : Fin n) : ℝ :=
  (if i = j then (if r i then 1 else 0) else 0) +
    (if r i = false ∧ nearestDonor p r i = some j then 1 else 0)

private def t14b3_rowNoise {n : ℕ} (p : Fin n → ℝ) (r e : Fin n → Bool)
    (i : Fin n) : ℝ :=
  if r i then noise (e i) else
    match nearestDonor p r i with
    | some j => noise (e j)
    | none => 0

private theorem t14b3_column_sum {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (j : Fin n) :
    (∑ i, t14b3_incidence p r i j) = donorReuseWeight p r j := by
  classical
  unfold t14b3_incidence
  rw [Finset.sum_add_distrib]
  have hself :
      (∑ i : Fin n, if i = j then (if r i then (1 : ℝ) else 0) else 0) =
        (if r j then 1 else 0) := by simp
  rw [hself, Finset.sum_boole]
  cases hj : r j with
  | true => simp [donorReuseWeight, hj]
  | false =>
      have hempty :
          (Finset.univ.filter (fun i => r i = false ∧ nearestDonor p r i = some j)) =
            ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hi
        have hd := t14b3_donor_responds p r i j hi.2
        simp [hj] at hd
      simp [donorReuseWeight, hj, hempty]

private theorem t14b3_row_sum {n : ℕ} (p : Fin n → ℝ)
    (r e : Fin n → Bool) (i : Fin n) :
    (∑ j, t14b3_incidence p r i j * noise (e j)) =
      t14b3_rowNoise p r e i := by
  classical
  unfold t14b3_incidence t14b3_rowNoise
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  cases hi : r i with
  | true => simp [hi, ite_mul]
  | false =>
      cases hd : nearestDonor p r i with
      | none => simp [hi, hd]
      | some j => simp [hi, hd, ite_mul, eq_comm]

private theorem t14b3_noise_regroup {n : ℕ} (p : Fin n → ℝ)
    (r e : Fin n → Bool) :
    (∑ i, t14b3_rowNoise p r e i) =
      ∑ j, donorReuseWeight p r j * noise (e j) := by
  classical
  calc
    (∑ i, t14b3_rowNoise p r e i) =
        ∑ i, ∑ j, t14b3_incidence p r i j * noise (e j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (t14b3_row_sum p r e i).symm
    _ = ∑ j, (∑ i, t14b3_incidence p r i j) * noise (e j) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
    _ = ∑ j, donorReuseWeight p r j * noise (e j) := by
      simp_rw [t14b3_column_sum]

private theorem t14b3_hotDeck_weights {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (r e : Fin n → Bool) :
    hotDeck (fun j => (p j, r j, e j)) - 50 =
      (∑ j, donorReuseWeight p r j * noise (e j)) / (n : ℝ) := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases hr : ∃ j, r j = true
  · have hrow (i : Fin n) :
        (if r i then 50 + noise (e i) else
          match nearestDonor p r i with
          | some j => 50 + noise (e j)
          | none => 50) = 50 + t14b3_rowNoise p r e i := by
      cases hi : r i with
      | true => simp [t14b3_rowNoise, hi]
      | false =>
          cases hd : nearestDonor p r i <;> simp [t14b3_rowNoise, hi, hd]
    have hsum :
        (∑ i, if r i then 50 + noise (e i) else
          match nearestDonor p r i with
          | some j => 50 + noise (e j)
          | none => 50) =
        (n : ℝ) * 50 + ∑ j, donorReuseWeight p r j * noise (e j) := by
      simp_rw [hrow]
      rw [Finset.sum_add_distrib, t14b3_noise_regroup]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (if ∃ j, r j = true then
        (∑ i, if r i then 50 + noise (e i) else
          match nearestDonor p r i with
          | some j => 50 + noise (e j)
          | none => 50) / (n : ℝ) else 50) - 50 = _
    rw [if_pos hr, hsum]
    field_simp [hnR]
    <;> ring
  · have hw (j : Fin n) : donorReuseWeight p r j = 0 := by
      have hj : r j = false := by
        cases h : r j with
        | false => rfl
        | true => exact False.elim (hr ⟨j, h⟩)
      simp [donorReuseWeight, hj]
    simp [hotDeck, hr, hw]

/-! The fair sign product has genuine finite integrals. -/

private def t14b3_signMeasure : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac true + (1/2 : ℝ≥0∞) • Measure.dirac false

private instance t14b3_signMeasure_probability : IsProbabilityMeasure t14b3_signMeasure := by
  constructor
  norm_num [t14b3_signMeasure, Measure.add_apply, Measure.smul_apply,
    ENNReal.inv_two_add_inv_two]

private instance t14b3_signProduct_probability (n : ℕ) :
    IsProbabilityMeasure (signProductLaw n) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => t14b3_signMeasure))
  infer_instance

private theorem t14b3_one_sign_mean : (∫ b, noise b ∂t14b3_signMeasure) = 0 := by
  have hb (b : Bool) : Integrable noise ((1/2 : ℝ≥0∞) • Measure.dirac b) :=
    (show Integrable noise (Measure.dirac b) from Integrable.of_finite).smul_measure
      (by norm_num)
  change (∫ b, noise b ∂((1/2 : ℝ≥0∞) • Measure.dirac true +
    (1/2 : ℝ≥0∞) • Measure.dirac false)) = 0
  rw [integral_add_measure (hb true) (hb false)]
  norm_num [integral_smul_measure, noise]

private theorem t14b3_sign_mean {n : ℕ} (j : Fin n) :
    (∫ e, noise (e j) ∂signProductLaw n) = 0 := by
  change (∫ e : Fin n → Bool, noise (e j)
    ∂Measure.pi (fun _ : Fin n => t14b3_signMeasure)) = 0
  rw [integral_comp_eval (μ := fun _ : Fin n => t14b3_signMeasure)
    (i := j) (show AEStronglyMeasurable noise t14b3_signMeasure from
      (measurable_of_countable noise).aestronglyMeasurable)]
  exact t14b3_one_sign_mean

private theorem t14b3_sign_cross {n : ℕ} (j k : Fin n) :
    (∫ e, noise (e j) * noise (e k) ∂signProductLaw n) =
      if j = k then 1 else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    have hs (e : Fin n → Bool) : noise (e j) * noise (e j) = 1 := by
      cases e j <;> norm_num [noise]
    simp_rw [hs]
    simp
  · have hind : iIndepFun (fun j (e : Fin n → Bool) => noise (e j))
        (signProductLaw n) := by
      change iIndepFun (fun j (e : Fin n → Bool) => noise (e j))
        (Measure.pi (fun _ : Fin n => t14b3_signMeasure))
      exact iIndepFun_pi (fun _ => (measurable_of_countable noise).aemeasurable)
    rw [(hind.indepFun hjk).integral_fun_mul_eq_mul_integral
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp only [t14b3_sign_mean, mul_zero, if_neg hjk]

private theorem t14b3_sign_square {n : ℕ} (c : Fin n → ℝ) :
    (∫ e, (∑ j, c j * noise (e j)) ^ 2 ∂signProductLaw n) = ∑ j, (c j)^2 := by
  classical
  have hex (e : Fin n → Bool) :
      (∑ j, c j * noise (e j)) ^ 2 =
        ∑ j, ∑ k, (c j * c k) * (noise (e j) * noise (e k)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (∫ e, (∑ j, c j * noise (e j)) ^ 2 ∂signProductLaw n) =
        ∑ j, ∑ k, ∫ e, (c j * c k) * (noise (e j) * noise (e k))
          ∂signProductLaw n := by
      simp_rw [hex]
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ (fun _ _ => Integrable.of_finite)
    _ = ∑ j, ∑ k, (c j * c k) * (if j = k then 1 else 0) := by
      simp_rw [integral_const_mul, t14b3_sign_cross]
    _ = ∑ j, (c j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_ite, pow_two]

/-! Centered finite variance equals one half of the average squared difference of two independent draws. -/

private theorem t14b3_two_draw_finite_variance {A : Type*} [Fintype A]
    (hcard : (Fintype.card A : ℝ) ≠ 0) (t : A → ℝ) :
    (∑ a, (t a - (∑ b, t b) / (Fintype.card A : ℝ))^2) /
        (Fintype.card A : ℝ) =
      (∑ a, ∑ b, (t a - t b)^2) / (2 * (Fintype.card A : ℝ)^2) := by
  classical
  let M : ℝ := Fintype.card A
  let S : ℝ := ∑ a, t a
  let Q : ℝ := ∑ a, (t a)^2
  have hM : M ≠ 0 := hcard
  have hlinear (z : ℝ) : (∑ a, 2 * t a * z) = 2 * z * S := by
    calc
      (∑ a, 2 * t a * z) = ∑ a, (2 * z) * t a := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 2 * z * S := by rw [← Finset.mul_sum]
  have hcenter (z : ℝ) : (∑ a, (t a - z)^2) = Q - 2 * z * S + M * z^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hlinear]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hinner (a : A) :
      (∑ b, (t a - t b)^2) = Q - 2 * t a * S + M * (t a)^2 := by
    calc
      (∑ b, (t a - t b)^2) = ∑ b, (t b - t a)^2 := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = Q - 2 * t a * S + M * (t a)^2 := hcenter (t a)
  have hpair : (∑ a, ∑ b, (t a - t b)^2) = 2 * M * Q - 2 * S^2 := by
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hlinear,
      ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change M * Q - 2 * S * S + M * Q = 2 * M * Q - 2 * S^2
    ring
  change (∑ a, (t a - S / M)^2) / M =
    (∑ a, ∑ b, (t a - t b)^2) / (2 * M^2)
  rw [hcenter, hpair]
  field_simp [hM]
  <;> ring

/-! Copies of one original observation use its original sign. -/

private theorem t14b3_bootstrap_weights {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (r : Fin n → Bool) (a : Fin n → Fin n)
    (e : Fin n → Bool) :
    hotDeck (resample (fun j => (p j, r j, e j)) a) - 50 =
      (∑ j, bootstrapOriginalReuse p r a j * noise (e j)) / (n : ℝ) := by
  classical
  have hgroup :
      (∑ j, bootstrapOriginalReuse p r a j * noise (e j)) =
        ∑ i, donorReuseWeight (p ∘ a) (r ∘ a) i * noise (e (a i)) := by
    simp only [bootstrapOriginalReuse, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul]
  rw [hgroup]
  exact t14b3_hotDeck_weights hn (p ∘ a) (r ∘ a) (e ∘ a)

private theorem t14b3_two_draw_sign_integral {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (r : Fin n → Bool) (a b : Fin n → Fin n) :
    (∫ e, (hotDeck (resample (fun j => (p j, r j, e j)) a) -
      hotDeck (resample (fun j => (p j, r j, e j)) b))^2 ∂signProductLaw n) =
      (∑ j, (bootstrapOriginalReuse p r a j - bootstrapOriginalReuse p r b j)^2) /
        (n : ℝ)^2 := by
  classical
  have hdiff (e : Fin n → Bool) :
      hotDeck (resample (fun j => (p j, r j, e j)) a) -
        hotDeck (resample (fun j => (p j, r j, e j)) b) =
      (∑ j, (bootstrapOriginalReuse p r a j - bootstrapOriginalReuse p r b j) *
        noise (e j)) / (n : ℝ) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, sub_div]
    linarith [t14b3_bootstrap_weights hn p r a e, t14b3_bootstrap_weights hn p r b e]
  simp_rw [hdiff, div_pow]
  rw [integral_div, t14b3_sign_square]

/-- P001-T14: the two-bootstrap-draw identity. -/
theorem hot_deck_two_bootstrap_draw_reuse_identity_proof {n : ℕ} (hn : 0 < n)
  (p : Fin n → ℝ) (r : Fin n → Bool) :
  mean (signProductLaw n) (fun e => bootVar hotDeck (fun j => (p j,r j,e j))) =
    (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n, ∑ j : Fin n,
      (bootstrapOriginalReuse p r a j-bootstrapOriginalReuse p r b j)^2)/
      (2*(n : ℝ)^2*((n : ℝ)^n)^2) := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcard : (Fintype.card (Fin n → Fin n) : ℝ) = (n : ℝ)^n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hcard_ne : (Fintype.card (Fin n → Fin n) : ℝ) ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero n hnR
  have hv (e : Fin n → Bool) :
      bootVar hotDeck (fun j => (p j, r j, e j)) =
        (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n,
          (hotDeck (resample (fun j => (p j, r j, e j)) a) -
            hotDeck (resample (fun j => (p j, r j, e j)) b))^2) /
          (2 * ((n : ℝ)^n)^2) := by
    unfold bootVar bootMean
    simpa only [hcard] using t14b3_two_draw_finite_variance hcard_ne
      (fun a => hotDeck (resample (fun j => (p j, r j, e j)) a))
  calc
    mean (signProductLaw n) (fun e => bootVar hotDeck (fun j => (p j, r j, e j))) =
        (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n,
          ∫ e, (hotDeck (resample (fun j => (p j, r j, e j)) a) -
            hotDeck (resample (fun j => (p j, r j, e j)) b))^2 ∂signProductLaw n) /
          (2 * ((n : ℝ)^n)^2) := by
      unfold mean
      simp_rw [hv]
      rw [integral_div]
      congr 1
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum _ (fun _ _ => Integrable.of_finite)
    _ = (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n,
          (∑ j : Fin n,
            (bootstrapOriginalReuse p r a j-bootstrapOriginalReuse p r b j)^2) /
              (n : ℝ)^2) / (2 * ((n : ℝ)^n)^2) := by
      simp_rw [t14b3_two_draw_sign_integral hn p r]
    _ = (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n, ∑ j : Fin n,
          (bootstrapOriginalReuse p r a j-bootstrapOriginalReuse p r b j)^2) /
          (2*(n : ℝ)^2*((n : ℝ)^n)^2) := by
      simp_rw [← Finset.sum_div]
      ring

end

end AronowAudit.P001.Wave1
