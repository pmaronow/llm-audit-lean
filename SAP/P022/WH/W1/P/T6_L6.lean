import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L6
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

lemma abs_max_zero_sub_max_zero (x y : ℝ) :
    |max 0 x - max 0 y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have hmono : max 0 x ≤ max 0 y := max_le_max le_rfl h
    have hupper : max 0 y ≤ max 0 x + (y - x) :=
      max_le (by positivity) (by linarith [le_max_right 0 x])
    rw [abs_le, abs_of_nonpos (sub_nonpos.mpr h)]
    constructor <;> nlinarith
  · have hmono : max 0 y ≤ max 0 x := max_le_max le_rfl h
    have hupper : max 0 x ≤ max 0 y + (x - y) :=
      max_le (by positivity) (by linarith [le_max_right 0 y])
    rw [abs_le, abs_of_nonneg (sub_nonneg.mpr h)]
    constructor <;> nlinarith

lemma abs_lower_frechet_sub (u v u' v' : ℝ) :
    |max 0 (u + v - 1) - max 0 (u' + v' - 1)| ≤
      |u - u'| + |v - v'| := by
  calc
    |max 0 (u + v - 1) - max 0 (u' + v' - 1)| ≤
        |(u + v - 1) - (u' + v' - 1)| := abs_max_zero_sub_max_zero _ _
    _ = |(u - u') + (v - v')| := by congr 1 <;> ring
    _ ≤ |u - u'| + |v - v'| := abs_add_le _ _

lemma marginal_as_variance {s : ℕ} (N : ℕ) (a : Fin s → ℝ) :
    marginalVarianceEstimate N a =
      (((N : ℝ) - 1) / N) * ((s : ℝ) * finiteVariance a / ((s : ℝ) - 1)) := by
  calc
    marginalVarianceEstimate N a = AronowAudit.P022.marginalVarianceEstimate N a :=
      (SAP.P022.Bridge.marginalVarianceEstimate_eq N a).symm
    _ = (((N : ℝ) - 1) / N) *
        ((s : ℝ) * AronowAudit.P022.finiteVariance a / ((s : ℝ) - 1)) :=
      AronowAudit.P022.Wave1.GP022B2b_proposition2_corrected_finite_marginal_as_variance N a
    _ = (((N : ℝ) - 1) / N) * ((s : ℝ) * finiteVariance a / ((s : ℝ) - 1)) := by
      rw [SAP.P022.Bridge.finiteVariance_eq]

lemma finite_variance_second_moment {N : ℕ} (hN : 0 < N) (v : Fin N → ℝ) :
    finiteVariance v = finiteMean (fun i => v i ^ 2) - finiteMean v ^ 2 := by
  simpa only [SAP.P022.Bridge.finiteVariance_eq, SAP.P022.Bridge.finiteMean_eq] using
    (AronowAudit.P022.finite_variance_second_moment hN v)

lemma lower_finite_union_bound (d : Design) (E : Assignment d → Prop)
    (F : Fin 7 → Assignment d → Prop) (h : ∀ π, E π → ∃ j, F j π) :
    designProbability d E ≤ ∑ j, designProbability d (F j) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · rw [if_pos hE]
    obtain ⟨j, hj⟩ := h π hE
    calc
      (1 : ℝ) = if F j π then 1 else 0 := by rw [if_pos hj]
      _ ≤ ∑ i : Fin 7, if F i π then (1 : ℝ) else 0 := by
        exact Finset.single_le_sum (f := fun i : Fin 7 => if F i π then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [if_neg hE]
    apply Finset.sum_nonneg
    intro j _
    dsimp only
    split_ifs <;> norm_num

lemma lowerFrechet_inner_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C x : ℝ) :
    IntervalIntegrable (fun y => frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y)
      volume (-C) C := by
  have hmono : Monotone (fun y => frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y) := by
    intro y y' hyy
    change max 0 (empiricalCDF a x + empiricalCDF b y - 1) ≤
      max 0 (empiricalCDF a x + empiricalCDF b y' - 1)
    apply max_le_max le_rfl
    apply sub_le_sub_right
    exact add_le_add le_rfl
      ((AronowAudit.P022.Wave1.GP022B2b_proposition2_corrected_finite_empiricalCDF_mono b) hyy)
  exact hmono.intervalIntegrable

lemma lowerFrechet_outer_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    IntervalIntegrable (fun x => ∫ y in (-C)..C,
      frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y) volume (-C) C := by
  have hmono : Monotone (fun x => ∫ y in (-C)..C,
      frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y) := by
    intro x x' hxx'
    apply intervalIntegral.integral_mono (by linarith) (lowerFrechet_inner_integrable a b C x)
      (lowerFrechet_inner_integrable a b C x')
    intro y
    change max 0 (empiricalCDF a x + empiricalCDF b y - 1) ≤
      max 0 (empiricalCDF a x' + empiricalCDF b y - 1)
    apply max_le_max le_rfl
    apply sub_le_sub_right
    exact add_le_add
      ((AronowAudit.P022.Wave1.GP022B2b_proposition2_corrected_finite_empiricalCDF_mono a) hxx')
      le_rfl
  exact hmono.intervalIntegrable

lemma lowerFrechet_double_integral_sub {m k N : ℕ}
    (a : Fin m → ℝ) (b : Fin k → ℝ) (y1 y0 : Fin N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y -
        frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y) =
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y) -
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y) := by
  have hinner : ∀ x,
      (∫ y in (-C)..C,
        frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y -
          frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y) =
      (∫ y in (-C)..C, frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y) -
        (∫ y in (-C)..C, frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y) := by
    intro x
    exact intervalIntegral.integral_sub (lowerFrechet_inner_integrable a b C x)
      (lowerFrechet_inner_integrable y1 y0 C x)
  simp_rw [hinner]
  exact intervalIntegral.integral_sub (lowerFrechet_outer_integrable a b C hC)
    (lowerFrechet_outer_integrable y1 y0 C hC)

lemma lower_seven_term_identity (hrepr : LowerQuantileRepresentation)
    (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C) (π : Assignment d) :
    (d.N : ℝ) * (estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L) =
      sevenTotal (lowerSevenTerms d y1 y0 C π) := by
  classical
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hm : (0 : ℝ) < d.m := by exact_mod_cast hmnat
  have hk : (0 : ℝ) < d.k := by exact_mod_cast hknat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hm₁ : (0 : ℝ) < (d.m : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ d.m := by exact_mod_cast d.treatment_min
    linarith
  have hk₁ : (0 : ℝ) < (d.k : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ d.k := by exact_mod_cast d.control_min
    linarith
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  have ha : ∀ i, |a i| ≤ C := by
    intro i
    exact (hy (π ⟨i.val, by have := d.sample_le; have := i.isLt; omega⟩)).1
  have hb : ∀ i, |b i| ≤ C := by
    intro i
    exact (hy (π ⟨d.m + i.val, by have := d.sample_le; have := i.isLt; omega⟩)).2
  have hrawa := hrepr hmnat hknat a b C hC ha hb
  have hrawy := hrepr hNnat hNnat y1 y0 C hC (fun i => (hy i).1) (fun i => (hy i).2)
  have hcov : sharpCovariance a b .L - sharpCovariance y1 y0 .L =
      C * (finiteMean a - finiteMean y1 + finiteMean b - finiteMean y0) -
      (finiteMean a * finiteMean b - finiteMean y1 * finiteMean y0) +
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y -
          frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y) := by
    simp [sharpCovariance]
    rw [hrawa, hrawy, lowerFrechet_double_integral_sub a b y1 y0 C hC]
    ring
  have hsplit : (d.N : ℝ) *
      (estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L) =
      (d.N : ℝ) / ((d.N : ℝ) - 1) *
        (((d.N : ℝ) - d.m) / d.m *
          (marginalVarianceEstimate d.N a - finiteVariance y1) +
         ((d.N : ℝ) - d.k) / d.k *
          (marginalVarianceEstimate d.N b - finiteVariance y0) +
         2 * (sharpCovariance a b .L - sharpCovariance y1 y0 .L)) := by
    dsimp [estimatedVariance, estimateBound, populationBound, varianceExpression, a, b]
    ring
  rw [hsplit, hcov, marginal_as_variance d.N a,
    marginal_as_variance d.N b,
    finite_variance_second_moment hmnat a,
    finite_variance_second_moment hknat b,
    finite_variance_second_moment hNnat y1,
    finite_variance_second_moment hNnat y0]
  simp [sevenTotal, lowerSevenTerms, sevenTerms, lowerLastIntegralTerm, frechetCDF]
  dsimp only [a, b]
  field_simp [ne_of_gt hN, ne_of_gt hm, ne_of_gt hk,
    ne_of_gt hN₁, ne_of_gt hm₁, ne_of_gt hk₁]
  <;> ring

lemma lower_last_integral_sup_bound (d : Design) (y1 y0 : Fin d.N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (π : Assignment d) :
    |lowerLastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) +
         cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let M := cdfDistance (empiricalCDF a) (empiricalCDF y1) +
    cdfDistance (empiricalCDF b) (empiricalCDF y0)
  let f : ℝ → ℝ → ℝ := fun x y =>
    frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y -
      frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y
  have hpoint : ∀ x y, |f x y| ≤ M := by
    intro x y
    have hL := abs_lower_frechet_sub (empiricalCDF a x) (empiricalCDF b y)
      (empiricalCDF y1 x) (empiricalCDF y0 y)
    have h1 := AronowAudit.P022.Wave1.GP022B2b_proposition2_corrected_finite_cdfDistance_pointwise
      hmnat hNnat a y1 x
    have h0 := AronowAudit.P022.Wave1.GP022B2b_proposition2_corrected_finite_cdfDistance_pointwise
      hknat hNnat b y0 y
    have hdist : |empiricalCDF a x - empiricalCDF y1 x| +
        |empiricalCDF b y - empiricalCDF y0 y| ≤ M := by
      dsimp [M]
      have h1' : |empiricalCDF a x - empiricalCDF y1 x| ≤
          cdfDistance (empiricalCDF a) (empiricalCDF y1) := by
        simpa only [SAP.P022.Bridge.cdfDistance_eq, SAP.P022.Bridge.empiricalCDF_eq] using h1
      have h0' : |empiricalCDF b y - empiricalCDF y0 y| ≤
          cdfDistance (empiricalCDF b) (empiricalCDF y0) := by
        simpa only [SAP.P022.Bridge.cdfDistance_eq, SAP.P022.Bridge.empiricalCDF_eq] using h0
      exact add_le_add h1' h0'
    have hLip : |f x y| ≤
        |empiricalCDF a x - empiricalCDF y1 x| +
          |empiricalCDF b y - empiricalCDF y0 y| := by
      simpa [f, frechetCDF] using hL
    exact hLip.trans hdist
  have hlen : |C - -C| = 2 * C := by
    rw [abs_of_nonneg (by linarith : 0 ≤ C - -C)]
    ring
  have hinner : ∀ x, |∫ y in (-C)..C, f x y| ≤ M * (2 * C) := by
    intro x
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := f x) (C := M)
      (fun y _ => by simpa only [Real.norm_eq_abs] using hpoint x y)
    simpa only [Real.norm_eq_abs, hlen] using h
  have houter : |∫ x in (-C)..C, ∫ y in (-C)..C, f x y| ≤
      (M * (2 * C)) * (2 * C) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := fun x => ∫ y in (-C)..C, f x y)
      (C := M * (2 * C))
      (fun x _ => by simpa only [Real.norm_eq_abs] using hinner x)
    simpa only [Real.norm_eq_abs, hlen] using h
  have hcoef : 0 ≤ 2 * (d.N : ℝ) / ((d.N : ℝ) - 1) := by positivity
  change |(2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) *
    (∫ x in (-C)..C, ∫ y in (-C)..C, f x y)| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    (2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) *
        |∫ x in (-C)..C, ∫ y in (-C)..C, f x y| ≤
        (2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) * ((M * (2 * C)) * (2 * C)) :=
      mul_le_mul_of_nonneg_left houter hcoef
    _ = (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M := by ring

end
end SAP.P022.WH.W1.P.T6_L6

open SAP.P022 SAP.P022.WH.W1
open SAP.P022.WH.W1.P.T6_L6

theorem SAP.P022.WH.W1.T6_L6_proof : SAP.P022.WH.W1.T6_L6 := by
  intro hrepr d y1 y0 C hC hy
  have hidentity := lower_seven_term_identity hrepr d y1 y0 C hC hy
  have hsup := lower_last_integral_sup_bound d y1 y0 C hC
  refine ⟨hidentity, ?_, hsup, ?_⟩
  · intro a ε ha hbudget
    have hpoint : ∀ π,
        ε ≤ (d.N : ℝ) * |estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L| →
        ∃ j, a j ≤ |lowerSevenTerms d y1 y0 C π j| := by
      intro π hlarge
      have habs : (d.N : ℝ) *
          |estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L| =
          |sevenTotal (lowerSevenTerms d y1 y0 C π)| := by
        calc
          _ = |(d.N : ℝ) *
              (estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L)| := by
            have hNabs : |(d.N : ℝ)| = (d.N : ℝ) := abs_of_nonneg (Nat.cast_nonneg d.N)
            calc
              _ = |(d.N : ℝ)| *
                  |estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L| := by
                rw [hNabs]
              _ = _ := by rw [abs_mul, hNabs]
          _ = _ := congrArg abs (hidentity π)
      rw [habs] at hlarge
      exact SAP.P022.Bridge.seven_term_budget (lowerSevenTerms d y1 y0 C π) a ε ha hbudget hlarge
    refine ⟨hpoint, ?_⟩
    exact lower_finite_union_bound d (fun π => ε ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L|)
      (fun j π => a j ≤ |lowerSevenTerms d y1 y0 C π j|) hpoint
  · intro hCp ε2 ε3 hε2 hε3 π hlarge
    have hN : (0 : ℝ) < d.N := by
      exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
    have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
      have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
      linarith
    have hden : 0 < 8 * (d.N : ℝ) * C ^ 2 := by positivity
    have hsum : ((d.N : ℝ) - 1) * (ε2 + ε3) ≤
        8 * (d.N : ℝ) * C ^ 2 *
          (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) +
           cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
      have hbound := hlarge.trans (hsup π)
      have hmul := mul_le_mul_of_nonneg_left hbound hN₁.le
      have heq : ((d.N : ℝ) - 1) *
          ((8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
            (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) +
             cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) =
          8 * (d.N : ℝ) * C ^ 2 *
            (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) +
             cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
        field_simp [ne_of_gt hN₁]
      calc
        _ ≤ ((d.N : ℝ) - 1) *
            ((8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
              (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) +
               cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) := hmul
        _ = _ := heq
    by_contra hnot
    push_neg at hnot
    have h1 : 8 * (d.N : ℝ) * C ^ 2 *
        cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) <
          ((d.N : ℝ) - 1) * ε2 := by
      have ht := (lt_div_iff₀ hden).mp hnot.1
      nlinarith [ht]
    have h0 : 8 * (d.N : ℝ) * C ^ 2 *
        cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0) <
          ((d.N : ℝ) - 1) * ε3 := by
      have ht := (lt_div_iff₀ hden).mp hnot.2
      nlinarith [ht]
    nlinarith [hsum]
