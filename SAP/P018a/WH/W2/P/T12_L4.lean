import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W2.P.T12_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private abbrev MixedUnit := ℝ × Bool
private abbrev MixedPair := MixedUnit × MixedUnit

private lemma fair_sign_square_integral :
    (∫ b, AronowAudit.P018.signValue b ^ 2 ∂AronowAudit.P018.fairLaw) = 1 := by
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  calc
    _ = ∫ _b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun b => by simp [AronowAudit.P018.signValue])
    _ = 1 := by
      rw [integral_const]
      have hp : AronowAudit.P018.fairLaw.real (Set.univ : Set Bool) = 1 := probReal_univ
      simpa using hp

private lemma fair_sign_constant_integral (c : ℝ) :
    (∫ _b : Bool, c ∂AronowAudit.P018.fairLaw) = c := by
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  rw [integral_const]
  have hp : AronowAudit.P018.fairLaw.real (Set.univ : Set Bool) = 1 := probReal_univ
  simpa using congrArg (fun x : ℝ => x * c) hp

private lemma uniform_constant_integral (c : ℝ) :
    (∫ _z : ℝ, c ∂AronowAudit.P018.uniformUnitLaw) = c := by
  letI : IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw := inferInstance
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

private lemma uniform_first_integral :
    (∫ z, z ∂AronowAudit.P018.uniformUnitLaw) = 0 := by
  exact AronowAudit.P018.uniform_unit_moments.1

private lemma uniform_second_integral :
    (∫ z, z ^ 2 ∂AronowAudit.P018.uniformUnitLaw) = 1 / 3 := by
  exact AronowAudit.P018.uniform_unit_moments.2.1

private lemma fair_sign_integral :
    (∫ b, AronowAudit.P018.signValue b ∂AronowAudit.P018.fairLaw) = 0 :=
  AronowAudit.P018.Wave1.printed_fair_integral

private lemma uniform_pair_support : ∀ᵐ zz : ℝ × ℝ ∂
    AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw,
    zz.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ zz.2 ∈ Set.Icc (-1 : ℝ) 1 := by
  have h : ∀ᵐ z ∂AronowAudit.P018.uniformUnitLaw, z ∈ Set.Icc (-1 : ℝ) 1 :=
    ProbabilityTheory.ae_cond_mem measurableSet_Icc
  apply (Measure.ae_prod_iff_ae_ae
    (p := fun zz : ℝ × ℝ => zz.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ zz.2 ∈ Set.Icc (-1 : ℝ) 1)
    (MeasurableSet.inter (measurableSet_Icc.preimage measurable_fst)
      (measurableSet_Icc.preimage measurable_snd))).2
  filter_upwards [h] with z hz
  filter_upwards [h] with z' hz'
  exact ⟨hz, hz'⟩

private lemma mixed_pair_uniform_support : ∀ᵐ uv : MixedPair ∂
    (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw).prod
      (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw),
    uv.1.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ uv.2.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  have hu : ∀ᵐ u : MixedUnit ∂
      AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw,
      u.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    have hz : ∀ᵐ z ∂AronowAudit.P018.uniformUnitLaw, z ∈ Set.Icc (-1 : ℝ) 1 :=
      ProbabilityTheory.ae_cond_mem measurableSet_Icc
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun u : MixedUnit => u.1 ∈ Set.Icc (-1 : ℝ) 1)
      (measurableSet_Icc.preimage measurable_fst)).2
    filter_upwards [hz] with z hz
    exact Filter.Eventually.of_forall (fun _ => hz)
  apply (Measure.ae_prod_iff_ae_ae
    (p := fun uv : MixedPair =>
      uv.1.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ uv.2.1 ∈ Set.Icc (-1 : ℝ) 1)
    (MeasurableSet.inter
      (measurableSet_Icc.preimage (measurable_fst.comp measurable_fst))
      (measurableSet_Icc.preimage (measurable_fst.comp measurable_snd)))).2
  filter_upwards [hu] with u hu₁
  filter_upwards [hu] with v hv
  exact ⟨hu₁, hv⟩

private lemma uniform_pair_power_integrable (n : Fin 3) :
    Integrable (fun zz : ℝ × ℝ => (zz.1 + zz.2) ^ (n : ℕ))
      (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := by
  letI : IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw := inferInstance
  letI : IsProbabilityMeasure
      (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := inferInstance
  apply (MemLp.of_bound (p := 2) (by fun_prop) 4 ?_).integrable one_le_two
  have hs := uniform_pair_support
  filter_upwards [hs] with zz hz
  have hsum : ‖zz.1 + zz.2‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    have h1 := abs_le.mpr hz.1
    have h2 := abs_le.mpr hz.2
    nlinarith [abs_add_le zz.1 zz.2]
  have hn : (n : ℕ) ≤ 2 := by omega
  calc
    ‖(zz.1 + zz.2) ^ (n : ℕ)‖ = ‖zz.1 + zz.2‖ ^ (n : ℕ) := norm_pow _ _
    _ ≤ 2 ^ (n : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hsum _
    _ ≤ 4 := by
      have hp : (2 : ℝ) ^ (n : ℕ) ≤ 2 ^ 2 := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hn)
      norm_num at hp ⊢
      exact hp

private lemma fair_pair_power_integrable (n : Fin 3) :
    Integrable (fun ww : Bool × Bool =>
      (AronowAudit.P018.signValue ww.1 + AronowAudit.P018.signValue ww.2) ^ (n : ℕ))
      (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := by
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure
      (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := inferInstance
  apply (MemLp.of_bound (p := 2) (by fun_prop) 4 ?_).integrable one_le_two
  filter_upwards [] with ww
  have hsum : ‖AronowAudit.P018.signValue ww.1 +
      AronowAudit.P018.signValue ww.2‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |AronowAudit.P018.signValue ww.1| +
          |AronowAudit.P018.signValue ww.2| := abs_add_le _ _
      _ = 2 := by cases ww.1 <;> cases ww.2 <;> norm_num [AronowAudit.P018.signValue]
  have hn : (n : ℕ) ≤ 2 := by omega
  calc
    ‖(AronowAudit.P018.signValue ww.1 +
        AronowAudit.P018.signValue ww.2) ^ (n : ℕ)‖ =
        ‖AronowAudit.P018.signValue ww.1 +
          AronowAudit.P018.signValue ww.2‖ ^ (n : ℕ) := norm_pow _ _
    _ ≤ 2 ^ (n : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hsum _
    _ ≤ 4 := by
      have hp : (2 : ℝ) ^ (n : ℕ) ≤ 2 ^ 2 := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hn)
      norm_num at hp ⊢
      exact hp

private lemma mixed_pair_power_integrable (a b : Fin 3) :
    Integrable (fun uv : MixedPair =>
      (uv.1.1 + uv.2.1) ^ (a : ℕ) *
      (AronowAudit.P018.signValue uv.1.2 +
          AronowAudit.P018.signValue uv.2.2) ^ (b : ℕ))
      ((AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw).prod
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw)) := by
  letI : IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw := inferInstance
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure
      ((AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw).prod
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw)) := inferInstance
  apply (MemLp.of_bound (p := 2) (by fun_prop) 16 ?_).integrable one_le_two
  have hs := mixed_pair_uniform_support
  filter_upwards [hs] with uv huv
  have hz : ‖uv.1.1 + uv.2.1‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    nlinarith [abs_add_le uv.1.1 uv.2.1, abs_le.mpr huv.1, abs_le.mpr huv.2]
  have hw : ‖AronowAudit.P018.signValue uv.1.2 +
      AronowAudit.P018.signValue uv.2.2‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |AronowAudit.P018.signValue uv.1.2| +
          |AronowAudit.P018.signValue uv.2.2| := abs_add_le _ _
      _ = 2 := by cases uv.1.2 <;> cases uv.2.2 <;> norm_num [AronowAudit.P018.signValue]
  have ha : (a : ℕ) ≤ 2 := by omega
  have hb : (b : ℕ) ≤ 2 := by omega
  calc
    ‖(uv.1.1 + uv.2.1) ^ (a : ℕ) *
        (AronowAudit.P018.signValue uv.1.2 +
          AronowAudit.P018.signValue uv.2.2) ^ (b : ℕ)‖ =
        ‖uv.1.1 + uv.2.1‖ ^ (a : ℕ) *
          ‖AronowAudit.P018.signValue uv.1.2 +
            AronowAudit.P018.signValue uv.2.2‖ ^ (b : ℕ) := by rw [norm_mul, norm_pow, norm_pow]
    _ ≤ 2 ^ (a : ℕ) * 2 ^ (b : ℕ) := mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_le_pow_left₀ (norm_nonneg _) hw _)
      (by positivity) (by positivity)
    _ ≤ 16 := by
      have h1 : (2 : ℝ) ^ (a : ℕ) ≤ 4 := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) ha)
      have h2 : (2 : ℝ) ^ (b : ℕ) ≤ 4 := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hb)
      calc
        _ ≤ (4 : ℝ) * 4 := mul_le_mul h1 h2 (by norm_num) (by norm_num)
        _ = 16 := by norm_num

private lemma separated_pair_integral (f : ℝ × ℝ → ℝ) (g : Bool × Bool → ℝ)
    (hf : Integrable f (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw))
    (hg : Integrable g (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw))
    (hfg : Integrable (fun uv : MixedPair => f (uv.1.1, uv.2.1) *
      g (uv.1.2, uv.2.2))
      ((AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw).prod
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw))) :
    (∫ uv : MixedPair, f (uv.1.1, uv.2.1) * g (uv.1.2, uv.2.2)
      ∂((AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw).prod
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw))) =
      (∫ zz, f zz ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw)) *
      (∫ ww, g ww ∂(AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw)) := by
  rw [integral_prod _ hfg]
  calc
    (∫ u : MixedUnit,
        ∫ v : MixedUnit, f (u.1, v.1) * g (u.2, v.2)
          ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw)
          ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw)) =
      ∫ u : MixedUnit,
        ((∫ z', f (u.1, z') ∂AronowAudit.P018.uniformUnitLaw) *
          ∫ b, g (u.2, b) ∂AronowAudit.P018.fairLaw)
          ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by
          simpa using (integral_prod_mul (fun z' => f (u.1, z'))
            (fun b => g (u.2, b))))
    _ = (∫ zz, f zz ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw)) *
      (∫ ww, g ww ∂(AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw)) := by
      rw [integral_prod_mul
        (fun z => ∫ z', f (z, z') ∂AronowAudit.P018.uniformUnitLaw)
        (fun b => ∫ b', g (b, b') ∂AronowAudit.P018.fairLaw)]
      rw [← integral_prod f hf, ← integral_prod g hg]

private lemma uniform_pair_sum_moment (n : Fin 3) :
    (∫ zz : ℝ × ℝ, (zz.1 + zz.2) ^ (n : ℕ)
      ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw)) =
      if n = 0 then 1 else if n = 1 then 0 else 2 / 3 := by
  letI : IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw := inferInstance
  letI : IsProbabilityMeasure
      (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := inferInstance
  fin_cases n
  · simp only [pow_zero]
    rw [integral_const]
    simp only [probReal_univ, one_smul]
    simp
  · have h1 : Integrable (fun zz : ℝ × ℝ => zz.1)
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := by
      simpa [pow_one] using
        ((AronowAudit.P018.uniform_unit_power_L2 1).integrable one_le_two).comp_fst
          AronowAudit.P018.uniformUnitLaw
    have h2 : Integrable (fun zz : ℝ × ℝ => zz.2)
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := by
      simpa [pow_one] using
        ((AronowAudit.P018.uniform_unit_power_L2 1).integrable one_le_two).comp_snd
          AronowAudit.P018.uniformUnitLaw
    have hpoint : (fun zz : ℝ × ℝ => (zz.1 + zz.2) ^ 1) = fun zz => zz.1 + zz.2 := by
      funext zz
      simp
    rw [hpoint, integral_add h1 h2]
    have hf : (∫ zz : ℝ × ℝ, zz.1 ∂
        AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) = 0 := by
      calc
        _ = (∫ z, z ∂AronowAudit.P018.uniformUnitLaw) *
            ∫ _z : ℝ, (1 : ℝ) ∂AronowAudit.P018.uniformUnitLaw := by
          simpa [uniform_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.uniformUnitLaw) (ν := AronowAudit.P018.uniformUnitLaw)
            (fun z : ℝ => z) (fun _ : ℝ => (1 : ℝ)))
        _ = 0 := by simp [uniform_first_integral, uniform_constant_integral]
    have hs : (∫ zz : ℝ × ℝ, zz.2 ∂
        AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) = 0 := by
      calc
        _ = (∫ _z : ℝ, (1 : ℝ) ∂AronowAudit.P018.uniformUnitLaw) *
            ∫ z, z ∂AronowAudit.P018.uniformUnitLaw := by
          simpa [uniform_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.uniformUnitLaw) (ν := AronowAudit.P018.uniformUnitLaw)
            (fun _ : ℝ => (1 : ℝ)) (fun z : ℝ => z))
        _ = 0 := by simp [uniform_first_integral, uniform_constant_integral]
    simp [hf, hs]
  · have hA : Integrable (fun zz : ℝ × ℝ => zz.1 ^ 2)
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := by
      simpa using ((AronowAudit.P018.uniform_unit_power_L2 2).integrable one_le_two).comp_fst
        AronowAudit.P018.uniformUnitLaw
    have hC : Integrable (fun zz : ℝ × ℝ => zz.2 ^ 2)
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := by
      simpa using ((AronowAudit.P018.uniform_unit_power_L2 2).integrable one_le_two).comp_snd
        AronowAudit.P018.uniformUnitLaw
    have hB : Integrable (fun zz : ℝ × ℝ => 2 * (zz.1 * zz.2))
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) := by
      simpa [pow_one] using (AronowAudit.P018.uniform_pair_monomial_integrable 1 1).const_mul 2
    have hpoint : (fun zz : ℝ × ℝ => (zz.1 + zz.2) ^ 2) =
        fun zz => zz.1 ^ 2 + 2 * (zz.1 * zz.2) + zz.2 ^ 2 := by
      funext zz
      ring
    rw [hpoint]
    have hfirst : (∫ zz : ℝ × ℝ, zz.1 ^ 2 ∂
        AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) = 1 / 3 := by
      calc
        _ = (∫ z, z ^ 2 ∂AronowAudit.P018.uniformUnitLaw) *
            ∫ _z : ℝ, (1 : ℝ) ∂AronowAudit.P018.uniformUnitLaw := by
          simpa [uniform_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.uniformUnitLaw) (ν := AronowAudit.P018.uniformUnitLaw)
            (fun z : ℝ => z ^ 2) (fun _ : ℝ => (1 : ℝ)))
        _ = 1 / 3 := by simp [uniform_second_integral, uniform_constant_integral]
    have hsecond : (∫ zz : ℝ × ℝ, zz.2 ^ 2 ∂
        AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) = 1 / 3 := by
      calc
        _ = (∫ _z : ℝ, (1 : ℝ) ∂AronowAudit.P018.uniformUnitLaw) *
            ∫ z, z ^ 2 ∂AronowAudit.P018.uniformUnitLaw := by
          simpa [uniform_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.uniformUnitLaw) (ν := AronowAudit.P018.uniformUnitLaw)
            (fun _ : ℝ => (1 : ℝ)) (fun z : ℝ => z ^ 2))
        _ = 1 / 3 := by simp [uniform_second_integral, uniform_constant_integral]
    have hcross : (∫ zz : ℝ × ℝ, zz.1 * zz.2 ∂
        AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) = 0 := by
      simpa [pow_one, AronowAudit.P018.uniform_unit_moment] using
        (AronowAudit.P018.uniform_pair_monomial 1 1)
    calc
      (∫ zz : ℝ × ℝ, zz.1 ^ 2 + 2 * (zz.1 * zz.2) + zz.2 ^ 2 ∂
        AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) =
        (∫ zz : ℝ × ℝ, zz.1 ^ 2 + 2 * (zz.1 * zz.2) ∂
          AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw) +
          ∫ zz : ℝ × ℝ, zz.2 ^ 2 ∂
            AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw :=
          integral_add (hA.add hB) hC
      _ = 2 / 3 := by
        rw [integral_add hA hB, integral_const_mul, hfirst, hsecond, hcross]
        norm_num

private lemma fair_pair_sum_moment (n : Fin 3) :
    (∫ ww : Bool × Bool,
      (AronowAudit.P018.signValue ww.1 + AronowAudit.P018.signValue ww.2) ^ (n : ℕ)
      ∂(AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw)) =
      if n = 0 then 1 else if n = 1 then 0 else 2 := by
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure
      (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := inferInstance
  fin_cases n
  · simp only [pow_zero]
    rw [integral_const]
    simp only [probReal_univ, one_smul]
    simp
  · have h1 : Integrable (fun ww : Bool × Bool => AronowAudit.P018.signValue ww.1)
        (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := by
      simpa using (AronowAudit.P018.Wave1.printed_finite_integrable
        AronowAudit.P018.fairLaw AronowAudit.P018.signValue).comp_fst AronowAudit.P018.fairLaw
    have h2 : Integrable (fun ww : Bool × Bool => AronowAudit.P018.signValue ww.2)
        (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := by
      simpa using (AronowAudit.P018.Wave1.printed_finite_integrable
        AronowAudit.P018.fairLaw AronowAudit.P018.signValue).comp_snd AronowAudit.P018.fairLaw
    rw [show (fun ww : Bool × Bool =>
        (AronowAudit.P018.signValue ww.1 + AronowAudit.P018.signValue ww.2) ^ 1) =
        fun ww => AronowAudit.P018.signValue ww.1 +
          AronowAudit.P018.signValue ww.2 by funext ww; simp,
      integral_add h1 h2]
    have ha : (∫ ww : Bool × Bool, AronowAudit.P018.signValue ww.1 ∂
        AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) = 0 := by
      calc
        _ = (∫ b, AronowAudit.P018.signValue b ∂AronowAudit.P018.fairLaw) *
            ∫ _b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw := by
          simpa [fair_sign_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.fairLaw) (ν := AronowAudit.P018.fairLaw)
            (fun b => AronowAudit.P018.signValue b) (fun _ : Bool => (1 : ℝ)))
        _ = 0 := by simp [fair_sign_integral, fair_sign_constant_integral]
    have hb : (∫ ww : Bool × Bool, AronowAudit.P018.signValue ww.2 ∂
        AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) = 0 := by
      calc
        _ = (∫ _b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw) *
            ∫ b, AronowAudit.P018.signValue b ∂AronowAudit.P018.fairLaw := by
          simpa [fair_sign_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.fairLaw) (ν := AronowAudit.P018.fairLaw)
            (fun _ : Bool => (1 : ℝ)) (fun b => AronowAudit.P018.signValue b))
        _ = 0 := by simp [fair_sign_integral, fair_sign_constant_integral]
    simp [ha, hb]
  · have hA : Integrable (fun ww : Bool × Bool => AronowAudit.P018.signValue ww.1 ^ 2)
        (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := by
      simpa using (AronowAudit.P018.Wave1.printed_finite_integrable
        AronowAudit.P018.fairLaw (fun b => AronowAudit.P018.signValue b ^ 2)).comp_fst
          AronowAudit.P018.fairLaw
    have hC : Integrable (fun ww : Bool × Bool => AronowAudit.P018.signValue ww.2 ^ 2)
        (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := by
      simpa using (AronowAudit.P018.Wave1.printed_finite_integrable
        AronowAudit.P018.fairLaw (fun b => AronowAudit.P018.signValue b ^ 2)).comp_snd
          AronowAudit.P018.fairLaw
    have hB : Integrable (fun ww : Bool × Bool =>
        2 * (AronowAudit.P018.signValue ww.1 * AronowAudit.P018.signValue ww.2))
        (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) := by
      simpa [pow_one] using ((AronowAudit.P018.Wave1.printed_finite_integrable
        AronowAudit.P018.fairLaw AronowAudit.P018.signValue).mul_prod
        (AronowAudit.P018.Wave1.printed_finite_integrable
          AronowAudit.P018.fairLaw AronowAudit.P018.signValue)).const_mul 2
    have hpoint : (fun ww : Bool × Bool =>
        (AronowAudit.P018.signValue ww.1 + AronowAudit.P018.signValue ww.2) ^ 2) =
        fun ww => AronowAudit.P018.signValue ww.1 ^ 2 +
          2 * (AronowAudit.P018.signValue ww.1 * AronowAudit.P018.signValue ww.2) +
          AronowAudit.P018.signValue ww.2 ^ 2 := by
      funext ww
      ring
    rw [hpoint]
    have hfirst : (∫ ww : Bool × Bool, AronowAudit.P018.signValue ww.1 ^ 2 ∂
        AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) = 1 := by
      calc
        _ = (∫ b, AronowAudit.P018.signValue b ^ 2 ∂AronowAudit.P018.fairLaw) *
            ∫ _b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw := by
          simpa [fair_sign_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.fairLaw) (ν := AronowAudit.P018.fairLaw)
            (fun b => AronowAudit.P018.signValue b ^ 2) (fun _ : Bool => (1 : ℝ)))
        _ = 1 := by rw [fair_sign_square_integral, fair_sign_constant_integral]; norm_num
    have hsecond : (∫ ww : Bool × Bool, AronowAudit.P018.signValue ww.2 ^ 2 ∂
        AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) = 1 := by
      calc
        _ = (∫ _b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw) *
            ∫ b, AronowAudit.P018.signValue b ^ 2 ∂AronowAudit.P018.fairLaw := by
          simpa [fair_sign_constant_integral] using (integral_prod_mul
            (μ := AronowAudit.P018.fairLaw) (ν := AronowAudit.P018.fairLaw)
            (fun _ : Bool => (1 : ℝ)) (fun b => AronowAudit.P018.signValue b ^ 2))
        _ = 1 := by rw [fair_sign_square_integral, fair_sign_constant_integral]; norm_num
    have hcross : (∫ ww : Bool × Bool,
        AronowAudit.P018.signValue ww.1 * AronowAudit.P018.signValue ww.2 ∂
        AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) = 0 := by
      rw [integral_prod_mul (μ := AronowAudit.P018.fairLaw) (ν := AronowAudit.P018.fairLaw),
        fair_sign_integral]
      ring
    calc
      (∫ ww : Bool × Bool,
        AronowAudit.P018.signValue ww.1 ^ 2 +
          2 * (AronowAudit.P018.signValue ww.1 * AronowAudit.P018.signValue ww.2) +
          AronowAudit.P018.signValue ww.2 ^ 2 ∂
        AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) =
        (∫ ww : Bool × Bool,
          AronowAudit.P018.signValue ww.1 ^ 2 +
            2 * (AronowAudit.P018.signValue ww.1 * AronowAudit.P018.signValue ww.2) ∂
          AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw) +
          ∫ ww : Bool × Bool, AronowAudit.P018.signValue ww.2 ^ 2 ∂
            AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw :=
        integral_add (hA.add hB) hC
      _ = 2 := by
        rw [integral_add hA hB, integral_const_mul, hfirst, hsecond, hcross]
        norm_num

private lemma mixed_pair_sum_moment (a b : Fin 3) :
    (∫ uv : MixedPair,
      (uv.1.1 + uv.2.1) ^ (a : ℕ) *
        (AronowAudit.P018.signValue uv.1.2 +
          AronowAudit.P018.signValue uv.2.2) ^ (b : ℕ)
      ∂((AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw).prod
        (AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw))) =
      (if a = 0 then 1 else if a = 1 then 0 else 2 / 3) *
      (if b = 0 then 1 else if b = 1 then 0 else 2) := by
  rw [separated_pair_integral _ _ (uniform_pair_power_integrable a)
    (fair_pair_power_integrable b) (mixed_pair_power_integrable a b),
    uniform_pair_sum_moment, fair_pair_sum_moment]

private lemma mixed_kernel_measure :
    wholeMixedKernel.μ = AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw := rfl

private lemma mixed_z_moment (n : Fin 3) :
    (∫ uv : MixedPair, (uv.1.1 + uv.2.1) ^ (n : ℕ)
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) =
      if n = 0 then 1 else if n = 1 then 0 else 2 / 3 := by
  rw [mixed_kernel_measure]
  simpa [pow_zero] using mixed_pair_sum_moment n 0

private lemma mixed_w_moment (n : Fin 3) :
    (∫ uv : MixedPair,
      (AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2) ^ (n : ℕ)
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) =
      if n = 0 then 1 else if n = 1 then 0 else 2 := by
  rw [mixed_kernel_measure]
  simpa [pow_zero] using mixed_pair_sum_moment 0 n

lemma mixed_population_gram :
    populationGram wholeMixedKernel = !![1,0;0,2/3] := by
  unfold populationGram meanMat
  ext i j
  fin_cases i <;> fin_cases j
  · change (∫ uv : MixedPair, 1 * 1 ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) = 1
    simpa using mixed_z_moment 0
  · change (∫ uv : MixedPair, 1 * (uv.1.1 + uv.2.1)
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) = 0
    simpa [pow_one] using mixed_z_moment 1
  · change (∫ uv : MixedPair, (uv.1.1 + uv.2.1) * 1
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) = 0
    simpa [pow_one] using mixed_z_moment 1
  · change (∫ uv : MixedPair, (uv.1.1 + uv.2.1) * (uv.1.1 + uv.2.1)
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) = 2 / 3
    simpa [pow_two] using mixed_z_moment 2

private lemma mixed_population_score_mean :
    meanVec (wholeMixedKernel.μ.prod wholeMixedKernel.μ)
      (fun uv => score (wholeMixedKernel.X uv.1 uv.2) (wholeMixedKernel.Y uv.1 uv.2)) = 0 := by
  unfold meanVec
  ext i
  fin_cases i
  · change (∫ uv : MixedPair,
      score (![1, uv.1.1 + uv.2.1] : Vec 2)
        (AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2) 0
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) = 0
    simpa [score] using mixed_w_moment 1
  · change (∫ uv : MixedPair,
      score (![1, uv.1.1 + uv.2.1] : Vec 2)
        (AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2) 1
      ∂wholeMixedKernel.μ.prod wholeMixedKernel.μ) = 0
    have h := mixed_pair_sum_moment 1 1
    simpa [score, pow_one, mul_comm, mixed_kernel_measure] using h

lemma mixed_population_beta : populationBeta wholeMixedKernel = 0 := by
  unfold populationBeta
  rw [mixed_population_score_mean]
  simp

private lemma mixed_population_score (uv : MixedPair) :
    populationScore wholeMixedKernel uv.1 uv.2 =
      ![AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2,
        (uv.1.1 + uv.2.1) *
          (AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2)] := by
  simp only [populationScore, populationResidual, mixed_population_beta]
  ext i
  fin_cases i
  · simp [dot, score, wholeMixedKernel, SAP.P018a.signValue,
      AronowAudit.P018.signValue]
  · simp [dot, score, wholeMixedKernel, SAP.P018a.signValue,
      AronowAudit.P018.signValue, Fin.sum_univ_succ, mul_comm]
    <;> ring

lemma mixed_scoreH :
    scoreH wholeMixedKernel = !![2,0;0,4/3] := by
  unfold scoreH meanMat
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [outer, mixed_population_score, pow_two, mul_comm, mul_left_comm, mul_assoc,
      mixed_kernel_measure] using
      mixed_pair_sum_moment 0 2
  · simpa [outer, mixed_population_score, pow_one, pow_two, mul_comm, mul_left_comm,
      mul_assoc, mixed_kernel_measure] using
      mixed_pair_sum_moment 1 2
  · simpa [outer, mixed_population_score, pow_one, pow_two, mul_comm, mul_left_comm,
      mul_assoc, mixed_kernel_measure] using
      mixed_pair_sum_moment 1 2
  · have h := mixed_pair_sum_moment 2 2
    norm_num at h
    simpa [outer, mixed_population_score, pow_two, mul_comm, mul_left_comm, mul_assoc,
      mixed_kernel_measure] using h

private lemma mixed_uniform_shift_integral (c : ℝ) :
    (∫ z, c + z ∂AronowAudit.P018.uniformUnitLaw) = c := by
  have hi : Integrable (fun z : ℝ => z) AronowAudit.P018.uniformUnitLaw :=
    by simpa [pow_one] using
      (AronowAudit.P018.uniform_unit_power_L2 1).integrable one_le_two
  have hc : Integrable (fun _z : ℝ => c) AronowAudit.P018.uniformUnitLaw := integrable_const c
  rw [integral_add hc hi]
  have hz : (∫ z, z ∂AronowAudit.P018.uniformUnitLaw) = 0 := uniform_first_integral
  have hconst : (∫ _z : ℝ, c ∂AronowAudit.P018.uniformUnitLaw) = c :=
    uniform_constant_integral c
  rw [hconst, hz]
  ring

private lemma mixed_fair_shift_integral (c : ℝ) :
    (∫ b, c + AronowAudit.P018.signValue b ∂AronowAudit.P018.fairLaw) = c := by
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  have hs : Integrable AronowAudit.P018.signValue AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_finite_integrable _ _
  have hc : Integrable (fun _b : Bool => c) AronowAudit.P018.fairLaw := integrable_const c
  rw [integral_add hc hs]
  have hm : (∫ b, AronowAudit.P018.signValue b ∂AronowAudit.P018.fairLaw) = 0 :=
    fair_sign_integral
  have hconst : (∫ _b : Bool, c ∂AronowAudit.P018.fairLaw) = c :=
    fair_sign_constant_integral c
  rw [hconst, hm]
  ring

private lemma mixed_projection (u : MixedUnit) :
    projection wholeMixedKernel u =
      ![SAP.P018a.signValue u.2, u.1 * SAP.P018a.signValue u.2] := by
  unfold projection meanVec
  ext i
  fin_cases i
  · change (∫ v : MixedUnit, (populationScore wholeMixedKernel u v) 0
      ∂wholeMixedKernel.μ) = SAP.P018a.signValue u.2
    rw [mixed_kernel_measure]
    have hcoord (v : MixedUnit) :
        (populationScore wholeMixedKernel u v) 0 =
          AronowAudit.P018.signValue u.2 + AronowAudit.P018.signValue v.2 := by
      simpa [SAP.P018a.signValue, AronowAudit.P018.signValue] using
        congrArg (fun x : Vec 2 => x 0) (mixed_population_score (u, v))
    simp_rw [hcoord]
    calc
      _ = (∫ _z : ℝ, (1 : ℝ) ∂AronowAudit.P018.uniformUnitLaw) *
          (∫ b, AronowAudit.P018.signValue u.2 + AronowAudit.P018.signValue b
            ∂AronowAudit.P018.fairLaw) := by
        simpa using (integral_prod_mul (μ := AronowAudit.P018.uniformUnitLaw)
          (ν := AronowAudit.P018.fairLaw) (fun _ : ℝ => (1 : ℝ))
          (fun b => AronowAudit.P018.signValue u.2 + AronowAudit.P018.signValue b))
      _ = SAP.P018a.signValue u.2 := by
        rw [uniform_constant_integral, mixed_fair_shift_integral]
        simp [SAP.P018a.signValue, AronowAudit.P018.signValue]
  · change (∫ v : MixedUnit, (populationScore wholeMixedKernel u v) 1
      ∂wholeMixedKernel.μ) = u.1 * SAP.P018a.signValue u.2
    rw [mixed_kernel_measure]
    have hcoord (v : MixedUnit) :
        (populationScore wholeMixedKernel u v) 1 =
          (u.1 + v.1) *
            (AronowAudit.P018.signValue u.2 + AronowAudit.P018.signValue v.2) := by
      simpa [SAP.P018a.signValue, AronowAudit.P018.signValue] using
        congrArg (fun x : Vec 2 => x 1) (mixed_population_score (u, v))
    simp_rw [hcoord]
    calc
      _ = (∫ z, u.1 + z ∂AronowAudit.P018.uniformUnitLaw) *
          (∫ b, AronowAudit.P018.signValue u.2 + AronowAudit.P018.signValue b
            ∂AronowAudit.P018.fairLaw) := by
        simpa using (integral_prod_mul (μ := AronowAudit.P018.uniformUnitLaw)
          (ν := AronowAudit.P018.fairLaw) (fun z => u.1 + z)
          (fun b => AronowAudit.P018.signValue u.2 + AronowAudit.P018.signValue b))
      _ = u.1 * SAP.P018a.signValue u.2 := by
        rw [mixed_uniform_shift_integral, mixed_fair_shift_integral]
        simp [SAP.P018a.signValue, AronowAudit.P018.signValue]

private lemma mixed_unit_moment (n : Fin 3) :
    (∫ u : MixedUnit, u.1 ^ (n : ℕ) * SAP.P018a.signValue u.2 ^ 2
      ∂wholeMixedKernel.μ) = if n = 0 then 1 else if n = 1 then 0 else 1 / 3 := by
  rw [mixed_kernel_measure]
  change (∫ u : MixedUnit, u.1 ^ (n : ℕ) *
    AronowAudit.P018.signValue u.2 ^ 2
    ∂(AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.fairLaw)) = _
  rw [integral_prod_mul (μ := AronowAudit.P018.uniformUnitLaw)
    (ν := AronowAudit.P018.fairLaw) (fun z => z ^ (n : ℕ))
    (fun b => AronowAudit.P018.signValue b ^ 2)]
  fin_cases n <;>
    simp [AronowAudit.P018.uniform_unit_moment, fair_sign_square_integral,
      uniform_constant_integral, uniform_first_integral, uniform_second_integral] <;>
    norm_num

lemma mixed_projection_gamma :
    projectionGamma wholeMixedKernel = !![1,0;0,1/3] := by
  unfold projectionGamma meanMat
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [outer, mixed_projection, pow_zero, mul_one, pow_two] using mixed_unit_moment 0
  · simpa [outer, mixed_projection, pow_one, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      mixed_unit_moment 1
  · simpa [outer, mixed_projection, pow_one, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      mixed_unit_moment 1
  · simpa [outer, mixed_projection, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      mixed_unit_moment 2

lemma mixed_standing : Standing wholeMixedKernel := by
  letI : IsProbabilityMeasure SAP.P018a.uniformUnitLaw := by
    simpa [SAP.P018a.uniformUnitLaw, AronowAudit.P018.uniformUnitLaw] using
      (inferInstance : IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw)
  letI : IsProbabilityMeasure SAP.P018a.fairLaw := by
    simpa [SAP.P018a.fairLaw, AronowAudit.P018.fairLaw] using
      AronowAudit.P018.Wave1.printed_fair_probability
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsProbabilityMeasure (SAP.P018a.uniformUnitLaw.prod SAP.P018a.fairLaw)
    infer_instance
  · change Measurable (fun uv : MixedPair => ![1, uv.1.1 + uv.2.1])
    fun_prop
  · change Measurable (fun uv : MixedPair =>
      SAP.P018a.signValue uv.1.2 + SAP.P018a.signValue uv.2.2)
    fun_prop
  · intro u v
    constructor
    · ext i
      fin_cases i <;> simp [wholeMixedKernel, add_comm]
    · simp [wholeMixedKernel, add_comm]
  · refine ⟨2, by norm_num, ?_⟩
    have hs := mixed_pair_uniform_support
    filter_upwards [hs] with uv huv
    constructor
    · change ‖![1, uv.1.1 + uv.2.1]‖ ≤ 2
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro i
      fin_cases i
      · norm_num
      · rw [Real.norm_eq_abs]
        calc
          |uv.1.1 + uv.2.1| ≤ |uv.1.1| + |uv.2.1| := abs_add_le _ _
          _ ≤ 1 + 1 := add_le_add (abs_le.mpr huv.1) (abs_le.mpr huv.2)
          _ = 2 := by norm_num
    · change |SAP.P018a.signValue uv.1.2 + SAP.P018a.signValue uv.2.2| ≤ 2
      calc
        _ ≤ |SAP.P018a.signValue uv.1.2| + |SAP.P018a.signValue uv.2.2| := abs_add_le _ _
        _ = 2 := by cases uv.1.2 <;> cases uv.2.2 <;> norm_num [SAP.P018a.signValue]
  · exact ⟨0, fun _ _ => rfl⟩
  · rw [mixed_population_gram]
    norm_num [Matrix.det_fin_two]

end SAP.P018a.WH.W2.P.T12_L4

theorem SAP.P018a.WH.W2.T12_L4_proof : SAP.P018a.WH.W2.T12_L4 := by
  exact ⟨SAP.P018a.WH.W2.P.T12_L4.mixed_standing,
    SAP.P018a.WH.W2.P.T12_L4.mixed_population_gram,
    SAP.P018a.WH.W2.P.T12_L4.mixed_population_beta,
    SAP.P018a.WH.W2.P.T12_L4.mixed_scoreH,
    SAP.P018a.WH.W2.P.T12_L4.mixed_projection_gamma⟩
