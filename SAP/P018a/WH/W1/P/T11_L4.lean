import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace SAP.P018a.WH.W1.P.T11_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

local instance fairProbability : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
  AronowAudit.P018.Wave1.printed_fair_probability
local instance sapFairProbability : IsProbabilityMeasure SAP.P018a.fairLaw := by
  change IsProbabilityMeasure AronowAudit.P018.fairLaw
  exact AronowAudit.P018.Wave1.printed_fair_probability
local instance sapUniformProbability : IsProbabilityMeasure SAP.P018a.uniformUnitLaw := by
  change IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw
  infer_instance

lemma sap_uniform_eq_audit :
    SAP.P018a.uniformUnitLaw = AronowAudit.P018.uniformUnitLaw := rfl
lemma sap_fair_eq_audit : SAP.P018a.fairLaw = AronowAudit.P018.fairLaw := rfl

abbrev mixedLaw : Measure (ℝ × Bool) :=
  SAP.P018a.uniformUnitLaw.prod SAP.P018a.fairLaw
abbrev pairLaw : Measure ((ℝ × Bool) × (ℝ × Bool)) := mixedLaw.prod mixedLaw

lemma fair_sign_integral :
    (∫ b, AronowAudit.P018.signValue b ∂AronowAudit.P018.fairLaw) = 0 :=
  AronowAudit.P018.Wave1.printed_fair_integral

lemma fair_sign_sq (b : Bool) : (AronowAudit.P018.signValue b)^2 = 1 := by
  cases b <;> norm_num [AronowAudit.P018.signValue]

lemma uniform_moment_zero :
    (∫ z, z^0 ∂AronowAudit.P018.uniformUnitLaw) = 1 := by
  simp

lemma uniform_moment_one :
    (∫ z, z^1 ∂AronowAudit.P018.uniformUnitLaw) = 0 := by
  simpa only [pow_one] using AronowAudit.P018.uniform_unit_moments.1

lemma uniform_moment_two :
    (∫ z, z^2 ∂AronowAudit.P018.uniformUnitLaw) = 1/3 :=
  AronowAudit.P018.uniform_unit_moments.2.1

lemma fair_one_integral :
    (∫ b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw) = 1 := by
  rw [integral_fintype (AronowAudit.P018.Wave1.printed_finite_integrable
    AronowAudit.P018.fairLaw (fun _ : Bool => (1 : ℝ)))]
  norm_num [AronowAudit.P018.fairLaw, Measure.real,
    PMF.toMeasure_uniformOfFintype_apply, Fintype.sum_bool, Fintype.card_bool]

lemma sign_moment_zero :
    (∫ b, AronowAudit.P018.signValue b^0 ∂AronowAudit.P018.fairLaw) = 1 := by
  simpa only [pow_zero, one_pow] using fair_one_integral

lemma sign_moment_one :
    (∫ b, AronowAudit.P018.signValue b^1 ∂AronowAudit.P018.fairLaw) = 0 := by
  simpa only [pow_one] using fair_sign_integral

lemma sign_moment_two :
    (∫ b, AronowAudit.P018.signValue b^2 ∂AronowAudit.P018.fairLaw) = 1 := by
  have h : (fun b : Bool => AronowAudit.P018.signValue b^2) = fun _ => (1 : ℝ) := by
    funext b
    exact fair_sign_sq b
  rw [h, fair_one_integral]

lemma mixed_monomial_integrable (a c : ℕ) :
    Integrable (fun u : ℝ × Bool => u.1^a * AronowAudit.P018.signValue u.2^c) mixedLaw :=
  by
  have h := ((AronowAudit.P018.uniform_unit_power_L2 a).integrable one_le_two).mul_prod
    ((AronowAudit.P018.Wave1.printed_finite_L2 AronowAudit.P018.fairLaw
      (fun b => AronowAudit.P018.signValue b^c)).integrable one_le_two)
  simpa [mixedLaw, sap_uniform_eq_audit, sap_fair_eq_audit] using h

lemma mixed_unit_monomial_integral (a c : ℕ) :
    (∫ u : ℝ × Bool, u.1^a * AronowAudit.P018.signValue u.2^c ∂mixedLaw) =
      (∫ z, z^a ∂AronowAudit.P018.uniformUnitLaw) *
      (∫ b, AronowAudit.P018.signValue b^c ∂AronowAudit.P018.fairLaw) := by
  rw [MeasureTheory.integral_prod_mul (fun z : ℝ => z^a)
    (fun b : Bool => AronowAudit.P018.signValue b^c)]
  rw [sap_uniform_eq_audit, sap_fair_eq_audit]

lemma pair_monomial_integrable (a b c d : ℕ) :
    Integrable
      (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
        (uv.1.1^a * AronowAudit.P018.signValue uv.1.2^c) *
          (uv.2.1^b * AronowAudit.P018.signValue uv.2.2^d)) pairLaw := by
  exact (mixed_monomial_integrable a c).mul_prod (mixed_monomial_integrable b d)

lemma pair_monomial_integral (a b c d : ℕ) :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool),
      (uv.1.1^a * AronowAudit.P018.signValue uv.1.2^c) *
        (uv.2.1^b * AronowAudit.P018.signValue uv.2.2^d) ∂pairLaw) =
      ((∫ z, z^a ∂AronowAudit.P018.uniformUnitLaw) *
        (∫ x, AronowAudit.P018.signValue x^c ∂AronowAudit.P018.fairLaw)) *
      ((∫ z, z^b ∂AronowAudit.P018.uniformUnitLaw) *
        (∫ x, AronowAudit.P018.signValue x^d ∂AronowAudit.P018.fairLaw)) := by
  rw [MeasureTheory.integral_prod_mul
      (fun u : ℝ × Bool => u.1^a * AronowAudit.P018.signValue u.2^c)
      (fun v : ℝ × Bool => v.1^b * AronowAudit.P018.signValue v.2^d),
    mixed_unit_monomial_integral a c, mixed_unit_monomial_integral b d]

lemma mixed_z_integrable (n : ℕ) : Integrable (fun u : ℝ × Bool => u.1^n) mixedLaw := by
  have h := ((AronowAudit.P018.uniform_unit_power_L2 n).integrable one_le_two).mul_prod
    ((AronowAudit.P018.Wave1.printed_finite_L2 AronowAudit.P018.fairLaw
      (fun _ : Bool => (1 : ℝ))).integrable one_le_two)
  simpa [mixedLaw, sap_uniform_eq_audit, sap_fair_eq_audit] using h

lemma mixed_one_integral :
    (∫ b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw) = 1 := fair_one_integral

lemma mixed_z_integral (n : ℕ) :
    (∫ u : ℝ × Bool, u.1^n ∂mixedLaw) =
      (∫ z, z^n ∂AronowAudit.P018.uniformUnitLaw) := by
  calc
    _ = (∫ u : ℝ × Bool, u.1^n * (1 : ℝ) ∂mixedLaw) := by congr 1; funext u; simp
    _ = (∫ z, z^n ∂AronowAudit.P018.uniformUnitLaw) *
        (∫ b : Bool, (1 : ℝ) ∂AronowAudit.P018.fairLaw) := by
      rw [MeasureTheory.integral_prod_mul (fun z : ℝ => z^n) (fun _ : Bool => (1 : ℝ))]
      rw [sap_uniform_eq_audit, sap_fair_eq_audit]
    _ = _ := by rw [mixed_one_integral]; ring

lemma triple_z_integrable (a b c : ℕ) :
    Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.1.1^a * z.1.2.1^b * z.2.1^c)
      ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
  have hpair : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      uv.1.1^a * uv.2.1^b) (mixedLaw.prod mixedLaw) :=
    (mixed_z_integrable a).mul_prod (mixed_z_integrable b)
  have h := hpair.mul_prod (mixed_z_integrable c)
  simpa [mul_assoc] using h

lemma triple_z_integral (a b c : ℕ) :
    (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
      z.1.1.1^a * z.1.2.1^b * z.2.1^c ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) =
      (∫ z, z^a ∂AronowAudit.P018.uniformUnitLaw) *
      (∫ z, z^b ∂AronowAudit.P018.uniformUnitLaw) *
      (∫ z, z^c ∂AronowAudit.P018.uniformUnitLaw) := by
  rw [MeasureTheory.integral_prod_mul
    (fun uv : (ℝ × Bool) × (ℝ × Bool) => uv.1.1^a * uv.2.1^b)
    (fun w : ℝ × Bool => w.1^c)]
  have hp (a b : ℕ) :
      (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1^a * uv.2.1^b ∂(mixedLaw.prod mixedLaw)) =
        (∫ z, z^a ∂AronowAudit.P018.uniformUnitLaw) *
        (∫ z, z^b ∂AronowAudit.P018.uniformUnitLaw) := by
    rw [MeasureTheory.integral_prod_mul (fun u : ℝ × Bool => u.1^a)
      (fun v : ℝ × Bool => v.1^b), mixed_z_integral, mixed_z_integral]
  rw [hp]
  rw [mixed_z_integral c]

def zVal (n : ℕ) : ℝ := if n = 0 then 1 else if n = 1 then 0 else 1/3
def sVal (n : ℕ) : ℝ := if n = 0 then 1 else if n = 1 then 0 else 1

lemma uniform_moment_small (n : ℕ) (hn : n ≤ 2) :
    (∫ z, z^n ∂AronowAudit.P018.uniformUnitLaw) = zVal n := by
  interval_cases n
  · simpa [zVal] using uniform_moment_zero
  · simpa [zVal] using uniform_moment_one
  · simpa [zVal] using uniform_moment_two

lemma sign_moment_small (n : ℕ) (hn : n ≤ 2) :
    (∫ b, AronowAudit.P018.signValue b^n ∂AronowAudit.P018.fairLaw) = sVal n := by
  interval_cases n
  · simpa [sVal] using fair_one_integral
  · simpa [sVal] using sign_moment_one
  · simpa [sVal] using sign_moment_two

lemma pair_monomial_small (a b c d : ℕ) (ha : a ≤ 2) (hb : b ≤ 2)
    (hc : c ≤ 2) (hd : d ≤ 2) :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool),
      (uv.1.1^a * AronowAudit.P018.signValue uv.1.2^c) *
        (uv.2.1^b * AronowAudit.P018.signValue uv.2.2^d) ∂pairLaw) =
      (zVal a * sVal c) * (zVal b * sVal d) := by
  rw [pair_monomial_integral, uniform_moment_small a ha, sign_moment_small c hc,
    uniform_moment_small b hb, sign_moment_small d hd]

lemma pair_z_monomial_integral (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1^a * uv.2.1^b ∂pairLaw) =
      zVal a * zVal b := by
  simpa [pow_zero, sVal] using pair_monomial_small a b 0 0 ha hb (by omega) (by omega)

lemma triple_z_small (a b c : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
      z.1.1.1^a * z.1.2.1^b * z.2.1^c ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) =
      zVal a * zVal b * zVal c := by
  rw [triple_z_integral, uniform_moment_small a ha, uniform_moment_small b hb,
    uniform_moment_small c hc]

lemma integral_add_four {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f g h k : Ω → ℝ) (hf : Integrable f ν) (hg : Integrable g ν)
    (hh : Integrable h ν) (hk : Integrable k ν) :
    (∫ x, f x + g x + h x + k x ∂ν) =
      (∫ x, f x ∂ν) + (∫ x, g x ∂ν) + (∫ x, h x ∂ν) + (∫ x, k x ∂ν) := by
  have hfg : (∫ x, f x + g x ∂ν) = (∫ x, f x ∂ν) + (∫ x, g x ∂ν) := by
    simpa only [Pi.add_apply] using (integral_add hf hg)
  have hfgh : (∫ x, f x + g x + h x ∂ν) =
      (∫ x, f x + g x ∂ν) + (∫ x, h x ∂ν) := by
    simpa only [Pi.add_apply] using (integral_add (hf.add hg) hh)
  have hall : (∫ x, f x + g x + h x + k x ∂ν) =
      (∫ x, f x + g x + h x ∂ν) + (∫ x, k x ∂ν) := by
    simpa only [Pi.add_apply] using (integral_add ((hf.add hg).add hh) hk)
  rw [hall, hfgh, hfg]

lemma pair_signsum_integral :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool),
      AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2 ∂pairLaw) = 0 := by
  calc
    _ = (∫ uv : (ℝ × Bool) × (ℝ × Bool),
        (uv.1.1^0 * AronowAudit.P018.signValue uv.1.2^1) *
          (uv.2.1^0 * AronowAudit.P018.signValue uv.2.2^0) ∂pairLaw) +
      (∫ uv : (ℝ × Bool) × (ℝ × Bool),
        (uv.1.1^0 * AronowAudit.P018.signValue uv.1.2^0) *
          (uv.2.1^0 * AronowAudit.P018.signValue uv.2.2^1) ∂pairLaw) := by
      simpa [pow_zero, pow_one, one_mul, mul_one] using
        (integral_add
          (pair_monomial_integrable (a := 0) (b := 0) (c := 1) (d := 0))
          (pair_monomial_integrable (a := 0) (b := 0) (c := 0) (d := 1)))
    _ = 0 := by
      rw [pair_monomial_small 0 0 1 0 (by omega) (by omega) (by omega) (by omega),
        pair_monomial_small 0 0 0 1 (by omega) (by omega) (by omega) (by omega)]
      norm_num [zVal, sVal]

lemma pair_zsign_integrable_terms :
    Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      uv.1.1*AronowAudit.P018.signValue uv.1.2) pairLaw ∧
    Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      uv.1.1*AronowAudit.P018.signValue uv.2.2) pairLaw ∧
    Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      uv.2.1*AronowAudit.P018.signValue uv.1.2) pairLaw ∧
    Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      uv.2.1*AronowAudit.P018.signValue uv.2.2) pairLaw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [pow_zero, pow_one, one_mul, mul_one] using
      (pair_monomial_integrable (a := 1) (b := 0) (c := 1) (d := 0))
  · simpa [pow_zero, pow_one, one_mul, mul_one] using
      (pair_monomial_integrable (a := 1) (b := 0) (c := 0) (d := 1))
  · simpa [pow_zero, pow_one, one_mul, mul_one, mul_comm] using
      (pair_monomial_integrable (a := 0) (b := 1) (c := 1) (d := 0))
  · simpa [pow_zero, pow_one, one_mul, mul_one] using
      (pair_monomial_integrable (a := 0) (b := 1) (c := 0) (d := 1))

lemma pair_zsign_integral :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool),
      (uv.1.1 + uv.2.1) *
        (AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2)
      ∂pairLaw) = 0 := by
  obtain ⟨h11,h12,h21,h22⟩ := pair_zsign_integrable_terms
  have hEq (uv : (ℝ × Bool) × (ℝ × Bool)) :
      (uv.1.1 + uv.2.1) *
          (AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2) =
        uv.1.1*AronowAudit.P018.signValue uv.1.2 +
        uv.1.1*AronowAudit.P018.signValue uv.2.2 +
        uv.2.1*AronowAudit.P018.signValue uv.1.2 +
        uv.2.1*AronowAudit.P018.signValue uv.2.2 := by ring
  calc
    _ = ∫ uv : (ℝ × Bool) × (ℝ × Bool),
        uv.1.1*AronowAudit.P018.signValue uv.1.2 +
        uv.1.1*AronowAudit.P018.signValue uv.2.2 +
        uv.2.1*AronowAudit.P018.signValue uv.1.2 +
        uv.2.1*AronowAudit.P018.signValue uv.2.2 ∂pairLaw := by
      apply integral_congr_ae
      filter_upwards [] with uv
      exact hEq uv
    _ = 0 := by
      rw [integral_add_four pairLaw _ _ _ _ h11 h12 h21 h22]
      have q11 : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          uv.1.1*AronowAudit.P018.signValue uv.1.2 ∂pairLaw) = 0 := by
        simpa [pow_one, pow_zero, one_mul, mul_one, zVal, sVal] using
          (pair_monomial_small 1 0 1 0 (by omega) (by omega) (by omega) (by omega))
      have q12 : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          uv.1.1*AronowAudit.P018.signValue uv.2.2 ∂pairLaw) = 0 := by
        simpa [pow_one, pow_zero, one_mul, mul_one, zVal, sVal] using
          (pair_monomial_small 1 0 0 1 (by omega) (by omega) (by omega) (by omega))
      have q21 : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          uv.2.1*AronowAudit.P018.signValue uv.1.2 ∂pairLaw) = 0 := by
        simpa [pow_one, pow_zero, one_mul, mul_one, mul_comm, zVal, sVal] using
          (pair_monomial_small 0 1 1 0 (by omega) (by omega) (by omega) (by omega))
      have q22 : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          uv.2.1*AronowAudit.P018.signValue uv.2.2 ∂pairLaw) = 0 := by
        simpa [pow_one, pow_zero, one_mul, mul_one, zVal, sVal] using
          (pair_monomial_small 0 1 0 1 (by omega) (by omega) (by omega) (by omega))
      rw [q11, q12, q21, q22]
      norm_num

lemma triple_z_firstsecond_integral :
    (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
      z.1.1.1 + z.1.2.1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0 := by
  calc
    _ = (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        z.1.1.1^1*z.1.2.1^0*z.2.1^0 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) +
      (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        z.1.1.1^0*z.1.2.1^1*z.2.1^0 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) := by
      simpa [pow_zero, pow_one, one_mul] using
        (integral_add (triple_z_integrable 1 0 0) (triple_z_integrable 0 1 0))
    _ = 0 := by
      rw [triple_z_small 1 0 0 (by omega) (by omega) (by omega),
        triple_z_small 0 1 0 (by omega) (by omega) (by omega)]
      norm_num [zVal]

lemma triple_z_firstthird_integral :
    (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
      z.1.1.1 + z.2.1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0 := by
  calc
    _ = (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        z.1.1.1^1*z.1.2.1^0*z.2.1^0 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) +
      (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        z.1.1.1^0*z.1.2.1^0*z.2.1^1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) := by
      simpa [pow_zero, pow_one, one_mul] using
        (integral_add (triple_z_integrable 1 0 0) (triple_z_integrable 0 0 1))
    _ = 0 := by
      rw [triple_z_small 1 0 0 (by omega) (by omega) (by omega),
        triple_z_small 0 0 1 (by omega) (by omega) (by omega)]
      norm_num [zVal]

lemma triple_shared_zsquare_integrable :
    Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      (z.1.1.1+z.1.2.1)*(z.1.1.1+z.2.1)^1)
      ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
  have h1 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) => z.1.1.1^2)
      ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero] using triple_z_integrable 2 0 0
  have h2 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.1.1*z.2.1) ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero, pow_one, one_mul] using triple_z_integrable 1 0 1
  have h3 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.1.1*z.1.2.1) ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero, pow_one, one_mul] using triple_z_integrable 1 1 0
  have h4 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.2.1*z.2.1) ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero, pow_one, one_mul] using triple_z_integrable 0 1 1
  have hs := ((h1.add h2).add h3).add h4
  apply hs.congr
  filter_upwards [] with z
  simp only [Pi.add_apply]
  change z.1.1.1^2 + z.1.1.1*z.2.1 + z.1.1.1*z.1.2.1 +
    z.1.2.1*z.2.1 = (z.1.1.1+z.1.2.1)*(z.1.1.1+z.2.1)^1
  ring

lemma triple_shared_zsquare_integral :
    (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
      (z.1.1.1+z.1.2.1)*(z.1.1.1+z.2.1)
      ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 1/3 := by
  have h1 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) => z.1.1.1^2)
      ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero] using triple_z_integrable 2 0 0
  have h2 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.1.1*z.2.1) ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero, pow_one, one_mul] using triple_z_integrable 1 0 1
  have h3 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.1.1*z.1.2.1) ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero, pow_one, one_mul] using triple_z_integrable 1 1 0
  have h4 : Integrable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
      z.1.2.1*z.2.1) ((mixedLaw.prod mixedLaw).prod mixedLaw) := by
    simpa [pow_zero, pow_one, one_mul] using triple_z_integrable 0 1 1
  have hEq (z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool)) :
      (z.1.1.1+z.1.2.1)*(z.1.1.1+z.2.1) =
        z.1.1.1^2 + z.1.1.1*z.2.1 + z.1.1.1*z.1.2.1 + z.1.2.1*z.2.1 := by ring
  calc
    _ = ∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        z.1.1.1^2 + z.1.1.1*z.2.1 + z.1.1.1*z.1.2.1 + z.1.2.1*z.2.1
        ∂((mixedLaw.prod mixedLaw).prod mixedLaw) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hEq z
    _ = (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool), z.1.1.1^2
          ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) +
        (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool), z.1.1.1*z.2.1
          ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) +
        (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool), z.1.1.1*z.1.2.1
          ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) +
        (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool), z.1.2.1*z.2.1
          ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) := by
      simpa only [Pi.add_apply] using integral_add_four
        ((mixedLaw.prod mixedLaw).prod mixedLaw)
        (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) => z.1.1.1^2)
        (fun z => z.1.1.1*z.2.1) (fun z => z.1.1.1*z.1.2.1)
        (fun z => z.1.2.1*z.2.1) h1 h2 h3 h4
    _ = 1/3 := by
      have q1 : (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
          z.1.1.1^2 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 1/3 := by
        simpa [pow_zero, zVal] using triple_z_small 2 0 0 (by omega) (by omega) (by omega)
      have q2 : (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
          z.1.1.1*z.2.1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0 := by
        simpa [pow_zero, pow_one, one_mul, zVal] using
          triple_z_small 1 0 1 (by omega) (by omega) (by omega)
      have q3 : (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
          z.1.1.1*z.1.2.1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0 := by
        simpa [pow_zero, pow_one, one_mul, zVal] using
          triple_z_small 1 1 0 (by omega) (by omega) (by omega)
      have q4 : (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
          z.1.2.1*z.2.1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0 := by
        simpa [pow_zero, pow_one, one_mul, zVal] using
          triple_z_small 0 1 1 (by omega) (by omega) (by omega)
      rw [q1,q2,q3,q4]
      norm_num

lemma pair_zsum_integral :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1 + uv.2.1 ∂pairLaw) = 0 := by
  calc
    _ = (∫ uv : (ℝ × Bool) × (ℝ × Bool),
        (uv.1.1^1 * AronowAudit.P018.signValue uv.1.2^0) *
          (uv.2.1^0 * AronowAudit.P018.signValue uv.2.2^0) ∂pairLaw) +
      (∫ uv : (ℝ × Bool) × (ℝ × Bool),
        (uv.1.1^0 * AronowAudit.P018.signValue uv.1.2^0) *
          (uv.2.1^1 * AronowAudit.P018.signValue uv.2.2^0) ∂pairLaw) := by
      simpa [pow_zero, pow_one, one_mul, mul_one] using
        (integral_add (pair_monomial_integrable (a := 1) (b := 0) (c := 0) (d := 0))
        (pair_monomial_integrable (a := 0) (b := 1) (c := 0) (d := 0)))
    _ = 0 := by
      rw [pair_monomial_small 1 0 0 0 (by omega) (by omega) (by omega) (by omega),
        pair_monomial_small 0 1 0 0 (by omega) (by omega) (by omega) (by omega)]
      norm_num [zVal, sVal]

lemma pair_zsquare_integrable :
    Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) => (uv.1.1 + uv.2.1)^2) pairLaw := by
  have h1 : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) => uv.1.1^2) pairLaw := by
    simpa [pow_zero] using (pair_monomial_integrable (a := 2) (b := 0) (c := 0) (d := 0))
  have h2 : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      2*(uv.1.1*uv.2.1)) pairLaw := by
    simpa [pow_zero, pow_one, mul_assoc] using
      (pair_monomial_integrable (a := 1) (b := 1) (c := 0) (d := 0)).const_mul (2 : ℝ)
  have h3 : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) => uv.2.1^2) pairLaw := by
    simpa [pow_zero] using (pair_monomial_integrable (a := 0) (b := 2) (c := 0) (d := 0))
  have hs := (h1.add h2).add h3
  apply hs.congr
  filter_upwards [] with uv
  change uv.1.1^2 + 2*(uv.1.1*uv.2.1) + uv.2.1^2 = (uv.1.1 + uv.2.1)^2
  ring

lemma pair_zsquare_integral :
    (∫ uv : (ℝ × Bool) × (ℝ × Bool), (uv.1.1 + uv.2.1)^2 ∂pairLaw) = 2/3 := by
  have h1 : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) => uv.1.1^2) pairLaw := by
    simpa [pow_zero] using (pair_monomial_integrable (a := 2) (b := 0) (c := 0) (d := 0))
  have h2 : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
      2*(uv.1.1*uv.2.1)) pairLaw := by
    simpa [pow_zero, pow_one, mul_assoc] using
      (pair_monomial_integrable (a := 1) (b := 1) (c := 0) (d := 0)).const_mul (2 : ℝ)
  have h3 : Integrable (fun uv : (ℝ × Bool) × (ℝ × Bool) => uv.2.1^2) pairLaw := by
    simpa [pow_zero] using (pair_monomial_integrable (a := 0) (b := 2) (c := 0) (d := 0))
  have hEq (uv : (ℝ × Bool) × (ℝ × Bool)) :
      (uv.1.1 + uv.2.1)^2 = uv.1.1^2 + 2*(uv.1.1*uv.2.1) + uv.2.1^2 := by ring
  calc
    _ = ∫ uv : (ℝ × Bool) × (ℝ × Bool),
        uv.1.1^2 + 2*(uv.1.1*uv.2.1) + uv.2.1^2 ∂pairLaw := by
      apply integral_congr_ae
      filter_upwards [] with uv
      exact hEq uv
    _ = (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1^2 ∂pairLaw) +
        (∫ uv : (ℝ × Bool) × (ℝ × Bool), 2*(uv.1.1*uv.2.1) ∂pairLaw) +
        (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.2.1^2 ∂pairLaw) := by
      have h12 : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          uv.1.1^2 + 2*(uv.1.1*uv.2.1) ∂pairLaw) =
          (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1^2 ∂pairLaw) +
          (∫ uv : (ℝ × Bool) × (ℝ × Bool), 2*(uv.1.1*uv.2.1) ∂pairLaw) := by
        simpa only [Pi.add_apply] using (integral_add h1 h2)
      have h123 : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          uv.1.1^2 + 2*(uv.1.1*uv.2.1) + uv.2.1^2 ∂pairLaw) =
          (∫ uv : (ℝ × Bool) × (ℝ × Bool),
            uv.1.1^2 + 2*(uv.1.1*uv.2.1) ∂pairLaw) +
          (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.2.1^2 ∂pairLaw) := by
        simpa only [Pi.add_apply] using (integral_add (h1.add h2) h3)
      rw [h123, h12]
    _ = 2/3 := by
      have q1 := pair_z_monomial_integral 2 0 (by omega) (by omega)
      have q2 := pair_z_monomial_integral 1 1 (by omega) (by omega)
      have q3 := pair_z_monomial_integral 0 2 (by omega) (by omega)
      have q1' : (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1^2 ∂pairLaw) = 1/3 := by
        simpa [pow_zero, zVal] using q1
      have q2'' : (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.1.1*uv.2.1 ∂pairLaw) = 0 := by
        simpa [pow_one, zVal] using q2
      have q3' : (∫ uv : (ℝ × Bool) × (ℝ × Bool), uv.2.1^2 ∂pairLaw) = 1/3 := by
        simpa [pow_zero, zVal] using q3
      have q2' : (∫ uv : (ℝ × Bool) × (ℝ × Bool),
          2*(uv.1.1*uv.2.1) ∂pairLaw) = 0 := by
        rw [integral_const_mul, q2'']
        norm_num
      rw [q1', q2', q3']
      norm_num

end SAP.P018a.WH.W1.P.T11_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open SAP.P018a.WH.W1.P.T11_L4

theorem SAP.P018a.WH.W1.T11_L4_proof : SAP.P018a.WH.W1.T11_L4 := by
  letI : MeasureTheory.IsProbabilityMeasure AronowAudit.P018.fairLaw :=
    AronowAudit.P018.Wave1.printed_fair_probability
  letI : MeasureTheory.IsProbabilityMeasure SAP.P018a.fairLaw := by
    change MeasureTheory.IsProbabilityMeasure AronowAudit.P018.fairLaw
    exact AronowAudit.P018.Wave1.printed_fair_probability
  letI : MeasureTheory.IsProbabilityMeasure SAP.P018a.uniformUnitLaw := by
    change MeasureTheory.IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw
    infer_instance
  letI : IsProbabilityMeasure mixedLaw := by
    change IsProbabilityMeasure
      (SAP.P018a.uniformUnitLaw.prod SAP.P018a.fairLaw)
    infer_instance
  letI : IsProbabilityMeasure pairLaw := by
    change IsProbabilityMeasure (mixedLaw.prod mixedLaw)
    infer_instance
  letI : IsProbabilityMeasure ((mixedLaw.prod mixedLaw).prod mixedLaw) := inferInstance
  have hQ : SAP.P018a.populationGram SAP.P018a.W1MixedKernel =
      !![1,0;0,2/3] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [SAP.P018a.populationGram, SAP.P018a.meanMat,
        SAP.P018a.outer, SAP.P018a.W1MixedKernel,
        pair_zsum_integral, pair_zsquare_integral]
    · simp [SAP.P018a.populationGram, SAP.P018a.meanMat,
        SAP.P018a.outer, SAP.P018a.W1MixedKernel,
        pair_zsum_integral]
    · simp [SAP.P018a.populationGram, SAP.P018a.meanMat,
        SAP.P018a.outer, SAP.P018a.W1MixedKernel,
        pair_zsum_integral]
    · change (∫ uv : (ℝ × Bool) × (ℝ × Bool),
        (uv.1.1+uv.2.1)*(uv.1.1+uv.2.1) ∂pairLaw) = 2/3
      simpa [pow_two] using pair_zsquare_integral
  have hBeta : SAP.P018a.populationBeta SAP.P018a.W1MixedKernel = 0 := by
    have hm : SAP.P018a.meanVec pairLaw
        (fun uv => SAP.P018a.score
          (SAP.P018a.W1MixedKernel.X uv.1 uv.2)
          (SAP.P018a.W1MixedKernel.Y uv.1 uv.2)) = 0 := by
      ext a
      fin_cases a
      · simpa [SAP.P018a.meanVec, SAP.P018a.score,
          SAP.P018a.W1MixedKernel, SAP.P018a.signValue,
          AronowAudit.P018.signValue] using pair_signsum_integral
      · simpa [SAP.P018a.meanVec, SAP.P018a.score,
          SAP.P018a.W1MixedKernel, SAP.P018a.signValue,
          AronowAudit.P018.signValue, mul_comm] using pair_zsign_integral
    change (SAP.P018a.populationGram SAP.P018a.W1MixedKernel)⁻¹.mulVec
      (SAP.P018a.meanVec pairLaw (fun uv => SAP.P018a.score
        (SAP.P018a.W1MixedKernel.X uv.1 uv.2)
        (SAP.P018a.W1MixedKernel.Y uv.1 uv.2))) = 0
    rw [hm]
    simp
  have hCross : SAP.P018a.W1CrossGram SAP.P018a.W1MixedKernel =
      !![1,0;0,1/3] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [SAP.P018a.W1CrossGram, SAP.P018a.meanMat,
        SAP.P018a.outer, SAP.P018a.W1MixedKernel]
    · change (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        1*(z.1.1.1+z.2.1) ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0
      simpa only [one_mul] using triple_z_firstthird_integral
    · change (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        (z.1.1.1+z.1.2.1)*1 ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 0
      simpa only [mul_one] using triple_z_firstsecond_integral
    · change (∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        (z.1.1.1+z.1.2.1)*(z.1.1.1+z.2.1)
        ∂((mixedLaw.prod mixedLaw).prod mixedLaw)) = 1/3
      exact triple_shared_zsquare_integral
  have hDot :
      (∫ uv : (ℝ × Bool) × (ℝ × Bool),
        SAP.P018a.dot (SAP.P018a.W1MixedKernel.X uv.1 uv.2)
          (SAP.P018a.W1MixedKernel.X uv.1 uv.2) ∂pairLaw) = 5/3 := by
    have hEq (uv : (ℝ × Bool) × (ℝ × Bool)) :
        SAP.P018a.dot (SAP.P018a.W1MixedKernel.X uv.1 uv.2)
          (SAP.P018a.W1MixedKernel.X uv.1 uv.2) =
            1+(uv.1.1+uv.2.1)^2 := by
      simp [SAP.P018a.W1MixedKernel, SAP.P018a.dot,
        Fin.sum_univ_succ]
      ring
    calc
      _ = ∫ uv : (ℝ × Bool) × (ℝ × Bool), 1+(uv.1.1+uv.2.1)^2 ∂pairLaw := by
        apply integral_congr_ae
        filter_upwards [] with uv
        exact hEq uv
      _ = (∫ uv : (ℝ × Bool) × (ℝ × Bool), (1:ℝ) ∂pairLaw) +
          (∫ uv : (ℝ × Bool) × (ℝ × Bool), (uv.1.1+uv.2.1)^2 ∂pairLaw) := by
        simpa only [Pi.add_apply] using
          (integral_add (integrable_const (1:ℝ)) pair_zsquare_integrable)
      _ = 5/3 := by
        simp only [integral_const, MeasureTheory.probReal_univ]
        rw [pair_zsquare_integral]
        norm_num
  have hStanding : SAP.P018a.Standing SAP.P018a.W1MixedKernel := by
    refine ⟨(by change IsProbabilityMeasure mixedLaw; infer_instance), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Measurable (fun uv : (ℝ × Bool) × (ℝ × Bool) => ![1,uv.1.1+uv.2.1])
      fun_prop
    · change Measurable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
        AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2)
      have hm : Measurable (fun b : Bool × Bool =>
          SAP.P018a.signValue b.1 + SAP.P018a.signValue b.2) := measurable_of_countable _
      have hp : Measurable (fun uv : (ℝ × Bool) × (ℝ × Bool) =>
          (uv.1.2, uv.2.2)) := by fun_prop
      exact hm.comp hp
    · intro u v
      dsimp [SAP.P018a.W1MixedKernel]
      constructor
      · ext i
        fin_cases i <;> simp <;> ring
      · simp [add_comm]
    · refine ⟨4, by norm_num, ?_⟩
      have hs : ∀ᵐ z ∂AronowAudit.P018.uniformUnitLaw,
          z ∈ Set.Icc (-1 : ℝ) 1 :=
        ProbabilityTheory.ae_cond_mem measurableSet_Icc
      have hu : ∀ᵐ u ∂mixedLaw, u.1 ∈ Set.Icc (-1 : ℝ) 1 :=
        (measurePreserving_fst (μ := AronowAudit.P018.uniformUnitLaw)
          (ν := AronowAudit.P018.fairLaw)).quasiMeasurePreserving.tendsto_ae hs
      have hfst : ∀ᵐ uv ∂pairLaw, uv.1.1 ∈ Set.Icc (-1 : ℝ) 1 :=
        (measurePreserving_fst (μ := mixedLaw) (ν := mixedLaw)).quasiMeasurePreserving.tendsto_ae hu
      have hsnd : ∀ᵐ uv ∂pairLaw, uv.2.1 ∈ Set.Icc (-1 : ℝ) 1 :=
        (measurePreserving_snd (μ := mixedLaw) (ν := mixedLaw)).quasiMeasurePreserving.tendsto_ae hu
      filter_upwards [hfst, hsnd] with uv hu hv
      change ‖(![1,uv.1.1+uv.2.1] : AronowAudit.P018.Vec 2)‖ ≤ 4 ∧
        |AronowAudit.P018.signValue uv.1.2 + AronowAudit.P018.signValue uv.2.2| ≤ 4
      have hsum : |uv.1.1+uv.2.1| ≤ 2 := by
        calc
          _ ≤ |uv.1.1|+|uv.2.1| := abs_add_le _ _
          _ ≤ 1+1 := add_le_add
            (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
            (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
          _ = 2 := by norm_num
      constructor
      · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 4)).mpr
        intro a
        fin_cases a
        · norm_num
        · simpa [Real.norm_eq_abs] using hsum.trans (by norm_num : (2:ℝ) ≤ 4)
      · calc
          _ ≤ |AronowAudit.P018.signValue uv.1.2|+
              |AronowAudit.P018.signValue uv.2.2| := abs_add_le _ _
          _ = 2 := by cases uv.1.2 <;> cases uv.2.2 <;>
            norm_num [AronowAudit.P018.signValue]
          _ ≤ 4 := by norm_num
    · exact ⟨0, by intro u v; simp [SAP.P018a.W1MixedKernel]⟩
    · rw [hQ]
      norm_num [Matrix.det_fin_two]
  exact ⟨hStanding, hBeta, hQ, hCross, hDot⟩
