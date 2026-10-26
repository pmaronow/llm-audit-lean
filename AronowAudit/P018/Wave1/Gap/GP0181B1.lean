import AronowAudit.P018.P018_Audit
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-! P018-T11 and P018-T12: fair-sign moments and finite target corrections. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Finite unordered-pair algebra. -/

lemma printed_endpoints_lt {N : ℕ} (d : Dyad N) : firstUnit d < secondUnit d := by
  exact Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)

lemma printed_members_endpoints {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [members_card]
    simp [ne_of_lt (printed_endpoints_lt d)]

/-- A dyad constructed from two distinct endpoints, with its membership proof. -/
def printed_mkDyad {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Dyad N :=
  ⟨{i, j}, by simp [dyads, Finset.mem_powersetCard, hij]⟩

lemma printed_mkDyad_endpoints {N : ℕ} (i j : Fin N) (hij : i < j) :
    firstUnit (printed_mkDyad i j hij.ne) = i ∧
    secondUnit (printed_mkDyad i j hij.ne) = j := by
  simp [firstUnit, secondUnit, members, printed_mkDyad,
    Finset.min'_pair, Finset.max'_pair, min_eq_left hij.le, max_eq_right hij.le]

lemma printed_upper_sum {N : ℕ} (F : Fin N → Fin N → ℝ) :
    (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then F i j else 0 := by
  classical
  let P := (univ ×ˢ univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
  have h : (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ p ∈ P, F p.1 p.2 := by
    apply Finset.sum_bij (fun d _ => (firstUnit d, secondUnit d))
    · intro d hd
      simp [P, printed_endpoints_lt]
    · intro d hd e he hde
      apply Subtype.ext
      change members d = members e
      rw [printed_members_endpoints d, printed_members_endpoints e]
      rw [Prod.mk.injEq] at hde
      rw [hde.1, hde.2]
    · intro p hp
      have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      refine ⟨printed_mkDyad p.1 p.2 hp'.ne, mem_univ _, ?_⟩
      obtain ⟨h₁, h₂⟩ := printed_mkDyad_endpoints p.1 p.2 hp'
      exact Prod.ext h₁ h₂
    · intro d hd
      rfl
  rw [h]
  simp only [P, Finset.sum_filter, Finset.sum_product]

lemma printed_offdiag {N : ℕ} (F : Fin N → Fin N → ℝ) (i : Fin N) :
    (∑ j, if i ≠ j then F i j else 0) = (∑ j, F i j) - F i i := by
  classical
  have h : (∑ j, F i j) = (∑ j, if i ≠ j then F i j else 0) + F i i := by
    calc
      _ = ∑ j, ((if i ≠ j then F i j else 0) + (if i = j then F i j else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j <;> simp [hij]
      _ = _ := by simp [Finset.sum_add_distrib]
  linarith

lemma printed_pair_sum {N : ℕ} (F : Fin N → Fin N → ℝ)
    (hs : ∀ i j, F i j = F j i) :
    2 * (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ i : Fin N, ((∑ j : Fin N, F i j) - F i i) := by
  classical
  rw [printed_upper_sum]
  have hp (i j : Fin N) : (if i ≠ j then F i j else 0) =
      (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, h.ne', not_lt_of_ge h.le]
  have hswap : (∑ i : Fin N, ∑ j : Fin N, if j < i then F i j else 0) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs i j]
  simp_rw [← printed_offdiag, hp, Finset.sum_add_distrib]
  rw [hswap]
  ring

lemma printed_pair_add {N : ℕ} (u : Fin N → ℝ) :
    (∑ d : Dyad N, (u (firstUnit d) + u (secondUnit d))) =
      ((N : ℝ) - 1) * ∑ i, u i := by
  have h := printed_pair_sum (fun i j => u i + u j) (fun i j => add_comm _ _)
  have hr : (∑ i : Fin N, ((∑ j : Fin N, (u i + u j)) - (u i + u i))) =
      2 * ((N : ℝ)-1) * (∑ i, u i) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  rw [hr] at h
  linarith

lemma printed_pair_square {N : ℕ} (u : Fin N → ℝ) :
    (∑ d : Dyad N, (u (firstUnit d) + u (secondUnit d))^2) =
      ((N : ℝ) - 2) * (∑ i, (u i)^2) + (∑ i, u i)^2 := by
  have h := printed_pair_sum (fun i j => (u i + u j)^2)
    (fun i j => by rw [add_comm (u i) (u j)])
  have hdiag (i : Fin N) : (u i + u i)^2 = 4 * (u i)^2 := by ring
  have hrow (i : Fin N) : (∑ j : Fin N, (u i + u j)^2) =
      (N : ℝ) * (u i)^2 + 2 * u i * (∑ j, u j) + ∑ j, (u j)^2 := by
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hr : (∑ i : Fin N, ((∑ j : Fin N, (u i + u j)^2) - (u i + u i)^2)) =
      2 * (((N : ℝ)-2) * (∑ i, (u i)^2) + (∑ i, u i)^2) := by
    simp_rw [hrow, hdiag]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  rw [hr] at h
  linarith

/-- Sum of edge values at one vertex. The formula also holds for N=1. -/
lemma printed_incident_add {N : ℕ} (u : Fin N → ℝ) (i : Fin N) :
    (∑ d : Dyad N, if i ∈ members d then u (firstUnit d) + u (secondUnit d) else 0) =
      ((N : ℝ) - 2) * u i + ∑ j, u j := by
  classical
  let F : Fin N → Fin N → ℝ := fun a b => if i ∈ ({a,b} : Finset (Fin N)) then u a + u b else 0
  have hs : ∀ a b, F a b = F b a := by
    intro a b
    simp only [F, Finset.mem_insert, Finset.mem_singleton]
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp [ha, hb, add_comm]
  have h := printed_pair_sum F hs
  have hrow (a : Fin N) : ((∑ b, F a b) - F a a) =
      if a = i then ((N : ℝ) - 2) * u i + ∑ b, u b else u a + u i := by
    by_cases ha : a = i
    · subst a
      simp [F, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] <;> ring
    · simp [F, ha, Ne.symm ha, eq_comm]
  simp_rw [hrow] at h
  have hrest : (∑ a : Fin N, if a ≠ i then u a + u i else 0) =
      (∑ a, u a) + (N : ℝ) * u i - 2 * u i := by
    have hh := printed_offdiag (fun _ a => u a + u i) i
    simpa [ne_comm, Finset.sum_add_distrib, nsmul_eq_mul, two_mul] using hh
  have hsplit : (∑ a : Fin N, if a = i then ((N : ℝ) - 2) * u i + ∑ b, u b else u a + u i) =
      (((N : ℝ) - 2) * u i + ∑ b, u b) +
      (∑ a : Fin N, if a ≠ i then u a + u i else 0) := by
    simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']
  rw [hsplit, hrest] at h
  simp_rw [F, ← printed_members_endpoints] at h
  linarith

lemma printed_card_real (N : ℕ) : (Fintype.card (Dyad N) : ℝ) = Dreal N := by
  rw [number_of_dyads]
  exact Nat.cast_choose_two ℝ N

lemma printed_dyads_card_real (N : ℕ) : ((dyads N).card : ℝ) = Dreal N := by
  have h := printed_card_real N
  simpa only [Fintype.card_coe] using h

instance printed_unit_probability {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] : IsProbabilityMeasure (unitSampleLaw K N) := by
  unfold unitSampleLaw
  infer_instance

lemma printed_Dpos {N : ℕ} (hN : 2 ≤ N) : 0 < Dreal N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ)-1 := by linarith
  dsimp [Dreal]
  positivity

/-- The finite sign-sample sum S. -/
def printed_S {N : ℕ} (ω : Fin N → Bool) : ℝ := ∑ i, signValue (ω i)

lemma printed_sign_square (b : Bool) : (signValue b)^2 = 1 := by
  cases b <;> norm_num [signValue]

lemma printed_gram {N : ℕ} (ω : Fin N → Bool) :
    sampleGram (design signKernel ω) = Dreal N • (1 : Mat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [sampleGram, design, signKernel, outer, printed_card_real, printed_dyads_card_real]

lemma printed_gram_inv {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    (sampleGram (design signKernel ω))⁻¹ = (Dreal N)⁻¹ • (1 : Mat 1) := by
  rw [printed_gram, matrix_inverse_scale_total _ _ (ne_of_gt (printed_Dpos hN))]
  simp

lemma printed_fit {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    sampleOLS (design signKernel ω) (response signKernel ω) 0 = 2 / (N : ℝ) * printed_S ω := by
  have hn : (N : ℝ) ≠ 0 := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [sampleOLS, printed_gram_inv hN]
  simp only [Matrix.mulVec, dotProduct,
    Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul,
    Finset.sum_apply, score, Pi.smul_apply, design, response, signKernel,
    Matrix.cons_val_zero, mul_one]
  rw [printed_pair_add (fun i => signValue (ω i))]
  dsimp [Dreal, printed_S]
  field_simp [hn, hn1]
  <;> ring

/-- Deterministic fitted-meat identity, valid for every sign sample. -/
lemma printed_scaled_sandwich {N : ℕ} (hN : 4 ≤ N) (ω : Fin N → Bool) :
    (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 =
      (4 * ((N : ℝ)-2) * ((N : ℝ)-3) / ((N : ℝ)-1)^2) *
        (1 - (printed_S ω / (N : ℝ))^2) := by
  classical
  have hN2 : 2 ≤ N := by omega
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  let v : Fin N → ℝ := fun i => signValue (ω i) - printed_S ω / (N : ℝ)
  have hvsum : (∑ i, v i) = 0 := by
    dsimp [v]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change printed_S ω - (N : ℝ) * (printed_S ω / (N : ℝ)) = 0
    field_simp [hn0] <;> ring
  have hvsq : (∑ i, (v i)^2) = (N : ℝ) - (printed_S ω)^2 / (N : ℝ) := by
    have he (i : Fin N) : (v i)^2 = (signValue (ω i))^2 -
        2 * (printed_S ω / (N : ℝ)) * signValue (ω i) + (printed_S ω / (N : ℝ))^2 := by
      dsimp [v]
      ring
    simp_rw [he, printed_sign_square]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, mul_one]
    change (N : ℝ) - 2 * (printed_S ω / (N : ℝ)) * printed_S ω +
      (N : ℝ) * (printed_S ω / (N : ℝ))^2 = _
    field_simp [hn0]
    <;> ring
  have he (d : Dyad N) : fittedResidual (design signKernel ω) (response signKernel ω) d =
      v (firstUnit d) + v (secondUnit d) := by
    simp only [fittedResidual, dot, Fin.sum_univ_one]
    rw [printed_fit hN2]
    simp [response, design, signKernel, v] <;> ring
  let q : Dyad N → Vec 1 := fun d => score (design signKernel ω d)
    (fittedResidual (design signKernel ω) (response signKernel ω) d)
  have hq (d : Dyad N) : q d 0 = v (firstUnit d) + v (secondUnit d) := by
    simp only [q, score, Pi.smul_apply, smul_eq_mul, he]
    simp [design, signKernel]
  have hu (i : Fin N) : unitScore members q i 0 = ((N : ℝ)-2) * v i := by
    simp only [unitScore, Finset.sum_apply, ite_apply, Pi.zero_apply, hq]
    rw [printed_incident_add, hvsum, add_zero]
  have hm : meat members q =
      (∑ i, outer (unitScore members q i) (unitScore members q i)) - dyadMeat q :=
    overlap_meat_identity members members_card (fun d e h => Subtype.ext h) q
  have hm00 : meat members q 0 0 =
      ((N : ℝ)-2) * ((N : ℝ)-3) * ((N : ℝ) - (printed_S ω)^2 / (N : ℝ)) := by
    rw [hm]
    simp only [Matrix.sub_apply, Matrix.sum_apply, outer, Matrix.of_apply, hu,
      dyadMeat, hq]
    have hsquare := printed_pair_square v
    rw [hvsum, zero_pow (by decide : 2 ≠ 0), add_zero] at hsquare
    have hterm (i : Fin N) : (((N : ℝ)-2) * v i) * (((N : ℝ)-2) * v i) =
        ((N : ℝ)-2)^2 * (v i)^2 := by ring
    have hedge (d : Dyad N) :
        (v (firstUnit d) + v (secondUnit d)) * (v (firstUnit d) + v (secondUnit d)) =
          (v (firstUnit d) + v (secondUnit d))^2 := by ring
    simp_rw [hterm, hedge, ← Finset.mul_sum]
    rw [hsquare, hvsq]
    ring
  change (N : ℝ) * sandwich (sampleGram (design signKernel ω))⁻¹ (meat members q) 0 0 = _
  rw [printed_gram_inv hN2]
  simp only [sandwich, Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply,
    Matrix.one_apply, if_true, smul_eq_mul]
  rw [hm00]
  dsimp [Dreal]
  field_simp [hn0, hn1]
  <;> ring

/-! Fair-law moments, followed by a direct Markov bound. -/

lemma printed_fair_probability : IsProbabilityMeasure fairLaw := by
  unfold fairLaw
  infer_instance

instance printed_sign_probability (N : ℕ) : IsProbabilityMeasure (unitSampleLaw signKernel N) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => fairLaw))
  letI := printed_fair_probability
  infer_instance

lemma printed_finite_integrable {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (f : A → ℝ) :
    Integrable f μ := by
  exact ⟨(measurable_of_countable f).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩

lemma printed_finite_L2 {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (f : A → ℝ) :
    MemLp f 2 μ := by
  exact MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (norm_le_pi_norm f))

lemma printed_fair_integral : (∫ b, signValue b ∂ fairLaw) = 0 := by
  letI := printed_fair_probability
  rw [integral_fintype (printed_finite_integrable fairLaw signValue)]
  norm_num [fairLaw, Measure.real, PMF.toMeasure_uniformOfFintype_apply, signValue,
    Fintype.sum_bool, Fintype.card_bool]

lemma printed_fair_variance : ProbabilityTheory.variance signValue fairLaw = 1 := by
  letI := printed_fair_probability
  rw [variance_eq_sub (printed_finite_L2 fairLaw signValue), printed_fair_integral]
  simp only [Pi.pow_apply, printed_sign_square, integral_const, probReal_univ, smul_eq_mul, one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero]

lemma printed_S_mean (N : ℕ) : (∫ ω, printed_S ω ∂ unitSampleLaw signKernel N) = 0 := by
  letI := printed_fair_probability
  change (∫ ω, ∑ i : Fin N, signValue (ω i) ∂ Measure.pi (fun _ : Fin N => fairLaw)) = 0
  rw [integral_finsetSum _ (fun i hi => printed_finite_integrable _ _)]
  have hi (i : Fin N) : (∫ ω : Fin N → Bool, signValue (ω i)
      ∂ Measure.pi (fun _ => fairLaw)) = 0 := by
    have hm := (measurePreserving_eval (fun _ : Fin N => fairLaw) i).map_eq
    calc
      _ = ∫ b, signValue b ∂ (Measure.pi (fun _ : Fin N => fairLaw)).map
          (fun ω : Fin N → Bool => ω i) :=
        (integral_map_of_stronglyMeasurable (measurable_pi_apply i)
          (measurable_of_countable signValue).stronglyMeasurable).symm
      _ = 0 := by rw [hm, printed_fair_integral]
  simp only [hi, Finset.sum_const_zero]

lemma printed_S_variance (N : ℕ) :
    ProbabilityTheory.variance (fun ω : Fin N → Bool => printed_S ω)
      (unitSampleLaw signKernel N) = (N : ℝ) := by
  letI := printed_fair_probability
  have h := variance_sum_pi (ι := Fin N) (μ := fun _ => fairLaw)
    (X := fun _ => signValue) (fun _ => printed_finite_L2 fairLaw signValue)
  have he : (∑ i : Fin N, (fun ω : Fin N → Bool => signValue (ω i))) =
      fun ω => printed_S ω := by
    funext ω
    simp only [Finset.sum_apply, printed_S]
  rw [he] at h
  simpa [printed_fair_variance, unitSampleLaw, signKernel] using h

lemma printed_S_second (N : ℕ) :
    (∫ ω, (printed_S ω)^2 ∂ unitSampleLaw signKernel N) = (N : ℝ) := by
  letI := printed_fair_probability
  have h := printed_S_variance N
  rw [variance_eq_sub (printed_finite_L2 _ _), printed_S_mean] at h
  simpa using h

lemma printed_scaled_coefficient_variance (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ)*ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) = 4 := by
  have hN2 : 2 ≤ N := by omega
  have hn : (N : ℝ) ≠ 0 := by
    have hncast : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp_rw [printed_fit hN2]
  rw [variance_const_mul, printed_S_variance]
  field_simp [hn]
  <;> ring

lemma printed_inv_n_limit : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma printed_missing_sum_limit : Tendsto (fun N : ℕ => 4/Dreal N) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 8 * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ / (1-(N : ℝ)⁻¹)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (8 : ℝ))).mul printed_inv_n_limit).mul
      (printed_inv_n_limit.div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub printed_inv_n_limit) (by norm_num))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (N : ℝ) ≠ 0 := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hden : 1-(N : ℝ)⁻¹ ≠ 0 := by
    intro hzero
    field_simp [hn] at hzero
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  dsimp [Dreal]
  field_simp [hn, hn1, hden]
  <;> ring

/-- A_n, the deterministic prefactor in the fitted sandwich. -/
def printed_A (N : ℕ) : ℝ := 4 * ((N : ℝ)-2) * ((N : ℝ)-3) / ((N : ℝ)-1)^2

lemma printed_A_limit : Tendsto printed_A atTop (𝓝 4) := by
  have h₁ : Tendsto (fun N : ℕ => 1-(N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub printed_inv_n_limit
  have h₂ : Tendsto (fun N : ℕ => 1-2*(N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (printed_inv_n_limit.const_mul 2)
  have h₃ : Tendsto (fun N : ℕ => 1-3*(N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (printed_inv_n_limit.const_mul 3)
  have h : Tendsto (fun N : ℕ =>
      4 * (1-2*(N : ℝ)⁻¹) * (1-3*(N : ℝ)⁻¹) / (1-(N : ℝ)⁻¹)^2)
      atTop (𝓝 4) := by
    have hl := (((tendsto_const_nhds (x := (4 : ℝ))).mul h₂).mul h₃).div
      (h₁.pow 2) (by norm_num)
    norm_num at hl
    convert hl using 1
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (N : ℝ) ≠ 0 := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hden : 1-(N : ℝ)⁻¹ ≠ 0 := by
    intro hzero
    field_simp [hn] at hzero
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  dsimp [printed_A]
  field_simp [hn, hn1, hden]
  <;> ring

lemma printed_A_bounds {N : ℕ} (hN : 4 ≤ N) : 0 ≤ printed_A N ∧ printed_A N ≤ 4 := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < ((N : ℝ)-1)^2 := sq_pos_of_ne_zero (by linarith)
  have hn2 : 0 ≤ (N : ℝ)-2 := by linarith
  have hn3 : 0 ≤ (N : ℝ)-3 := by linarith
  constructor
  · dsimp [printed_A]
    positivity
  · apply (div_le_iff₀ hd).mpr
    nlinarith

lemma printed_Z_mean {N : ℕ} (hN : 1 ≤ N) :
    (∫ ω, (printed_S ω / (N : ℝ))^2 ∂ unitSampleLaw signKernel N) = (N : ℝ)⁻¹ := by
  have hn : (N : ℝ) ≠ 0 := by
    have hncast : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp_rw [div_pow, div_eq_mul_inv]
  rw [integral_mul_const, printed_S_second]
  field_simp [hn] <;> ring

lemma printed_sandwich_probability_limit :
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ)*(sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 - 4) := by
  letI := printed_fair_probability
  intro ε hε
  have he : 0 < ε/8 := by positivity
  have hA : ∀ᶠ N in atTop, |printed_A N - 4| < ε/2 := by
    exact (Metric.tendsto_nhds.mp printed_A_limit) (ε/2) (by positivity) |>.mono
      (fun N hN => by simpa [Real.dist_eq] using hN)
  have hupper : ∀ᶠ N in atTop,
      ((unitSampleLaw signKernel N) {ω | ε ≤ ‖(N : ℝ) *
        (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 - 4‖}).toReal
      ≤ (N : ℝ)⁻¹ / (ε/8) := by
    filter_upwards [hA, eventually_ge_atTop 4] with N ha hN
    let Z : (Fin N → Bool) → ℝ := fun ω => (printed_S ω / (N : ℝ))^2
    have hb := printed_A_bounds hN
    have hsub : {ω | ε ≤ ‖(N : ℝ) *
        (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 - 4‖}
        ⊆ {ω | ε/8 ≤ Z ω} := by
      intro ω hω
      have heq := printed_scaled_sandwich hN ω
      change ε ≤ |(N : ℝ) *
        (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 - 4| at hω
      change (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 =
        printed_A N * (1-Z ω) at heq
      have herr : |printed_A N * (1-Z ω)-4| ≤ |printed_A N-4| + 4*Z ω := by
        calc
          _ = |(printed_A N-4) - printed_A N * Z ω| := by congr 1; ring
          _ ≤ |printed_A N-4| + |printed_A N * Z ω| := by
            simpa using (abs_sub_le (printed_A N-4) 0 (printed_A N * Z ω))
          _ ≤ _ := by
            rw [abs_mul, abs_of_nonneg hb.1]
            rw [abs_of_nonneg (show 0 ≤ Z ω from sq_nonneg _)]
            nlinarith [sq_nonneg (printed_S ω / (N : ℝ))]
      rw [heq] at hω
      change ε/8 ≤ Z ω
      linarith
    have hm : ((unitSampleLaw signKernel N) {ω | ε/8 ≤ Z ω}).toReal ≤ (N : ℝ)⁻¹ / (ε/8) := by
      have hmark := mul_meas_ge_le_integral_of_nonneg
        (μ := unitSampleLaw signKernel N) (f := Z)
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
        (printed_finite_integrable _ Z) (ε/8)
      rw [printed_Z_mean (by omega : 1 ≤ N)] at hmark
      apply (le_div_iff₀ he).mpr
      simpa [Measure.real, mul_comm] using hmark
    exact le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)) hm
  have hz : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ / (ε/8)) atTop (𝓝 0) := by
    simpa using printed_inv_n_limit.div_const (ε/8)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun N => ENNReal.toReal_nonneg)) hupper hz

theorem printed_targets_counterexample_proof :
    (∀ N : ℕ, 3 ≤ N → (N : ℝ)*ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) = 4) ∧
    Tendsto (fun N : ℕ => 4/Dreal N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ)*(sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 - 4) := by
  exact ⟨printed_scaled_coefficient_variance, printed_missing_sum_limit,
    printed_sandwich_probability_limit⟩

/-! Two-coordinate transport and the expected finite sums. -/

lemma corrected_pair_preserving {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] (d : Dyad N) :
    MeasurePreserving (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d)))
      (unitSampleLaw K N) (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure (unitSampleLaw K N) := printed_unit_probability K
  have hind : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (unitSampleLaw K N) := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hi := (measurePreserving_eval (fun _ : Fin N => K.μ) (firstUnit d)).map_eq
  have hj := (measurePreserving_eval (fun _ : Fin N => K.μ) (secondUnit d)).map_eq
  refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _), ?_⟩
  have hp := (hind.indepFun (printed_endpoints_lt d).ne).map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable
  change (Measure.pi (fun _ : Fin N => K.μ)).map _ = _ at hp ⊢
  simp only [unitSampleLaw] at hp
  rw [hi, hj] at hp
  exact hp

lemma corrected_pair_integral {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] (d : Dyad N)
    (f : U × U → ℝ) (hf : Measurable f) :
    (∫ ω, f (ω (firstUnit d), ω (secondUnit d)) ∂ unitSampleLaw K N) =
      ∫ uv, f uv ∂ K.μ.prod K.μ := by
  have hp := corrected_pair_preserving K d
  have h := integral_map_of_stronglyMeasurable (μ := unitSampleLaw K N) hp.measurable hf.stronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm

lemma corrected_pair_integrable {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] (d : Dyad N)
    (f : U × U → ℝ) (hf : Integrable f (K.μ.prod K.μ)) :
    Integrable (fun ω => f (ω (firstUnit d), ω (secondUnit d))) (unitSampleLaw K N) := by
  exact (corrected_pair_preserving K d).integrable_comp_of_integrable hf

lemma corrected_pair_products {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    (∀ a b, Integrable (fun uv : U × U => K.X uv.1 uv.2 a * K.X uv.1 uv.2 b)
      (K.μ.prod K.μ)) ∧
    (∀ a, Integrable (fun uv : U × U => K.Y uv.1 uv.2 * K.X uv.1 uv.2 a)
      (K.μ.prod K.μ)) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨C, hC, hb⟩ := hK.2.2.2.2.1
  have hmX (a : Fin k) : Measurable (fun uv : U × U => K.X uv.1 uv.2 a) :=
    (measurable_pi_apply a).comp hK.2.1
  have hcoord (a : Fin k) : ∀ᵐ uv ∂ K.μ.prod K.μ, |K.X uv.1 uv.2 a| ≤ C := by
    filter_upwards [hb] with uv huv
    exact (norm_le_pi_norm (K.X uv.1 uv.2) a).trans huv.1
  constructor
  · intro a b
    apply (integrable_const (C*C)).mono' ((hmX a).mul (hmX b)).aestronglyMeasurable
    filter_upwards [hcoord a, hcoord b] with uv ha hb'
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
      mul_le_mul ha hb' (abs_nonneg _) hC
  · intro a
    apply (integrable_const (C*C)).mono' (hK.2.2.1.mul (hmX a)).aestronglyMeasurable
    filter_upwards [hb, hcoord a] with uv huv ha
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
      mul_le_mul huv.2 ha (abs_nonneg _) hC

lemma corrected_expected_gram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    meanMat (unitSampleLaw K N) (fun ω => sampleGram (design K ω)) =
      Dreal N • populationGram K := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hp := (corrected_pair_products K hK).1
  ext a b
  simp only [meanMat, sampleGram, Matrix.sum_apply, outer, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  change (∫ ω, (∑ d : Dyad N, design K ω d a * design K ω d b)
    ∂ unitSampleLaw K N) = Dreal N * (populationGram K) a b
  rw [integral_finsetSum _ (fun d hd => show Integrable (fun ω => design K ω d a * design K ω d b) (unitSampleLaw K N) from corrected_pair_integrable K d _ (hp a b))]
  have he (d : Dyad N) : (∫ ω, design K ω d a * design K ω d b ∂ unitSampleLaw K N) =
      (populationGram K) a b := by
    change (∫ ω, design K ω d a * design K ω d b ∂ unitSampleLaw K N) =
      ∫ uv, K.X uv.1 uv.2 a * K.X uv.1 uv.2 b ∂ K.μ.prod K.μ
    exact corrected_pair_integral K d (fun uv => K.X uv.1 uv.2 a * K.X uv.1 uv.2 b)
      (((measurable_pi_apply a).comp hK.2.1).mul ((measurable_pi_apply b).comp hK.2.1))
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, printed_card_real]

lemma corrected_expected_XY {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    meanVec (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
      score (design K ω d) (response K ω d)) =
      Dreal N • meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hp := (corrected_pair_products K hK).2
  ext a
  simp only [meanVec, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun d hd => show Integrable (fun ω => response K ω d * design K ω d a) (unitSampleLaw K N) from corrected_pair_integrable K d _ (hp a))]
  have he (d : Dyad N) : (∫ ω, response K ω d * design K ω d a ∂ unitSampleLaw K N) =
      ∫ uv, K.Y uv.1 uv.2 * K.X uv.1 uv.2 a ∂ K.μ.prod K.μ := by
    exact corrected_pair_integral K d (fun uv => K.Y uv.1 uv.2 * K.X uv.1 uv.2 a)
      (hK.2.2.1.mul ((measurable_pi_apply a).comp hK.2.1))
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, printed_card_real]

/-- Cancellation in the unnormalized population normal equation. -/
lemma corrected_expected_beta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    (meanMat (unitSampleLaw K N) (fun ω => sampleGram (design K ω)))⁻¹.mulVec
      (meanVec (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
        score (design K ω d) (response K ω d))) = populationBeta K := by
  have hd : Dreal N ≠ 0 := ne_of_gt (printed_Dpos hN)
  rw [corrected_expected_gram K hK, corrected_expected_XY K hK,
    matrix_inverse_scale_total _ _ hd, Matrix.smul_mulVec, Matrix.mulVec_smul,
    smul_smul, inv_mul_cancel₀ hd, one_smul] <;> rfl

lemma corrected_single_law {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (N : ℕ) : repeatedLaw (singleRecord K) N = unitSampleLaw K N := rfl

lemma corrected_single_L {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (N : ℕ) : repeatedL (singleRecord K) N = Dreal N := by
  simp [repeatedL, singleRecord, printed_card_real, printed_dyads_card_real]

lemma corrected_single_gram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    repeatedGram (singleRecord K) ω = sampleGram (design K ω) := by
  unfold repeatedGram sampleGram
  apply Finset.sum_congr rfl
  intro d _
  change (∑ _ : Fin 1, outer (design K ω d) (design K ω d)) = _
  rw [Fin.sum_univ_one]

lemma corrected_single_gram_fun {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) :
    (repeatedGram (singleRecord K) : (Fin N → U) → Mat k) =
      (fun ω => sampleGram (design K ω)) := by
  funext ω
  exact corrected_single_gram K ω

lemma corrected_single_XY {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    (∑ d : Dyad N, ∑ t, score (repeatedX (singleRecord K) ω d t)
      (repeatedY (singleRecord K) ω d t)) =
      ∑ d : Dyad N, score (design K ω d) (response K ω d) := by
  apply Finset.sum_congr rfl
  intro d _
  change (∑ _ : Fin 1, score (design K ω d) (response K ω d)) = _
  rw [Fin.sum_univ_one]

lemma corrected_single_H {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    repeatedH (singleRecord K) N = populationGram K := by
  have hd : Dreal N ≠ 0 := ne_of_gt (printed_Dpos hN)
  simp only [repeatedH, corrected_single_L, corrected_single_law,
    corrected_single_gram_fun, corrected_expected_gram K hK, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

lemma corrected_single_beta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    repeatedBeta (singleRecord K) N = populationBeta K := by
  simp only [repeatedBeta, corrected_single_law, corrected_single_gram_fun, corrected_single_XY]
  exact corrected_expected_beta K hK hN

lemma corrected_single_score {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) (ω : Fin N → U) :
    (∑ d : Dyad N, repeatedBlockScore (singleRecord K) (repeatedBeta (singleRecord K) N) ω d) =
      scoreSum K ω := by
  rw [corrected_single_beta K hK hN]
  unfold scoreSum
  apply Finset.sum_congr rfl
  intro d _
  change (∑ _ : Fin 1, score (design K ω d)
    (response K ω d - dot (design K ω d) (populationBeta K))) = _
  rw [Fin.sum_univ_one]
  rfl

lemma corrected_one_gram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    weightedGram K (fun _ : Dyad N => 1) ω = sampleGram (design K ω) := by
  simp [weightedGram, sampleGram]

lemma corrected_one_gram_fun {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) :
    (weightedGram K (fun _ : Dyad N => 1)) = (fun ω => sampleGram (design K ω)) := by
  funext ω
  exact corrected_one_gram K ω

lemma corrected_one_H {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    weightedPopulationGram K (fun _ : Dyad N => 1) = populationGram K := by
  have hd : Dreal N ≠ 0 := ne_of_gt (printed_Dpos hN)
  simp only [weightedPopulationGram, corrected_one_gram_fun,
    corrected_expected_gram K hK, smul_smul, inv_mul_cancel₀ hd, one_smul]

lemma corrected_one_beta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    weightedPopulationBeta K (fun _ : Dyad N => 1) = populationBeta K := by
  simp only [weightedPopulationBeta, corrected_one_gram_fun, one_mul]
  exact corrected_expected_beta K hK hN

lemma corrected_one_score {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) (ω : Fin N → U) :
    weightedScoreSum K (fun _ : Dyad N => 1) ω = scoreSum K ω := by
  simp only [weightedScoreSum, corrected_one_beta K hK hN, one_mul,
    scoreSum, epsilon, populationResidual, design, response, Fintype.card_unique]

theorem corrected_target_reductions_proof {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    repeatedTarget (singleRecord K) N = trueTarget K N ∧
    weightedTarget K (fun _ : Dyad N => 1) = trueTarget K N := by
  constructor
  · simp only [repeatedTarget, corrected_single_L, corrected_single_H K hK hN,
      corrected_single_law, corrected_single_score K hK hN, trueTarget]
  · have hs : weightedScoreSum K (fun _ : Dyad N => 1) = scoreSum K := by
      funext ω
      exact corrected_one_score K hK hN ω
    simp only [weightedTarget, corrected_one_H K hK hN, hs, trueTarget]

end AronowAudit.P018.Wave1
