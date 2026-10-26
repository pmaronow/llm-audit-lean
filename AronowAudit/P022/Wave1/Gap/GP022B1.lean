import AronowAudit.P022.P022_Variance
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Function.Floor



namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section

/-! ## P022-T12: finite permutation moments and the sharp null -/

private lemma t12_mean_sum {s : ℕ} (a : Fin s → ℝ) :
    finiteMean a = (∑ i, a i) / (s : ℝ) := by
  simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]

private lemma t12_sum_mean {s : ℕ} (a : Fin s → ℝ) :
    (∑ i, a i) = (s : ℝ) * finiteMean a := by
  simpa only [finiteMean, Fintype.card_fin] using
    (Fintype.card_mul_expect a).symm

private lemma t12_center_sum {N : ℕ} (y : Fin N → ℝ) :
    (∑ i, (y i - finiteMean y)) = 0 := by
  rw [Finset.sum_sub_distrib, t12_sum_mean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma t12_variance_nonneg {s : ℕ} (a : Fin s → ℝ) :
    0 ≤ finiteVariance a :=
  Finset.expect_nonneg (fun _ _ => sq_nonneg _)

private lemma t12_mean_sub {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ) (c : ℝ) :
    finiteMean (fun i => a i - c) = finiteMean a - c := by
  letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
  simp only [finiteMean, Finset.expect_sub_distrib, Fintype.expect_const]

private lemma t12_recenter {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ) (c : ℝ) :
    finiteVariance a = finiteMean (fun i => (a i - c) ^ 2) -
      (finiteMean a - c) ^ 2 := by
  letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
  rw [finite_variance_second_moment hs]
  have hexp : finiteMean (fun i => (a i - c) ^ 2) =
      finiteMean (fun i => a i ^ 2) - 2 * c * finiteMean a + c ^ 2 := by
    unfold finiteMean
    simp_rw [sub_sq]
    rw [Finset.expect_add_distrib, Finset.expect_sub_distrib]
    simp only [← Finset.expect_mul, ← Finset.mul_expect, Fintype.expect_const]
    ring
  rw [hexp]
  ring

private lemma t12_marginal_factor {N s : ℕ} (a : Fin s → ℝ) :
    marginalVarianceEstimate N a =
      (((N : ℝ) - 1) * s / ((N : ℝ) * ((s : ℝ) - 1))) *
        finiteVariance a := by
  unfold marginalVarianceEstimate sampleVariance finiteVariance
  rw [t12_sum_mean]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private lemma t12_marginal_nonneg {N s : ℕ} (hN : 1 ≤ N) (hs : 2 ≤ s)
    (a : Fin s → ℝ) : 0 ≤ marginalVarianceEstimate N a := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  rw [t12_marginal_factor]
  exact mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by positivity))
    (mul_nonneg (by positivity) (by linarith))) (t12_variance_nonneg a)

/-- The mean of an arbitrary injected block has the usual finite-population
second centered moment. The averaging carrier remains the actual permutations. -/
private lemma t12_block_moment {N s : ℕ} (hN : 2 ≤ N) (hs : 0 < s)
    (a : Fin s → Fin N) (ha : Function.Injective a) (y : Fin N → ℝ) :
    (𝔼 π : Equiv.Perm (Fin N),
      (finiteMean (fun i => y (π (a i))) - finiteMean y) ^ 2) =
        ((N : ℝ) - s) / (((N : ℝ) - 1) * s) * finiteVariance y := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hsum (π : Equiv.Perm (Fin N)) :
      (∑ i, (y (π (a i)) - finiteMean y)) =
        (s : ℝ) * (finiteMean (fun i => y (π (a i))) - finiteMean y) := by
    rw [Finset.sum_sub_distrib, t12_sum_mean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h := StatLean.HypothesisTesting.avg_perm_blockSum_sq hN a ha
    (fun i => y i - finiteMean y) (t12_center_sum y)
  have hnorm (f : Equiv.Perm (Fin N) → ℝ) :
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * ∑ π, f π = 𝔼 π, f π := by
    rw [Fintype.expect_eq_sum_div_card]
    ring
  rw [hnorm] at h
  simp_rw [hsum, mul_pow] at h
  rw [← Finset.mul_expect, t12_sum_mean] at h
  change (s : ℝ) ^ 2 * (𝔼 π : Equiv.Perm (Fin N),
      (finiteMean (fun i => y (π (a i))) - finiteMean y) ^ 2) =
    (s : ℝ) * ((N : ℝ) - s) / ((N : ℝ) * ((N : ℝ) - 1)) *
      ((N : ℝ) * finiteVariance y) at h
  have hc : (s : ℝ) * ((N : ℝ) - s) / ((N : ℝ) * ((N : ℝ) - 1)) *
      ((N : ℝ) * finiteVariance y) =
      (s : ℝ) ^ 2 * (((N : ℝ) - s) / (((N : ℝ) - 1) * s) *
        finiteVariance y) := by
    field_simp [hN0, hN1, hs0]
    <;> ring
  rw [hc] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hs0) h

private lemma t12_block_marginal_unbiased {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (a : Fin s → Fin N) (ha : Function.Injective a) (y : Fin N → ℝ) :
    (𝔼 π : Equiv.Perm (Fin N),
      marginalVarianceEstimate N (fun i => y (π (a i)))) = finiteVariance y := by
  have hNp : 0 < N := by omega
  have hsp : 0 < s := by omega
  letI : NeZero s := ⟨Nat.ne_of_gt hsp⟩
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hs1 : (s : ℝ) - 1 ≠ 0 := by linarith
  have hraw : (𝔼 π : Equiv.Perm (Fin N),
      finiteMean (fun i => (y (π (a i)) - finiteMean y) ^ 2)) = finiteVariance y := by
    unfold finiteMean
    rw [Finset.expect_comm]
    have he (i : Fin s) : (𝔼 π : Equiv.Perm (Fin N),
        (y (π (a i)) - finiteMean y) ^ 2) = finiteVariance y :=
      permutation_eval_mean hNp (fun j => (y j - finiteMean y) ^ 2) (a i)
    exact (Finset.expect_congr rfl (fun i _ => he i)).trans (Fintype.expect_const _)
  have hv : (𝔼 π : Equiv.Perm (Fin N), finiteVariance (fun i => y (π (a i)))) =
      finiteVariance y -
        ((N : ℝ) - s) / (((N : ℝ) - 1) * s) * finiteVariance y := by
    simp_rw [t12_recenter hsp _ (finiteMean y)]
    rw [Finset.expect_sub_distrib, hraw, t12_block_moment hN hsp a ha y]
  simp_rw [t12_marginal_factor]
  rw [← Finset.mul_expect, hv]
  field_simp [hN0, hN1, hs0, hs1]
  <;> ring

/-- The centered two-position cross moment, derived from the off-diagonal
permutation marginal rather than an assumed randomization variance formula. -/
private lemma t12_pair_centered {N : ℕ} (hN : 2 ≤ N) (y : Fin N → ℝ)
    (u v : Fin N) (huv : u ≠ v) :
    (𝔼 π : Equiv.Perm (Fin N),
      (y (π u) - finiteMean y) * (y (π v) - finiteMean y)) =
        -(finiteVariance y / ((N : ℝ) - 1)) := by
  classical
  let z : Fin N → ℝ := fun i => y i - finiteMean y
  have hz : ∑ i, z i = 0 := t12_center_sum y
  have hprod : ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
      z p.1 * z p.2 = ∑ i, ∑ j, z i * z j := Finset.sum_product _ _ _
  have hfull : (∑ i, ∑ j, z i * z j) = 0 := by
    rw [← Finset.sum_mul_sum, hz]
    ring
  have hdecomp : ((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ) =
      (Finset.univ : Finset (Fin N)).diag ∪ Finset.univ.offDiag :=
    (Finset.diag_union_offDiag _).symm
  rw [hdecomp, Finset.sum_union (Finset.disjoint_diag_offDiag _),
    Finset.sum_diag, hfull] at hprod
  have hoff : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, z p.1 * z p.2 =
      -(∑ i, z i ^ 2) := by
    simp only [← pow_two] at hprod
    linarith
  have h := StatLean.HypothesisTesting.avg_perm_apply_pair huv (fun i j => z i * z j)
  rw [Fintype.card_fin, hoff, t12_sum_mean] at h
  rw [Fintype.expect_eq_sum_div_card]
  change (∑ π : Equiv.Perm (Fin N), z (π u) * z (π v)) /
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ) = _
  rw [div_eq_inv_mul, h]
  change ((N : ℝ) * ((N : ℝ) - 1))⁻¹ *
      -((N : ℝ) * finiteVariance y) = _
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hN0, hN1]
  <;> ring

private def t12_treatment_position (d : Design) (i : Fin d.m) : Fin d.N :=
  ⟨i.val, by have := d.sample_le; omega⟩

private def t12_control_position (d : Design) (i : Fin d.k) : Fin d.N :=
  ⟨d.m + i.val, by have := d.sample_le; omega⟩

private lemma t12_treatment_injective (d : Design) :
    Function.Injective (t12_treatment_position d) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin d.N => x.val) h

private lemma t12_control_injective (d : Design) :
    Function.Injective (t12_control_position d) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  dsimp [t12_control_position] at he
  omega

private lemma t12_arm_marginals (d : Design) (y : Fin d.N → ℝ) :
    designExpectation d (fun π => marginalVarianceEstimate d.N
      (observedTreatment d y π)) = finiteVariance y ∧
    designExpectation d (fun π => marginalVarianceEstimate d.N
      (observedControl d y π)) = finiteVariance y := by
  have hN : 2 ≤ d.N := by have := d.population_min; omega
  constructor
  · exact t12_block_marginal_unbiased hN d.treatment_min
      (t12_treatment_position d) (t12_treatment_injective d) y
  · exact t12_block_marginal_unbiased hN d.control_min
      (t12_control_position d) (t12_control_injective d) y

private lemma t12_sqrt_cauchy {Ω : Type*} [Fintype Ω] (A C : Ω → ℝ)
    (hA : ∀ ω, 0 ≤ A ω) (hC : ∀ ω, 0 ≤ C ω) (v : ℝ) (hv : 0 ≤ v)
    (hEA : (𝔼 ω, A ω) = v) (hEC : (𝔼 ω, C ω) = v) :
    (𝔼 ω, Real.sqrt (A ω * C ω)) ≤ v := by
  have hc := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
    (fun ω => Real.sqrt (A ω)) (fun ω => Real.sqrt (C ω))
  have hmul : ∀ ω, Real.sqrt (A ω) * Real.sqrt (C ω) = Real.sqrt (A ω * C ω) := by
    intro ω
    exact (Real.sqrt_mul (hA ω) _).symm
  simp_rw [hmul, Real.sq_sqrt (hA _), Real.sq_sqrt (hC _)] at hc
  rw [hEA, hEC] at hc
  have hn : 0 ≤ (𝔼 ω, Real.sqrt (A ω * C ω)) :=
    Finset.expect_nonneg (fun _ _ => Real.sqrt_nonneg _)
  nlinarith

/-- Actual sharp-null randomization variance, proved from the same block
moments and the centered cross moment. -/
private lemma t12_sharp_null_variance (d : Design) (y : Fin d.N → ℝ) :
    trueVariance d y y = varianceExpression d.N d.m d.k
      (finiteVariance y) (finiteVariance y) (finiteVariance y) := by
  have hN : 2 ≤ d.N := by have := d.population_min; omega
  have hm : 0 < d.m := by have := d.treatment_min; omega
  have hk : 0 < d.k := by have := d.control_min; omega
  letI : NeZero d.m := ⟨Nat.ne_of_gt hm⟩
  letI : NeZero d.k := ⟨Nat.ne_of_gt hk⟩
  let T : Assignment d → ℝ := fun π => finiteMean (observedTreatment d y π) - finiteMean y
  let K : Assignment d → ℝ := fun π => finiteMean (observedControl d y π) - finiteMean y
  have ht : designExpectation d (fun π => T π ^ 2) =
      ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m) * finiteVariance y :=
    t12_block_moment hN hm (t12_treatment_position d) (t12_treatment_injective d) y
  have hk' : designExpectation d (fun π => K π ^ 2) =
      ((d.N : ℝ) - d.k) / (((d.N : ℝ) - 1) * d.k) * finiteVariance y :=
    t12_block_moment hN hk (t12_control_position d) (t12_control_injective d) y
  have hcross : designExpectation d (fun π => T π * K π) =
      -(finiteVariance y / ((d.N : ℝ) - 1)) := by
    have hT (π : Assignment d) : T π = finiteMean (fun i : Fin d.m =>
        y (π (t12_treatment_position d i)) - finiteMean y) :=
      (t12_mean_sub hm _ _).symm
    have hK (π : Assignment d) : K π = finiteMean (fun i : Fin d.k =>
        y (π (t12_control_position d i)) - finiteMean y) :=
      (t12_mean_sub hk _ _).symm
    simp_rw [hT, hK]
    unfold designExpectation finiteMean
    simp only [Finset.expect_mul_expect]
    rw [Finset.expect_comm]
    apply Eq.trans (Finset.expect_congr rfl (fun i _ => ?_))
      (Fintype.expect_const _)
    rw [Finset.expect_comm]
    have hp (j : Fin d.k) :
        t12_treatment_position d i ≠ t12_control_position d j := by
      intro he
      have he' := congrArg Fin.val he
      dsimp [t12_treatment_position, t12_control_position] at he'
      omega
    have he (j : Fin d.k) : (𝔼 π : Equiv.Perm (Fin d.N),
        (y (π (t12_treatment_position d i)) - finiteMean y) *
        (y (π (t12_control_position d j)) - finiteMean y)) =
        -(finiteVariance y / ((d.N : ℝ) - 1)) := t12_pair_centered hN y _ _ (hp j)
    exact (Finset.expect_congr rfl (fun i _ => he i)).trans (Fintype.expect_const _)
  have hmean : designExpectation d (estimatedEffect d y y) = 0 := by
    rw [difference_in_means_unbiased]
    simp only [averageEffect, sub_self]
  have heffect (π : Assignment d) : estimatedEffect d y y π = T π - K π := by
    dsimp [estimatedEffect, T, K]
    ring
  unfold trueVariance designVariance
  rw [hmean]
  simp_rw [sub_zero, heffect,
    show ∀ a b : ℝ, (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) by intros; ring]
  unfold designExpectation at ht hk' hcross ⊢
  rw [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    ht, hk', hcross]
  unfold varianceExpression
  have hm0 : (d.m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hk0 : (d.k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hNR : (2 : ℝ) ≤ d.N := by exact_mod_cast hN
  have hN1 : (d.N : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hm0, hk0, hN1]
  <;> ring

theorem sharp_null_neyman_bias_proof (d : Design) (hn : d.m + d.k = d.N)
    (y : Fin d.N → ℝ) :
    designExpectation d (neymanEstimate d y y .H) ≤ trueVariance d y y := by
  let A : Assignment d → ℝ := fun π =>
    marginalVarianceEstimate d.N (observedTreatment d y π)
  let C : Assignment d → ℝ := fun π =>
    marginalVarianceEstimate d.N (observedControl d y π)
  have hN : 1 ≤ d.N := by have := d.population_min; omega
  have hA : ∀ π, 0 ≤ A π := fun π =>
    t12_marginal_nonneg hN d.treatment_min _
  have hC : ∀ π, 0 ≤ C π := fun π =>
    t12_marginal_nonneg hN d.control_min _
  have hEA : (𝔼 π, A π) = finiteVariance y := (t12_arm_marginals d y).1
  have hEC : (𝔼 π, C π) = finiteVariance y := (t12_arm_marginals d y).2
  have hs := t12_sqrt_cauchy A C hA hC (finiteVariance y)
    (t12_variance_nonneg y) hEA hEC
  have hN1 : 0 < (d.N : ℝ) - 1 := by
    have h : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have heq : designExpectation d (neymanEstimate d y y .H) =
      varianceExpression d.N d.m d.k (finiteVariance y) (finiteVariance y)
        (𝔼 π, Real.sqrt (A π * C π)) := by
    change (𝔼 π, (((d.N : ℝ) - d.m) / d.m * A π +
      ((d.N : ℝ) - d.k) / d.k * C π + 2 * Real.sqrt (A π * C π)) /
        ((d.N : ℝ) - 1)) = _
    rw [← Finset.expect_div, Finset.expect_add_distrib, Finset.expect_add_distrib,
      ← Finset.mul_expect, ← Finset.mul_expect, ← Finset.mul_expect, hEA, hEC]
    rfl
  rw [heq, t12_sharp_null_variance]
  unfold varianceExpression
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hN1)

/-! ## P022-T14: finite quantile integration and covariance ordering

The proof below uses only finite quantiles. The reflection argument for the two
endpoint covariances avoids a bounded-support covariance/CDF identity.
-/

private def t14_Good (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (Set.range f).Finite

private lemma t14_good_const (c : ℝ) : t14_Good (fun _ => c) := by
  exact ⟨measurable_const, (Set.finite_singleton c).subset (by simp)⟩

private lemma t14_good_precomp {f : ℝ → ℝ} (hf : t14_Good f)
    (g : ℝ → ℝ) (hg : Measurable g) : t14_Good (fun u => f (g u)) := by
  refine ⟨hf.1.comp hg, hf.2.subset ?_⟩
  rintro _ ⟨u, rfl⟩
  exact ⟨g u, rfl⟩

private lemma t14_good_binary {f g : ℝ → ℝ} (hf : t14_Good f) (hg : t14_Good g)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    t14_Good (fun u => F (f u, g u)) := by
  refine ⟨hF.measurable.comp (hf.1.prodMk hg.1),
    ((hf.2.prod hg.2).image F).subset ?_⟩
  rintro _ ⟨u, rfl⟩
  exact ⟨(f u, g u), ⟨⟨u, rfl⟩, ⟨u, rfl⟩⟩, rfl⟩

private lemma t14_good_add {f g : ℝ → ℝ} (hf : t14_Good f) (hg : t14_Good g) :
    t14_Good (fun u => f u + g u) :=
  t14_good_binary hf hg (fun p => p.1 + p.2) (by fun_prop)

private lemma t14_good_sub {f g : ℝ → ℝ} (hf : t14_Good f) (hg : t14_Good g) :
    t14_Good (fun u => f u - g u) :=
  t14_good_binary hf hg (fun p => p.1 - p.2) (by fun_prop)

private lemma t14_good_mul {f g : ℝ → ℝ} (hf : t14_Good f) (hg : t14_Good g) :
    t14_Good (fun u => f u * g u) :=
  t14_good_binary hf hg (fun p => p.1 * p.2) (by fun_prop)

private lemma t14_good_sq {f : ℝ → ℝ} (hf : t14_Good f) :
    t14_Good (fun u => f u ^ 2) := by
  simpa only [pow_two] using t14_good_mul hf hf

private lemma t14_good_integrable {f : ℝ → ℝ} (hf : t14_Good f) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  obtain ⟨C, hC⟩ := (hf.2.image (fun x : ℝ => ‖x‖)).bddAbove
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
    dsimp [Set.uIoc]
    infer_instance
  apply intervalIntegrable_iff.mpr
  exact Integrable.of_bound hf.1.aestronglyMeasurable.restrict C
    (Filter.Eventually.of_forall (fun u => hC ⟨f u, ⟨u, rfl⟩, rfl⟩))

private lemma t14_sorted_length {s : ℕ} (a : Fin s → ℝ) :
    (sortedOutcomes a).length = s := by
  simp only [sortedOutcomes, List.length_mergeSort, List.length_ofFn]

private lemma t14_quantile_good {s : ℕ} (a : Fin s → ℝ) :
    t14_Good (empiricalQuantile a) := by
  classical
  refine ⟨(measurable_of_countable (orderStatistic a)).comp
    ((measurable_const.mul measurable_id).nat_ceil), ?_⟩
  let l := sortedOutcomes a
  have hl : l.length = s := t14_sorted_length a
  apply ((Set.finite_range (fun i : Fin (s + 1) => l.getD i.val 0))).subset
  rintro _ ⟨u, rfl⟩
  let j := Nat.ceil ((s : ℝ) * u) - 1
  by_cases hj : j < s
  · exact ⟨⟨j, by omega⟩, rfl⟩
  · refine ⟨⟨s, by omega⟩, ?_⟩
    change l.getD s 0 = l.getD j 0
    rw [List.getD_eq_default l 0 (by omega), List.getD_eq_default l 0 (by omega)]

private lemma t14_quantile_cell {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ)
    (j : ℕ) (u : ℝ) (hu : (j : ℝ) / s < u ∧ u < ((j : ℝ) + 1) / s) :
    empiricalQuantile a u = (sortedOutcomes a).getD j 0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlo : (j : ℝ) < (s : ℝ) * u := by
    have := (div_lt_iff₀ hsR).mp hu.1
    nlinarith
  have hhi : (s : ℝ) * u ≤ (j + 1 : ℕ) := by
    have := (lt_div_iff₀ hsR).mp hu.2
    push_cast
    nlinarith
  have hrank : Nat.ceil ((s : ℝ) * u) = j + 1 := by
    apply (Nat.ceil_eq_iff (by omega : j + 1 ≠ 0)).mpr
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using (show (j : ℝ) < (s : ℝ) * u ∧ (s : ℝ) * u ≤ (j + 1 : ℕ) from ⟨hlo, hhi⟩)
  simp only [empiricalQuantile, orderStatistic, hrank, Nat.add_sub_cancel]

private lemma t14_sorted_sum {s : ℕ} (a : Fin s → ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin s, f ((sortedOutcomes a).getD i.val 0)) = ∑ i, f (a i) := by
  let l := sortedOutcomes a
  have hl : l.length = s := t14_sorted_length a
  have hlist : (∑ i : Fin l.length, f (l.getD i.val 0)) = (l.map f).sum := by
    have hg (i : Fin l.length) : l.getD i.val 0 = l[i.val] :=
      List.getD_eq_getElem l 0 i.isLt
    simp_rw [hg]
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  have he := Fintype.sum_equiv (finCongr hl)
    (fun i : Fin l.length => f (l.getD i.val 0))
    (fun i : Fin s => f (l.getD i.val 0)) (fun _ => rfl)
  rw [hlist] at he
  calc
    _ = (l.map f).sum := he.symm
    _ = ((List.ofFn a).map f).sum :=
      ((List.mergeSort_perm (List.ofFn a) (fun x y => decide (x ≤ y))).map f).sum_eq
    _ = ∑ i, f (a i) := by rw [← List.ofFn_comp' a f, List.sum_ofFn]

/-- The exact finite empirical quantile law, also for nonlinear tests.
The open cell interiors avoid every endpoint convention in `Nat.ceil`. -/
private lemma t14_quantile_integral {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ)
    (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (empiricalQuantile a u)) = finiteMean (fun i => f (a i)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hsR
  let p : ℕ → ℝ := fun j => (j : ℝ) / s
  have hle (j : ℕ) : p j ≤ p (j + 1) := by
    dsimp [p]
    apply div_le_div_of_nonneg_right _ hsR.le
    exact_mod_cast (Nat.le_succ j)
  have hcell (j : ℕ) : Set.EqOn (fun u => f (empiricalQuantile a u))
      (fun _ => f ((sortedOutcomes a).getD j 0)) (Set.uIoo (p j) (p (j + 1))) := by
    intro u hu
    rw [Set.uIoo_of_le (hle j)] at hu
    apply congrArg f
    apply t14_quantile_cell hs a j u
    simpa [p, Nat.cast_add, Nat.cast_one] using hu
  have hint (j : ℕ) : IntervalIntegrable (fun u => f (empiricalQuantile a u))
      volume (p j) (p (j + 1)) :=
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => f ((sortedOutcomes a).getD j 0)) volume (p j) (p (j + 1))).congr_uIoo
        (hcell j).symm
  have hi := intervalIntegral.sum_integral_adjacent_intervals
    (fun j (_ : j < s) => hint j)
  have hp0 : p 0 = 0 := by simp [p]
  have hp1 : p s = 1 := by simp [p, hs0]
  rw [hp0, hp1] at hi
  rw [← hi]
  have hcellint (j : ℕ) :
      (∫ u in p j..p (j + 1), f (empiricalQuantile a u)) =
        f ((sortedOutcomes a).getD j 0) / s := by
    rw [intervalIntegral.integral_congr_uIoo (hcell j), intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    dsimp [p]
    push_cast
    field_simp [hs0]
    <;> ring
  simp_rw [hcellint]
  rw [← Finset.sum_div, ← Fin.sum_univ_eq_sum_range, t14_sorted_sum, t12_mean_sum]

private lemma t14_quantile_monotone {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ) :
    MonotoneOn (empiricalQuantile a) (Set.Icc (0 : ℝ) 1) := by
  have hlen := t14_sorted_length a
  have hsort : (sortedOutcomes a).SortedLE := by
    exact List.sortedLE_mergeSort
  intro u hu v hv huv
  have hsR : (0 : ℝ) ≤ s := by positivity
  have hru : Nat.ceil ((s : ℝ) * u) ≤ s := by
    apply Nat.ceil_le.mpr
    nlinarith [hu.2]
  have hrv : Nat.ceil ((s : ℝ) * v) ≤ s := by
    apply Nat.ceil_le.mpr
    nlinarith [hv.2]
  have hidx : Nat.ceil ((s : ℝ) * u) - 1 ≤ Nat.ceil ((s : ℝ) * v) - 1 :=
    Nat.sub_le_sub_right (Nat.ceil_mono (mul_le_mul_of_nonneg_left huv hsR)) 1
  have hiu : Nat.ceil ((s : ℝ) * u) - 1 < (sortedOutcomes a).length := by omega
  have hiv : Nat.ceil ((s : ℝ) * v) - 1 < (sortedOutcomes a).length := by omega
  unfold empiricalQuantile orderStatistic
  rw [List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hiv]
  exact hsort.getElem_le_getElem_of_le hidx

/-- Cauchy--Schwarz for these finite-range functions, obtained by integrating
the nonnegative quadratic `(t*f+g)^2` and taking its discriminant. -/
private lemma t14_integral_cauchy {f g : ℝ → ℝ} (hf : t14_Good f) (hg : t14_Good g) :
    (∫ u in (0 : ℝ)..1, f u * g u) ^ 2 ≤
      (∫ u in (0 : ℝ)..1, f u ^ 2) * (∫ u in (0 : ℝ)..1, g u ^ 2) := by
  have hq (t : ℝ) : 0 ≤
      (∫ u in (0 : ℝ)..1, f u ^ 2) * (t * t) +
        (2 * (∫ u in (0 : ℝ)..1, f u * g u)) * t +
          (∫ u in (0 : ℝ)..1, g u ^ 2) := by
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (fun u : ℝ => sq_nonneg (t * f u + g u))
    have hexp : (fun u => (t * f u + g u) ^ 2) =
        (fun u => t ^ 2 * f u ^ 2 + (2 * t) * (f u * g u) + g u ^ 2) := by
      funext u; ring
    rw [hexp, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hn
    · nlinarith only [hn]
    all_goals
      first
      | exact (t14_good_integrable (t14_good_sq hf) 0 1).const_mul _
      | exact (t14_good_integrable (t14_good_mul hf hg) 0 1).const_mul _
      | exact t14_good_integrable (t14_good_sq hg) 0 1
      | exact ((t14_good_integrable (t14_good_sq hf) 0 1).const_mul _).add
          ((t14_good_integrable (t14_good_mul hf hg) 0 1).const_mul _)
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith only [hd]

private lemma t14_covariance_cauchy {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    |sharpCovariance a b B| ≤ Real.sqrt (finiteVariance a * finiteVariance b) := by
  let F : ℝ → ℝ := fun u => empiricalQuantile a u - finiteMean a
  let G : ℝ → ℝ := fun u => empiricalQuantile b u - finiteMean b
  let r : ℝ → ℝ := fun u => if B = .H then u else 1 - u
  have hF : t14_Good F := t14_good_sub (t14_quantile_good a) (t14_good_const _)
  have hG : t14_Good G := t14_good_sub (t14_quantile_good b) (t14_good_const _)
  have hr : Measurable r := by cases B <;> dsimp [r] <;> fun_prop
  have hGr := t14_good_precomp hG r hr
  have hmeanF : (∫ u in (0 : ℝ)..1, F u) = 0 := by
    dsimp [F]
    rw [intervalIntegral.integral_sub (t14_good_integrable (t14_quantile_good a) 0 1)
      intervalIntegrable_const]
    rw [show (∫ u in (0 : ℝ)..1, empiricalQuantile a u) = finiteMean a from
      t14_quantile_integral hm a (fun x => x)]
    simp
  have hmeanG : (∫ u in (0 : ℝ)..1, G u) = 0 := by
    dsimp [G]
    rw [intervalIntegral.integral_sub (t14_good_integrable (t14_quantile_good b) 0 1)
      intervalIntegrable_const]
    rw [show (∫ u in (0 : ℝ)..1, empiricalQuantile b u) = finiteMean b from
      t14_quantile_integral hk b (fun x => x)]
    simp
  have hreflect (f : ℝ → ℝ) :
      (∫ u in (0 : ℝ)..1, f (r u)) = ∫ u in (0 : ℝ)..1, f u := by
    cases B
    · rfl
    · simpa [r] using (intervalIntegral.integral_comp_sub_left f (a := 0) (b := 1) 1)
  have hmeanGr : (∫ u in (0 : ℝ)..1, G (r u)) = 0 := by rw [hreflect, hmeanG]
  have hsqF : (∫ u in (0 : ℝ)..1, F u ^ 2) = finiteVariance a :=
    t14_quantile_integral hm a (fun x => (x - finiteMean a) ^ 2)
  have hsqG : (∫ u in (0 : ℝ)..1, G (r u) ^ 2) = finiteVariance b := by
    rw [hreflect (fun u => G u ^ 2)]
    exact t14_quantile_integral hk b (fun x => (x - finiteMean b) ^ 2)
  have hcov : (∫ u in (0 : ℝ)..1, F u * G (r u)) = sharpCovariance a b B := by
    have hpoint : (fun u => empiricalQuantile a u * empiricalQuantile b (r u)) =
        (fun u => F u * G (r u) + finiteMean b * F u +
          finiteMean a * G (r u) + finiteMean a * finiteMean b) := by
      funext u; dsimp [F, G]; ring
    unfold sharpCovariance
    change _ = (∫ u in (0 : ℝ)..1,
      empiricalQuantile a u * empiricalQuantile b (r u)) - _
    rw [hpoint]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hmeanF, hmeanGr]
    · simp
    all_goals
      first
      | exact intervalIntegrable_const
      | exact t14_good_integrable (t14_good_mul hF hGr) 0 1
      | exact (t14_good_integrable hF 0 1).const_mul _
      | exact (t14_good_integrable hGr 0 1).const_mul _
      | exact (t14_good_integrable (t14_good_add
          (t14_good_mul hF hGr) (t14_good_mul (t14_good_const _) hF)) 0 1)
      | exact (t14_good_integrable (t14_good_add
          (t14_good_add (t14_good_mul hF hGr) (t14_good_mul (t14_good_const _) hF))
          (t14_good_mul (t14_good_const _) hGr)) 0 1)
  have hc := t14_integral_cauchy hF hGr
  rw [hsqF, hsqG, hcov] at hc
  have hv := t12_variance_nonneg a
  have hw := t12_variance_nonneg b
  have hs := Real.sq_sqrt (mul_nonneg hv hw)
  have hn := Real.sqrt_nonneg (finiteVariance a * finiteVariance b)
  nlinarith [sq_abs (sharpCovariance a b B), abs_nonneg (sharpCovariance a b B)]

private lemma t14_covariance_order {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    sharpCovariance a b .L ≤ sharpCovariance a b .H := by
  let F := empiricalQuantile a
  let G := empiricalQuantile b
  let R : ℝ → ℝ := fun u => 1 - u
  have hF := t14_quantile_good a
  have hG := t14_quantile_good b
  have hFR := t14_good_precomp hF R (by fun_prop)
  have hGR := t14_good_precomp hG R (by fun_prop)
  have hmonoF := t14_quantile_monotone hm a
  have hmonoG := t14_quantile_monotone hk b
  have hp : 0 ≤ ∫ u in (0 : ℝ)..1, (F u - F (R u)) * (G u - G (R u)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have hRu : R u ∈ Set.Icc (0 : ℝ) 1 := by dsimp [R]; constructor <;> linarith [hu.1, hu.2]
    by_cases h : u ≤ R u
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hmonoF hu hRu h)) (sub_nonpos.mpr (hmonoG hu hRu h))
    · exact mul_nonneg (sub_nonneg.mpr (hmonoF hRu hu (le_of_not_ge h)))
        (sub_nonneg.mpr (hmonoG hRu hu (le_of_not_ge h)))
  have hreflect (f : ℝ → ℝ) :
      (∫ u in (0 : ℝ)..1, f (R u)) = ∫ u in (0 : ℝ)..1, f u := by
    simpa [R] using (intervalIntegral.integral_comp_sub_left f (a := 0) (b := 1) 1)
  have hcross : (∫ u in (0 : ℝ)..1, F (R u) * G u) =
      ∫ u in (0 : ℝ)..1, F u * G (R u) := by
    have h := hreflect (fun u => F u * G (R u))
    simpa [R] using h
  have hpoint : (fun u => (F u - F (R u)) * (G u - G (R u))) =
      (fun u => F u * G u + F (R u) * G (R u) -
        F u * G (R u) - F (R u) * G u) := by funext u; ring
  rw [hpoint, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, hreflect (fun u => F u * G u), hcross] at hp
  · change (∫ u in (0 : ℝ)..1, F u * G (R u)) - _ ≤
      (∫ u in (0 : ℝ)..1, F u * G u) - _
    linarith
  all_goals
    first
    | exact t14_good_integrable (t14_good_mul hF hG) 0 1
    | exact t14_good_integrable (t14_good_mul hFR hGR) 0 1
    | exact t14_good_integrable (t14_good_mul hF hGR) 0 1
    | exact t14_good_integrable (t14_good_mul hFR hG) 0 1
    | exact t14_good_integrable (t14_good_add (t14_good_mul hF hG)
        (t14_good_mul hFR hGR)) 0 1
    | exact t14_good_integrable (t14_good_sub
        (t14_good_add (t14_good_mul hF hG) (t14_good_mul hFR hGR))
        (t14_good_mul hF hGR)) 0 1

private lemma t14_variance_comparison {N s : ℕ} (hs : 2 ≤ s) (hsN : s ≤ N)
    (a : Fin s → ℝ) : finiteVariance a ≤ marginalVarianceEstimate N a := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hsNR : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hden : 0 < (N : ℝ) * ((s : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hfactor : 1 ≤ ((N : ℝ) - 1) * s / ((N : ℝ) * ((s : ℝ) - 1)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  rw [t12_marginal_factor]
  nlinarith [t12_variance_nonneg a]

private lemma t14_variance_mono (N m k : ℕ) (hN : 1 < N)
    (A C x z : ℝ) (hxz : x ≤ z) :
    varianceExpression N m k A C x ≤ varianceExpression N m k A C z := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  unfold varianceExpression
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem estimated_bound_ordering_proof (d : Design) (hn : d.m + d.k = d.N)
    (y1 y0 : Fin d.N → ℝ) (π : Assignment d) :
    neymanEstimate d y1 y0 .L π ≤ estimatedVariance d y1 y0 .L π ∧
    estimatedVariance d y1 y0 .L π ≤ estimatedVariance d y1 y0 .H π ∧
    estimatedVariance d y1 y0 .H π ≤ neymanEstimate d y1 y0 .H π ∧
    neymanEstimate d y1 y0 .H π ≤ conventionalEstimate d y1 y0 π := by
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let A := marginalVarianceEstimate d.N a
  let C := marginalVarianceEstimate d.N b
  have hN : 1 < d.N := by have := d.population_min; omega
  have hm : 0 < d.m := by have := d.treatment_min; omega
  have hk : 0 < d.k := by have := d.control_min; omega
  have hmN : d.m ≤ d.N := by have := d.sample_le; omega
  have hkN : d.k ≤ d.N := by have := d.sample_le; omega
  have hA : 0 ≤ A := t12_marginal_nonneg (by omega) d.treatment_min a
  have hC : 0 ≤ C := t12_marginal_nonneg (by omega) d.control_min b
  have hv := t12_variance_nonneg a
  have hw := t12_variance_nonneg b
  have hvA := t14_variance_comparison d.treatment_min hmN a
  have hwC := t14_variance_comparison d.control_min hkN b
  have hroot : Real.sqrt (finiteVariance a * finiteVariance b) ≤ Real.sqrt (A * C) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul hvA hwC hw hA
  have hlow : -Real.sqrt (A * C) ≤ sharpCovariance a b .L := by
    have hh := (abs_le.mp ((t14_covariance_cauchy hm hk a b .L).trans hroot)).1
    exact hh
  have hhigh : sharpCovariance a b .H ≤ Real.sqrt (A * C) :=
    (abs_le.mp ((t14_covariance_cauchy hm hk a b .H).trans hroot)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change varianceExpression d.N d.m d.k A C (-Real.sqrt (A * C)) ≤
      varianceExpression d.N d.m d.k A C (sharpCovariance a b .L)
    exact t14_variance_mono _ _ _ hN A C _ _ hlow
  · change varianceExpression d.N d.m d.k A C (sharpCovariance a b .L) ≤
      varianceExpression d.N d.m d.k A C (sharpCovariance a b .H)
    exact t14_variance_mono _ _ _ hN A C _ _ (t14_covariance_order hm hk a b)
  · change varianceExpression d.N d.m d.k A C (sharpCovariance a b .H) ≤
      varianceExpression d.N d.m d.k A C (Real.sqrt (A * C))
    exact t14_variance_mono _ _ _ hN A C _ _ hhigh
  · have hNR : (1 : ℝ) < d.N := by exact_mod_cast hN
    have hm0 : (d.m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hk0 : (d.k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    have hN1 : (d.N : ℝ) - 1 ≠ 0 := by linarith
    have hdiff : conventionalEstimate d y1 y0 π - neymanEstimate d y1 y0 .H π =
        (A + C - 2 * Real.sqrt (A * C)) / ((d.N : ℝ) - 1) := by
      change (d.N : ℝ) / ((d.N : ℝ) - 1) * (A / d.m + C / d.k) -
        varianceExpression d.N d.m d.k A C (Real.sqrt (A * C)) = _
      unfold varianceExpression
      field_simp [hm0, hk0, hN1]
      <;> ring
    have hnon : 0 ≤ conventionalEstimate d y1 y0 π - neymanEstimate d y1 y0 .H π := by
      rw [hdiff]
      exact div_nonneg (by linarith [sqrt_product_le_arithmetic A C hA hC]) (by linarith)
    linarith

end
end AronowAudit.P022.Wave1
