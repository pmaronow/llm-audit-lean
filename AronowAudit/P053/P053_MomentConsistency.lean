import AronowAudit.P053.P053_Completion

/-! SRS moment consistency under bounded-fourth-moment regularity.
-/

namespace AronowAudit.P053
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace MomentCompletion

open Causalean.Experimentation.FinitePopulationMoments

/-- A fourth-moment bound controls the square of the largest centered
squared outcome. No independence or randomization assertion is used here. -/
theorem max_deviation_fourth_bound {U : Type*} [Fintype U] [Nonempty U]
    (y : U → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hfourth : (∑ i, (y i)^4) ≤ B*(Fintype.card U : ℝ)) :
    (popMaxSqDev y)^2 ≤ 16*B*(Fintype.card U : ℝ) := by
  classical
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => |y i|)
  have hM (i : U) : |y i| ≤ M :=
    Finset.le_sup' (fun i => |y i|) (Finset.mem_univ i)
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset U)) Finset.univ_nonempty (fun i => |y i|)
  have hMnonneg : 0 ≤ M := (abs_nonneg (y j)).trans (hM j)
  have hMfourth : M^4 ≤ B*(Fintype.card U : ℝ) := by
    calc
      M^4 = (y j)^4 := by
        rw [show M = |y j| from he, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (y j)^4)]
      _ ≤ ∑ i, (y i)^4 := Finset.single_le_sum (f := fun i => (y i)^4)
        (fun i _ => by positivity) (Finset.mem_univ j)
      _ ≤ _ := hfourth
  have hN : (0:ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hmean : |popMean y| ≤ M := by
    unfold popMean
    rw [abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    calc
      |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : U, M := Finset.sum_le_sum (fun i _ => hM i)
      _ = M*(Fintype.card U : ℝ) := by simp [mul_comm]
  have hcenter (i : U) : (y i-popMean y)^2 ≤ 4*M^2 := by
    have hab : |y i-popMean y| ≤ 2*M := by
      calc
        _ = |y i + -popMean y| := by rw [sub_eq_add_neg]
        _ ≤ |y i|+|-popMean y| := abs_add_le _ _
        _ = |y i|+|popMean y| := by rw [abs_neg]
        _ ≤ M+M := add_le_add (hM i) hmean
        _ = _ := by ring
    have hh := (sq_le_sq₀ (abs_nonneg (y i-popMean y)) (by positivity : 0 ≤ 2*M)).mpr hab
    simpa only [sq_abs, mul_pow, show (2:ℝ)^2=4 by norm_num] using hh
  have hmax : popMaxSqDev y ≤ 4*M^2 := by
    apply Finset.sup'_le
    intro i hi
    exact hcenter i
  have hmaxnonneg : 0 ≤ popMaxSqDev y :=
    (sq_nonneg (y j-popMean y)).trans (Finset.le_sup' (fun i => (y i-popMean y)^2) (Finset.mem_univ j))
  have hs := (sq_le_sq₀ hmaxnonneg (by positivity : 0 ≤ 4*M^2)).mpr hmax
  calc
    (popMaxSqDev y)^2 ≤ 16*M^4 := by nlinarith only [hs]
    _ ≤ 16*(B*(Fintype.card U : ℝ)) := mul_le_mul_of_nonneg_left hMfourth (by norm_num)
    _ = _ := by ring

/-- The maximal centered squared deviation divided by sample size tends to zero
under bounded fourth moments, growing populations, and a nonzero limiting sampling fraction. -/
theorem maximal_square_rate {U : ℕ → Type*} [∀ k, Fintype (U k)]
    [∀ k, Nonempty (U k)] (y : ∀ k, U k → ℝ) (n : ℕ → ℕ)
    (hn : ∀ k, 0 < n k) (hnN : ∀ k, n k ≤ Fintype.card (U k))
    (B q : ℝ) (hB : 0 ≤ B) (hq : q ≠ 0)
    (hfourth : ∀ k, (∑ i, (y k i)^4) ≤ B*(Fintype.card (U k) : ℝ))
    (hNinv : Tendsto (fun k => 1/(Fintype.card (U k) : ℝ)) atTop (𝓝 0))
    (hfrac : Tendsto (fun k => (n k : ℝ)/(Fintype.card (U k) : ℝ)) atTop (𝓝 q)) :
    Tendsto (fun k => popMaxSqDev (y k)/(n k : ℝ)) atTop (𝓝 0) := by
  have hbound (k : ℕ) :
      (popMaxSqDev (y k)/(n k : ℝ))^2 ≤
      (16*B)*(1/(Fintype.card (U k) : ℝ)) /
        ((n k : ℝ)/(Fintype.card (U k) : ℝ))^2 := by
    have hn0 : (n k : ℝ) ≠ 0 := by exact_mod_cast (hn k).ne'
    have hN0 : (Fintype.card (U k) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := U k)).ne'
    calc
      _ = (popMaxSqDev (y k))^2/(n k : ℝ)^2 := div_pow _ _ _
      _ ≤ (16*B*(Fintype.card (U k) : ℝ))/(n k : ℝ)^2 :=
        div_le_div_of_nonneg_right (max_deviation_fourth_bound (y k) B hB (hfourth k))
          (sq_nonneg _)
      _ = _ := by field_simp
  have hlimit : Tendsto (fun k => (16*B)*(1/(Fintype.card (U k) : ℝ)) /
      ((n k : ℝ)/(Fintype.card (U k) : ℝ))^2) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := 16*B)).mul hNinv).div (hfrac.pow 2) (pow_ne_zero 2 hq)
    change Tendsto (fun k => (16*B)*(1/(Fintype.card (U k) : ℝ)) /
      ((n k : ℝ)/(Fintype.card (U k) : ℝ))^2) atTop (𝓝 ((16*B)*0/q^2)) at hh
    simpa using hh
  have hs : Tendsto (fun k => (popMaxSqDev (y k)/(n k : ℝ))^2) atTop (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) hbound hlimit
  have hnonneg (k : ℕ) : 0 ≤ popMaxSqDev (y k)/(n k : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    obtain ⟨i⟩ := (inferInstance : Nonempty (U k))
    exact (sq_nonneg (y k i-popMean (y k))).trans
      (Finset.le_sup' (fun i => (y k i-popMean (y k))^2) (Finset.mem_univ i))
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg _), Real.sqrt_zero]
    using hs.sqrt

/-- A positive asymptotic sampling fraction forces the sample size to grow. -/
theorem sample_size_diverges (N n : ℕ → ℕ) (q : ℝ) (hq : 0 < q)
    (hN : Tendsto N atTop atTop)
    (hfrac : Tendsto (fun k => (n k : ℝ)/(N k : ℝ)) atTop (𝓝 q)) :
    Tendsto n atTop atTop := by
  have hNR : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hN
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply (hNR.atTop_mul_pos hq hfrac).congr'
  filter_upwards [hN.eventually_ge_atTop 1] with k hk
  have h0 : (N k : ℝ) ≠ 0 := by exact_mod_cast (by omega : N k ≠ 0)
  field_simp


/-- Arm sample-variance consistency under bounded-fourth-moment regularity
when both arm sizes are at least two at every index. -/
theorem arm_variance_limits_all_sizes (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ)
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) :
    InProbability E (fun k z => AronowAudit.P053.sampleVariance z (observed (E k) z)) v1 ∧
    InProbability E (fun k z => AronowAudit.P053.sampleVariance zᶜ (observed (E k) z)) v0 := by
  letI : ∀ k, Nonempty (Fin (E k).size) := fun k =>
    ⟨⟨0, by have hh := hsize k; dsimp [Population.size]; omega⟩⟩
  obtain ⟨B,hB,hfourth⟩ := h.fourth_moments
  have hNpos (k : ℕ) : (0:ℝ) < (E k).size := by
    have hh := hsize k
    exact_mod_cast (by dsimp [Population.size]; omega : 0 < (E k).size)
  have htotal (k : ℕ) :
      (∑ i : Fin (E k).size, (((E k).Y1 i)^4+((E k).Y0 i)^4)) ≤ B*(E k).size :=
    (div_le_iff₀ (hNpos k)).mp (hfourth k)
  have hfourth1 (k : ℕ) : (∑ i, ((E k).Y1 i)^4) ≤ B*(Fintype.card (Fin (E k).size) : ℝ) := by
    simp only [Fintype.card_fin]
    exact (Finset.sum_le_sum (fun i _ => le_add_of_nonneg_right (by positivity))).trans (htotal k)
  have hfourth0 (k : ℕ) : (∑ i, ((E k).Y0 i)^4) ≤ B*(Fintype.card (Fin (E k).size) : ℝ) := by
    simp only [Fintype.card_fin]
    exact (Finset.sum_le_sum (fun i _ => le_add_of_nonneg_left (by positivity))).trans (htotal k)
  have hNinv : Tendsto (fun k => 1/(Fintype.card (Fin (E k).size) : ℝ)) atTop (𝓝 0) := by
    simpa only [Fintype.card_fin] using regularity_inverse_size E p v1 v0 vt τ h
  have hmax1 := maximal_square_rate (fun k => (E k).Y1) (fun k => (E k).n1)
    (fun k => by have hh := hsize k; omega) (fun k => by simp [Population.size])
    B p hB (ne_of_gt h.p_positive) hfourth1 hNinv
    (by simpa only [Fintype.card_fin] using h.allocation)
  have hmax0 := maximal_square_rate (fun k => (E k).Y0) (fun k => (E k).n0)
    (fun k => by have hh := hsize k; omega) (fun k => by simp [Population.size])
    B (1-p) hB (by linarith [h.p_less_one]) hfourth0 hNinv
    (by simpa only [Fintype.card_fin] using regularity_allocation_control E p v1 v0 vt τ h)
  have hvar1 : Tendsto (fun k => popVar (E k).Y1) atTop (𝓝 v1) := by
    simpa only [CausalBridge.populationVariance_eq] using h.variance1
  have hvar0 : Tendsto (fun k => popVar (E k).Y0) atTop (𝓝 v0) := by
    simpa only [CausalBridge.populationVariance_eq] using h.variance0
  have ht := SampleVarianceConsistency.sampleVariance_tendstoInProb
    (U := fun k => Fin (E k).size) (fun k => (E k).n1) (fun k => (hsize k).1)
    (fun k => by simp [Population.size]) (fun k => (E k).Y1) v1
    (sample_size_diverges (fun k => (E k).size) (fun k => (E k).n1) p h.p_positive
      h.size_diverges h.allocation) hvar1 hmax1
  have hc := SampleVarianceConsistency.sampleVariance_tendstoInProb
    (U := fun k => Fin (E k).size) (fun k => (E k).n0) (fun k => (hsize k).2)
    (fun k => by simp [Population.size]) (fun k => (E k).Y0) v0
    (sample_size_diverges (fun k => (E k).size) (fun k => (E k).n0) (1-p)
      (by linarith [h.p_less_one]) h.size_diverges
      (regularity_allocation_control E p v1 v0 vt τ h)) hvar0 hmax0
  have ht' := CausalBridge.treated_limit E
    (fun k z => AronowAudit.P053.sampleVariance z (E k).Y1)
    (fun k => popVar (E k).Y1) v1
    (by simpa only [Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb,
      CausalBridge.sampleVariance_eq] using ht) hvar1
  have hc' := CausalBridge.control_limit E
    (fun k z => AronowAudit.P053.sampleVariance z (E k).Y0)
    (fun k => popVar (E k).Y0) v0
    (by simpa only [Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb,
      CausalBridge.sampleVariance_eq] using hc) hvar0
  simpa only [treated_variance_observed, control_variance_observed] using And.intro ht' hc'

/-- Regularity is preserved when an arbitrary finite prefix is removed. -/
theorem regularity_shift (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) (K : ℕ) :
    Regularity (fun k => E (k+K)) p v1 v0 vt τ := by
  have hs := tendsto_add_atTop_nat K
  refine ⟨h.size_diverges.comp hs, hs.eventually h.arm_sizes,
    h.p_positive, h.p_less_one, h.allocation.comp hs,
    h.variance1.comp hs, h.variance0.comp hs, h.varianceEffect.comp hs,
    h.average_effect.comp hs, ?_⟩
  obtain ⟨B,hB,hfourth⟩ := h.fourth_moments
  exact ⟨B,hB,fun k => hfourth (k+K)⟩

/-- Complete arm sample-variance consistency under bounded-fourth-moment regularity;
initial populations with small arms are allowed. -/
theorem arm_variance_limits (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    InProbability E (fun k z => AronowAudit.P053.sampleVariance z (observed (E k) z)) v1 ∧
    InProbability E (fun k z => AronowAudit.P053.sampleVariance zᶜ (observed (E k) z)) v0 := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp h.arm_sizes
  have hs := arm_variance_limits_all_sizes (fun k => E (k+K)) p v1 v0 vt τ
    (regularity_shift E p v1 v0 vt τ h K) (fun k => hK (k+K) (by omega))
  constructor
  · intro ε hε
    exact (tendsto_add_atTop_iff_nat K).mp (hs.1 ε hε)
  · intro ε hε
    exact (tendsto_add_atTop_iff_nat K).mp (hs.2 ε hε)

/-- Chebyshev consistency of the actual difference in means, using its
exact finite variance and unbiasedness. -/
theorem estimate_limit (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    InProbability E (fun k z => estimate (E k) z) τ := by
  apply CausalBridge.chebyshev_limit
  · have hh := (regularity_inverse_size E p v1 v0 vt τ h).mul
      (actual_variance_limit_bound E p v1 v0 vt τ h).1
    apply (show Tendsto (fun k => (1/((E k).size : ℝ))*
      (((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))) atTop (𝓝 0)
      from by simpa using hh).congr'
    filter_upwards [h.arm_sizes] with k hk
    have hN : ((E k).size : ℝ) ≠ 0 := by
      exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
    field_simp
  · apply h.average_effect.congr'
    filter_upwards [h.arm_sizes] with k hk
    exact (difference_in_means_unbiased (E k) (by omega) (by omega)).symm

end MomentCompletion

/-- The finite-population sampling theorem implies the moment LLN. -/
theorem finitePopulationMomentLLN : FinitePopulationMomentLLN := by
  intro E p v1 v0 vt τ h
  exact ⟨(MomentCompletion.arm_variance_limits E p v1 v0 vt τ h).1,
    (MomentCompletion.arm_variance_limits E p v1 v0 vt τ h).2,
    MomentCompletion.estimate_limit E p v1 v0 vt τ h⟩

/-- T5(a)–(c) and their probability-limit consequences: all three unnumbered
variance expansions of Section 2, p. 347, under the full `Regularity` assumptions. -/
theorem fisher_ols_asymptotics (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) :
    LittleOInvSize E (fun k z => fisherVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1 + (averageEffect (E k))^2/(E k).size)) ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1)) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*
      (fisherVariance (E k) z-olsVariance (E k) z)-(averageEffect (E k))^2) 0 ∧
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z)
      (olsLimit p v1 v0+tauInf^2) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) (olsLimit p v1 v0) := by
  exact fisher_ols_asymptotics_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h

/-- T6(a), p. 347: local average effects tau_N→0 give o_p(N^{-1})
Fisher–OLS difference, and ratio convergence when the variance limit is positive. -/
theorem local_alternative_equivalence (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf)
    (hl : Tendsto (fun k => averageEffect (E k)) atTop (nhds 0)) :
    LittleOInvSize E (fun k z => fisherVariance (E k) z-olsVariance (E k) z) ∧
    (0 < olsLimit p v1 v0 →
      InProbability E (fun k z => fisherVariance (E k) z/olsVariance (E k) z) 1) := by
  exact local_alternative_equivalence_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h hl

/-- T6(b), Section 2 p. 347: under constant effects the pooled variance
estimates the actual randomization variance to first order; the Fisher form
exceeds it by tau_N²/N to first order. Includes Fisher's null. -/
theorem constant_effect_asymptotics (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) (hc : ∀ k, ConstantEffects (E k)) :
    LittleOInvSize E (fun k z => olsVariance (E k) z-
      randomizationVariance (E k) (estimate (E k))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*
      (fisherVariance (E k) z-randomizationVariance (E k) (estimate (E k))) -
      (averageEffect (E k))^2) 0 := by
  exact constant_effect_asymptotics_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h hc

/-- T7(a)–(c), pp. 346–347: Neyman's consistency, the OLS–Neyman expansion,
their two scaled probability limits, and the necessary unequal-variance and
unbalanced-allocation conditions for those limits to differ. -/
theorem wald_comparison_asymptotics (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) :
    LittleOInvSize E (fun k z => neymanVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n1 +
       populationVariance (E k) (E k).Y0/(E k).n0)) ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z-neymanVariance (E k) z -
      ((populationVariance (E k) (E k).Y1/(E k).n0 +
        populationVariance (E k) (E k).Y0/(E k).n1) -
       (populationVariance (E k) (E k).Y1/(E k).n1 +
        populationVariance (E k) (E k).Y0/(E k).n0))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) (olsLimit p v1 v0) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0) ∧
    olsLimit p v1 v0-neymanLimit p v1 v0 = ((v1-v0)*(2*p-1))/(p*(1-p)) ∧
    (olsLimit p v1 v0 ≠ neymanLimit p v1 v0 → v1 ≠ v0 ∧ p ≠ 1/2) := by
  exact wald_comparison_asymptotics_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h

/-- T7(d), bracketed sentence p. 347: with tau_N→0, the same OLS–Neyman
expansion and limit statements hold with Fisher's form replacing OLS's. -/
theorem fisher_neyman_local_comparison (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf)
    (hl : Tendsto (fun k => averageEffect (E k)) atTop (nhds 0)) :
    LittleOInvSize E (fun k z => fisherVariance (E k) z-neymanVariance (E k) z -
      ((populationVariance (E k) (E k).Y1/(E k).n0 +
        populationVariance (E k) (E k).Y0/(E k).n1) -
       (populationVariance (E k) (E k).Y1/(E k).n1 +
        populationVariance (E k) (E k).Y0/(E k).n0))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z) (olsLimit p v1 v0) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0) := by
  exact fisher_neyman_local_comparison_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h hl

/-- T8(a), pp. 347–348: the actual scaled randomization variance tends to
Neyman's limit minus the limiting effect variance, hence is bounded by
Neyman's variance-estimator limit. -/
theorem neyman_asymptotic_bound (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) :
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0-vt)) ∧
    neymanLimit p v1 v0-vt ≤ neymanLimit p v1 v0 ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0) := by
  exact neyman_asymptotic_bound_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h

/-- T8(b), pp. 347–348: constant effects force S1²=S0² and S_tau²=0
at every population size; both variance estimates have the same first-order
limit as the actual randomization variance. -/
theorem constant_effect_limit_agreement (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) (hc : ∀ k, ConstantEffects (E k)) :
    (∀ k, populationVariance (E k) (E k).Y1 = populationVariance (E k) (E k).Y0 ∧
      populationVariance (E k) (unitEffects (E k)) = 0) ∧
    v1=v0 ∧ vt=0 ∧
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0)) ∧
    neymanLimit p v1 v0 = olsLimit p v1 v0 ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z-neymanVariance (E k) z) := by
  exact constant_effect_limit_agreement_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt tauInf h hc

/-- T8(c), p. 348: existence of regular heterogeneous Neyman-null populations
whose limiting actual variance (81/4) exceeds the OLS probability limit (10).
The conclusion concerns variances and does not assert a normal-approximation
rejection rate. -/
theorem anticonservative_limit_exists :
    Regularity heterogeneousWitness (1/5) 4 1 1 0 ∧
    (∀ k, averageEffect (heterogeneousWitness k) = 0) ∧
    Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)*
      randomizationVariance (heterogeneousWitness k) (estimate (heterogeneousWitness k)))
        atTop (nhds (81/4)) ∧
    InProbability heterogeneousWitness (fun k z =>
      ((heterogeneousWitness k).size : ℝ)*olsVariance (heterogeneousWitness k) z) 10 ∧
    olsLimit (1/5) 4 1 = 10 ∧ neymanLimit (1/5) 4 1 = 85/4 ∧ (10 : ℝ) < 81/4 := by
  exact anticonservative_limit_exists_completed

end
end AronowAudit.P053

