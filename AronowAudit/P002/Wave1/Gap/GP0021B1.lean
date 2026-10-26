import AronowAudit.P002.P002_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.Order.Field

/-! Finite-sampling second moments, normalized moment bounds, balance, and
randomization moments. -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments
  (E_sampleMean Var_sampleMean sampleMean)

/-! Assignment-space bridge and second moment. -/

private theorem C17_expectation_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ}
    (hfg : ∀ S ∈ assignments P, f S = g S) :
    expectation P f = expectation P g := by
  unfold expectation
  rw [Finset.sum_congr rfl hfg]

private theorem C17_expectation_bridge {n} (P : Population n)
    (hn : P.n1 ≤ Fintype.card (Fin n)) (f : Finset (Fin n) → ℝ) :
    expectation P f = (completeRandomization P.n1 hn).E (fun S => f S.val) := by
  have hsum : (∑ S ∈ assignments P, f S) =
      ∑ S : {S : Finset (Fin n) // S.card = P.n1}, f S.val := by
    refine Finset.sum_bij
      (fun S hS => (⟨S, (Finset.mem_powersetCard.mp hS).2⟩ :
        {S : Finset (Fin n) // S.card = P.n1})) ?_ ?_ ?_ ?_
    · intro S hS
      exact Finset.mem_univ _
    · intro S hS T hT heq
      exact congrArg Subtype.val heq
    · intro S hS
      have hmem : S.val ∈ assignments P := by
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩
      exact ⟨S.val, hmem, Subtype.ext rfl⟩
    · intro S hS
      rfl
  have hcard : (assignments P).card =
      Fintype.card {S : Finset (Fin n) // S.card = P.n1} := by
    rw [completeRandomization_card]
    simp only [assignments, Finset.card_powersetCard, Finset.card_univ]
  unfold expectation FiniteDesign.E
  simp only [completeRandomization]
  rw [hcard, hsum, ← Finset.mul_sum]
  ring

private theorem C17_sampleMean_bridge {n} (t : ℕ) (q : Fin n → ℝ)
    (S : {S : Finset (Fin n) // S.card = t}) :
    sampleMean t q S = groupMean S.val q := by
  unfold sampleMean groupMean
  rw [S.property]
  congr 1
  exact Finset.sum_ite_mem_eq S.val q

private theorem C17_sample_mean_unbiased {n} (P : Population n)
    (h : ValidDesign P) (q : Fin n → ℝ) :
    expectation P (fun S => groupMean S q) = mean q := by
  have hn : P.n1 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2
  rw [C17_expectation_bridge P hn]
  have hfun : (fun S : {S : Finset (Fin n) // S.card = P.n1} =>
      groupMean S.val q) = sampleMean P.n1 q := by
    funext S
    exact (C17_sampleMean_bridge P.n1 q S).symm
  rw [hfun, E_sampleMean P.n1 hn h.2.1]
  simp only [Causalean.Experimentation.FinitePopulationMoments.popMean,
    mean, Fintype.card_fin]

private theorem C17_sample_mean_second_moment {n} (P : Population n)
    (h : ValidDesign P) (q : Fin n → ℝ) :
    expectation P (fun S => (groupMean S q - mean q)^2) =
      controlSize P / ((P.n1 : ℝ) * (n : ℝ) * ((n : ℝ)-1)) *
      ∑ i, (q i - mean q)^2 := by
  have hn : P.n1 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2
  have hn2 : 2 ≤ Fintype.card (Fin n) := by simpa using h.1
  have hN : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := h.1; omega)
  have ht : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h.2.1.ne'
  have hN1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h.1
    linarith
  have hmean : (completeRandomization P.n1 hn).E (sampleMean P.n1 q) = mean q := by
    rw [E_sampleMean P.n1 hn h.2.1]
    simp only [Causalean.Experimentation.FinitePopulationMoments.popMean,
      mean, Fintype.card_fin]
  have hvar := Var_sampleMean P.n1 hn h.2.1 hn2 q
  have hbridge : expectation P (fun S => (groupMean S q - mean q)^2) =
      (completeRandomization P.n1 hn).Var (sampleMean P.n1 q) := by
    rw [C17_expectation_bridge P hn, FiniteDesign.Var, hmean]
    apply FiniteDesign.E_congr
    intro S
    rw [C17_sampleMean_bridge]
  rw [hbridge, hvar]
  have hpm : Causalean.Experimentation.FinitePopulationMoments.popMean q = mean q := by
    simp only [Causalean.Experimentation.FinitePopulationMoments.popMean, mean,
      Fintype.card_fin]
  have hpv : Causalean.Experimentation.FinitePopulationMoments.popVar q =
      (∑ i, (q i - mean q)^2) / ((n : ℝ) - 1) := by
    simp only [Causalean.Experimentation.FinitePopulationMoments.popVar, hpm,
      Fintype.card_fin]
  rw [hpv]
  simp only [Fintype.card_fin, controlSize]
  field_simp

private theorem C17_corrected_bracket {n} (P : Population n) (β : ℝ)
    (S : Finset (Fin n)) :
    groupMean S (w P true β) - mean (fun i => P.y i (P.d i true)) +
      β*mean (fun i => binary (P.d i true)) =
        groupMean S (w P true β) - mean (w P true β) := by
  have hm : mean (w P true β) = mean (fun i => P.y i (P.d i true)) -
      β * mean (fun i => binary (P.d i true)) := mean_sub_smul _ _ β
  rw [hm]
  ring

theorem corrected_C17_proof {n} (P : Population n) (hP : ValidDesign P) (β : ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    groupMean S (fun i => (observedW P β S i-armMean (observedW P β S) S true)^2) =
      groupMean S (fun i => v P true β i ^ 2) -
        (groupMean S (w P true β) - mean (fun i => P.y i (P.d i true)) +
          β*mean (fun i => binary (P.d i true)))^2 ∧
    expectation P (fun T => (groupMean T (w P true β) - mean (fun i => P.y i (P.d i true)) +
        β*mean (fun i => binary (P.d i true)))^2) =
      controlSize P/((P.n1 : ℝ)*(n : ℝ)*((n : ℝ)-1))*∑ i, v P true β i^2 := by
  refine ⟨corrected_C17_identity P hP β S hS, ?_⟩
  simp_rw [C17_corrected_bracket]
  simpa only [v] using C17_sample_mean_second_moment P hP (w P true β)

/-! Normalized moment, balance, and deterministic limit. -/

private theorem C17rate_balance (r p : ℝ) (hr : 0 < r ∧ r ≤ 1/2)
    (hlo : r ≤ p) (hhi : p ≤ 1-r) :
    0 < r^2*(1-r)^2 ∧ r^2*(1-r)^2 ≤ p^2*(1-p)^2 := by
  have hr1 : 0 < 1-r := by linarith [hr.2]
  have hp : 0 < p := lt_of_lt_of_le hr.1 hlo
  have hp1 : 0 < 1-p := by linarith [hr.1]
  have hprod : r*(1-r) ≤ p*(1-p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (by linarith : 0 ≤ 1-r-p)]
  constructor
  · exact mul_pos (pow_pos hr.1 2) (pow_pos hr1 2)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hprod)
      (show 0 ≤ p*(1-p)+r*(1-r) from
        add_nonneg (mul_pos hp hp1).le (mul_pos hr.1 hr1).le)]

private theorem C17rate_normalized {n} (P : Population n) (h : ValidDesign P)
    (β : ℝ) (hS : 0 < S2 P β true) :
    expectation P (fun S =>
      (groupMean S (w P true β) - mean (fun i => P.y i (P.d i true)) +
        β*mean (fun i => binary (P.d i true)))^2 / S2 P β true) =
      (controlSize P/((P.n1 : ℝ)*(n : ℝ))) /
        ((fraction P)^2*(1-fraction P)^2) := by
  have hN1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h.1
    linarith
  have hN : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := h.1; omega)
  have ht : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h.2.1.ne'
  have hmul : (fraction P)^2*(1-fraction P)^2 * popVar (w P true β) ≠ 0 := hS.ne'
  have hD : (fraction P)^2*(1-fraction P)^2 ≠ 0 := (mul_ne_zero_iff.mp hmul).1
  have hV : popVar (w P true β) ≠ 0 := (mul_ne_zero_iff.mp hmul).2
  rw [expectation_div]
  simp_rw [C17_corrected_bracket]
  rw [C17_sample_mean_second_moment P h]
  have he : controlSize P / ((P.n1 : ℝ)*(n : ℝ)*((n : ℝ)-1)) *
      (∑ i, (w P true β i - mean (w P true β))^2) =
      (controlSize P/((P.n1 : ℝ)*(n : ℝ))) * popVar (w P true β) := by
    unfold popVar
    field_simp [hN, ht, hN1] <;> ring
  rw [he]
  unfold S2
  exact mul_div_mul_right _ _ hV

theorem corrected_C17_rate_proof (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n)) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ n, Theta (P n) δ r A)
    (hS : ∀ n, 0 < S2 (P n) (late (P n)) true) :
    let f : ℕ → ℝ := fun n => expectation (P n) (fun S =>
      (groupMean S (w (P n) true (late (P n))) -
        mean (fun i => (P n).y i ((P n).d i true)) +
        late (P n)*mean (fun i => binary ((P n).d i true)))^2 / S2 (P n) (late (P n)) true)
    Asymptotics.IsBigO atTop f (fun n => controlSize (P n)/((P n).n1*(sizes n : ℝ))) ∧
    Tendsto f atTop (nhds 0) := by
  dsimp only
  let f : ℕ → ℝ := fun j => expectation (P j) (fun S =>
    (groupMean S (w (P j) true (late (P j))) -
      mean (fun i => (P j).y i ((P j).d i true)) +
      late (P j)*mean (fun i => binary ((P j).d i true)))^2 /
        S2 (P j) (late (P j)) true)
  let g : ℕ → ℝ := fun j => controlSize (P j)/((P j).n1*(sizes j : ℝ))
  let C : ℝ := 1/(r^2*(1-r)^2)
  have hR : 0 < r^2*(1-r)^2 := by
    have : 0 < 1-r := by linarith [hr.2]
    exact mul_pos (pow_pos hr.1 2) (pow_pos this 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hexact (j : ℕ) : f j = g j /
      ((fraction (P j))^2*(1-fraction (P j))^2) :=
    C17rate_normalized (P j) (hP j).1 _ (hS j)
  have hdata (j : ℕ) : 0 ≤ g j ∧
      r^2*(1-r)^2 ≤ (fraction (P j))^2*(1-fraction (P j))^2 ∧
      g j ≤ 1/(r*(sizes j : ℝ)) := by
    have hd := (hP j).1
    have hN : (0 : ℝ) < sizes j := by
      exact_mod_cast (show 0 < sizes j by have := hd.1; omega)
    have ht : (0 : ℝ) < (P j).n1 := by exact_mod_cast hd.2.1
    have htn : ((P j).n1 : ℝ) < sizes j := by exact_mod_cast hd.2.2
    have hlo := (hP j).2.2.2.1
    have hhi := (hP j).2.2.2.2.1
    have hp : r ≤ fraction (P j) := (le_div_iff₀ hN).mpr hlo
    have hp' : fraction (P j) ≤ 1-r := (div_le_iff₀ hN).mpr hhi
    refine ⟨?_, (C17rate_balance r _ hr hp hp').2, ?_⟩
    · dsimp [g, controlSize]
      exact div_nonneg (sub_nonneg.mpr htn.le) (mul_pos ht hN).le
    · dsimp [g, controlSize]
      apply (div_le_div_iff₀ (mul_pos ht hN) (mul_pos hr.1 hN)).mpr
      have ha : r*((sizes j : ℝ)-(P j).n1) ≤ (P j).n1 := by
        nlinarith [mul_nonneg hr.1.le ht.le]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) hN.le]
  have hbound (j : ℕ) : 0 ≤ f j ∧ f j ≤ C*g j := by
    have hg := (hdata j).1
    have hD := lt_of_lt_of_le hR (hdata j).2.1
    rw [hexact]
    constructor
    · exact div_nonneg hg hD.le
    · have hinv := one_div_le_one_div_of_le hR (hdata j).2.1
      have := mul_le_mul_of_nonneg_left hinv hg
      dsimp [C]
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using this
  change Asymptotics.IsBigO atTop f g ∧ Tendsto f atTop (nhds 0)
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, Filter.Eventually.of_forall (fun j => ?_)⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound j).1,
      abs_of_nonneg (hdata j).1] using (hbound j).2
  · have hsize : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
    have hmajor : Tendsto (fun j => C/(r*(sizes j : ℝ))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (hsize.const_mul_atTop hr.1)
    apply squeeze_zero (fun j => (hbound j).1) (fun j => ?_) hmajor
    calc f j ≤ C*g j := (hbound j).2
         _ ≤ C*(1/(r*(sizes j : ℝ))) :=
           mul_le_mul_of_nonneg_left (hdata j).2.2 hC
         _ = C/(r*(sizes j : ℝ)) := by ring

/-! Sample-mean second moment. -/

theorem sample_mean_variance_proof {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) :
    expectation P (fun S => (groupMean S q - mean q)^2) =
      controlSize P / ((P.n1 : ℝ) * (n : ℝ) * ((n : ℝ)-1)) *
      ∑ i, (q i - mean q)^2 := by
  exact C17_sample_mean_second_moment P h q

/-! Randomization moments and (C.31). -/

private theorem C31_rawTau_on_support {n} (P : Population n)
    (h : ValidDesign P) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P q S = fraction P * (groupMean S q - mean q) := by
  have hcard : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
  have ht : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h.2.1.ne'
  have hN : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := h.1; omega)
  rw [rawTau_sum]
  simp only [fraction, groupMean, mean, hcard]
  field_simp [ht, hN] <;> ring

private theorem C31_raw_moments {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) :
    expectation P (rawTau P q) = 0 ∧
    designVariance P (rawTau P q) = (fraction P)^2 * (1-fraction P)^2 *
      popVar q * (1/(P.n1 : ℝ) + 1/controlSize P) := by
  have hN : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := h.1; omega)
  have ht : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h.2.1.ne'
  have hc : controlSize P ≠ 0 := by
    have : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    dsimp [controlSize]
    linarith
  have hN1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h.1
    linarith
  have hmean : expectation P (rawTau P q) = 0 := by
    calc expectation P (rawTau P q) = expectation P
          (fun S => fraction P * (groupMean S q - mean q)) :=
            C17_expectation_congr P (C31_rawTau_on_support P h q)
         _ = 0 := by
           rw [expectation_mul, expectation_sub, C17_sample_mean_unbiased P h q,
             expectation_const P h]
           ring
  refine ⟨hmean, ?_⟩
  unfold designVariance
  rw [hmean]
  have hsquare : expectation P (fun S => (rawTau P q S - 0)^2) =
      expectation P (fun S => (fraction P)^2*(groupMean S q - mean q)^2) := by
    apply C17_expectation_congr
    intro S hS
    rw [C31_rawTau_on_support P h q S hS]
    ring
  rw [hsquare, expectation_mul, sample_mean_variance_proof P h q]
  unfold popVar
  have hc' : (n : ℝ)-(P.n1 : ℝ) ≠ 0 := hc
  simp only [fraction, controlSize]
  field_simp [hN, ht, hc', hN1] <;> ring

private theorem C31_group_decomposition {n} (S : Finset (Fin n))
    (q : Fin n → ℝ) (μ : ℝ) (hS : S.Nonempty) :
    (∑ i ∈ S, (q i-μ)^2) =
      (∑ i ∈ S, (q i-groupMean S q)^2) +
        (S.card : ℝ)*(groupMean S q-μ)^2 := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have he := square_centering S q μ hS
  change (∑ i ∈ S, (q i-groupMean S q)^2)/(S.card : ℝ) =
    (∑ i ∈ S, (q i-μ)^2)/(S.card : ℝ) - (groupMean S q-μ)^2 at he
  field_simp [hcard] at he
  nlinarith only [he]

private theorem C31_between_bound {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    (P.n1 : ℝ)*controlSize P/(n : ℝ) *
      (armMean q S true-armMean q S false)^2 ≤
        ∑ i, (q i-mean q)^2 := by
  let N : ℝ := n
  let t : ℝ := P.n1
  let c : ℝ := controlSize P
  let a := groupMean S q
  let b := groupMean Sᶜ q
  let μ := mean q
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < n by have := h.1; omega)
  have ht : 0 < t := by dsimp [t]; exact_mod_cast h.2.1
  have htn : t < N := by dsimp [t, N]; exact_mod_cast h.2.2
  have hcdef : c = N-t := rfl
  have hc : 0 < c := by rw [hcdef]; linarith
  have hsc : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
  have hscR : (S.card : ℝ) = t := by dsimp [t]; exact_mod_cast hsc
  have hccR : (Sᶜ.card : ℝ) = c := by
    simp only [Finset.card_compl, Fintype.card_fin, hsc]
    dsimp [c, controlSize]
    rw [Nat.cast_sub (Nat.le_of_lt h.2.2)]
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hsc]; exact h.2.1)
  have hCne : Sᶜ.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < Sᶜ.card := by rw [hccR]; exact hc
    exact_mod_cast this
  have hta : t*a = ∑ i ∈ S, q i := by
    dsimp [a, groupMean]
    rw [hscR]
    field_simp [ht.ne']
  have hcb : c*b = ∑ i ∈ Sᶜ, q i := by
    dsimp [b, groupMean]
    rw [hccR]
    field_simp [hc.ne']
  have hNμ : N*μ = ∑ i, q i := by
    dsimp [N, μ, mean]
    field_simp [show (n : ℝ) ≠ 0 from hN.ne']
  have hlinear : t*a+c*b-N*μ = 0 := by
    rw [hta, hcb, hNμ, Finset.sum_add_sum_compl]
    ring
  have halgebra : t*(a-μ)^2+c*(b-μ)^2-t*c/N*(a-b)^2 =
      (t*a+c*b-N*μ)^2/N := by
    rw [hcdef]
    field_simp [hN.ne'] <;> ring
  have hweighted : t*(a-μ)^2+c*(b-μ)^2 = t*c/N*(a-b)^2 := by
    rw [hlinear] at halgebra
    simp only [zero_pow (by decide : 2 ≠ 0), zero_div] at halgebra
    linarith only [halgebra]
  have htreated := C31_group_decomposition S q μ hSne
  have hcontrol := C31_group_decomposition Sᶜ q μ hCne
  rw [hscR] at htreated
  rw [hccR] at hcontrol
  have hpart := Finset.sum_add_sum_compl S (fun i => (q i-μ)^2)
  have hnonneg1 : 0 ≤ ∑ i ∈ S, (q i-a)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnonneg0 : 0 ≤ ∑ i ∈ Sᶜ, (q i-b)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  change t*c/N*(a-b)^2 ≤ ∑ i, (q i-μ)^2
  change (∑ i ∈ S, (q i-μ)^2) = (∑ i ∈ S, (q i-a)^2)+t*(a-μ)^2 at htreated
  change (∑ i ∈ Sᶜ, (q i-μ)^2) = (∑ i ∈ Sᶜ, (q i-b)^2)+c*(b-μ)^2 at hcontrol
  linarith only [htreated, hcontrol, hpart, hweighted, hnonneg1, hnonneg0]

theorem corrected_C31_proof {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P)
    (r : ℝ) (hr : 0 < r ∧ r ≤ 1/2)
    (hlo : r*(n : ℝ) ≤ (P.n1 : ℝ)) (hhi : (P.n1 : ℝ) ≤ (1-r)*(n : ℝ)) :
    (fraction P)^2*(1-fraction P)^2/((n : ℝ)-1)*(armMean q S true-armMean q S false)^2 ≤
      designVariance P (rawTau P q) ∧
    r^2*(1-r)^2/(n : ℝ)*(armMean q S true-armMean q S false)^2 ≤
      designVariance P (rawTau P q) := by
  have hN : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by have := h.1; omega)
  have ht : (0 : ℝ) < P.n1 := by exact_mod_cast h.2.1
  have htn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
  have hc : 0 < controlSize P := by dsimp [controlSize]; linarith
  have hN1 : 0 < (n : ℝ)-1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h.1
    linarith
  let D : ℝ := (fraction P)^2*(1-fraction P)^2
  let d : ℝ := armMean q S true-armMean q S false
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfirst : D/((n : ℝ)-1)*d^2 ≤ designVariance P (rawTau P q) := by
    have hb := C31_between_bound P h q S hS
    have hfac : 0 ≤ D*(n : ℝ)/((P.n1 : ℝ)*controlSize P*((n : ℝ)-1)) := by
      positivity
    calc D/((n : ℝ)-1)*d^2 =
          (D*(n : ℝ)/((P.n1 : ℝ)*controlSize P*((n : ℝ)-1))) *
            ((P.n1 : ℝ)*controlSize P/(n : ℝ)*d^2) := by
              field_simp [hN.ne', ht.ne', hc.ne', hN1.ne'] <;> ring
         _ ≤ (D*(n : ℝ)/((P.n1 : ℝ)*controlSize P*((n : ℝ)-1))) *
               ∑ i, (q i-mean q)^2 := mul_le_mul_of_nonneg_left hb hfac
         _ = designVariance P (rawTau P q) := by
           rw [(C31_raw_moments P h q).2]
           change _ = D * popVar q * (1/(P.n1 : ℝ)+1/controlSize P)
           unfold popVar
           dsimp [controlSize]
           have hc' : (n : ℝ)-(P.n1 : ℝ) ≠ 0 := hc.ne'
           field_simp [hN.ne', ht.ne', hc', hN1.ne'] <;> ring
  refine ⟨hfirst, le_trans ?_ hfirst⟩
  have hbalance := C17rate_balance r (fraction P) hr
    ((le_div_iff₀ hN).mpr hlo) ((div_le_iff₀ hN).mpr hhi)
  have hcoeff : r^2*(1-r)^2/(n : ℝ) ≤ D/((n : ℝ)-1) := by
    calc r^2*(1-r)^2/(n : ℝ) ≤ D/(n : ℝ) :=
           div_le_div_of_nonneg_right hbalance.2 hN.le
         _ ≤ D/((n : ℝ)-1) :=
           div_le_div_of_nonneg_left hD hN1 (by linarith)
  exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg d)

/-! Randomization moments. -/

theorem randomization_moments_proof {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) :
    expectation P (rawTau P q) = 0 ∧
    designVariance P (rawTau P q) = (fraction P)^2 * (1-fraction P)^2 *
      popVar q * (1/(P.n1 : ℝ) + 1/controlSize P) := by
  exact C31_raw_moments P h q

end
end AronowAudit.P002.Wave1
