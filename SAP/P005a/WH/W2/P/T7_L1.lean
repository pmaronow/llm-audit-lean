import SAP.P005a.WH.W2.Leaves
import AronowAudit.P005.Wave1.InteractedExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T7_L1

noncomputable section
open Finset Set
open scoped BigOperators

lemma spikeQ_pos (n : ℕ) (hn : 6 ≤ n) : 0 < spikeQ n :=
  AronowAudit.P005.Wave1.InteractedExpansion.spikeQ_pos_of_S1
    AronowAudit.P005.Wave1.InteractedExpansion.n1_proof n (by omega)

lemma spike_leverage_eq (n : ℕ) (hn : 6 ≤ n) (i : Fin n) :
    leverage (spikePopulation n) i = spikeZ n i ^ 2 / spikeQ n := by
  have hq := spikeQ_pos n hn
  simp only [leverage, dot, Fin.sum_univ_one, spikePopulation]
  rw [← pow_two, div_pow, Real.sq_sqrt hq.le]

lemma spike_special_Z (n : ℕ) (hn : 6 ≤ n) :
    spikeZ n (⟨0, by omega⟩ : Fin n) = 1 - 1 / (n : ℝ) := by
  simp [spikeZ, spikeA]

lemma spike_ordinary_Z_abs (n : ℕ) (hn : 6 ≤ n) (i : Fin n)
    (hi : i.val ≠ 0) : |spikeZ n i| ≤ 1 - 1 / (n : ℝ) := by
  have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : (0 : ℝ) < (n : ℝ) := by linarith
  have hq := spikeQ_pos n hn
  have hv := abs_le.mp
    (AronowAudit.P005.Wave1.InteractedExpansion.spikeV_abs n (by omega) i)
  have hz : spikeZ n i = spikeV n i / (n : ℝ)^2 - 1 / (n : ℝ) := by
    simp [spikeZ, spikeA, hi]
  have hlow : -(1/(n : ℝ)^2) - 1/(n : ℝ) ≤ spikeZ n i := by
    rw [hz]
    have hden : 0 < (n : ℝ)^2 := by positivity
    have hdiv : (-1 : ℝ) / (n : ℝ)^2 ≤ spikeV n i / (n : ℝ)^2 :=
      div_le_div_of_nonneg_right hv.1 (le_of_lt hden)
    convert add_le_add_right hdiv (-(1/(n : ℝ))) using 1 <;> ring
  have hhigh : spikeZ n i ≤ 1/(n : ℝ)^2 - 1/(n : ℝ) := by
    rw [hz]
    have hden : 0 < (n : ℝ)^2 := by positivity
    have hdiv : spikeV n i / (n : ℝ)^2 ≤ (1 : ℝ) / (n : ℝ)^2 :=
      div_le_div_of_nonneg_right hv.2 (le_of_lt hden)
    convert add_le_add_right hdiv (-(1/(n : ℝ))) using 1 <;> ring
  have hrec : 0 < 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 / 6 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnp).2
      nlinarith
  have hsmall : 1/(n : ℝ) + 1/(n : ℝ)^2 ≤ 7/36 := by
    have hu0 : 0 ≤ 1/(n : ℝ) := le_of_lt hrec.1
    have hu1 : 0 ≤ 1/6 - 1/(n : ℝ) := sub_nonneg.mpr hrec.2
    have hu2 : 0 ≤ 1/6 + 1/(n : ℝ) := by positivity
    have hprod := mul_nonneg hu1 hu2
    have hsq : (1/(n : ℝ))^2 ≤ (1/6 : ℝ)^2 := by
      nlinarith
    have hpow : 1/(n : ℝ)^2 = (1/(n : ℝ))^2 := by ring
    rw [hpow]
    nlinarith [hrec.2, hsq]
  have htarget : 7/36 ≤ 1 - 1/(n : ℝ) := by nlinarith
  rw [abs_le]
  constructor
  · calc
      -(1 - 1 / (n : ℝ)) ≤ -(1/(n : ℝ)^2) - 1/(n : ℝ) := by
        have : 1 - 1/(n : ℝ) ≥ 1/(n : ℝ) + 1/(n : ℝ)^2 := by linarith [hsmall, htarget]
        linarith
      _ ≤ spikeZ n i := hlow
  · calc
      spikeZ n i ≤ 1/(n : ℝ)^2 - 1/(n : ℝ) := hhigh
      _ ≤ 1 - 1 / (n : ℝ) := by nlinarith [sq_nonneg (1/(n : ℝ))]

lemma spike_Z_sq_le_special (n : ℕ) (hn : 6 ≤ n) (i : Fin n) :
    spikeZ n i ^ 2 ≤ spikeZ n (⟨0, by omega⟩ : Fin n) ^ 2 := by
  by_cases hi : i.val = 0
  · have hiEq : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi
    rw [hiEq]
  · have habs := spike_ordinary_Z_abs n hn i hi
    rw [spike_special_Z n hn]
    have hpair : 0 ≤ ((1 - 1 / (n : ℝ)) - spikeZ n i) *
        ((1 - 1 / (n : ℝ)) + spikeZ n i) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr (abs_le.mp habs).2
      · linarith [(abs_le.mp habs).1]
    nlinarith

lemma spike_kappa_eq_special (n : ℕ) (hn : 6 ≤ n) :
    kappa (spikePopulation n) =
      leverage (spikePopulation n) (⟨0, by omega⟩ : Fin n) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbdd : BddAbove (Set.range
      (fun i : Fin n => leverage (spikePopulation n) i / (n : ℝ))) :=
    (Set.finite_range _).bddAbove
  have hupper : ∀ x ∈ Set.range
      (fun i : Fin n => leverage (spikePopulation n) i / (n : ℝ)),
      x ≤ leverage (spikePopulation n) (⟨0, by omega⟩ : Fin n) / (n : ℝ) := by
    rintro x ⟨i, rfl⟩
    apply div_le_div_of_nonneg_right _ (le_of_lt hnR)
    rw [spike_leverage_eq n hn, spike_leverage_eq n hn]
    exact div_le_div_of_nonneg_right (spike_Z_sq_le_special n hn i) (le_of_lt (spikeQ_pos n hn))
  have hmem : leverage (spikePopulation n) (⟨0, by omega⟩ : Fin n) / (n : ℝ) ∈
      Set.range (fun i : Fin n => leverage (spikePopulation n) i / (n : ℝ)) :=
    Set.mem_range_self _
  unfold kappa
  apply le_antisymm
  · exact csSup_le ⟨_, hmem⟩ hupper
  · exact le_csSup hbdd hmem

end
end SAP.P005a.WH.W2.P.T7_L1

open SAP.P005a.WH.W2.P.T7_L1
open SAP.P005a.WH.W2

/-- The exact finite maximum leverage identities for the spike population. -/
theorem SAP.P005a.WH.W2.T7_L1_proof : SAP.P005a.WH.W2.T7_L1 := by
  unfold SAP.P005a.WH.W2.T7_L1 SAP.P005a.spikeLeverageFacts
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by
    have h : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
    linarith
  have hq : 0 < spikeQ n := spikeQ_pos n hn
  have hz0 := spike_special_Z n hn
  have hlev0 : leverage (spikePopulation n) (⟨0, by omega⟩ : Fin n) =
      (1 - 1/(n : ℝ))^2 / spikeQ n := by
    rw [spike_leverage_eq n hn, hz0]
  have hk := spike_kappa_eq_special n hn
  have hqformula : spikeQ n =
      ((n : ℝ) - 1) / (n : ℝ)^2 *
        (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2)) :=
    (AronowAudit.P005.Wave1.InteractedExpansion.n1_proof n (by omega)).2.2.2.2
  have hk1 : kappa (spikePopulation n) = (1-1/(n : ℝ))^2 / (n * spikeQ n) := by
    rw [hk, hlev0]
    field_simp [ne_of_gt hnR, ne_of_gt hq]
  refine ⟨hk1, ?_, ?_⟩
  · rw [hk1, hqformula]
    field_simp [ne_of_gt hnR, hn1, hn2]
  · intro i j hj
    have hj0 : j = (⟨0, by omega⟩ : Fin n) := Fin.ext hj
    rw [hj0]
    rw [spike_leverage_eq n hn, spike_leverage_eq n hn]
    exact div_le_div_of_nonneg_right (spike_Z_sq_le_special n hn i)
      (le_of_lt hq)
