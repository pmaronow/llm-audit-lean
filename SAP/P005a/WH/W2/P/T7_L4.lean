import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P005a.WH.W2.P.T7_L4

open Finset Filter
open SAP.P005a
open SAP.P005a.WH.W2

lemma design_card_pos (n : ℕ) (hn : 6 ≤ n) :
    0 < (design n (n/2)).card := by
  rw [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.choose_pos (by omega)

lemma tail_lower_bound_diverges :
    Tendsto (fun j : ℕ => ((2*j : ℕ)-6 : ℝ) * Real.sqrt (2*j : ℕ)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  filter_upwards [Filter.eventually_ge_atTop (max 6 N)] with j hj
  have hj6 : 6 ≤ j := le_trans (le_max_left 6 N) hj
  have hjN : N ≤ j := le_trans (le_max_right 6 N) hj
  have hfac : (j : ℝ) ≤ 2*(j : ℝ)-6 := by
    have hjR : (6 : ℝ) ≤ j := by exact_mod_cast hj6
    linarith
  have hfac0 : 0 ≤ 2*(j : ℝ)-6 := by
    have hjR : (6 : ℝ) ≤ j := by exact_mod_cast hj6
    linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2*j : ℕ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ 2*j by omega)
  have hprod : (j : ℝ) ≤ (2*(j : ℝ)-6) * Real.sqrt (2*j : ℕ) := by
    calc
      (j : ℝ) ≤ 2*(j : ℝ)-6 := hfac
      _ = (2*(j : ℝ)-6) * 1 := by ring
      _ ≤ (2*(j : ℝ)-6) * Real.sqrt (2*j : ℕ) :=
        mul_le_mul_of_nonneg_left hsqrt hfac0
  have hcast : b < (j : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hjN)
  have hshape : ((2*j : ℕ)-6 : ℝ) * Real.sqrt (2*j : ℕ) =
      (2*(j : ℝ)-6) * Real.sqrt (2*j : ℕ) := by norm_num
  rw [hshape]
  exact le_of_lt (lt_of_lt_of_le hcast hprod)

end SAP.P005a.WH.W2.P.T7_L4

open Finset Filter SAP.P005a SAP.P005a.WH.W2

theorem SAP.P005a.WH.W2.T7_L4_proof : SAP.P005a.WH.W2.T7_L4 := by
  classical
  have hrem : ∀ n : ℕ, 6 ≤ n → Even n →
      ∀ S ∈ design n (n/2), (n : ℝ)-6 ≤ |spikeR n S| := by
    have hbase := AronowAudit.P005.Wave1.univariate_endpoint_counterexample_proof
    intro n hn he S hS
    have h := hbase.2.2.2.2.2.2.1 n hn he S hS
    rw [SAP.P005a.Bridge.spikePopulation_eq n] at h
    change (n : ℝ)-6 ≤
      |AronowAudit.P005.interactedATE
          (SAP.P005a.Bridge.toPopulation (spikePopulation n)) S -
        AronowAudit.P005.ate (SAP.P005a.Bridge.toPopulation (spikePopulation n)) -
        AronowAudit.P005.armLeading
          (SAP.P005a.Bridge.toPopulation (spikePopulation n)) S|
    exact h
  have hrate : ∀ n : ℕ, 6 ≤ n → 0 < spikeRate n ∧ spikeRate n ≤ 1/Real.sqrt n := by
    intro n hn
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hgram : AronowAudit.P005.gram
        (SAP.P005a.Bridge.toPopulation (spikePopulation n)) = 1 := by
      rw [← SAP.P005a.Bridge.spikePopulation_eq n]
      exact (AronowAudit.P005.Wave1.t7_standardized n (by omega)).2
    have hkOld := AronowAudit.P005.kappa_bounds
      (SAP.P005a.Bridge.toPopulation (spikePopulation n)) hn0 hgram
    have hk : (1 : ℝ)/n ≤ kappa (spikePopulation n) ∧
        kappa (spikePopulation n) ≤ 1 := by
      simpa only [Nat.cast_one, SAP.P005a.Bridge.kappa_eq] using hkOld
    have hkpos : 0 < kappa (spikePopulation n) :=
      lt_of_lt_of_le (div_pos one_pos hnR) hk.1
    have hrpos : 0 < spikeRate n := by
      exact Real.sqrt_pos.2 (div_pos hkpos hnR)
    have hkdiv : kappa (spikePopulation n)/n ≤ (1 : ℝ)/n :=
      (div_le_div_iff₀ hnR hnR).2
        (mul_le_mul_of_nonneg_right hk.2 hnR.le)
    have hsqrtbound : Real.sqrt (kappa (spikePopulation n)/n) ≤ 1/Real.sqrt n := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hsquare : (1/Real.sqrt n)^2 = (1 : ℝ)/n := by
          rw [div_pow, Real.sq_sqrt hnR.le]
          norm_num
        rw [hsquare]
        exact hkdiv
    exact ⟨hrpos, hsqrtbound⟩
  have hratio : ∀ n : ℕ, 6 ≤ n → Even n →
      ∀ S ∈ design n (n/2),
        ((n : ℝ)-6)*Real.sqrt n ≤ |spikeR n S| / spikeRate n := by
    intro n hn he S hS
    have hr := (hrate n hn).2
    have hrpos := (hrate n hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
    have hinv : Real.sqrt n ≤ 1/spikeRate n := by
      apply (le_div_iff₀ hrpos).2
      calc
        Real.sqrt n * spikeRate n ≤ Real.sqrt n * (1/Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg n)
        _ = 1 := by field_simp [ne_of_gt hsqrtpos]
    have hnonneg : 0 ≤ (n : ℝ)-6 := by
      have hnR6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hraw := hrem n hn he S hS
    calc
      ((n : ℝ)-6)*Real.sqrt n ≤ ((n : ℝ)-6)*(1/spikeRate n) :=
        mul_le_mul_of_nonneg_left hinv hnonneg
      _ = ((n : ℝ)-6)/spikeRate n := by ring
      _ ≤ |spikeR n S|/spikeRate n := div_le_div_of_nonneg_right hraw hrpos.le
  have hdiv : Filter.Tendsto
      (fun j : ℕ => ((2*j : ℕ)-6 : ℝ) * Real.sqrt (2*j : ℕ)) atTop atTop :=
    SAP.P005a.WH.W2.P.T7_L4.tail_lower_bound_diverges
  refine ⟨hrate, hratio, hdiv, ?_⟩
  intro M
  have hev := (Filter.tendsto_atTop.1 hdiv) (M+1)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  let N : ℕ := max 6 (2*J)
  refine ⟨N, le_max_left _ _, ?_⟩
  intro n hn he
  rcases he with ⟨j, hj⟩
  have heven : Even n := ⟨j, hj⟩
  have hjJ : J ≤ j := by dsimp [N] at hn; omega
  have hthreshold : M < ((n : ℝ)-6)*Real.sqrt n := by
    have h1 : M+1 ≤ ((2*j : ℕ)-6 : ℝ) * Real.sqrt (2*j : ℕ) := hJ j hjJ
    have hstrict : M < ((2*j : ℕ)-6 : ℝ) * Real.sqrt (2*j : ℕ) := by linarith
    rw [hj]
    simpa only [two_mul] using hstrict
  have hall : ∀ S ∈ design n (n/2),
      |spikeR n S| > M*spikeRate n := by
    intro S hS
    have hr := hratio n (by omega) heven S hS
    have hstrict : M < |spikeR n S|/spikeRate n := lt_of_lt_of_le hthreshold hr
    exact (lt_div_iff₀ (hrate n (by omega)).1).mp hstrict
  unfold probability
  have hfilter : (design n (n/2)).filter (fun S => |spikeR n S| > M*spikeRate n) =
      design n (n/2) := Finset.filter_eq_self.2 hall
  rw [hfilter]
  have hcard : ((design n (n/2)).card : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (SAP.P005a.WH.W2.P.T7_L4.design_card_pos n (by omega)))
  exact div_self hcard
