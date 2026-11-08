import SAP.P005b.Defs
import SAP.P005b.Bridge
import AronowAudit.P005.P005_ConfidenceCompletion
import AronowAudit.P005.Wave1.Gap.FidP005
import AronowAudit.P005.Wave1.Gap.GP005B2
import AronowAudit.P005.Wave1.Gap.GP005B3b
import AronowAudit.P005.Wave1.ExactDecomposition
import AronowAudit.P005.Wave1.InteractedExpansion
import AronowAudit.P005.Wave1.DebiasedLinearTailC
import SAP.P005b.WH.W1.Proofs.T17
import SAP.P005b.WH.W1.Proofs.T21
import SAP.P005b.WH.W1.Proofs.T26
import SAP.P005b.WH.W1.Proofs.T27

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix
open Finset Filter
open SAP.P005b SAP.P005b.Bridge

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

theorem SAP.P005b.T15 : SAP.P005b.T15Statement := by
  intro t c ht hc
  have h := AronowAudit.P005.collected_covariance_coefficients t c ht hc 0 0
  have hmid :
      (((t+c : ℕ) : ℝ) - (t : ℝ)*(t+c : ℕ)) /
          (((t+c : ℕ)-2 : ℝ)*((t : ℝ)-1)*(t+c : ℕ)) =
        -1 / ((t+c : ℕ)-2 : ℝ) := by
    have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have ht1 : (t : ℝ)-1 ≠ 0 := by linarith
    have hn0 : ((t+c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show t+c ≠ 0 by omega)
    field_simp [ht1, hn0]; ring
  refine ⟨h.1, h.2.1.trans hmid.symm, hmid, ?_⟩
  intro d P S _
  exact (AronowAudit.P005.collected_covariance_coefficients t c ht hc
    (sampleCov S (leverage P) P.yT) (sampleCov (control S) (leverage P) P.yC)).2.2

theorem SAP.P005b.T16 : SAP.P005b.T16Statement := by
  intro n m hn hm hmn a b c ha hb hc
  rcases AronowAudit.P005.Wave1.corrected_third_moment_calculation_proof
      hn hm hmn a b c ha hb hc with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have h1s : ∀ i j : Fin n, i ≠ j → expectation m (fun S => indicator S i*indicator S j) =
      (m : ℝ)*(m-1)/((n : ℝ)*(n-1)) := h1
  have h3s : expectation m (fun S => repeatedPair S a b c) =
      ∑ i, ∑ j ∈ univ.erase i, expectation m (fun S => indicator S i*indicator S j)*a i*b i*c j := h3
  have hp : expectation m (fun S => repeatedPair S a b c) =
      ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
        (∑ i, ∑ j ∈ univ.erase i, a i*b i*c j) := by
    rw [h3s]
    simp only [Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [h1s i j (Finset.mem_erase.mp hj).1.symm]
  have hs : (∑ i, ∑ j ∈ univ.erase i, a i*b i*c j) =
      (∑ i, ∑ j, a i*b i*c j) - ∑ i, a i*b i*c i := by
    rw [AronowAudit.P005.Wave1.t13_pair_sum, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have he : (1/(n : ℝ))*NTTT n m =
      ((n : ℝ)-m)*(n-2*m : ℝ)/((n : ℝ)*(m : ℝ)^2*(n-1)*(n-2)) := by
    simp only [NTTT, div_eq_mul_inv, mul_inv_rev]
    ring
  have hmixed : NTTC n m = -((m : ℝ)/((n : ℝ)-m))*NTTT n m := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    dsimp [NTTT, NTTC]
    field_simp [ne_of_gt hmR, show (n : ℝ)-1 ≠ 0 by linarith,
      show (n : ℝ)-2 ≠ 0 by linarith, show (n : ℝ)-m ≠ 0 by linarith]
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,
    AronowAudit.P005.third_moment_coefficient n m hn hm,hp,congrArg _ hs,he,?_,hmixed⟩
  intro S hS
  exact AronowAudit.P005.Wave1.t13_complement_mean hmn c hc S hS

theorem SAP.P005b.T17 : SAP.P005b.T17WholeStatement := SAP.P005b.WH.W1.T17_whole

theorem SAP.P005b.T18 : SAP.P005b.T18Statement := by
  constructor
  · intro n d m P hn hm hmn S hS eT eC he
    exact AronowAudit.P005.corrected_residual_brackets (toProject P) hn hm hmn S hS eT eC he
  · intro n d m P hn hm hmn hP S hS
    exact AronowAudit.P005.corrected_residual_term_identification (toProject P) hn hm hmn hP S hS

theorem SAP.P005b.T19 : SAP.P005b.T19Statement := by
  intro h
  apply AronowAudit.P005.ConfidenceFollowup02.printed_covariance_lemma_refuted
  intro n m hn hm hmn t a b
  cases t with
  | treated => exact h hn hm hmn .treated a b
  | control => exact h hn hm hmn .control a b

theorem SAP.P005b.T20 : SAP.P005b.T20Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n d m P hn hm hmn hP hinv
    exact AronowAudit.P005.Wave1.interacted_exact_decomposition_completion
      (toProject P) hn hm hmn hP hinv
  · intro h
    apply AronowAudit.P005.ConfidenceFollowup02.printed_interacted_third_bias_refuted
    intro n d m P hn hm hmn hP hinv
    exact h (fromProject P) hn hm hmn hP hinv
  · intro h
    apply AronowAudit.P005.Wave1.printed_interacted_expansion_refuted
    intro d m P hP hinv hκ
    exact h d m (fun n => fromProject (P n)) hP hinv hκ

theorem SAP.P005b.T21 : SAP.P005b.T21WholeStatement := SAP.P005b.WH.W1.T21_whole

theorem SAP.P005b.T22 : SAP.P005b.T22Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n d m P hn hm hmn hP hinv
    rcases AronowAudit.P005.Wave1.interacted_exact_unbiasedness_proof
      (toProject P) hn hm hmn hP hinv with ⟨h1,h2,h3,h4⟩
    refine ⟨h1,h2,h3,h4,?_⟩
    intro S _
    exact AronowAudit.P005.interacted_debiased_cancellation (toProject P) m S
  · intro n d m P hn hm hmn hx
    exact AronowAudit.P005.Wave1.control_arm_unbiased_any_size (toProject P)
      hn (by omega) (le_of_lt hmn) hx P.yT
  · intro n d m P hn hm hmn hc hx
    change AronowAudit.P005.expectation m (fun S =>
      AronowAudit.P005.armDebiased (toProject P) (AronowAudit.P005.control S) P.yC) = _
    rw [AronowAudit.P005.Wave1.control_arm_transport (le_of_lt hmn)
      (fun U => AronowAudit.P005.armDebiased (toProject P) U P.yC)]
    exact AronowAudit.P005.Wave1.control_arm_unbiased_any_size (toProject P)
      hn (Nat.sub_pos_of_lt hmn) (Nat.sub_le n m) hx P.yC

theorem SAP.P005b.T23 : SAP.P005b.T23Statement := by
  intro n d m P hn hm hmn hP hinv
  exact AronowAudit.P005.Wave1.noninteracted_exact_decomposition_proof
    (toProject P) hn hm hmn hP hinv

theorem SAP.P005b.T24 : SAP.P005b.T24Statement := by
  intro n d m P hn hm hmn hP hinv
  exact AronowAudit.P005.Wave1.interacted_exact_decomposition_proof
    (toProject P) hn hm hmn hP hinv

theorem SAP.P005b.T25 : SAP.P005b.T25Statement := by
  intro d m P h hinv hd
  exact AronowAudit.P005.Wave1.noninteracted_stochastic_expansion_proof
    d m (fun n => toProject (P n)) h hinv hd

theorem SAP.P005b.T26 : SAP.P005b.T26WholeStatement := SAP.P005b.WH.W1.T26_whole

theorem SAP.P005b.T27 : SAP.P005b.T27WholeStatement := SAP.P005b.WH.W1.T27_whole
