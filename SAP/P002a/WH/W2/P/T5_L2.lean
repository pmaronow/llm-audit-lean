import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace SAP.P002a.WH.W2.P.T5_L2

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

lemma centered_zero_of_small_moment
    (hL1 : SAP.P002a.WH.W2.T5_L1) {n : ℕ}
    (P : SAP.P002a.Population n) (δ r A : ℝ)
    (hP : SAP.P002a.Theta P δ r A) (hAnonneg : 0 ≤ A) (hn : 2 ≤ n)
    (hthreshold : A ^ 2 < ((n : ℝ) - 1) / (n : ℝ)) :
    ∀ a i, SAP.P002a.v P a (SAP.P002a.late P) i = 0 := by
  rcases hP with ⟨_, _, _, _, _, _, hfour⟩
  have hvar (a : Bool) :
      SAP.P002a.popVar (SAP.P002a.w P a (SAP.P002a.late P)) =
        (∑ i, (SAP.P002a.v P a (SAP.P002a.late P) i) ^ 2) / ((n : ℝ) - 1) := by
    simp [SAP.P002a.popVar, SAP.P002a.v]
  intro a i
  have hmoment : SAP.P002a.fourthNorm (SAP.P002a.v P a (SAP.P002a.late P)) ≤
      A * Real.sqrt ((∑ i, (SAP.P002a.v P a (SAP.P002a.late P) i) ^ 2) / ((n : ℝ) - 1)) := by
    simpa only [hvar a] using hfour a
  have hcollapse := hL1 (SAP.P002a.v P a (SAP.P002a.late P)) A hn hAnonneg
    hthreshold hmoment
  exact hcollapse i

lemma coverage_one_of_centered_zero {n : ℕ} (P : SAP.P002a.Population n)
    (hD : SAP.P002a.ValidDesign P) (hm : SAP.P002a.MonotoneReceipt P)
    (hc : (SAP.P002a.compliers P).Nonempty)
    (hzero : ∀ a i, SAP.P002a.v P a (SAP.P002a.late P) i = 0)
    (α : ℝ) : SAP.P002a.coverage P (SAP.P002a.late P) α = 1 := by
  have hmA : AronowAudit.P002.MonotoneReceipt (toPopulation P) := by
    change SAP.P002a.MonotoneReceipt P
    exact hm
  have hcA : (AronowAudit.P002.compliers (toPopulation P)).Nonempty := by
    change (SAP.P002a.compliers P).Nonempty
    exact hc
  have hmeansA := AronowAudit.P002.mean_w_equal_at_late (toPopulation P) hmA hcA
  have hmeans : SAP.P002a.mean (SAP.P002a.w P true (SAP.P002a.late P)) =
      SAP.P002a.mean (SAP.P002a.w P false (SAP.P002a.late P)) := by
    change AronowAudit.P002.mean (AronowAudit.P002.w (toPopulation P) true
      (AronowAudit.P002.late (toPopulation P))) =
      AronowAudit.P002.mean (AronowAudit.P002.w (toPopulation P) false
      (AronowAudit.P002.late (toPopulation P)))
    exact hmeansA
  let c : ℝ := SAP.P002a.mean (SAP.P002a.w P false (SAP.P002a.late P))
  have hw : ∀ a i, SAP.P002a.w P a (SAP.P002a.late P) i = c := by
    intro a i
    cases a
    · have hz := hzero false i
      unfold SAP.P002a.v at hz
      exact sub_eq_zero.mp hz
    · have hz := hzero true i
      unfold SAP.P002a.v at hz
      rw [hmeans] at hz
      exact sub_eq_zero.mp hz
  have hobsA (O : Finset (Fin n)) :
      AronowAudit.P002.observedW (toPopulation P) (AronowAudit.P002.late (toPopulation P)) O =
        fun _ => c := by
    apply AronowAudit.P002.observedW_constant (toPopulation P)
      (AronowAudit.P002.late (toPopulation P)) c
    simpa only [← w_eq, ← late_eq] using hw
  have hobs (O : Finset (Fin n)) :
      SAP.P002a.observedW P (SAP.P002a.late P) O = fun _ => c := by
    simpa only [observedW_eq, late_eq] using hobsA O
  have hD_A : AronowAudit.P002.ValidDesign (toPopulation P) := by
    change SAP.P002a.ValidDesign P
    exact hD
  have hTauA (O : Finset (Fin n)) (hO : O ∈ SAP.P002a.assignments P) :
      AronowAudit.P002.rawTau (toPopulation P) (fun _ => c) O = 0 := by
    apply AronowAudit.P002.rawTau_constant (toPopulation P) hD_A c O
    simpa only [assignments_eq] using hO
  have htrue (O : Finset (Fin n)) (hO : O ∈ SAP.P002a.assignments P) :
      SAP.P002a.accepted P (SAP.P002a.late P) α O := by
    unfold SAP.P002a.accepted
    rw [hobs O]
    have hTau : SAP.P002a.rawTau P (fun _ => c) O = 0 := by
      simpa only [rawTau_eq] using hTauA O hO
    have hAR : SAP.P002a.rawAR P (fun _ => c) O = 0 := by
      simp [SAP.P002a.rawAR, SAP.P002a.absStudent, hTau]
    rw [hAR]
    exact bot_le
  have hAssignments : (SAP.P002a.assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using Nat.le_of_lt hD.2.2
  have hcard : ((SAP.P002a.assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast hAssignments.card_ne_zero
  unfold SAP.P002a.coverage SAP.P002a.probability
  rw [Finset.filter_eq_self.mpr htrue]
  exact div_self hcard

lemma infCoverage_eq_one_of_size {n : ℕ} (δ r A α : ℝ)
    (hsize : n ∈ SAP.P002a.thetaSizes δ r A)
    (hcoverage : ∀ P : SAP.P002a.Population n, SAP.P002a.Theta P δ r A →
      SAP.P002a.coverage P (SAP.P002a.late P) α = 1) :
    SAP.P002a.infCoverageTheta n δ r A α = 1 := by
  rcases hsize with ⟨P, hP⟩
  unfold SAP.P002a.infCoverageTheta
  apply le_antisymm
  · exact iInf_le_of_le (SAP.P002a.late P)
      (iInf_le_of_le ⟨P, hP, rfl⟩ (by simp [hcoverage P hP]))
  · refine le_iInf fun β => le_iInf fun Q => ?_
    rcases Q.property with ⟨hQ, hβ⟩
    have hcov := hcoverage Q.val hQ
    rw [hβ] at hcov
    simp [hcov]

end
end SAP.P002a.WH.W2.P.T5_L2

open Filter
open scoped ENNReal

theorem SAP.P002a.WH.W2.T5_L2_proof : SAP.P002a.WH.W2.T5_L2 := by
  intro hL1 δ r A α hδ hr hA hα hnom
  by_contra hAone
  have hA_lt : A < 1 := lt_of_not_ge hAone
  have hden : 0 < 1 - A ^ 2 := by nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - A ^ 2))
  let M : ℕ := max N 2
  have hM2 : 2 ≤ M := le_trans (by decide : 2 ≤ 2) (Nat.le_max_right N 2)
  have hthreshold_event : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ A ^ 2 < ((n : ℝ) - 1) / (n : ℝ) := by
    have hfor (n : ℕ) (hMn : M ≤ n) :
        2 ≤ n ∧ A ^ 2 < ((n : ℝ) - 1) / (n : ℝ) := by
      have hn2 : 2 ≤ n := le_trans hM2 hMn
      have hNn : N ≤ n := le_trans (Nat.le_max_left N 2) hMn
      have hNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      have hrecip : 1 / (1 - A ^ 2) < (n : ℝ) := lt_of_lt_of_le hN hNreal
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hmul := mul_lt_mul_of_pos_right hrecip hden
      have hone : 1 < (n : ℝ) * (1 - A ^ 2) := by
        have heq : (1 / (1 - A ^ 2)) * (1 - A ^ 2) = 1 := by
          field_simp [ne_of_gt hden]
        calc
          1 = (1 / (1 - A ^ 2)) * (1 - A ^ 2) := heq.symm
          _ < (n : ℝ) * (1 - A ^ 2) := hmul
      have hthreshold : A ^ 2 < ((n : ℝ) - 1) / (n : ℝ) := by
        rw [lt_div_iff₀ hnpos]
        nlinarith
      exact ⟨hn2, hthreshold⟩
    exact Filter.eventually_atTop.2 ⟨M, hfor⟩
  let F : Filter ℕ := atTop ⊓ Filter.principal (SAP.P002a.thetaSizes δ r A)
  have hbot_or_nebot : F = ⊥ ∨ NeBot F := F.eq_or_neBot
  rcases hbot_or_nebot with hF | hF
  · have htop : (⊤ : ℝ≥0∞) = ENNReal.ofReal (1 - α) := by
      simpa [F, hF, Filter.liminf_bot] using hnom
    exact ENNReal.ofReal_ne_top htop.symm
  · letI : NeBot F := hF
    have hsize_event : ∀ᶠ n in F, n ∈ SAP.P002a.thetaSizes δ r A := by
      change ∀ᶠ n in Filter.atTop ⊓ Filter.principal (SAP.P002a.thetaSizes δ r A),
        n ∈ SAP.P002a.thetaSizes δ r A
      rw [Filter.eventually_inf_principal]
      simp
    have hthreshold_F : ∀ᶠ n : ℕ in F,
        2 ≤ n ∧ A ^ 2 < ((n : ℝ) - 1) / (n : ℝ) :=
      hthreshold_event.filter_mono inf_le_left
    have hcoverage_all (n : ℕ) (hn : 2 ≤ n)
        (hth : A ^ 2 < ((n : ℝ) - 1) / (n : ℝ))
        (P : SAP.P002a.Population n) (hP : SAP.P002a.Theta P δ r A) :
        SAP.P002a.coverage P (SAP.P002a.late P) α = 1 := by
      have hzero : ∀ a i, SAP.P002a.v P a (SAP.P002a.late P) i = 0 :=
        SAP.P002a.WH.W2.P.T5_L2.centered_zero_of_small_moment hL1 P δ r A hP hA.le hn hth
      rcases hP with ⟨hD, hm, hc, _, _, _, _⟩
      exact SAP.P002a.WH.W2.P.T5_L2.coverage_one_of_centered_zero P hD hm hc hzero α
    have hcoverage_event : ∀ᶠ n in F,
        SAP.P002a.infCoverageTheta n δ r A α = 1 := by
      filter_upwards [hthreshold_F, hsize_event] with n hn hsize
      exact SAP.P002a.WH.W2.P.T5_L2.infCoverage_eq_one_of_size δ r A α hsize
        (fun P hP => hcoverage_all n hn.1 hn.2 P hP)
    have hliminf : Filter.liminf
        (fun n => SAP.P002a.infCoverageTheta n δ r A α) F = 1 := by
      rw [Filter.liminf_congr hcoverage_event]
      exact Filter.liminf_const 1
    have hnom' : (1 : ℝ≥0∞) = ENNReal.ofReal (1 - α) := by
      exact hliminf.symm.trans (by simpa [F] using hnom)
    have htargetpos : 0 < 1 - α := by linarith [hα.2]
    have hlt : ENNReal.ofReal (1 - α) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2
        (by linarith [hα.1])
    exact (ne_of_lt hlt) hnom'.symm
