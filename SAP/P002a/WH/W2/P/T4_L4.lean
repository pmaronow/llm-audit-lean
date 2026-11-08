import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W2.P.T4_L4
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Matrix Classical
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

theorem exact_full_rank {n : ℕ} (P : CovPopulation n 1)
    (hXi : Xi P 0 (1/4) 4 (1/2) (1/4)) :
    (∀ a i, residual P a (late P.pop) i = 0) ∧
    psi P true (late P.pop) none = psi P false (late P.pop) none ∧
    (∀ O ∈ assignments P.pop, W2FullRank P O →
      (∀ a, fitted P (observedW P.pop (late P.pop) O) O a = psi P a (late P.pop)) ∧
      (∀ i, observedW P.pop (late P.pop) O i -
        dotProduct (augmented P.x i)
          (fitted P (observedW P.pop (late P.pop) O) O (decide (i ∈ O))) = 0) ∧
      adjustedTau P (observedW P.pop (late P.pop) O) O = 0 ∧
      adjustedSigma2 P (observedW P.pop (late P.pop) O) O = 0 ∧
      adjustedAR P (observedW P.pop (late P.pop) O) O = 0) := by
  let Pa := toCovPopulation P
  have hXiA : AronowAudit.P002.Xi Pa 0 (1/4) 4 (1/2) (1/4) := by
    simpa only [SAP.P002a.Bridge.xi_eq] using hXi
  have hres : ∀ a i, residual P a (late P.pop) i = 0 :=
    by
      have hresA := AronowAudit.P002.Wave1.T4SC_residuals_vanish n Pa hXiA
      simpa only [SAP.P002a.Bridge.residual_eq, SAP.P002a.Bridge.late_eq,
        Pa, toCovPopulation, toPopulation] using hresA
  have hgA : (AronowAudit.P002.gram Pa.x Finset.univ).det ≠ 0 :=
    AronowAudit.P002.Wave1.PrintedTheorem2.n1_proof
      n 1 Pa 0 (1/4) 4 (1/2) (1/4) (by norm_num) hXiA
  have hg : (gram P.x Finset.univ).det ≠ 0 := by
    simpa only [SAP.P002a.Bridge.gram_eq, Pa, toCovPopulation] using hgA
  rcases hXi with ⟨hD, hm, hc, _, _, _, _, hx, _, _⟩
  rcases hXiA with ⟨hDA, hmA, hcA, _, _, _, _, hxA, _, _⟩
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hD.1
  let β : ℝ := late P.pop
  have hphiA (a : Bool) : AronowAudit.P002.psi Pa a β none =
      AronowAudit.P002.mean (AronowAudit.P002.w Pa.pop a β) :=
    AronowAudit.P002.population_intercept_mean Pa.x
      (AronowAudit.P002.w Pa.pop a β) hn hxA hgA
  have hphi (a : Bool) : psi P a β none = mean (w P.pop a β) := by
    simpa only [SAP.P002a.Bridge.psi_eq, SAP.P002a.Bridge.mean_eq,
      SAP.P002a.Bridge.w_eq, Pa, toCovPopulation, toPopulation] using hphiA a
  have hphieq : psi P true β none = psi P false β none := by
    rw [hphi true, hphi false]
    have hmeanA := AronowAudit.P002.mean_w_equal_at_late Pa.pop hmA hcA
    have hβA : β = AronowAudit.P002.late Pa.pop := by
      simpa [β, Pa, toCovPopulation, toPopulation] using
        (SAP.P002a.Bridge.late_eq P.pop)
    simpa only [SAP.P002a.Bridge.mean_eq, SAP.P002a.Bridge.w_eq,
      Pa, toCovPopulation, toPopulation, hβA] using hmeanA
  refine ⟨hres, ?_, ?_⟩
  · simpa [β] using hphieq
  · intro O hO hfull
    let q : Fin n → ℝ := observedW P.pop β O
    have hcard : O.card = P.pop.n1 := (Finset.mem_powersetCard.mp hO).2
    have hOne : O.Nonempty := Finset.card_pos.mp (by
      rw [hcard]
      exact hD.2.1)
    have hCne : Oᶜ.Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_compl, Fintype.card_fin, hcard]
      exact Nat.sub_pos_of_lt hD.2.2)
    have hresponse1 : ∀ i ∈ O,
        q i = dotProduct (augmented P.x i) (psi P true β) := by
      intro i hi
      have hobsA := AronowAudit.P002.observedW_treated Pa.pop β O i hi
      have hobs : observedW P.pop β O i = w P.pop true β i := by
        simpa only [SAP.P002a.Bridge.observedW_eq, SAP.P002a.Bridge.w_eq,
          Pa, toCovPopulation, toPopulation] using hobsA
      change observedW P.pop β O i = _
      rw [hobs]
      exact sub_eq_zero.mp (hres true i)
    have hresponse0 : ∀ i ∈ Oᶜ,
        q i = dotProduct (augmented P.x i) (psi P false β) := by
      intro i hi
      have hobsA := AronowAudit.P002.observedW_control Pa.pop β O i hi
      have hobs : observedW P.pop β O i = w P.pop false β i := by
        simpa only [SAP.P002a.Bridge.observedW_eq, SAP.P002a.Bridge.w_eq,
          Pa, toCovPopulation, toPopulation] using hobsA
      change observedW P.pop β O i = _
      rw [hobs]
      exact sub_eq_zero.mp (hres false i)
    have hrecover (S : Finset (Fin n)) (c : Option (Fin 1) → ℝ)
        (hS : (gram P.x S).det ≠ 0)
        (hq : ∀ i ∈ S, q i = dotProduct (augmented P.x i) c) :
        ols P.x S q = c := by
      have hs : score P.x S q = gram P.x S *ᵥ c :=
        (AronowAudit.P002.score_congr P.x S q
          (fun i => dotProduct (augmented P.x i) c) hq).trans
          (AronowAudit.P002.score_of_dot P.x S c)
      rw [ols, if_pos hS, hs, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS), Matrix.one_mulVec]
    have hfit1 : fitted P q O true = psi P true β := by
      simpa only [fitted, if_true] using
        hrecover O (psi P true β) hfull.1 hresponse1
    have hfit0 : fitted P q O false = psi P false β := by
      simpa only [fitted, Bool.false_eq_true, ite_false] using
        hrecover Oᶜ (psi P false β) hfull.2 hresponse0
    have hrss1 : rss P.x O q (fitted P q O true) = 0 := by
      rw [hfit1]
      unfold rss
      apply Finset.sum_eq_zero
      intro i hi
      rw [hresponse1 i hi]
      ring
    have hrss0 : rss P.x Oᶜ q (fitted P q O false) = 0 := by
      rw [hfit0]
      unfold rss
      apply Finset.sum_eq_zero
      intro i hi
      rw [hresponse0 i hi]
      ring
    have hdot (i : Fin n) (c : Option (Fin 1) → ℝ) :
        dotProduct (augmented P.x i) c = c none + slopeDot (P.x i) c := by
      simp only [dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot]
    have hmean1 : groupMean O
        (fun i => q i - slopeDot (P.x i) (psi P true β)) = psi P true β none := by
      calc
        _ = groupMean O (fun _ => (0 : ℝ) + psi P true β none) := by
          apply AronowAudit.P002.groupMean_congr
          intro i hi
          rw [hresponse1 i hi, hdot]
          ring
        _ = groupMean O (fun _ => (0 : ℝ)) + psi P true β none :=
          AronowAudit.P002.groupMean_add_const O (fun _ => (0 : ℝ))
            (psi P true β none) hOne
        _ = _ := by simp [groupMean]
    have hmean0 : groupMean Oᶜ
        (fun i => q i - slopeDot (P.x i) (psi P false β)) = psi P false β none := by
      calc
        _ = groupMean Oᶜ (fun _ => (0 : ℝ) + psi P false β none) := by
          apply AronowAudit.P002.groupMean_congr
          intro i hi
          rw [hresponse0 i hi, hdot]
          ring
        _ = groupMean Oᶜ (fun _ => (0 : ℝ)) + psi P false β none :=
          AronowAudit.P002.groupMean_add_const Oᶜ (fun _ => (0 : ℝ))
            (psi P false β none) hCne
        _ = _ := by simp [groupMean]
    have htau : adjustedTau P q O = 0 := by
      simp only [adjustedTau, adjustedWith, hfit1, hfit0, hmean1, hmean0,
        hphieq, sub_self]
    have hsigma : adjustedSigma2 P q O = 0 := by
      simp only [adjustedSigma2, hrss1, hrss0, zero_div, add_zero]
    have hresid_fit : ∀ i,
        q i - dotProduct (augmented P.x i)
          (fitted P q O (decide (i ∈ O))) = 0 := by
      intro i
      by_cases hi : i ∈ O
      · have hfi : fitted P q O (decide (i ∈ O)) = psi P true β := by
          simp [hi, hfit1]
        rw [hfi]
        change q i - dotProduct (augmented P.x i) (psi P true β) = 0
        rw [hresponse1 i hi]
        ring
      · have hfi : fitted P q O (decide (i ∈ O)) = psi P false β := by
          simp [hi, hfit0]
        rw [hfi]
        change q i - dotProduct (augmented P.x i) (psi P false β) = 0
        rw [hresponse0 i (Finset.mem_compl.mpr hi)]
        ring
    have har : adjustedAR P q O = 0 := by
      unfold adjustedAR
      rw [htau, hsigma]
      simp [absStudent]
    have hfit_all : ∀ a, fitted P (observedW P.pop (late P.pop) O) O a =
        psi P a (late P.pop) := by
      intro a
      cases a with
      | false => simpa [q, β] using hfit0
      | true => simpa [q, β] using hfit1
    refine ⟨hfit_all, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa [q, β] using hresid_fit i
    · simpa [q, β] using htau
    · simpa [q, β] using hsigma
    · simpa [q, β] using har

end
end SAP.P002a.WH.W2.P.T4_L4

theorem SAP.P002a.WH.W2.T4_L4_proof : SAP.P002a.WH.W2.T4_L4 := by
  intro n P hXi
  have hexact := SAP.P002a.WH.W2.P.T4_L4.exact_full_rank P hXi
  refine ⟨hexact.1, hexact.2.1, hexact.2.2, ?_⟩
  intro F hcompletion α
  let event : Finset (Fin n) → Prop := fun O => W2FullRank P O
  let failure : Finset (Fin n) → Prop := fun O => ¬ W2FullRank P O
  let Pa := SAP.P002a.Bridge.toCovPopulation P
  have hXiA : AronowAudit.P002.Xi Pa 0 (1/4) 4 (1/2) (1/4) := by
    simpa only [SAP.P002a.Bridge.xi_eq] using hXi
  have hcalc := AronowAudit.P002.Wave1.PrintedTheorem2.n11_proof n Pa.pop
  have hvalid : AronowAudit.P002.ValidDesign Pa.pop := by
    exact hXiA.1
  have hcompA : AronowAudit.P002.probability Pa.pop failure =
      1 - AronowAudit.P002.probability Pa.pop event := by
    have h := hcalc.2.2.2.1 hvalid event
    simpa only [event, failure] using h
  have hgoodA : AronowAudit.P002.probability Pa.pop event =
      1 - AronowAudit.P002.probability Pa.pop failure := by
    dsimp [event, failure] at hcompA ⊢
    linarith
  have hgoodprob : probability P.pop (fun O => W2FullRank P O) =
      1 - probability P.pop (fun O => ¬ W2FullRank P O) := by
    simpa only [event, failure, SAP.P002a.Bridge.probability_eq,
      Pa, SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using hgoodA
  have hrank := SAP.P002a.WH.W2.t4_ranks P hXi
  have hfail : probability P.pop failure ≤ 1548 / ((n : ℝ) - 1) := by
    simpa [failure] using hrank.2.2.2.2
  have hcontainA : AronowAudit.P002.probability Pa.pop event ≤
      AronowAudit.P002.probability Pa.pop (fun O =>
        W2CompletedAR P F (observedW P.pop (late P.pop) O) O ≤
          quantile P.pop (fun S =>
            W2CompletedAR P F (observedW P.pop (late P.pop) O) S) α) := by
    apply hcalc.2.1
    intro O hO hOgood
    have hOSAP : O ∈ assignments P.pop := by
      simpa only [SAP.P002a.Bridge.assignments_eq, Pa,
        SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using hO
    let q : Fin n → ℝ := observedW P.pop (late P.pop) O
    have hfit1 : F q O true = fitted P q O true := by
      exact hcompletion q O true (by simpa [q] using hOgood.1)
    have hfit0 : F q O false = fitted P q O false := by
      exact hcompletion q O false (by simpa [q] using hOgood.2)
    have hzero : W2CompletedAR P F q O = 0 := by
      have hz := (hexact.2.2 O hO hOgood).2.2.2.2
      simpa [W2CompletedAR, adjustedAR, adjustedTau, adjustedSigma2,
        hfit1, hfit0] using hz
    have haccept : W2CompletedAR P F q O ≤
        quantile P.pop (fun S => W2CompletedAR P F q S) α := by
      rw [hzero]
      exact bot_le
    simpa only [q] using haccept
  have hcontain : probability P.pop event ≤ W2CompletedCoverage P F (late P.pop) α := by
    unfold W2CompletedCoverage
    simpa only [SAP.P002a.Bridge.probability_eq, Pa,
      SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using hcontainA
  have hnonneg : 0 ≤ probability P.pop event := by
    simpa only [SAP.P002a.Bridge.probability_eq, Pa,
      SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using
        (hcalc.1 event).1
  have hcovnonneg := hnonneg.trans hcontain
  rw [hgoodprob] at hcontain
  apply max_le
  · exact hcovnonneg
  linarith
