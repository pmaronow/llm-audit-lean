import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Exact population fits are recovered on each nonsingular observed arm. -/
theorem n3_proof : N3 := by
  intro hGram n P α O hXi hres hO hg1 hg0
  have hg : (gram P.x Finset.univ).det ≠ 0 :=
    hGram n 1 P 0 (1/4) 4 (1/2) (1/4) (by norm_num) hXi
  rcases hXi with ⟨hD, hm, hc, _, _, _, _, hx, _, _⟩
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hD.1
  let β : ℝ := late P.pop
  let q : Fin n → ℝ := observedW P.pop β O
  have hcard : O.card = P.pop.n1 := (Finset.mem_powersetCard.mp hO).2
  have hOne : O.Nonempty := Finset.card_pos.mp (by
    rw [hcard]
    exact hD.2.1)
  have hCne : Oᶜ.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    exact Nat.sub_pos_of_lt hD.2.2)
  have hphi (a : Bool) : psi P a β none = mean (w P.pop a β) :=
    population_intercept_mean P.x (w P.pop a β) hn hx hg
  have hphieq : psi P true β none = psi P false β none := by
    rw [hphi true, hphi false]
    exact mean_w_equal_at_late P.pop hm hc
  have hresponse1 : ∀ i ∈ O,
      q i = dotProduct (augmented P.x i) (psi P true β) := by
    intro i hi
    change observedW P.pop β O i = _
    rw [observedW_treated P.pop β O i hi]
    exact sub_eq_zero.mp (hres true i)
  have hresponse0 : ∀ i ∈ Oᶜ,
      q i = dotProduct (augmented P.x i) (psi P false β) := by
    intro i hi
    change observedW P.pop β O i = _
    rw [observedW_control P.pop β O i hi]
    exact sub_eq_zero.mp (hres false i)
  have hrecover (S : Finset (Fin n)) (c : Option (Fin 1) → ℝ)
      (hS : (gram P.x S).det ≠ 0)
      (hq : ∀ i ∈ S, q i = dotProduct (augmented P.x i) c) :
      ols P.x S q = c := by
    have hs : score P.x S q = gram P.x S *ᵥ c :=
      (score_congr P.x S q (fun i => dotProduct (augmented P.x i) c) hq).trans
        (score_of_dot P.x S c)
    rw [ols, if_pos hS, hs, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS), Matrix.one_mulVec]
  have hfit1 : fitted P q O true = psi P true β := by
    simpa only [fitted, if_true] using
      hrecover O (psi P true β) hg1 hresponse1
  have hfit0 : fitted P q O false = psi P false β := by
    simpa only [fitted, Bool.false_eq_true, ite_false] using
      hrecover Oᶜ (psi P false β) hg0 hresponse0
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
        apply groupMean_congr
        intro i hi
        rw [hresponse1 i hi, hdot]
        ring
      _ = groupMean O (fun _ => (0 : ℝ)) + psi P true β none :=
        groupMean_add_const O (fun _ => (0 : ℝ)) (psi P true β none) hOne
      _ = _ := by simp [groupMean]
  have hmean0 : groupMean Oᶜ
      (fun i => q i - slopeDot (P.x i) (psi P false β)) = psi P false β none := by
    calc
      _ = groupMean Oᶜ (fun _ => (0 : ℝ) + psi P false β none) := by
        apply groupMean_congr
        intro i hi
        rw [hresponse0 i hi, hdot]
        ring
      _ = groupMean Oᶜ (fun _ => (0 : ℝ)) + psi P false β none :=
        groupMean_add_const Oᶜ (fun _ => (0 : ℝ)) (psi P false β none) hCne
      _ = _ := by simp [groupMean]
  have htau : adjustedTau P q O = 0 := by
    simp only [adjustedTau, adjustedWith, hfit1, hfit0, hmean1, hmean0,
      hphieq, sub_self]
  have hsigma : adjustedSigma2 P q O = 0 := by
    simp only [adjustedSigma2, hrss1, hrss0, zero_div, add_zero]
  change adjustedAR P q O ≤ quantile P.pop (adjustedAR P q) α
  rw [adjustedAR, htau, hsigma]
  simp only [absStudent, if_pos rfl]
  exact zero_le

end
end AronowAudit.P002.Wave1.PrintedTheorem2
