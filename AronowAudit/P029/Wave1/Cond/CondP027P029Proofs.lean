import AronowAudit.Literature.CondP027P029

namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set
open AronowAudit.Literature

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma CondP027P029_cover (i j : Fin 2) :
    orderedBinomialCover (fun i j : Fin 2 => i < j) i j ↔ i < j := by
  constructor
  · exact And.left
  · intro hij
    refine ⟨hij, ?_⟩
    rintro ⟨h, hih, hhj⟩
    omega

lemma CondP027P029_removed :
    (fun h l : Fin 2 => orderedBinomialCover (fun i j => i < j) h l ∧
      ¬ (h = 0 ∧ l = 1)) = (fun _ _ => False) := by
  funext h l
  apply propext
  rw [CondP027P029_cover]
  fin_cases h <;> fin_cases l <;> simp

lemma CondP027P029_domain (x : Fin 2 → ℝ) :
    orderedBinomialDomain (orderedBinomialCover (fun i j : Fin 2 => i < j)) x ↔
      (x 1, x 0) ∈ receiptTriangle := by
  simp only [orderedBinomialDomain, CondP027P029_cover, receiptTriangle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hb, ho⟩
    exact ⟨(hb 0).1, ho 0 1 (by decide), (hb 1).2⟩
  · rintro ⟨h0, h01, h1⟩
    constructor
    · intro i
      fin_cases i
      · exact ⟨h0, h01.trans h1⟩
      · exact ⟨h0.trans h01, h1⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all

lemma CondP027P029_kernel (n1 n0 k1 k0 : ℕ) (x : Fin 2 → ℝ) :
    orderedBinomialKernel ![n0, n1] ![k0, k1] x =
      saturatedLikelihood n1 n0 k1 k0 (x 1) (x 0) := by
  simp [orderedBinomialKernel, Fin.prod_univ_two, saturatedLikelihood]
  <;> ring

lemma CondP027P029_pair_max (n1 n0 k1 k0 : ℕ) (x : Fin 2 → ℝ)
    (hx : orderedBinomialMax ![n0, n1] ![k0, k1]
      (orderedBinomialCover (fun i j : Fin 2 => i < j)) x) :
    (x 1, x 0) ∈ receiptTriangle ∧
    ∀ v ∈ receiptTriangle,
      saturatedLikelihood n1 n0 k1 k0 v.1 v.2 ≤
        saturatedLikelihood n1 n0 k1 k0 (x 1) (x 0) ∧
      (saturatedLikelihood n1 n0 k1 k0 v.1 v.2 =
        saturatedLikelihood n1 n0 k1 k0 (x 1) (x 0) ↔ v = (x 1, x 0)) := by
  refine ⟨(CondP027P029_domain x).mp hx.1, ?_⟩
  intro v hv
  have hd : orderedBinomialDomain
      (orderedBinomialCover (fun i j : Fin 2 => i < j)) ![v.2, v.1] :=
    (CondP027P029_domain _).mpr (by simpa using hv)
  have hm := hx.2 _ hd
  rw [CondP027P029_kernel, CondP027P029_kernel] at hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hm
  refine ⟨hm.1, hm.2.trans ?_⟩
  constructor
  · intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    exact Prod.ext (by simpa using h1) (by simpa using h0)
  · intro he
    subst v
    funext i
    fin_cases i <;> simp

lemma CondP027P029_diagonal (n1 n0 k1 k0 : ℕ)
    (hk1 : k1 ≤ n1) (hk0 : k0 ≤ n0) (t : ℝ) :
    orderedBinomialKernel ![n0, n1] ![k0, k1] ![t, t] =
      orderedBinomialKernel ![n1 + n0] ![k1 + k0] ![t] := by
  have hs : (n1 + n0) - (k1 + k0) = (n1 - k1) + (n0 - k0) := by omega
  simp [orderedBinomialKernel, Fin.prod_univ_two, hs, pow_add]
  <;> ring

/-- The two-arm closed likelihood characterization conditional on the general
ordered-binomial maximum theorem, including the endpoint count cases. -/
theorem saturated_ml_characterization_conditional :
    AronowAudit.P029.saturated_ml_characterization_conditional_statement := by
  intro literature n1 n0 k1 k0 hn1 hn0 hk1 hk0
  have hn : ∀ i : Fin 2, 0 < (![n0, n1] i) := by
    intro i; fin_cases i
    · exact hn0
    · exact hn1
  have hk : ∀ i : Fin 2, ![k0, k1] i ≤ ![n0, n1] i := by
    intro i; fin_cases i
    · exact hk0
    · exact hk1
  obtain ⟨hr, horder⟩ := literature 2 (by decide) ![n0, n1] ![k0, k1] hn hk
  obtain ⟨⟨x, hx⟩, hrestrict⟩ := horder (fun i j => i < j)
    (by intros; assumption) (by intro i j h hij hjh; exact lt_trans hij hjh)
  let r : Fin 2 → ℝ := fun i => ((![k0, k1] i : ℕ) : ℝ) / ![n0, n1] i
  have hr' : orderedBinomialMax ![n0, n1] ![k0, k1]
      (fun h l => orderedBinomialCover (fun i j : Fin 2 => i < j) h l ∧
        ¬ (h = 0 ∧ l = 1)) r := by
    rw [CondP027P029_removed]
    exact hr
  have hcases := hrestrict 0 1 ((CondP027P029_cover _ _).mpr (by decide)) x r hx hr'
  have hfit : (x 1, x 0) = saturatedFit n1 n0 k1 k0 := by
    by_cases hle : (k0 : ℝ) / n0 ≤ (k1 : ℝ) / n1
    · have he := hcases.1 (by simpa [r] using hle)
      simp [saturatedFit, hle, he, r]
    · have he : x 0 = x 1 := hcases.2 (by simpa [r] using lt_of_not_ge hle)
      let b : ℝ := ((k1 + k0 : ℕ) : ℝ) / (n1 + n0)
      have hnp : 0 < n1 + n0 := by omega
      have hkp : k1 + k0 ≤ n1 + n0 := by omega
      have hp := (literature 1 (by decide) ![n1 + n0] ![k1 + k0]
        (by intro i; fin_cases i; exact hnp)
        (by intro i; fin_cases i; exact hkp)).1
      have hb : orderedBinomialMax ![n1 + n0] ![k1 + k0]
          (fun _ _ => False) ![b] := by
        convert hp using 1
        funext i
        fin_cases i
        simp [b, Nat.cast_add]
      have hb0 : 0 ≤ b := (hb.1.1 0).1
      have hb1 : b ≤ 1 := (hb.1.1 0).2
      have hdb : orderedBinomialDomain
          (orderedBinomialCover (fun i j : Fin 2 => i < j)) ![b, b] :=
        (CondP027P029_domain _).mpr (by exact ⟨hb0, le_refl _, hb1⟩)
      have hdx : orderedBinomialDomain (fun _ _ : Fin 1 => False) ![x 0] := by
        refine ⟨?_, ?_⟩
        · intro i; fin_cases i; exact hx.1.1 0
        · intros i j h; exact h.elim
      have hdiag : x = ![x 0, x 0] := by
        funext i
        fin_cases i
        · simp
        · simpa using he.symm
      have hlo := (hx.2 ![b, b] hdb).1
      rw [hdiag, CondP027P029_diagonal n1 n0 k1 k0 hk1 hk0,
        CondP027P029_diagonal n1 n0 k1 k0 hk1 hk0] at hlo
      have hhi := hb.2 ![x 0] hdx
      have heq : ![x 0] = ![b] := hhi.2.mp (le_antisymm hhi.1 hlo)
      have ht : x 0 = b := by simpa using congrFun heq 0
      simp [saturatedFit, hle, ← he, ht, b]
  have hm := CondP027P029_pair_max n1 n0 k1 k0 x hx
  rw [hfit] at hm
  have hx1 : x 1 = (saturatedFit n1 n0 k1 k0).1 := congrArg Prod.fst hfit
  have hx0 : x 0 = (saturatedFit n1 n0 k1 k0).2 := congrArg Prod.snd hfit
  rw [hx1, hx0] at hm
  refine ⟨hm.1, hm.2, ?_⟩
  by_cases hle : (k0 : ℝ) / n0 ≤ (k1 : ℝ) / n1
  · simp [saturatedFit, hle, positiveScore]
  · simp [saturatedFit, hle, positiveScore,
      max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hle)))]

end
end AronowAudit.P029.Wave1
