import SAP.P029b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2.P.T27_L3

open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

def sampleCell (n : ℕ) (ω : CancelSpaceW2) (i : Fin (n + 1)) : Bool × Bool :=
  ((ω i.val).1.1, (ω i.val).2)

def sampleReceipt (n : ℕ) (ω : CancelSpaceW2) (i : Fin (n + 1)) : Bool :=
  (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)

theorem cell_success_eq_numerator (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) :
    cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) =
      ∑ i : Fin (n + 1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then
        bit (sampleReceipt n ω i) else 0 := by
  unfold cellSuccessWeight sampleCell sampleReceipt
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : ((ω i.val).1.1, (ω i.val).2) = (x, z)
  · have hc' : (ω i.val).1.1 = x ∧ (ω i.val).2 = z := by
      cases hc
      exact ⟨rfl, rfl⟩
    by_cases hd : (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω) = true
    · simp [hc', hd, bit]
    · have hd' : (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω) = false :=
        Bool.eq_false_of_not_eq_true hd
      simp [hc', hd, bit]
  · have hc' : ¬ ((ω i.val).1.1 = x ∧ (ω i.val).2 = z) := by
      intro hh
      exact hc (Prod.ext hh.1 hh.2)
    simp [hc, hc']

theorem cell_count_eq_weights (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) :
    cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) +
      cellFailureWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) =
        ∑ i : Fin (n + 1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0 := by
  unfold cellSuccessWeight cellFailureWeight sampleCell sampleReceipt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : ((ω i.val).1.1, (ω i.val).2) = (x, z)
  · have hc' : (ω i.val).1.1 = x ∧ (ω i.val).2 = z := by
      cases hc
      exact ⟨rfl, rfl⟩
    by_cases hd : (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω) = true
    · simp [hc', hd]
    · have hd' : (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω) = false :=
        Bool.eq_false_of_not_eq_true hd
      simp [hc', hd]
  · have hc' : ¬ ((ω i.val).1.1 = x ∧ (ω i.val).2 = z) := by
      intro hh
      exact hc (Prod.ext hh.1 hh.2)
    simp [hc, hc']

theorem receipt_parameter_interior (q : ReceiptParameters) (x z : Bool) :
    q.val (x, z) ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h01, h1⟩ := q.property x
  cases z
  · exact ⟨h0, lt_trans h01 h1⟩
  · exact ⟨lt_trans h0 h01, h1⟩

theorem fitted_rate_interior (n : ℕ) (ω : CancelSpaceW2)
    (hgood : cancelFitGoodW2 n ω) (x z : Bool) :
    cancelRateW2 n ω x z ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h01, h1⟩ := hgood x
  cases z
  · exact ⟨h0, lt_trans h01 h1⟩
  · exact ⟨lt_trans h0 h01, h1⟩

theorem cell_stats (n : ℕ) (ω : CancelSpaceW2) (hgood : cancelFitGoodW2 n ω)
    (x z : Bool) :
    0 < cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) ∧
    0 < cellFailureWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) ∧
    cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) /
      (cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z) +
        cellFailureWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z)) =
      cancelRateW2 n ω x z := by
  let S := cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z)
  let F := cellFailureWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) (x, z)
  let N := ∑ i : Fin (n + 1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then
    bit (sampleReceipt n ω i) else 0
  let M := ∑ i : Fin (n + 1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0
  change 0 < S ∧ 0 < F ∧ S / (S + F) = cancelRateW2 n ω x z
  have hS : S = N := by
    dsimp [S, N]
    exact cell_success_eq_numerator n ω x z
  have hcount : S + F = M := by
    dsimp [S, F, M]
    exact cell_count_eq_weights n ω x z
  have hrateEq : cancelRateW2 n ω x z = N / M := by
    dsimp [cancelRateW2, N, M]
    rfl
  have hrate : cancelRateW2 n ω x z ∈ Set.Ioo (0 : ℝ) 1 :=
    fitted_rate_interior n ω hgood x z
  have hMne : M ≠ 0 := by
    intro hzero
    rw [hrateEq, hzero, div_zero] at hrate
    norm_num at hrate
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> norm_num
  have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hMne)
  have hnum : N = cancelRateW2 n ω x z * M := by
    rw [hrateEq]
    field_simp [hMne]
  have hsuccess : S = cancelRateW2 n ω x z * M := hS.trans hnum
  have hSpos : 0 < S := by
    rw [hsuccess]
    exact mul_pos hrate.1 hMpos
  have hmul : cancelRateW2 n ω x z * M < M := by
    nlinarith [mul_lt_mul_of_pos_right hrate.2 hMpos]
  have hFpos : 0 < F := by
    nlinarith [hcount, hsuccess, hmul]
  refine ⟨hSpos, hFpos, ?_⟩
  calc
    S / (S + F) = N / M := by rw [hcount, hS]
    _ = cancelRateW2 n ω x z := hrateEq.symm

end

end SAP.P029b.WH.W2.P.T27_L3

open SAP.P029b.WH.W2.P.T27_L3 AronowAudit.P029

theorem SAP.P029b.WH.W2.T27_L3_proof : SAP.P029b.WH.W2.T27_L3 := by
  classical
  intro n ω hgood q
  let fit : Bool × Bool → ℝ := fun c => cancelRateW2 n ω c.1 c.2
  have hSpos : ∀ c : Bool × Bool,
      0 < cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) c := by
    rintro ⟨x, z⟩
    exact (cell_stats n ω hgood x z).1
  have hFpos : ∀ c : Bool × Bool,
      0 < cellFailureWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) c := by
    rintro ⟨x, z⟩
    exact (cell_stats n ω hgood x z).2.1
  have hsat := saturated_weighted_objective_minimum (sampleCell n ω)
    (sampleReceipt n ω) (fun _ => (1 : ℝ)) (by intro i; norm_num) hSpos hFpos
  have hqhat : ∀ c : Bool × Bool,
      cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) c /
        (cellSuccessWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) c +
          cellFailureWeight (sampleCell n ω) (sampleReceipt n ω) (fun _ => (1 : ℝ)) c) =
        fit c := by
    rintro ⟨x, z⟩
    exact (cell_stats n ω hgood x z).2.2
  dsimp only at hsat
  simp_rw [hqhat] at hsat
  have hqint : ∀ c : Bool × Bool, q.val c ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro ⟨x, z⟩
    exact receipt_parameter_interior q x z
  have hobj := (hsat.2 q.val hqint).1
  have hsum :
      (∑ i : Fin (n + 1), Real.log (bernoulliFactor (q.val (sampleCell n ω i))
        (sampleReceipt n ω i))) ≤
      ∑ i : Fin (n + 1), Real.log (bernoulliFactor (fit (sampleCell n ω i))
        (sampleReceipt n ω i)) := by
    have hobj' := hobj
    change -(∑ i : Fin (n + 1), (1 : ℝ) * Real.log
        (bernoulliFactor (fit (sampleCell n ω i)) (sampleReceipt n ω i))) ≤
      -(∑ i : Fin (n + 1), (1 : ℝ) * Real.log
        (bernoulliFactor (q.val (sampleCell n ω i)) (sampleReceipt n ω i))) at hobj'
    simpa only [one_mul] using (neg_le_neg_iff.mp hobj')
  have hqfactor : ∀ i : Fin (n + 1),
      0 < bernoulliFactor (q.val (sampleCell n ω i)) (sampleReceipt n ω i) := by
    intro i
    have hp := hqint (sampleCell n ω i)
    cases hd : sampleReceipt n ω i <;>
      simp [bernoulliFactor] <;> linarith [hp.1, hp.2]
  have hfitfactor : ∀ i : Fin (n + 1),
      0 < bernoulliFactor (fit (sampleCell n ω i)) (sampleReceipt n ω i) := by
    intro i
    rcases sampleCell n ω i with ⟨x, z⟩
    have hp := fitted_rate_interior n ω hgood x z
    cases hd : sampleReceipt n ω i <;>
      simp [fit, bernoulliFactor] <;> linarith [hp.1, hp.2]
  have hqprod : 0 < cancelLikelihoodW2 n ω q.val := by
    unfold cancelLikelihoodW2
    apply Finset.prod_pos
    intro i hi
    exact hqfactor i
  have hfitprod : 0 < cancelLikelihoodW2 n ω fit := by
    unfold cancelLikelihoodW2
    apply Finset.prod_pos
    intro i hi
    exact hfitfactor i
  have hqlog : Real.log (cancelLikelihoodW2 n ω q.val) =
      ∑ i : Fin (n + 1), Real.log (bernoulliFactor (q.val (sampleCell n ω i))
        (sampleReceipt n ω i)) := by
    unfold cancelLikelihoodW2
    rw [Real.log_prod]
    · rfl
    · intro i hi
      exact (ne_of_gt (hqfactor i))
  have hfitlog : Real.log (cancelLikelihoodW2 n ω fit) =
      ∑ i : Fin (n + 1), Real.log (bernoulliFactor (fit (sampleCell n ω i))
        (sampleReceipt n ω i)) := by
    unfold cancelLikelihoodW2
    rw [Real.log_prod]
    · rfl
    · intro i hi
      exact (ne_of_gt (hfitfactor i))
  have hlog : Real.log (cancelLikelihoodW2 n ω q.val) ≤
      Real.log (cancelLikelihoodW2 n ω fit) := by
    rw [hqlog, hfitlog]
    exact hsum
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hqprod, Real.exp_log hfitprod] at hexp
  exact hexp
