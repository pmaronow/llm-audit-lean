import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W2.P.T14_L3

open MeasureTheory
open scoped BigOperators Classical
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

private theorem K_bounds {m : ℕ} {T : Finset (Fin (2*m))}
    (hT : T ∈ SAP.P002a.assignments (SAP.P002a.signModel m)) :
    SAP.P002a.W2K m T ≤ m := by
  have hsub : T.filter (fun i => m ≤ i.val) ⊆ T := Finset.filter_subset _ _
  have hc := Finset.card_le_card hsub
  have hsize : T.card = m := (Finset.mem_powersetCard.mp hT).2
  unfold SAP.P002a.W2K
  simpa [hsize] using hc

private theorem q_sq_le_one {m : ℕ} (hm : 2 ≤ m) {T : Finset (Fin (2*m))}
    (hT : T ∈ SAP.P002a.assignments (SAP.P002a.signModel m)) :
    SAP.P002a.W2q m T ^ 2 ≤ 1 := by
  have hk := K_bounds hT
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hk0 : (0 : ℝ) ≤ (SAP.P002a.W2K m T : ℝ) := Nat.cast_nonneg _
  have hkm : (SAP.P002a.W2K m T : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
  have hqlo : -1 ≤ SAP.P002a.W2q m T := by
    unfold SAP.P002a.W2q
    apply (le_div_iff₀ hmpos).2
    linarith
  have hqhi : SAP.P002a.W2q m T ≤ 1 := by
    unfold SAP.P002a.W2q
    apply (div_le_iff₀ hmpos).2
    linarith
  nlinarith [mul_nonneg (show 0 ≤ 1 - SAP.P002a.W2q m T by linarith)
    (show 0 ≤ 1 + SAP.P002a.W2q m T by linarith)]

private theorem q_support_gap {m : ℕ} (hm : 2 ≤ m) {T : Finset (Fin (2*m))}
    (hT : T ∈ SAP.P002a.assignments (SAP.P002a.signModel m))
    (hne : SAP.P002a.W2q m T ^ 2 ≠ 1) :
    8 * ((2*m : ℕ) - (2 : ℝ)) / (2*m : ℕ)^2 ≤ 1-SAP.P002a.W2q m T^2 := by
  have hk := K_bounds hT
  have hk0 : 0 ≤ SAP.P002a.W2K m T := Nat.zero_le _
  have hinterior : 1 ≤ SAP.P002a.W2K m T ∧ SAP.P002a.W2K m T < m := by
    by_contra h
    have hend : SAP.P002a.W2K m T = 0 ∨ SAP.P002a.W2K m T = m := by omega
    rcases hend with hzero | hfull
    · apply hne
      unfold SAP.P002a.W2q
      rw [hzero]
      have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
      field_simp
      ring
    · apply hne
      unfold SAP.P002a.W2q
      rw [hfull]
      have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
      field_simp
      ring
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hprod : (m : ℝ)-1 ≤ (SAP.P002a.W2K m T : ℝ) *
      ((m : ℝ)-(SAP.P002a.W2K m T : ℝ)) := by
    have hkloR : 1 ≤ (SAP.P002a.W2K m T : ℝ) := by exact_mod_cast hinterior.1
    have hkhiR : (SAP.P002a.W2K m T : ℝ)+1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.lt_iff_add_one_le.mp hinterior.2)
    have hleft : 0 ≤ (SAP.P002a.W2K m T : ℝ)-1 := by linarith
    have hright : 0 ≤ ((m : ℝ)-(SAP.P002a.W2K m T : ℝ))-1 := by linarith
    have := mul_nonneg hleft hright
    nlinarith
  have hident : 1-SAP.P002a.W2q m T^2 =
      4*(SAP.P002a.W2K m T : ℝ)*((m : ℝ)-(SAP.P002a.W2K m T : ℝ))/(m : ℝ)^2 := by
    unfold SAP.P002a.W2q
    field_simp
    ring
  have hsmall : 4*((m : ℝ)-1)/(m : ℝ)^2 ≤
      4*(SAP.P002a.W2K m T : ℝ)*((m : ℝ)-(SAP.P002a.W2K m T : ℝ))/(m : ℝ)^2 := by
    apply (div_le_div_of_nonneg_right ?_ (sq_nonneg (m : ℝ)))
    nlinarith
  have hnR : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
  have hscale :
      8*((2*m : ℕ) - (2 : ℝ))/(2*m : ℕ)^2 = 4*((m : ℝ)-1)/(m : ℝ)^2 := by
    rw [hnR]
    field_simp
    ring
  rw [hscale, hident]
  exact hsmall

end SAP.P002a.WH.W2.P.T14_L3

open SAP.P002a.WH.W2.P.T14_L3

theorem SAP.P002a.WH.W2.T14_L3_proof : SAP.P002a.WH.W2.T14_L3 := by
  intro hL2
  intro m hm
  have h := hL2 m hm
  rcases h with ⟨hobs, hqE, hvar, hform⟩
  have hvalid : SAP.P002a.ValidDesign (SAP.P002a.signModel m) := by
    change 2 ≤ 2*m ∧ 0 < m ∧ m < 2*m
    omega
  have hmR : 2 ≤ (m : ℝ) := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < (2*m : ℕ) := by exact_mod_cast (by omega : 0 < 2*m)
  have hnne : ((2*m : ℕ) : ℝ) ≠ 0 := ne_of_gt hnpos
  refine ⟨hobs, hqE, hvar, ?_, ?_⟩
  · intro T hT
    have hF := hform T hT
    rcases hF with ⟨hmean, hsigma, hU, hR⟩
    have hq2 : SAP.P002a.W2q m T^2 ≤ 1 := q_sq_le_one hm hT
    have hq0 : 0 ≤ 1-SAP.P002a.W2q m T^2 := by linarith
    refine ⟨hmean, hsigma, hU, hR, ?_, ?_, ?_⟩
    · intro heq
      rw [hU, heq]
      simp
    · intro hne
      refine ⟨q_support_gap hm hT hne, ?_⟩
      have hnR : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
      have hsZ : Real.sqrt (1-SAP.P002a.W2q m T^2)^2 = 1-SAP.P002a.W2q m T^2 :=
        Real.sq_sqrt hq0
      have hnR : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
      have hgap : 8*((2*(m : ℝ))-2)/(2*(m : ℝ))^2 ≤
          1-SAP.P002a.W2q m T^2 := by
        simpa only [hnR] using q_support_gap hm hT hne
      have hcoefpos : 0 < 2*((2*(m : ℝ))-1)/Real.sqrt (2*(m : ℝ)) := by
        apply div_pos
        · nlinarith
        · exact Real.sqrt_pos.2 (by nlinarith)
      have hsquare : 9 ≤
          (2*((2*(m : ℝ))-1)/Real.sqrt (2*(m : ℝ)) *
            Real.sqrt (1-SAP.P002a.W2q m T^2))^2 := by
        rw [mul_pow, div_pow, hsZ]
        have hcoef : (2*((2*(m : ℝ))-1))^2 /
            (Real.sqrt (2*(m : ℝ)))^2 =
            4*((2*(m : ℝ))-1)^2/(2*(m : ℝ)) := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ (2*(m : ℝ)))]
          ring
        rw [hcoef]
        have hmain : 9 ≤ 8*(2*(m : ℝ)-1)^2*((m : ℝ)-1)/(m : ℝ)^3 := by
          have hquad : 0 ≤ 23*(m : ℝ)^2-18*(m : ℝ)+4 := by
            nlinarith [sq_nonneg ((m : ℝ)-1)]
          have hfact : 0 ≤ ((m : ℝ)-2)*(23*(m : ℝ)^2-18*(m : ℝ)+4) :=
            mul_nonneg (by linarith) hquad
          have hpoly : 8*(2*(m : ℝ)-1)^2*((m : ℝ)-1)-9*(m : ℝ)^3 =
              ((m : ℝ)-2)*(23*(m : ℝ)^2-18*(m : ℝ)+4) := by ring
          apply (le_div_iff₀ (by positivity : 0 < (m : ℝ)^3)).2
          nlinarith [hpoly, hfact]
        have hfactor : 0 ≤ 4*((2*(m : ℝ))-1)^2/(2*(m : ℝ)) := by positivity
        have hbound :
            4*((2*(m : ℝ))-1)^2/(2*(m : ℝ)) *
              (8*((2*(m : ℝ))-2)/(2*(m : ℝ))^2) =
            8*(2*(m : ℝ)-1)^2*((m : ℝ)-1)/(m : ℝ)^3 := by
          field_simp
          ring
        calc
          9 ≤ 8*(2*(m : ℝ)-1)^2*((m : ℝ)-1)/(m : ℝ)^3 := hmain
          _ = 4*((2*(m : ℝ))-1)^2/(2*(m : ℝ)) *
              (8*((2*(m : ℝ))-2)/(2*(m : ℝ))^2) := hbound.symm
          _ ≤ 4*((2*(m : ℝ))-1)^2/(2*(m : ℝ)) *
              (1-SAP.P002a.W2q m T^2) := mul_le_mul_of_nonneg_left hgap hfactor
      have hUform : SAP.P002a.W2U m T =
          2*((2*(m : ℝ))-1)/Real.sqrt (2*(m : ℝ)) *
            Real.sqrt (1-SAP.P002a.W2q m T^2) := by
        simpa only [hnR] using hU
      rw [hUform]
      have hsqrtpos : 0 ≤ Real.sqrt (1-SAP.P002a.W2q m T^2) := Real.sqrt_nonneg _
      have hprodpos : 0 ≤ 2*((2*(m : ℝ))-1)/Real.sqrt (2*(m : ℝ)) *
          Real.sqrt (1-SAP.P002a.W2q m T^2) := mul_nonneg (le_of_lt hcoefpos) hsqrtpos
      nlinarith
    · constructor
      · rw [hR]
        have hnR : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
        have hcoef0 : 0 ≤ (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ) := by
          rw [hnR]
          apply div_nonneg
          · linarith
          · positivity
        have hcoef1 : (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ) ≤ 1 := by
          rw [hnR]
          apply (div_le_one (by positivity)).2
          linarith
        have hmul0 := mul_nonneg hcoef0 hq0
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul0
      · rw [hR]
        have hnR : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
        have hcoef0 : 0 ≤ (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ) := by
          rw [hnR]
          apply div_nonneg
          · linarith
          · positivity
        have hcoef1 : (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ) ≤ 1 := by
          rw [hnR]
          apply (div_le_one (by positivity)).2
          linarith
        have hmul : (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ) *
            (1-SAP.P002a.W2q m T^2) ≤ 1 := by
          have hzle : 1-SAP.P002a.W2q m T^2 ≤ 1 := by
            nlinarith [sq_nonneg (SAP.P002a.W2q m T)]
          calc
            _ ≤ 1*1 := mul_le_mul hcoef1 hzle hq0 (by norm_num)
            _ = 1 := by ring
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hpoint (T : Finset (Fin (2*m))) (hT : T ∈ SAP.P002a.assignments (SAP.P002a.signModel m)) :
        1-SAP.P002a.W2R m T = 1/((2*m : ℕ) : ℝ) +
          (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ)*SAP.P002a.W2q m T^2 := by
      have hR := (hform T hT).2.2.2
      rw [hR]
      field_simp [hnne]
      ring
    let PA := SAP.P002a.Bridge.toPopulation (SAP.P002a.signModel m)
    have hvalidA : AronowAudit.P002.ValidDesign PA := by
      simpa only [SAP.P002a.Bridge.validDesign_eq] using hvalid
    have hqEA : AronowAudit.P002.expectation PA (fun T => SAP.P002a.W2q m T^2) =
        1/((2*m : ℕ)-(1 : ℝ)) := by
      simpa only [SAP.P002a.Bridge.expectation_eq] using hqE
    have hpointA (T : Finset (Fin (2*m)))
        (hT : T ∈ AronowAudit.P002.assignments PA) :
        1-SAP.P002a.W2R m T = 1/((2*m : ℕ) : ℝ) +
          (((2*m : ℕ) : ℝ)-1)/((2*m : ℕ) : ℝ)*SAP.P002a.W2q m T^2 := by
      apply hpoint T
      simpa only [SAP.P002a.Bridge.assignments_eq] using hT
    change AronowAudit.P002.expectation PA (fun T => 1-SAP.P002a.W2R m T) = _
    rw [AronowAudit.P002.Wave1.DecisionLemma12_expectation_congr PA hpointA]
    rw [AronowAudit.P002.Wave1.DecisionLemma12_expectation_add,
      AronowAudit.P002.expectation_const PA hvalidA,
      AronowAudit.P002.expectation_mul]
    rw [hqEA]
    have hnR : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
    have hmden : ((2*m : ℕ) : ℝ)-1 ≠ 0 := by rw [hnR]; linarith
    field_simp [hnne, hmden]
    ring
