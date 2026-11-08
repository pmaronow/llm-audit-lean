import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T14_L2

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

theorem sign_sum_zero (m : ℕ) :
    (∑ i : Fin (2*m), SAP.P002a.W2sign m i) = 0 := by
  have h : (∑ i : Fin (m+m), if i.val < m then (-1 : ℝ) else 1) = 0 := by
    rw [Fin.sum_univ_add]
    have hl (i : Fin m) : (Fin.castAdd m i).val < m := i.isLt
    have hr (i : Fin m) : ¬ (Fin.natAdd m i).val < m := by
      change ¬ m + i.val < m
      omega
    simp only [hl, hr, if_true, if_false, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  change (∑ i : Fin (2*m), if i.val < m then (-1 : ℝ) else 1) = 0
  rw [two_mul]
  exact h

theorem sign_sq (m : ℕ) (i : Fin (2*m)) :
    SAP.P002a.W2sign m i ^ 2 = 1 := by
  dsimp [SAP.P002a.W2sign, signModel]
  split_ifs <;> norm_num

theorem sign_centered_sum (m : ℕ) (S : Finset (Fin (2*m)))
    (hS : S.Nonempty) :
    (∑ i ∈ S, (SAP.P002a.W2sign m i - groupMean S (SAP.P002a.W2sign m))^2) =
      (S.card : ℝ) * (1-(groupMean S (SAP.P002a.W2sign m))^2) := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  have hsecond : groupMean S (fun i => SAP.P002a.W2sign m i ^ 2) = 1 := by
    simp [groupMean, sign_sq m, hc]
  have hcentD := AronowAudit.P002.square_centering S (SAP.P002a.W2sign m) 0 hS
  have hcent : groupMean S (fun i => (SAP.P002a.W2sign m i -
      groupMean S (SAP.P002a.W2sign m))^2) =
      groupMean S (fun i => (SAP.P002a.W2sign m i-0)^2) -
        (groupMean S (SAP.P002a.W2sign m)-0)^2 := by
    simpa only [SAP.P002a.Bridge.groupMean_eq] using hcentD
  simp only [sub_zero] at hcent
  rw [hsecond] at hcent
  change (∑ i ∈ S, (SAP.P002a.W2sign m i - groupMean S (SAP.P002a.W2sign m))^2) /
      (S.card : ℝ) = 1-(groupMean S (SAP.P002a.W2sign m))^2 at hcent
  have hout := (div_eq_iff hc).mp hcent
  calc
    _ = (1-groupMean S (SAP.P002a.W2sign m)^2) * (S.card : ℝ) := hout
    _ = (S.card : ℝ) * (1-groupMean S (SAP.P002a.W2sign m)^2) := by ring

theorem observed_sign (m : ℕ) (O : Finset (Fin (2*m))) :
    observedW (signModel m) 0 O = SAP.P002a.W2sign m := by
  funext i
  simp [observedW, observedY, observedD, SAP.P002a.W2sign, signModel]

theorem positive_count_sum (m : ℕ) (T : Finset (Fin (2*m)))
    (hT : T ∈ assignments (signModel m)) :
    (∑ i ∈ T, SAP.P002a.W2sign m i) =
      2*(SAP.P002a.W2K m T : ℝ)-(m : ℝ) := by
  have hcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
  have hc : (T.filter (fun i => m ≤ i.val)).card +
      (T.filter (fun i => ¬ m ≤ i.val)).card = m := by
    have h := T.card_filter_add_card_filter_not (fun i => m ≤ i.val)
    rw [hcard] at h
    exact h
  have hsign : SAP.P002a.W2sign m = fun i => if m ≤ i.val then (1 : ℝ) else -1 := by
    funext i
    by_cases h : i.val < m
    · have hnot : ¬ m ≤ i.val := by omega
      simp [SAP.P002a.W2sign, signModel, h, hnot]
    · have hge : m ≤ i.val := by omega
      simp [SAP.P002a.W2sign, signModel, h, hge]
  rw [hsign]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (SAP.P002a.W2K m T : ℝ) * 1 +
      ((T.filter (fun i => ¬ m ≤ i.val)).card : ℝ) * (-1) = _
  have hcR : (SAP.P002a.W2K m T : ℝ) +
      ((T.filter (fun i => ¬ m ≤ i.val)).card : ℝ) = (m : ℝ) := by
    exact_mod_cast hc
  unfold SAP.P002a.W2K at hcR ⊢
  nlinarith

theorem sign_arm_mean (m : ℕ) (hm : 0 < m) (T : Finset (Fin (2*m)))
    (hT : T ∈ assignments (signModel m)) :
    armMean (SAP.P002a.W2sign m) T true = SAP.P002a.W2q m T := by
  have hcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [armMean, if_true, groupMean]
  rw [positive_count_sum m T hT, hcard]
  unfold SAP.P002a.W2q
  field_simp [hmR]
  <;> ring

theorem sign_control_mean (m : ℕ) (hm : 0 < m) (T : Finset (Fin (2*m)))
    (hT : T ∈ assignments (signModel m)) :
    armMean (SAP.P002a.W2sign m) T false = -SAP.P002a.W2q m T := by
  have hcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
  have hcomp : (Tᶜ).card = m := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  have hsum := AronowAudit.P002.sum_complement_eq T (SAP.P002a.W2sign m)
  rw [sign_sum_zero m] at hsum
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [armMean, Bool.false_eq_true, ite_false, groupMean]
  rw [hsum, positive_count_sum m T hT, hcomp]
  unfold SAP.P002a.W2q
  field_simp [hmR]
  <;> ring

theorem sign_sigma (m : ℕ) (hm2 : 2 ≤ m) (T : Finset (Fin (2*m)))
    (hT : T ∈ assignments (signModel m)) :
    rawSigma2 (signModel m) (SAP.P002a.W2sign m) T =
      (1-SAP.P002a.W2q m T^2)/(4*((2*m : ℕ) : ℝ)) := by
  have hcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
  have hcomp : (Tᶜ).card = m := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  have htne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hcne : (Tᶜ).Nonempty := Finset.card_pos.mp (by omega)
  have htss := sign_centered_sum m T htne
  have hcss := sign_centered_sum m Tᶜ hcne
  have hmpos : 0 < m := by omega
  have hmeanT := sign_arm_mean m hmpos T hT
  have hmeanC := sign_control_mean m hmpos T hT
  have hgmT : groupMean T (SAP.P002a.W2sign m) = SAP.P002a.W2q m T := by
    simpa only [armMean, if_true] using hmeanT
  have hgmC : groupMean Tᶜ (SAP.P002a.W2sign m) = -SAP.P002a.W2q m T := by
    simpa only [armMean, Bool.false_eq_true, ite_false] using hmeanC
  have htss' : (∑ i ∈ T, (SAP.P002a.W2sign m i - armMean (SAP.P002a.W2sign m) T true)^2) =
      (m : ℝ)*(1-SAP.P002a.W2q m T^2) := by
    rw [hmeanT]
    simpa [hgmT, hcard] using htss
  have hcss' : (∑ i ∈ Tᶜ, (SAP.P002a.W2sign m i - armMean (SAP.P002a.W2sign m) T false)^2) =
      (m : ℝ)*(1-SAP.P002a.W2q m T^2) := by
    rw [hmeanC]
    simpa [hgmC, hcomp] using hcss
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN : (0 : ℝ) < (2*m : ℕ) := by exact_mod_cast (show 0 < 2*m by omega)
  rw [rawSigma2, htss', hcss']
  simp [fraction, controlSize, signModel, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hm, ne_of_gt hN]
  <;> ring

theorem sign_q_sq_le_one (m : ℕ) (hm : 2 ≤ m)
    (T : Finset (Fin (2*m))) (hT : T ∈ assignments (signModel m)) :
    SAP.P002a.W2q m T ^ 2 ≤ 1 := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hKle : SAP.P002a.W2K m T ≤ m := by
    unfold SAP.P002a.W2K
    exact (Finset.card_filter_le _ _).trans (Finset.mem_powersetCard.mp hT).2.le
  have hKlo : 0 ≤ (SAP.P002a.W2K m T : ℝ) := Nat.cast_nonneg _
  have hKhi : (SAP.P002a.W2K m T : ℝ) ≤ m := by exact_mod_cast hKle
  have hqlo : -1 ≤ SAP.P002a.W2q m T := by
    unfold SAP.P002a.W2q
    apply (le_div_iff₀ hmpos).2
    push_cast
    nlinarith
  have hqhi : SAP.P002a.W2q m T ≤ 1 := by
    unfold SAP.P002a.W2q
    apply (div_le_iff₀ hmpos).2
    push_cast
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hqhi) (by linarith : 0 ≤ 1+SAP.P002a.W2q m T)]

end
end SAP.P002a.WH.W2.P.T14_L2

open SAP.P002a
open SAP.P002a.WH.W2
open SAP.P002a.WH.W2.P.T14_L2
open SAP.P002a.Bridge

theorem SAP.P002a.WH.W2.T14_L2_proof : SAP.P002a.WH.W2.T14_L2 := by
  intro m hm
  let P := signModel m
  have hvalid : ValidDesign P := by
    dsimp [P, ValidDesign, signModel]
    omega
  have hmean : mean (SAP.P002a.W2sign m) = 0 := by
    rw [mean, sign_sum_zero m]
    simp
  have hobs (O : Finset (Fin (2*m))) :
      observedW P 0 O = SAP.P002a.W2sign m := by
    exact observed_sign m O
  have hcountMoment :
      expectation P (fun T => SAP.P002a.W2q m T^2) =
        1/(((2*m : ℕ) : ℝ)-1) := by
    have hvalidD : AronowAudit.P002.ValidDesign (toPopulation P) := by
      simpa only [SAP.P002a.Bridge.validDesign_eq] using hvalid
    have hsmD := AronowAudit.P002.Wave1.sample_mean_variance_proof (toPopulation P) hvalidD
      (SAP.P002a.W2sign m)
    have hsm : expectation P (fun S =>
        (groupMean S (SAP.P002a.W2sign m)-mean (SAP.P002a.W2sign m))^2) =
        controlSize P / ((P.n1 : ℝ) * ((2*m : ℕ) : ℝ) * (((2*m : ℕ) : ℝ)-1)) *
          ∑ i, (SAP.P002a.W2sign m i-mean (SAP.P002a.W2sign m))^2 := by
      simpa [SAP.P002a.Bridge.expectation_eq, SAP.P002a.Bridge.groupMean_eq,
        SAP.P002a.Bridge.mean_eq, SAP.P002a.controlSize, AronowAudit.P002.controlSize,
        toPopulation] using hsmD
    have hsumSq : (∑ i, SAP.P002a.W2sign m i^2) = (2*m : ℕ) := by
      simp [sign_sq]
    have hfactor :
        controlSize P / ((P.n1 : ℝ) * ((2*m : ℕ) : ℝ) * (((2*m : ℕ) : ℝ)-1)) *
          (2*m : ℕ) = 1/(((2*m : ℕ) : ℝ)-1) := by
      dsimp [P, controlSize, signModel]
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hNR : (((2*m : ℕ) : ℝ)-1) ≠ 0 := by
        have : (4 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast (show 4 ≤ 2*m by omega)
        linarith
      push_cast
      field_simp [hmR, hNR]
      <;> ring
    have hgroup : expectation P (fun T => (groupMean T (SAP.P002a.W2sign m))^2) =
        1/(((2*m : ℕ) : ℝ)-1) := by
      rw [hmean] at hsm
      simp only [sub_zero] at hsm
      rw [hsumSq, hfactor] at hsm
      exact hsm
    have hcongr : expectation P (fun T => SAP.P002a.W2q m T^2) =
        expectation P (fun T => (groupMean T (SAP.P002a.W2sign m))^2) := by
      unfold expectation
      congr 1
      apply Finset.sum_congr rfl
      intro T hT
      have ha : SAP.P002a.W2q m T = groupMean T (SAP.P002a.W2sign m) := by
        simpa only [armMean, if_true] using (sign_arm_mean m (by omega) T hT).symm
      exact congrArg (fun z : ℝ => z^2) ha
    rw [hcongr, hgroup]
  have hnonempty : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa [P, signModel] using (show m ≤ 2*m by omega)
  have ⟨T₀, hT₀⟩ := hnonempty
  have hdonor := (AronowAudit.P002.Wave1.missing_square_counterexample_proof.1 m hm)
  rcases hdonor with ⟨_, _, hdonorVariance⟩
  have hvariance : designVariance P (rawTau P (SAP.P002a.W2sign m)) =
      1/(4*(((2*m : ℕ) : ℝ)-1)) := by
    have hT₀D : T₀ ∈ AronowAudit.P002.assignments (AronowAudit.P002.signModel m) := by
      change T₀ ∈ Finset.univ.powersetCard m at hT₀ ⊢
      exact hT₀
    have h := hdonorVariance T₀ hT₀D
    rcases h with ⟨hV, _, _⟩
    have hV' : AronowAudit.P002.designVariance (AronowAudit.P002.signModel m)
        (AronowAudit.P002.rawTau (AronowAudit.P002.signModel m)
          (AronowAudit.P002.observedW (AronowAudit.P002.signModel m) 0 T₀)) =
        1/(4*(((2*m : ℕ) : ℝ)-1)) := hV
    have hbridge := congrFun (SAP.P002a.Bridge.observedW_eq (signModel m) 0) T₀
    rw [observed_sign m T₀] at hbridge
    have hobsD : AronowAudit.P002.observedW (AronowAudit.P002.signModel m) 0 T₀ =
        SAP.P002a.W2sign m := by
      simpa [SAP.P002a.signModel, AronowAudit.P002.signModel, toPopulation] using hbridge.symm
    rw [hobsD] at hV'
    have hVto : AronowAudit.P002.designVariance (toPopulation P)
        (AronowAudit.P002.rawTau (toPopulation P) (SAP.P002a.W2sign m)) =
        1/(4*(((2*m : ℕ) : ℝ)-1)) := by
      simpa [P, SAP.P002a.signModel, AronowAudit.P002.signModel, toPopulation] using hV'
    simpa only [SAP.P002a.Bridge.designVariance_eq, SAP.P002a.Bridge.rawTau_eq] using hVto
  have hvariance_pos : 0 < designVariance P (rawTau P (SAP.P002a.W2sign m)) := by
    rw [hvariance]
    have hN1 : (0 : ℝ) < ((2*m : ℕ) : ℝ)-1 := by
      have hN4 : (4 : ℝ) ≤ (2*m : ℕ) := by
        exact_mod_cast (show 4 ≤ 2*m by omega)
      linarith
    exact div_pos one_pos (mul_pos (by norm_num) hN1)
  refine ⟨?_, hcountMoment, hvariance_pos, ?_⟩
  · intro O hO
    exact hobs O
  · intro T hT
    refine ⟨sign_arm_mean m (by omega) T hT, sign_sigma m hm T hT, ?_, ?_⟩
    · have hq := sign_q_sq_le_one m hm T hT
      have hqnonneg : 0 ≤ 1-SAP.P002a.W2q m T^2 := by nlinarith
      have hN : 0 < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
      have hN1 : 0 < ((2*m : ℕ) : ℝ)-1 := by
        have : (4 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast (show 4 ≤ 2*m by omega)
        linarith
      have hsqrtN : Real.sqrt (4*((2*m : ℕ) : ℝ)) = 2*Real.sqrt ((2*m : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num)]
        norm_num
      change Real.sqrt (rawSigma2 P (SAP.P002a.W2sign m) T) /
          designVariance P (rawTau P (SAP.P002a.W2sign m)) = _
      rw [sign_sigma m hm T hT, hvariance, Real.sqrt_div hqnonneg, hsqrtN]
      field_simp [ne_of_gt hN, ne_of_gt hN1, ne_of_gt (Real.sqrt_pos.2 hN)]
      <;> ring
    · change rawSigma2 P (SAP.P002a.W2sign m) T /
          designVariance P (rawTau P (SAP.P002a.W2sign m)) = _
      rw [sign_sigma m hm T hT, hvariance]
      have hN : (((2*m : ℕ) : ℝ)) ≠ 0 := by
        have : 0 < (2*m : ℕ) := by omega
        exact_mod_cast this.ne'
      have hN1 : (((2*m : ℕ) : ℝ)-1) ≠ 0 := by
        have : (4 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast (show 4 ≤ 2*m by omega)
        linarith
      field_simp [hN, hN1]
      <;> ring

