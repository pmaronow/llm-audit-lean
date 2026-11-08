import SAP.P027a.WH.W1.Leaves
import AronowAudit.P027.P027_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section
open SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

theorem SAP.P027a.WH.W1.T2_L1_proof : SAP.P027a.WH.W1.T2_L1 := by
  intro r m hr hm z hz
  dsimp only
  let D := SAP.P027a.phaseOriginal r m hr
  let Y := SAP.P027a.groupTotal (fun _ : Fin r × Fin 2 => m) z
  let S := ∑ g, Y g^2
  let N : ℝ := (m:ℝ)*(2*r)
  let B := SAP.P027a.expect D
      (fun ω => SAP.P027a.htVarianceEstimator D z ω/N^2) -
    SAP.P027a.variance D (SAP.P027a.htMean D z)
  rcases SAP.P027a.WH.W1.periodic_bias_core r m hr hm z hz with
    ⟨hYraw, hAraw, hSraw, hSeqraw, _, hvar, hexpect, _, _, _⟩
  have hY : (∑ g, Y g) = 0 := by
    simpa only [Y] using hYraw
  have hAneg : SAP.P027a.biasA D z = -S := by
    simpa only [D, Y, S] using hAraw
  have hSnonneg : 0 ≤ S := by
    simpa only [Y, S] using hSraw
  have hSeq : S = 0 ↔ ∀ g, Y g = 0 := by
    simpa only [Y, S] using hSeqraw
  have hcross : SAP.P027a.biasA D z =
      ∑ g, ∑ h, if g ≠ h then Y g * Y h else 0 := by
    calc
      SAP.P027a.biasA D z = -S := hAneg
      _ = ∑ g, ∑ h, if g ≠ h then Y g * Y h else 0 := by
        convert (AronowAudit.P027.centered_cross_products Y hY).symm using 1
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro h _
        congr 1
  have hAform : SAP.P027a.biasA D z = (∑ g, Y g)^2 - S := by
    rw [hAneg, hY]
    ring
  have hAzero : SAP.P027a.biasA D z = 0 ↔ ∀ g, Y g = 0 := by
    rw [hAneg]
    constructor
    · intro h
      apply hSeq.mp
      linarith
    · intro h
      have hs := hSeq.mpr h
      linarith
  have hE : SAP.P027a.expect D (SAP.P027a.htVarianceEstimator D z) =
        ∑ g, (1 / SAP.P027a.phaseProb r g - 1) * Y g^2 := by
    rw [hexpect, hvar]
    calc
      (∑ g, Y g^2 / SAP.P027a.phaseProb r g) - S =
          ∑ g, (Y g^2 / SAP.P027a.phaseProb r g - Y g^2) := by
        simp only [S]
        rw [← Finset.sum_sub_distrib]
      _ = ∑ g, (1 / SAP.P027a.phaseProb r g - 1) * Y g^2 := by
        apply Finset.sum_congr rfl
        intro g _
        ring
  have hcard : (Fintype.card (Σ _ : Fin r × Fin 2, Fin m) : ℝ) = N := by
    dsimp [N]
    simp [Fintype.card_sigma, Fintype.card_prod]
    ring
  let AD := AronowAudit.P027.phaseOriginal r m hr
  have hvld : SAP.P027a.Valid D := (SAP.P027a.Bridge.periodic_inclusions r m hr).1
  have hAD : SAP.P027a.Bridge.toAudit D hvld = AD := by
    rfl
  have hAbridge : SAP.P027a.biasA D z = AronowAudit.P027.biasA AD z := by
    calc
      SAP.P027a.biasA D z =
          AronowAudit.P027.biasA (SAP.P027a.Bridge.toAudit D hvld) z :=
            SAP.P027a.Bridge.bias_eq D hvld z
      _ = AronowAudit.P027.biasA AD z := by rw [hAD]
  have hexpectScale : SAP.P027a.expect D
        (fun ω => SAP.P027a.htVarianceEstimator D z ω/N^2) =
      AronowAudit.P027.expect AD
        (fun ω => AronowAudit.P027.htVarianceEstimator AD z ω/N^2) := by
    calc
      SAP.P027a.expect D
          (fun ω => SAP.P027a.htVarianceEstimator D z ω/N^2) =
        AronowAudit.P027.expect (SAP.P027a.Bridge.toAudit D hvld)
          (fun ω => SAP.P027a.htVarianceEstimator D z ω/N^2) :=
            SAP.P027a.Bridge.expect_eq D hvld _
      _ = AronowAudit.P027.expect AD
          (fun ω => AronowAudit.P027.htVarianceEstimator AD z ω/N^2) := by
        rw [← hAD]
        congr 1
  have hmeanFun : SAP.P027a.htMean D z =
      AronowAudit.P027.htMean (SAP.P027a.Bridge.toAudit D hvld) z := by
    funext ω
    rw [SAP.P027a.htMean, AronowAudit.P027.htMean,
      SAP.P027a.Bridge.total_eq D hvld z]
  have hvarScale : SAP.P027a.variance D (SAP.P027a.htMean D z) =
      AronowAudit.P027.variance AD (AronowAudit.P027.htMean AD z) := by
    rw [SAP.P027a.Bridge.variance_eq D hvld, ← hAD, hmeanFun]
  have hpa : AronowAudit.P027.Positive AD := by
    simpa only [AD] using AronowAudit.P027.phaseOriginal_positive r m hr
  have hmeanAudit : AronowAudit.P027.expect AD
        (fun ω => AronowAudit.P027.htVarianceEstimator AD z ω/N^2) -
      AronowAudit.P027.variance AD (AronowAudit.P027.htMean AD z) =
        AronowAudit.P027.biasA AD z/N^2 := by
    have hh := AronowAudit.P027.mean_bias_identity AD hpa z
    rw [hcard] at hh
    exact hh
  have hmean : B = SAP.P027a.biasA D z/N^2 := by
    dsimp [B]
    rw [hexpectScale, hvarScale, hmeanAudit, hAbridge]
  have hBneg : B = -S/N^2 := by
    rw [hmean, hAneg]
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hBnonpos : B ≤ 0 := by
    rw [hBneg]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr hSnonneg
    · positivity
  have hBzero : B = 0 ↔ ∀ g, Y g = 0 := by
    rw [hBneg]
    have hden : N^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hN)
    constructor
    · intro h
      have hs : S = 0 := by
        have hh := (div_eq_zero_iff).mp h
        rcases hh with hh | hh
        · linarith
        · exact False.elim (hden hh)
      exact hSeq.mp hs
    · intro h
      have hs := hSeq.mpr h
      have hs' : S = 0 := by simpa only [Y, S] using hs
      rw [hs']
      simp
  refine ⟨hcross, hAform, ?_, hAzero, hE, hmean, hBneg, hBnonpos, hBzero⟩
  rw [hAneg]
  exact neg_nonpos.mpr hSnonneg
