import SAP.P005b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.WH.W1.P.T17_L1

open scoped BigOperators Matrix
open Finset

private theorem sum_covariate_centered {n d : ℕ} (P : SAP.P005b.Population n d)
    (hn : 0 < n) (hP : SAP.P005b.standardized P) (k : Fin d) :
    ∑ i, P.x i k = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hk := congrArg (fun v : Fin d → ℝ => v k) hP.1
  have hz : (∑ i, P.x i k) / (n : ℝ) = 0 := by
    simpa [SAP.P005b.xMean, SAP.P005b.mean] using hk
  exact (div_eq_zero_iff.mp hz).resolve_right hn0

private theorem kernel_row_sum {n d : ℕ} (P : SAP.P005b.Population n d)
    (hn : 0 < n) (δ : Fin n → ℝ) (i : Fin n) :
    ∑ j, SAP.P005b.wholeW1Kernel P δ i j = 0 := by
  dsimp only [SAP.P005b.wholeW1Kernel, SAP.P005b.dot]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  change (∑ j, P.x i k * (P.x j k * δ j - SAP.P005b.populationSlope P δ k)) = 0
  rw [← Finset.mul_sum]
  have hs : ∑ j, (P.x j k * δ j - SAP.P005b.populationSlope P δ k) = 0 := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hsl : SAP.P005b.populationSlope P δ k =
        (∑ j, δ j * P.x j k) / (n : ℝ) := by
      simp [SAP.P005b.populationSlope, SAP.P005b.popMean, SAP.P005b.mean]
    have hcomm : (∑ j, P.x j k * δ j) = ∑ j, δ j * P.x j k := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsl]
    field_simp [hn0]
    rw [hcomm]
    ring
  rw [hs]
  simp

private theorem kernel_column_sum {n d : ℕ} (P : SAP.P005b.Population n d)
    (hn : 0 < n) (hP : SAP.P005b.standardized P) (δ : Fin n → ℝ) (j : Fin n) :
    ∑ i, SAP.P005b.wholeW1Kernel P δ i j = 0 := by
  dsimp only [SAP.P005b.wholeW1Kernel, SAP.P005b.dot]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  change (∑ i, P.x i k * (P.x j k * δ j - SAP.P005b.populationSlope P δ k)) = 0
  rw [← Finset.sum_mul, sum_covariate_centered P hn hP k]
  simp

private theorem kernel_trace {n d : ℕ} (P : SAP.P005b.Population n d)
    (hn : 0 < n) (hP : SAP.P005b.standardized P) (δ : Fin n → ℝ) :
    (∑ i, SAP.P005b.wholeW1Kernel P δ i i) =
      (n : ℝ) * SAP.P005b.popMean (fun i => SAP.P005b.leverage P i * δ i) := by
  have hdot : ∑ i, SAP.P005b.dot (P.x i) (SAP.P005b.populationSlope P δ) = 0 := by
    unfold SAP.P005b.dot
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    change (∑ i, P.x i k * SAP.P005b.populationSlope P δ k) = 0
    rw [← Finset.sum_mul, sum_covariate_centered P hn hP k]
    simp
  have hentry (i : Fin n) :
      SAP.P005b.dot (P.x i) (fun k => P.x i k * δ i - SAP.P005b.populationSlope P δ k) =
        SAP.P005b.leverage P i * δ i - SAP.P005b.dot (P.x i) (SAP.P005b.populationSlope P δ) := by
    change (∑ k, P.x i k * (P.x i k * δ i - SAP.P005b.populationSlope P δ k)) = _
    unfold SAP.P005b.leverage SAP.P005b.dot
    calc
      _ = ∑ k, (P.x i k * P.x i k * δ i -
          P.x i k * SAP.P005b.populationSlope P δ k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (∑ k, P.x i k * P.x i k) * δ i -
          ∑ k, P.x i k * SAP.P005b.populationSlope P δ k := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  calc
    _ = ∑ i, (SAP.P005b.leverage P i * δ i -
        SAP.P005b.dot (P.x i) (SAP.P005b.populationSlope P δ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [SAP.P005b.wholeW1Kernel] using hentry i
    _ = ∑ i, SAP.P005b.leverage P i * δ i := by rw [Finset.sum_sub_distrib, hdot, sub_zero]
    _ = (n : ℝ) * SAP.P005b.popMean (fun i => SAP.P005b.leverage P i * δ i) := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      simp only [SAP.P005b.popMean, SAP.P005b.mean, Finset.card_univ, Fintype.card_fin]
      field_simp [hn0]

private theorem treated_principal_expansion {n d m : ℕ}
    (P : AronowAudit.P005.Population n d) (hn : 0 < n) (hm : 0 < m) (hmn : m < n)
    (S : Finset (Fin n)) (hS : S.card = m) (δ : Fin n → ℝ) :
    (1 / AronowAudit.P005.pC n m) * AronowAudit.P005.dot (AronowAudit.P005.xMean P S)
        (fun k => (∑ j ∈ S,
          (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k)) / (n : ℝ)) =
      (∑ i ∈ S, ∑ j ∈ S,
        AronowAudit.P005.dot (P.x i)
          (fun k => P.x j k * δ j - AronowAudit.P005.populationSlope P δ k)) /
        (AronowAudit.P005.pC n m * m * n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnc0 : ((n : ℝ) - m) ≠ 0 := by
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hnum :
      (∑ k, (∑ i ∈ S, P.x i k) *
          (∑ j ∈ S, (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k))) =
        ∑ i ∈ S, ∑ j ∈ S, ∑ k,
          P.x i k * (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k) := by
    calc
      _ = ∑ k, ∑ i ∈ S, ∑ j ∈ S,
          P.x i k * (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          _ = ∑ i ∈ S, P.x i k *
              (∑ j ∈ S, (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k)) := by
            rw [Finset.sum_mul]
          _ = ∑ i ∈ S, ∑ j ∈ S,
              P.x i k * (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
  unfold AronowAudit.P005.dot AronowAudit.P005.xMean AronowAudit.P005.mean
  simp only [hS]
  have hfrac :
      (∑ k, (∑ i ∈ S, P.x i k) / (m : ℝ) *
        ((∑ j ∈ S, (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k)) / (n : ℝ))) =
      (∑ k, (∑ i ∈ S, P.x i k) *
        (∑ j ∈ S, (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k))) /
        ((m : ℝ) * n) := by
    calc
      _ = ∑ k, ((∑ i ∈ S, P.x i k) *
          (∑ j ∈ S, (P.x j k * δ j - AronowAudit.P005.populationSlope P δ k))) /
          ((m : ℝ) * n) := by
        apply Finset.sum_congr rfl
        intro k hk
        field_simp [hm0, hn0]
      _ = _ := by rw [Finset.sum_div]
  rw [hfrac, hnum]
  field_simp [hm0, hn0, hnc0, AronowAudit.P005.pC]

end SAP.P005b.WH.W1.P.T17_L1

theorem SAP.P005b.WH.W1.T17_L1_proof : SAP.P005b.WH.W1.T17_L1 := by
  intro n d m P hn hm hmn hP
  dsimp [SAP.P005b.WH.W1.T17_L1]
  let δ := SAP.P005b.wholeW1Delta P m
  let Q := SAP.P005b.wholeW1Kernel P δ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa [Q] using SAP.P005b.WH.W1.P.T17_L1.kernel_row_sum P (by omega) δ i
  · intro j
    simpa [Q] using SAP.P005b.WH.W1.P.T17_L1.kernel_column_sum P (by omega) hP δ j
  · simpa [Q, δ] using SAP.P005b.WH.W1.P.T17_L1.kernel_trace P (by omega) hP δ
  · intro S hS
    have hn0 : 0 < n := by omega
    have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
    have hPproj : AronowAudit.P005.standardized (SAP.P005b.Bridge.toProject P) := by
      rw [← SAP.P005b.Bridge.standardized_eq]
      exact hP
    let pET := AronowAudit.P005.commonResidual (SAP.P005b.Bridge.toProject P) m
      (SAP.P005b.Bridge.toProject P).yT
    let pEC := AronowAudit.P005.commonResidual (SAP.P005b.Bridge.toProject P) m
      (SAP.P005b.Bridge.toProject P).yC
    let δp := fun i => pET i - pEC i
    let Qp : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      AronowAudit.P005.dot ((SAP.P005b.Bridge.toProject P).x i)
        (fun k => (SAP.P005b.Bridge.toProject P).x j k * δp j -
          AronowAudit.P005.populationSlope (SAP.P005b.Bridge.toProject P) δp k)
    have hid := AronowAudit.P005.corrected_residual_term_identification
      (SAP.P005b.Bridge.toProject P) hn0 hm hmn hPproj S hS
    have hbr := AronowAudit.P005.corrected_residual_brackets
      (SAP.P005b.Bridge.toProject P) hn0 hm hmn S hs pET pEC
      (AronowAudit.P005.common_residual_normal_equation
        (SAP.P005b.Bridge.toProject P) hn0 hPproj)
    have hstarProj : AronowAudit.P005.residualStarTerm
        (SAP.P005b.Bridge.toProject P) S pET pEC =
        (∑ i ∈ S, ∑ j ∈ S, Qp i j) /
          (AronowAudit.P005.pC n m * m * n) := by
      calc
        _ = (1 / AronowAudit.P005.pC n m) *
            AronowAudit.P005.dot
              (AronowAudit.P005.xMean (SAP.P005b.Bridge.toProject P) S)
              ((fun k => (∑ j ∈ S, (SAP.P005b.Bridge.toProject P).x j k *
                (pET j-pEC j))/(n : ℝ)) +
                AronowAudit.P005.populationSlope (SAP.P005b.Bridge.toProject P) pEC) := by
          simpa [pET, pEC] using hid.2.2
        _ = (1 / AronowAudit.P005.pC n m) *
            AronowAudit.P005.dot
              (AronowAudit.P005.xMean (SAP.P005b.Bridge.toProject P) S)
              (fun k => (∑ j ∈ S, ((SAP.P005b.Bridge.toProject P).x j k * δp j -
                AronowAudit.P005.populationSlope (SAP.P005b.Bridge.toProject P) δp k)) /
                (n : ℝ)) := by
          exact congrArg (fun v => (1 / AronowAudit.P005.pC n m) *
            AronowAudit.P005.dot
              (AronowAudit.P005.xMean (SAP.P005b.Bridge.toProject P) S) v)
            (funext (fun k => congrFun hbr.2.2.1 k))
        _ = _ := by
          exact SAP.P005b.WH.W1.P.T17_L1.treated_principal_expansion
            (SAP.P005b.Bridge.toProject P) hn0 hm hmn S hs δp
    have hstar : SAP.P005b.wholeW1Star P m S =
        (∑ i ∈ S, ∑ j ∈ S, Q i j) / (SAP.P005b.pC n m * m * n) := by
      simpa [Q, Qp, pET, pEC, δp, δ, SAP.P005b.pT, SAP.P005b.pC,
        AronowAudit.P005.pT, AronowAudit.P005.pC,
        SAP.P005b.wholeW1Star, SAP.P005b.wholeW1Kernel,
        SAP.P005b.wholeW1Delta, SAP.P005b.commonResidual,
        SAP.P005b.residualStarTerm, SAP.P005b.observedResidual,
        SAP.P005b.populationSlope, SAP.P005b.popMean, SAP.P005b.mean,
        SAP.P005b.centered, SAP.P005b.N, SAP.P005b.dot,
        SAP.P005b.xMean, SAP.P005b.control,
        AronowAudit.P005.residualStarTerm, AronowAudit.P005.observedResidual,
        AronowAudit.P005.commonResidual, AronowAudit.P005.populationSlope,
        AronowAudit.P005.popMean, AronowAudit.P005.mean,
        AronowAudit.P005.centered, AronowAudit.P005.N, AronowAudit.P005.dot,
        AronowAudit.P005.xMean, AronowAudit.P005.control,
        SAP.P005b.Bridge.toProject] using hstarProj
    simpa [Q] using hstar
