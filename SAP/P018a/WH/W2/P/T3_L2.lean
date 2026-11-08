import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018a.WH.W2.P.T3_L2

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma fourth_expansion {N : ℕ} (hm : SAP.P018a.WholeFourthSignMoment)
    (a b c d : Fin N → ℝ) :
    (∫ ω, SAP.P018a.wholeSignLinear a ω *
      SAP.P018a.wholeSignLinear b ω *
      SAP.P018a.wholeSignLinear c ω *
      SAP.P018a.wholeSignLinear d ω
      ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) =
      ∑ l, ∑ k, ∑ j, ∑ i,
        (a i * b j * c k * d l) *
          ((if i = j ∧ k = l then 1 else 0) +
            (if i = k ∧ j = l then 1 else 0) +
            (if i = l ∧ j = k then 1 else 0) -
            (if i = j ∧ j = k ∧ k = l then 2 else 0)) := by
  classical
  letI : IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) :=
    AronowAudit.P018.Wave1.printed_sign_probability N
  have hp (ω : Fin N → Bool) :
      SAP.P018a.wholeSignLinear a ω *
        SAP.P018a.wholeSignLinear b ω *
        SAP.P018a.wholeSignLinear c ω *
        SAP.P018a.wholeSignLinear d ω =
      ∑ l, ∑ k, ∑ j, ∑ i,
        (a i * b j * c k * d l) *
          (SAP.P018a.signValue (ω i) * SAP.P018a.signValue (ω j) *
            SAP.P018a.signValue (ω k) * SAP.P018a.signValue (ω l)) := by
    simp [SAP.P018a.wholeSignLinear, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfun :
      (fun ω => SAP.P018a.wholeSignLinear a ω *
        SAP.P018a.wholeSignLinear b ω *
        SAP.P018a.wholeSignLinear c ω *
        SAP.P018a.wholeSignLinear d ω) =
      (fun ω => ∑ l, ∑ k, ∑ j, ∑ i,
        (a i * b j * c k * d l) *
          (SAP.P018a.signValue (ω i) * SAP.P018a.signValue (ω j) *
            SAP.P018a.signValue (ω k) * SAP.P018a.signValue (ω l))) := by
    funext ω
    exact hp ω
  rw [hfun]
  rw [integral_finsetSum _ (fun l hl =>
        integrable_finset_sum _ (fun k hk =>
          integrable_finset_sum _ (fun j hj =>
            integrable_finset_sum _ (fun i hi =>
              AronowAudit.P018.Wave1.printed_finite_integrable _ _))))]
  simp_rw [integral_finsetSum _ (fun k hk =>
        integrable_finset_sum _ (fun j hj =>
          integrable_finset_sum _ (fun i hi =>
            AronowAudit.P018.Wave1.printed_finite_integrable _ _)))]
  simp_rw [integral_finsetSum _ (fun j hj =>
        integrable_finset_sum _ (fun i hi =>
          AronowAudit.P018.Wave1.printed_finite_integrable _ _))]
  simp_rw [integral_finsetSum _ (fun i hi =>
    AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm N i j k l]

lemma fourth_contraction {N : ℕ} (a b c d : Fin N → ℝ) :
    (∑ l, ∑ k, ∑ j, ∑ i,
      (a i * b j * c k * d l) *
        ((if i = j ∧ k = l then 1 else 0) +
          (if i = k ∧ j = l then 1 else 0) +
          (if i = l ∧ j = k then 1 else 0) -
          (if i = j ∧ j = k ∧ k = l then 2 else 0))) =
      (∑ i, a i * b i) * (∑ i, c i * d i) +
      (∑ i, a i * c i) * (∑ i, b i * d i) +
      (∑ i, a i * d i) * (∑ i, b i * c i) -
      2 * (∑ i, a i * b i * c i * d i) := by
  classical
  have hs (i j k l : Fin N) :
      (a i * b j * c k * d l) *
        ((if i = j ∧ k = l then 1 else 0) +
          (if i = k ∧ j = l then 1 else 0) +
          (if i = l ∧ j = k then 1 else 0) -
          (if i = j ∧ j = k ∧ k = l then 2 else 0)) =
      (a i * b j * c k * d l) * (if i = j ∧ k = l then 1 else 0) +
      (a i * b j * c k * d l) * (if i = k ∧ j = l then 1 else 0) +
      (a i * b j * c k * d l) * (if i = l ∧ j = k then 1 else 0) -
      (a i * b j * c k * d l) * (if i = j ∧ j = k ∧ k = l then 2 else 0) := by
    ring
  have hp1 :
      (∑ l : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
        (a i * b j * c k * d l) * (if i = j ∧ k = l then 1 else 0)) =
        (∑ i, a i * b i) * (∑ k, c k * d k) := by
    have he (i j k l : Fin N) :
        (a i * b j * c k * d l) * (if i = j ∧ k = l then 1 else 0) =
          if k = l then if i = j then a i * b j * c k * d l else 0 else 0 := by
      by_cases hkl : k = l <;> by_cases hij : i = j <;> simp [hkl, hij]
    simp_rw [he]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]
  have hp2 :
      (∑ l : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
        (a i * b j * c k * d l) * (if i = k ∧ j = l then 1 else 0)) =
        (∑ i, a i * c i) * (∑ j, b j * d j) := by
    have he (i j k l : Fin N) :
        (a i * b j * c k * d l) * (if i = k ∧ j = l then 1 else 0) =
          if j = l then if i = k then a i * b j * c k * d l else 0 else 0 := by
      by_cases hjl : j = l <;> by_cases hik : i = k <;> simp [hjl, hik]
    simp_rw [he]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]
  have hp3 :
      (∑ l : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
        (a i * b j * c k * d l) * (if i = l ∧ j = k then 1 else 0)) =
        (∑ i, a i * d i) * (∑ j, b j * c j) := by
    have he (i j k l : Fin N) :
        (a i * b j * c k * d l) * (if i = l ∧ j = k then 1 else 0) =
          if j = k then if i = l then a i * b j * c k * d l else 0 else 0 := by
      by_cases hjk : j = k <;> by_cases hil : i = l <;> simp [hjk, hil]
    simp_rw [he]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]
    conv_rhs => rw [Finset.sum_comm]
  have hp4 :
      (∑ l : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
        (a i * b j * c k * d l) * (if i = j ∧ j = k ∧ k = l then 2 else 0)) =
        2 * (∑ i, a i * b i * c i * d i) := by
    have he (i j k l : Fin N) :
        (a i * b j * c k * d l) * (if i = j ∧ j = k ∧ k = l then 2 else 0) =
          if k = l then if j = k then if i = j then 2 * (a i * b j * c k * d l) else 0 else 0 else 0 := by
      by_cases hkl : k = l <;> by_cases hjk : j = k <;> by_cases hij : i = j <;>
        simp [hkl, hjk, hij] <;> ring_nf
    simp_rw [he]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have hsum :
      (∑ l : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
        (a i * b j * c k * d l) *
          ((if i = j ∧ k = l then 1 else 0) +
            (if i = k ∧ j = l then 1 else 0) +
            (if i = l ∧ j = k then 1 else 0) -
            (if i = j ∧ j = k ∧ k = l then 2 else 0))) =
      (∑ l, ∑ k, ∑ j, ∑ i, (a i * b j * c k * d l) * (if i = j ∧ k = l then 1 else 0)) +
      (∑ l, ∑ k, ∑ j, ∑ i, (a i * b j * c k * d l) * (if i = k ∧ j = l then 1 else 0)) +
      (∑ l, ∑ k, ∑ j, ∑ i, (a i * b j * c k * d l) * (if i = l ∧ j = k then 1 else 0)) -
      (∑ l, ∑ k, ∑ j, ∑ i, (a i * b j * c k * d l) * (if i = j ∧ j = k ∧ k = l then 2 else 0)) := by
    have hdistrib :
        (∑ l : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
          (a i * b j * c k * d l) *
            ((if i = j ∧ k = l then 1 else 0) +
              (if i = k ∧ j = l then 1 else 0) +
              (if i = l ∧ j = k then 1 else 0) -
              (if i = j ∧ j = k ∧ k = l then 2 else 0))) =
        ∑ l, ∑ k, ∑ j, ∑ i,
          ((a i * b j * c k * d l) * (if i = j ∧ k = l then 1 else 0) +
            (a i * b j * c k * d l) * (if i = k ∧ j = l then 1 else 0) +
            (a i * b j * c k * d l) * (if i = l ∧ j = k then 1 else 0) -
            (a i * b j * c k * d l) * (if i = j ∧ j = k ∧ k = l then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      exact hs i j k l
    rw [hdistrib]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsum, hp1, hp2, hp3, hp4]

end SAP.P018a.WH.W2.P.T3_L2

open MeasureTheory ProbabilityTheory

theorem SAP.P018a.WH.W2.T3_L2_proof : SAP.P018a.WH.W2.T3_L2 := by
  intro hm N a b c d
  letI : IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) :=
    AronowAudit.P018.Wave1.printed_sign_probability N
  have hX : MemLp
      (fun ω => SAP.P018a.wholeSignLinear a ω *
        SAP.P018a.wholeSignLinear b ω) 2
      (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) :=
    AronowAudit.P018.Wave1.printed_finite_L2 _ _
  have hY : MemLp
      (fun ω => SAP.P018a.wholeSignLinear c ω *
        SAP.P018a.wholeSignLinear d ω) 2
      (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) :=
    AronowAudit.P018.Wave1.printed_finite_L2 _ _
  rw [covariance_eq_sub hX hY]
  have hgroup :
      (∫ ω, ((fun ω => SAP.P018a.wholeSignLinear a ω * SAP.P018a.wholeSignLinear b ω) *
        (fun ω => SAP.P018a.wholeSignLinear c ω * SAP.P018a.wholeSignLinear d ω)) ω
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) =
      (∫ ω, SAP.P018a.wholeSignLinear a ω * SAP.P018a.wholeSignLinear b ω *
        SAP.P018a.wholeSignLinear c ω * SAP.P018a.wholeSignLinear d ω
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [Pi.mul_apply]
    ring
  have hAB :
      (∫ ω, SAP.P018a.wholeSignLinear a ω * SAP.P018a.wholeSignLinear b ω
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = SAP.P018a.dot a b := by
    simpa [SAP.P018a.wholeSignLinear, SAP.P018a.unitSampleLaw,
      SAP.P018a.signKernel, SAP.P018a.fairLaw, SAP.P018a.signValue,
      SAP.P018a.dot, AronowAudit.P018.unitSampleLaw,
      AronowAudit.P018.signKernel, AronowAudit.P018.fairLaw,
      AronowAudit.P018.signValue, AronowAudit.P018.dot] using
      (AronowAudit.P018.Wave1.appendixB_linear_product a b)
  have hCD :
      (∫ ω, SAP.P018a.wholeSignLinear c ω * SAP.P018a.wholeSignLinear d ω
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = SAP.P018a.dot c d := by
    simpa [SAP.P018a.wholeSignLinear, SAP.P018a.unitSampleLaw,
      SAP.P018a.signKernel, SAP.P018a.fairLaw, SAP.P018a.signValue,
      SAP.P018a.dot, AronowAudit.P018.unitSampleLaw,
      AronowAudit.P018.signKernel, AronowAudit.P018.fairLaw,
      AronowAudit.P018.signValue, AronowAudit.P018.dot] using
      (AronowAudit.P018.Wave1.appendixB_linear_product c d)
  rw [hgroup, SAP.P018a.WH.W2.P.T3_L2.fourth_expansion hm a b c d]
  rw [hAB, hCD,
    SAP.P018a.WH.W2.P.T3_L2.fourth_contraction]
  simp only [SAP.P018a.dot]
  ring
