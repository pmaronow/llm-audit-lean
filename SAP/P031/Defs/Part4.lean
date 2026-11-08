import SAP.P031.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

def T1Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) (h : Admissible s),
    hc2 s Y = neyman s Y

def T2Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℕ) (hM : 2 ≤ M) (hK : 2 ≤ Fintype.card ι - M)
    (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ),
    randomizationVariance M y1 y0 ≤ expectation M (fun s => hc2 s (observed s y1 y0))

def T3Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ)
    (h : Admissible s),
    ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1) * ols s Y =
      constantEffects s Y

def T4Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) (h : Admissible s)
    (hb : Fintype.card ι = 2 * s.card),
    ((Fintype.card ι : ℝ) - 1) / ((Fintype.card ι : ℝ) - 2) *
        constantEffects s Y = ols s Y ∧
      ols s Y = neyman s Y ∧ neyman s Y = hc2 s Y

def T7Statement : Prop :=
    Admissible proofExampleTreated ∧ proofExampleTreated.card = 2 ∧
    ((univ : Finset (Fin 4)).powersetCard 2).card = 6 ∧
    proofExampleTreated ∈ (univ : Finset (Fin 4)).powersetCard 2 ∧
    observed proofExampleTreated proofExampleOutcomes proofExampleOutcomes =
      proofExampleOutcomes ∧
    groupMean proofExampleTreated proofExampleOutcomes = 1 ∧
    intercept proofExampleTreated proofExampleOutcomes = 7 ∧
    estimate proofExampleTreated proofExampleOutcomes = -6 ∧
    imputed0 proofExampleTreated proofExampleOutcomes = ![6, 8, 5, 9] ∧
    imputed1 proofExampleTreated proofExampleOutcomes = ![0, 2, -1, 3] ∧
    (∀ i, imputed0 proofExampleTreated proofExampleOutcomes i =
      imputed1 proofExampleTreated proofExampleOutcomes i -
        estimate proofExampleTreated proofExampleOutcomes) ∧
    popVariance (imputed0 proofExampleTreated proofExampleOutcomes) = 5 / 2 ∧
    popVariance (imputed1 proofExampleTreated proofExampleOutcomes) = 5 / 2 ∧
    popCovariance proofExampleOutcomes proofExampleOutcomes = 23 / 2 ∧
    popVariance (imputed1 proofExampleTreated proofExampleOutcomes) ≠
      popCovariance proofExampleOutcomes proofExampleOutcomes

def T8Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ)
    (h : Admissible s),
    let N : ℝ := Fintype.card ι
    let M : ℝ := s.card
    let K : ℝ := sᶜ.card
    let S : ℝ := ∑ i, residual s Y i ^ 2
    (∀ i, imputed0 s Y i = imputed1 s Y i - estimate s Y) ∧
    popVariance (imputed0 s Y) = popVariance (imputed1 s Y) ∧
    popVariance (imputed1 s Y) = popCovariance (imputed0 s Y) (imputed1 s Y) ∧
    constantEffects s Y = N / (N - 1) * (N / (M * K)) * popVariance (imputed0 s Y) ∧
    S / N = (∑ i, (Y i - intercept s Y - treatment s i * estimate s Y) ^ 2) / N ∧
    (∑ i, (Y i - intercept s Y - treatment s i * estimate s Y) ^ 2) / N =
      (∑ i, (imputed0 s Y i - intercept s Y) ^ 2) / N ∧
    (∑ i, (imputed0 s Y i - intercept s Y) ^ 2) / N = popVariance (imputed0 s Y) ∧
    (N - 2) / (N - 1) * ols s Y =
      (N - 2) / (N - 1) * (S / (N - 2)) * (N / (M * K)) ∧
    (N - 2) / (N - 1) * (S / (N - 2)) * (N / (M * K)) =
      N / (N - 1) * (S / N) * (N / (M * K)) ∧
    N / (N - 1) * (S / N) * (N / (M * K)) =
      N / (N - 1) * (N / (M * K)) * popVariance (imputed0 s Y) ∧
    N / (N - 1) * (N / (M * K)) * popVariance (imputed0 s Y) = constantEffects s Y

def T9Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ)
    (h : Admissible s) (hb : Fintype.card ι = 2 * s.card),
    let N : ℝ := Fintype.card ι
    let M : ℝ := s.card
    let S : ℝ := ∑ i, residual s Y i ^ 2
    (N - 1) / (N - 2) * constantEffects s Y = ols s Y ∧
    ols s Y = S / (2 * (M - 1)) * (2 * M / M ^ 2) ∧
    S / (2 * (M - 1)) * (2 * M / M ^ 2) =
      ((∑ i ∈ s, residual s Y i ^ 2) / (M - 1)) / M +
        ((∑ i ∈ sᶜ, residual s Y i ^ 2) / (M - 1)) / M ∧
    ((∑ i ∈ s, residual s Y i ^ 2) / (M - 1)) / M +
        ((∑ i ∈ sᶜ, residual s Y i ^ 2) / (M - 1)) / M =
      sampleVariance s Y / M + sampleVariance sᶜ Y / M ∧
    sampleVariance s Y / M + sampleVariance sᶜ Y / M = neyman s Y ∧
    neyman s Y = hc2 s Y

end
end SAP.P031
