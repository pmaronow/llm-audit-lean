import Mathlib
import SAP.P027a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

def Periodic8Witness : Prop :=
  Valid periodic8 ∧ Positive periodic8 ∧
  (∀ k, pi periodic8 k = if k.val % 2 = 0 then 1/12 else 5/12) ∧
  (∀ k l, joint periodic8 k l = if k.val % 4 = l.val % 4 then
    (if k.val % 2 = 0 then 1/12 else 5/12) else 0) ∧
  (Finset.univ.filter (fun kl : Fin 8 × Fin 8 =>
    kl.1 ≠ kl.2 ∧ joint periodic8 kl.1 kl.2 = 0)).card = 48 ∧
  (∀ (g : Fin 4) (u : ℝ),
    fourLeft 2 10 g ≤ u ∧ u < fourLeft 2 10 g+(if g.val % 2 = 0 then 2 else 10) →
    ∀ k, systematicSelected periodicSize8 2 u k ↔ periodic8.selected g k = true) ∧
  (∑ k, alternating8 k) = 0 ∧ biasA periodic8 alternating8 = -16 ∧
  quadraticA periodic8 alternating8 = 48 ∧
  (∀ g : Fin 4,
    htMean periodic8 alternating8 g = (if g.val % 2 = 0 then -3 else 3/5) ∧
    htVarianceEstimator periodic8 alternating8 g / 64 =
      (if g.val % 2 = 0 then 33/4 else 21/100) ∧
    c2Estimator periodic8 alternating8 g / 64 =
      (if g.val % 2 = 0 then 21/2 else 33/50) ∧ wrEstimator periodic8 alternating8 2 g = 0) ∧
  expect periodic8 (htMean periodic8 alternating8) = 0 ∧
  variance periodic8 (htMean periodic8 alternating8) = 9/5 ∧
  expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) = 31/20 ∧
  expect periodic8 (fun g => c2Estimator periodic8 alternating8 g/64) = 23/10 ∧
  expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) -
    variance periodic8 (htMean periodic8 alternating8) = -1/4

def AlternatingFamily : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r), 0 < m →
  let D := phaseOriginal r m hr
  let z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ := fun k => if k.1.2 = 0 then -1 else 1
  let q : ℝ := 2*r
  let N : ℝ := m*q
  (∑ k, z k) = 0 ∧ biasA D z = -q*(m:ℝ)^2 ∧
  variance D (htMean D z) = 9/5 ∧
  expect D (fun ω => htVarianceEstimator D z ω/N^2)-variance D (htMean D z) = -1/q

def T1Statement : Prop :=
  Periodic8Witness ∧ AlternatingFamily

def PeriodicStartLaw : Prop :=
  (∀ (r m : ℕ) (hr : 0 < r), 0 < m →
      let K := (Σ _ : Fin r × Fin 2, Fin m)
      let L : ℝ := 12 * (r : ℝ)
      let left : K → ℝ := fun k =>
        ∑ a : K, if phaseIndex a < phaseIndex k then phaseSize a else 0
      let s : ℝ → K → Bool := fun u k => decide
        (∃ j : Fin m, left k ≤ u + (j : ℝ) * L ∧
          u + (j : ℝ) * L < left k + phaseSize k)
      let ν : Measure ℝ :=
        (ENNReal.ofReal L)⁻¹ • (volume.restrict (Set.Ico (0 : ℝ) L))
      IsProbabilityMeasure ν ∧
      (∀ k : K, left k = phaseStartLeft k.1 + L * (k.2 : ℝ)) ∧
      (∀ u : ℝ, u ∈ Set.Ico (0 : ℝ) L →
        ∃! g : Fin r × Fin 2,
          u ∈ Set.Ico (phaseStartLeft g)
            (phaseStartLeft g + (if g.2 = 0 then 2 else 10))) ∧
      (∀ (g : Fin r × Fin 2) (u : ℝ),
        u ∈ Set.Ico (phaseStartLeft g)
          (phaseStartLeft g + (if g.2 = 0 then 2 else 10)) →
        s u = (phaseOriginal r m hr).selected g) ∧
      (∀ g : Fin r × Fin 2,
        ν (Set.Ico (phaseStartLeft g)
          (phaseStartLeft g + (if g.2 = 0 then 2 else 10))) =
            ENNReal.ofReal (phaseProb r g)) ∧
      (∀ F : (K → Bool) → ℝ,
        Integrable (fun u => F (s u)) ν ∧
        (∫ u, F (s u) ∂ν) =
          expect (phaseOriginal r m hr)
            (fun g => F ((phaseOriginal r m hr).selected g))))

def PeriodicInclusions : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r),
  Valid (phaseOriginal r m hr) ∧ Positive (phaseOriginal r m hr) ∧
  (∀ k : Σ _ : Fin r × Fin 2, Fin m, pi (phaseOriginal r m hr) k = phaseProb r k.1) ∧
  (∀ k l : Σ _ : Fin r × Fin 2, Fin m,
    joint (phaseOriginal r m hr) k l = if k.1 = l.1 then phaseProb r k.1 else 0) ∧
  (∀ (g : Fin r × Fin 2) (k : Σ _ : Fin r × Fin 2, Fin m),
    (phaseOriginal r m hr).selected g k = decide (g = k.1)) ∧
  (∀ k l : Σ _ : Fin r × Fin 2, Fin m,
    (∀ g, (phaseOriginal r m hr).selected g k = (phaseOriginal r m hr).selected g l) ↔ k.1 = l.1)

def PeriodicBiasClaim : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
  (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ), (∑ k, z k) = 0 →
  let D := phaseOriginal r m hr
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  let S := ∑ g, Y g^2
  let q : ℝ := 2*r
  let N : ℝ := m*q
  let V := variance D (htTotal D z)
  (∑ g, Y g) = 0 ∧ biasA D z = -S ∧ 0 ≤ S ∧ (S = 0 ↔ ∀ g, Y g = 0) ∧
  expect D (htTotal D z) = 0 ∧ V = ∑ g, Y g^2/phaseProb r g ∧
  expect D (htVarianceEstimator D z) = V-S ∧
  (∀ g, htVarianceEstimator D z g = (1-phaseProb r g)*Y g^2/(phaseProb r g)^2) ∧
  (expect D (htVarianceEstimator D z)-V)/N^2 = -S/N^2 ∧
  (0 < V → -5/(3*q) ≤ biasA D z/V ∧ biasA D z/V ≤ -1/(3*q))
end
end SAP.P027a
