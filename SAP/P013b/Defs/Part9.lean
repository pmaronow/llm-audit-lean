import Mathlib
import SAP.P013b.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]


def T25Statement : Prop :=
  (schoolBadHosts.card = 28 ∧ schoolBadHosts ∈ schoolCSupport ∧
    (∀ z ∈ schoolBSupport, blockSchoolHosts z ≠ schoolBadHosts) ∧
    uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) =
      1/7648690600760440 ∧
    0 < uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) ∧
    uniformSchoolProbability schoolBSupport (fun z => blockSchoolHosts z = schoolBadHosts) = 0) ∧
  (∀ (a b : School) (hab : a ≠ b),
    (∀ i d, schoolPotentialOutcome a b i d = 0 ∨ schoolPotentialOutcome a b i d = 1) ∧
    (∑ i, schoolPotentialOutcome a b i true) = 2 ∧
    (∀ i, schoolPotentialOutcome a b i false = 0) ∧
    (∀ {α : Type*} (hosts : α → School → Bool) z i,
      schoolExampleObserved hosts a b z i = schoolHostBit hosts z i * schoolActiveOutcome a b i)) ∧
  (∀ {α : Type*} (hosts : α → School → Bool)
    (a b : School) (hab : a ≠ b) (z : α),
    schoolTwoHT hosts a b z = 2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) ∧
    (∑ i : School, schoolActiveOutcome a b i) = 2) ∧
  (∀ {α : Type*} (hosts : α → School → Bool)
    (a b : School) (hab : a ≠ b) (q : ℝ) (z : α), 0 < q →
    schoolTwoVarianceInput hosts a b q z =
      2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) +
        8 * schoolHostBit hosts z a * schoolHostBit hosts z b * ((q - 1/4)/q)) ∧
  (∀ {α : Type*} (S : Finset α)
    (hosts : α → School → Bool) (a b : School) (hab : a ≠ b) (p q : ℝ)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2)
    (hb : uniformSchoolProbability S (fun z => hosts z b = true) = 1/2)
    (hp : uniformSchoolProbability S (fun z => hosts z a = true ∧ hosts z b = true) = p), 0 < q →
    uniformSchoolMean S (schoolTwoHT hosts a b) = 2 ∧
    uniformSchoolVariance S (schoolTwoHT hosts a b) = 8*p ∧
    uniformSchoolMean S (schoolTwoVarianceInput hosts a b q) = 2+8*p*((q-1/4)/q)) ∧
  (∀ {α : Type*} (S : Finset α)
    (hosts : α → School → Bool) (a b : School) (hab : a ≠ b) (p : ℝ) (hpos : 0 < p)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2)
    (hb : uniformSchoolProbability S (fun z => hosts z b = true) = 1/2)
    (hp : uniformSchoolProbability S (fun z => hosts z a = true ∧ hosts z b = true) = p),
    uniformSchoolMean S (schoolTwoVarianceInput hosts a b p) =
      uniformSchoolVariance S (schoolTwoHT hosts a b)) ∧
  (uniformSchoolMean schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 2 ∧
    uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 4/3 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (0,1) (27/110)) = 160/81 ∧
    uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) = 2 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) = 53/27 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) <
        uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) ∧
    uniformSchoolVariance schoolCSupport (schoolTwoHT schoolCHosts (0,0) (0,1)) = 108/55 ∧
    uniformSchoolMean schoolCSupport
      (schoolTwoVarianceInput schoolCHosts (0,0) (0,1) (27/110)) = 108/55) ∧
  (uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (0,1) (27/110)) -
      uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 52/81 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) -
      uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) = -(1/27)) ∧
  (∀ a : School,
    uniformSchoolProbability schoolBSupport (fun z => schoolBHosts z a = true) = 1/2 ∧
    uniformSchoolProbability schoolBSupport (fun z => schoolBHosts z a = false) = 1/2 ∧
    uniformSchoolProbability schoolCSupport (fun z => schoolCHosts z a = true) = 1/2 ∧
    uniformSchoolProbability schoolCSupport (fun z => schoolCHosts z a = false) = 1/2) ∧
  (uniformSchoolProbability schoolBSupport
      (fun z => schoolBHosts z (0,0) = true ∧ schoolBHosts z (0,1) = true) = 1/6 ∧
    uniformSchoolProbability schoolBSupport
      (fun z => schoolBHosts z (0,0) = true ∧ schoolBHosts z (1,0) = true) = 1/4 ∧
    uniformSchoolProbability schoolCSupport
      (fun z => schoolCHosts z (0,0) = true ∧ schoolCHosts z (0,1) = true) = 27/110) ∧
  ((1 : ℝ) / (Nat.choose 56 28 : ℝ) = 1/7648690600760440)

end
end SAP.P013b
