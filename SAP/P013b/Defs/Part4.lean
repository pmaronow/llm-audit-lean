import Mathlib
import SAP.P013b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

abbrev School := Fin 14 × Fin 4

def schoolBlockChoices : Finset (Finset (Fin 4)) := univ.powersetCard 2

def schoolBSupport : Finset (Fin 14 → Finset (Fin 4)) :=
  Fintype.piFinset (fun _ => schoolBlockChoices)

def schoolCSupport : Finset (Finset School) := (univ : Finset School).powersetCard 28

def blockSchoolHosts (z : Fin 14 → Finset (Fin 4)) : Finset School :=
  univ.filter (fun a => a.2 ∈ z a.1)

/-- Uniform finite expectation; probabilistic clauses use nonempty exact supports. -/
def uniformSchoolMean {α : Type*} (S : Finset α) (X : α → ℝ) : ℝ :=
  (∑ z ∈ S, X z) / (S.card : ℝ)

def uniformSchoolProbability {α : Type*} (S : Finset α) (A : α → Prop) [DecidablePred A] : ℝ :=
  ((S.filter A).card : ℝ) / (S.card : ℝ)

def uniformSchoolVariance {α : Type*} (S : Finset α) (X : α → ℝ) : ℝ :=
  uniformSchoolMean S (fun z => X z ^ 2) - (uniformSchoolMean S X)^2

def schoolBadHosts : Finset School :=
  (univ.filter (fun b : Fin 14 => b.val < 7)).product univ

def schoolActiveOutcome (a b i : School) : ℝ := if i = a then 1 else if i = b then 1 else 0

def schoolHostBit {α : Type*} (hosts : α → School → Bool) (z : α) (i : School) : ℝ :=
  if hosts z i then 1 else 0

def schoolTwoHT {α : Type*} (hosts : α → School → Bool) (a b : School) (z : α) : ℝ :=
  ∑ i : School, schoolHostBit hosts z i * (schoolActiveOutcome a b i / (1/2))

def schoolTwoVarianceInput {α : Type*} (hosts : α → School → Bool)
    (a b : School) (q : ℝ) (z : α) : ℝ :=
  (∑ i : School, schoolHostBit hosts z i * (1 - (1/2 : ℝ)) *
    (schoolActiveOutcome a b i / (1/2))^2) +
  ∑ i : School, ∑ j ∈ univ.erase i,
    (schoolHostBit hosts z i * schoolHostBit hosts z j) *
      ((q - (1/2 : ℝ)*(1/2)) / q) *
      (schoolActiveOutcome a b i / (1/2)) * (schoolActiveOutcome a b j / (1/2))

def schoolBHosts (z : Fin 14 → Finset (Fin 4)) (a : School) : Bool := decide (a.2 ∈ z a.1)

def schoolCHosts (z : Finset School) (a : School) : Bool := decide (a ∈ z)

def schoolHostedExposure (host : Bool) (studentCode : Fin 4) : Fin 5 :=
  if host then ⟨studentCode.val + 1, by omega⟩ else 0

def schoolStudentExposure {Ξ : Type*} {N : ℕ} {α : Type*}
    (hosts : α → School → Bool) (school : Fin N → School)
    (studentCode : Ξ → Fin N → Fin 4) (z : α) (x : Ξ) (i : Fin N) : Fin 5 :=
  schoolHostedExposure (hosts z (school i)) (studentCode x i)

/-- Product of the uniform school law and the common independent student law. -/
def schoolStudentJoint {Ξ : Type*} [Fintype Ξ] {N : ℕ} {α : Type*}
    (S : Finset α) (hosts : α → School → Bool) (Q : Ξ → ℝ)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4)
    (i j : Fin N) (d e : Fin 5) : ℝ :=
  uniformSchoolMean S (fun z => ∑ x, Q x *
    (if schoolStudentExposure hosts school studentCode z x i = d ∧
        schoolStudentExposure hosts school studentCode z x j = e then 1 else 0))

def schoolStudentMarginal {Ξ : Type*} [Fintype Ξ] {N : ℕ} {α : Type*}
    (S : Finset α) (hosts : α → School → Bool) (Q : Ξ → ℝ)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4)
    (i : Fin N) (d : Fin 5) : ℝ :=
  schoolStudentJoint S hosts Q school studentCode i i d d

def schoolPotentialOutcome (a b i : School) (d : Bool) : ℝ :=
  if d then schoolActiveOutcome a b i else 0

def schoolExampleObserved {α : Type*} (hosts : α → School → Bool)
    (a b : School) (z : α) (i : School) : ℝ :=
  schoolPotentialOutcome a b i (hosts z i)

end
end SAP.P013b
