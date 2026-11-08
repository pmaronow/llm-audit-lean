import AronowAudit.P015.P015_Regression
/- Printed claims and the overstrong remainder draft, retained solely as
propositions. No declaration in this module asserts these propositions. Their
checked refutations or validator-approved correction are separate theorems. -/
namespace AronowAudit.P015.PrintedClaims
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
noncomputable section

def printed_inverse_link_claim : Prop :=
  ∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hinverse : Function.Injective (I.restrict m))
    (hprob : ∀ η ∈ I, 0 < m η ∧ m η < 1)
    (θ : Fin (K+2) → ℝ) (hθ : ∀ i, W.mulVec θ i ∈ I)
    (hML : ∀ θ' : Fin (K+2) → ℝ, (∀ i, W.mulVec θ' i ∈ I) →
      groupedLikelihood W (fun _ => 1) Y m θ' ≤ groupedLikelihood W (fun _ => 1) Y m θ),
groupedResidual W (fun _ => 1) Y m θ = 0

def printed_effective_positivity : Prop :=
  ∀ {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P) (d d' : ℝ) (hd : d ≠ d')
    (hpd : 0 < P {s | D s=d}) (hpd' : 0 < P {s | D s=d'})
    (hw : Integrable (discreteWeight P X D) P)
    (hpos : 0 < ∫ s, discreteWeight P X D s ∂P),
∀ x, 0 < discreteEffective P X D {s | X s=x} →
      0 < cellProb (discreteEffective P X D) X D x d ∧
      0 < cellProb (discreteEffective P X D) X D x d'

def full_score_matrix_expansion : Prop :=
  ∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η ∈ I, 0 < m η ∧ m η < 1)
    (η₀ p₀ : ℝ) (hη : η₀∈I) (hp : 0<p₀) (hu : p₀<1) (hmean : m η₀=p₀)
    (hm₂ : DifferentiableAt ℝ (deriv m) η₀),
let θ₀ : Fin (K+2) → ℝ := fun j => if j=0 then η₀ else 0
    let h₀ := scoreMultiplier m η₀
    let f₀ := deriv m η₀
    let h₁ := deriv (scoreMultiplier m) η₀
    let r := W.transpose.mulVec (fun i => Y i-p₀)
    let A := W.transpose*W
    let B : Matrix (Fin (K+2)) (Fin (K+2)) ℝ :=
      fun j k => ∑ i, (Y i-p₀)*W i j*W i k
    ((fun δ : Fin (K+2) → ℝ =>
      groupedScore W (fun _ => 1) Y m (θ₀+δ)-
        (h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ))
      =O[𝓝 0] (fun δ : Fin (K+2) → ℝ => ‖δ‖^2)) ∧
    (∀ δ, h₀≠0 →
      (h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ=0 ↔
        (f₀ • A-(h₁/h₀) • B).mulVec δ=r)) ∧
    (∀ δ, h₀≠0 → (h₁=0 ∨ B.mulVec δ=0) →
      (h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ=0 ↔
        (f₀ • A).mulVec δ=r))

end
end AronowAudit.P015.PrintedClaims
