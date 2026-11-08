import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u v

/-! Finite weighted population laws, independent assignment, consistent mediation outcomes, and the two specified witnesses. -/

structure Population (Ω : Type u) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

def mean {Ω : Type u} [Fintype Ω] (P : Population Ω) (f : Ω → ℝ) : ℝ :=
  ∑ i, P.mass i * f i

def indicator (A : Prop) : ℝ := @ite ℝ A (Classical.propDecidable A) 1 0

def eventProb {Ω : Type u} [Fintype Ω] (P : Population Ω) (A : Ω → Prop) : ℝ :=
  mean P (fun i => indicator (A i))

def eventMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (A : Ω → Prop) (f : Ω → ℝ) : ℝ :=
  mean P (fun i => indicator (A i) * f i) / eventProb P A

def assignment (t : Bool) : ℝ := if t then 1 else 0

def armProb (p : ℝ) (t : Bool) : ℝ := if t then p else 1 - p

def jointMass {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (t : Bool) (i : Ω) : ℝ := armProb p t * P.mass i

def armMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (t : Bool) (f : Bool → Ω → ℝ) : ℝ :=
  (∑ i, jointMass P p t i * f t i) / armProb p t

def contrast {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ :=
  armMean P p true f - armMean P p false f

def designMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ :=
  (1 - p) * mean P (f false) + p * mean P (f true)

def covariance {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f g : Bool → Ω → ℝ) : ℝ :=
  designMean P p (fun t i => f t i * g t i) - designMean P p f * designMean P p g

def variance {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ := covariance P p f f

def assignmentSlope {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ :=
  covariance P p (fun t _ => assignment t) f /
    variance P p (fun t _ => assignment t)

structure MediationModel (Ω : Type u) where
  knowledge : Bool → Ω → ℝ
  support : Bool → ℝ → Ω → ℝ

def observedSupport {Ω : Type u} (m : MediationModel Ω) (t : Bool) (i : Ω) : ℝ :=
  m.support t (m.knowledge t i) i

def reducedForm {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : MediationModel Ω) : ℝ := contrast P p (observedSupport m)

def mediated {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : MediationModel Ω) : ℝ :=
  mean P (fun i => m.support false (m.knowledge true i) i -
    m.support false (m.knowledge false i) i)

def direct {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : MediationModel Ω) : ℝ :=
  mean P (fun i => m.support true (m.knowledge true i) i -
    m.support false (m.knowledge true i) i)

def linearModel {Ω : Type u} (α a σ b c : ℝ) (u₁ u₂ : Ω → ℝ) : MediationModel Ω :=
  ⟨fun t i => α + a * assignment t + u₁ i,
   fun t k i => σ + b * k + c * assignment t + u₂ i⟩

def uniformPopulation (Ω : Type u) [Fintype Ω] [Nonempty Ω] : Population Ω where
  mass := fun _ => 1 / (Fintype.card Ω : ℝ)
  nonneg := fun _ => by positivity
  total := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

def productPopulation {Ω Ξ : Type u} [Fintype Ω] [Fintype Ξ]
    (P : Population Ω) (Q : Population Ξ) : Population (Ω × Ξ) where
  mass := fun i => P.mass i.1 * Q.mass i.2
  nonneg := fun i => mul_nonneg (P.nonneg i.1) (Q.nonneg i.2)
  total := by simp [Fintype.sum_prod_type, ← mul_sum, P.total, Q.total]

def linearPopulation : Population (Bool × Bool) :=
  productPopulation (uniformPopulation Bool) (uniformPopulation Bool)

def linearU₁ (i : Bool × Bool) : ℝ := if i.1 then 1/5 else -1/5

def linearU₂ (i : Bool × Bool) : ℝ := if i.2 then 1/10 else -1/10

def linearWitness : MediationModel (Bool × Bool) :=
  ⟨fun t i => 8 + (6/5) * assignment t + linearU₁ i,
   fun t k i => 23/10 + (1/20) * (k-8) - (3/50) * assignment t + linearU₂ i⟩

def integerPopulation : Population (Fin 5 × Fin 100) :=
  productPopulation (uniformPopulation (Fin 5)) (uniformPopulation (Fin 100))

def integerWitness : MediationModel (Fin 5 × Fin 100) :=
  ⟨fun t i => 8 + assignment t * (1 + indicator (i.1.val = 4)),
   fun t k i => 2 + indicator ((i.2.val : ℝ) + 1 ≤
     36 + 5 * (k-8) - 6 * assignment t)⟩

def integerGeneralKnowledge (_t : Bool) (_i : Fin 5 × Fin 100) : ℝ := 2



end
end SAP.P043
