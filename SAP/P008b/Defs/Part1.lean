import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

abbrev Assignment (N : ℕ) := Fin N → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ z, 0 ≤ mass z
  total : ∑ z, mass z = 1

def FiniteLaw.expect {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ z, Q.mass z * f z

def FiniteLaw.prob {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (P : Ω → Prop) : ℝ :=
  by classical exact ∑ z ∈ Finset.univ.filter P, Q.mass z

def FiniteLaw.cov {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f g : Ω → ℝ) : ℝ :=
  Q.expect (fun z => (f z - Q.expect f) * (g z - Q.expect g))

def FiniteLaw.var {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  Q.cov f f

def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero (α := Ω)))

def marginal {N : ℕ} (Q : FiniteLaw (Assignment N))
    (F : Assignment N → ℝ) (i : Fin N) (b : Bool) : ℝ :=
  Q.expect (fun z => F (Function.update z i b))

abbrev Plane := EuclideanSpace ℝ (Fin 2)

structure SpatialModel (N : ℕ) where
  field : Set Plane
  node : Fin N → Plane
  node_mem : ∀ i, node i ∈ field
  ζ : Measure Plane
  Y : Plane → Assignment N → ℝ

def SpatialModel.circle {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) : Set Plane :=
  {x | x ∈ P.field ∧ dist (P.node i) x = d}

def SpatialModel.circleMeasure {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :=
  P.ζ.restrict (P.circle i d)

def SpatialModel.circleMass {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) : ℝ :=
  (P.circleMeasure i d Set.univ).toReal

def SpatialModel.average {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (f : Plane → ℝ) : ℝ :=
  (P.circleMass i d)⁻¹ * ∫ x, f x ∂P.circleMeasure i d

def SpatialModel.M {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (z : Assignment N) : ℝ := P.average i d (fun x => P.Y x z)

def SpatialModel.marginalY {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (b : Bool) (x : Plane) : ℝ :=
  marginal Q (P.Y x) i b

def SpatialModel.pointEffect {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (x : Plane) : ℝ :=
  P.marginalY Q i true x - P.marginalY Q i false x

def SpatialModel.m {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (b : Bool) (d : ℝ) : ℝ :=
  marginal Q (P.M i d) i b

def SpatialModel.nodeEffect {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) : ℝ :=
  P.m Q i true d - P.m Q i false d

def SpatialModel.amr {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, P.nodeEffect Q i d

def nTreated {N : ℕ} (z : Assignment N) : ℝ := ∑ i, bit (z i)

def nControl {N : ℕ} (z : Assignment N) : ℝ := N - nTreated z

def hajek {N : ℕ} (M : Fin N → Assignment N → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, bit (z i) * M i z) / nTreated z -
    (∑ i, (1 - bit (z i)) * M i z) / nControl z

def countMean {X : Type*} (C : Finset X) (f : X → ℝ) : ℝ :=
  (∑ x ∈ C, f x) / C.card

end

end SAP.P008b
