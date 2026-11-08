import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators
noncomputable section
open Classical

/-- A probability distribution on a finite observable population. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

variable {Ω : Type*} [Fintype Ω]

def FiniteLaw.mean (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * f ω

def FiniteLaw.prob (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.mean fun ω => if D ω then 1 else 0

/-- Event conditional mean; statements using it require a nonzero event probability. -/
def FiniteLaw.ce (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  (P.mean fun ω => if D ω then f ω else 0) / P.prob D

def FiniteLaw.variance (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω ^ 2) - (P.mean f) ^ 2

def FiniteLaw.cv (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω ^ 2) D - (P.ce f D) ^ 2

def FiniteLaw.cov (P : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω * g ω) - P.mean f * P.mean g

def FiniteLaw.ccov (P : FiniteLaw Ω) (f g : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω * g ω) D - P.ce f D * P.ce g D

def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- Baseline count, sensitive behavior, direct answer, assignment, and reported count. -/
structure Study (Ω : Type*) [Fintype Ω] where
  law : FiniteLaw Ω
  W : Ω → ℕ
  X : Ω → Bool
  Y : Ω → Bool
  Z : Ω → Bool
  V : Ω → ℕ

def Study.monotone (S : Study Ω) : Prop :=
  ∀ ω, 0 < S.law.mass ω → S.Y ω = true → S.X ω = true

def Study.noLiarsDesign (S : Study Ω) : Prop :=
  ∀ ω, 0 < S.law.mass ω →
    (S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω) * bitVal (S.Z ω)

/-- Factorization against every function of the whole (W,X,Y) triple. -/
def Study.treatmentIndependent (S : Study Ω) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    S.law.mean (fun ω => if S.Z ω = z then f (S.W ω) (S.X ω) (S.Y ω) else 0) =
    S.law.prob (fun ω => S.Z ω = z) *
      S.law.mean (fun ω => f (S.W ω) (S.X ω) (S.Y ω))

def Study.cell (S : Study Ω) (z y : Bool) (ω : Ω) : Prop := S.Z ω = z ∧ S.Y ω = y

/-- Assumption 4 includes existence of all four conditional distributions. -/
def Study.nondegenerate (S : Study Ω) : Prop :=
  (∀ z y, 0 < S.law.prob (S.cell z y) ∧
    0 < S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y)) ∧
  0 < S.law.variance (fun ω => bitVal (S.Z ω)) ∧
  0 < S.law.variance (fun ω => bitVal (S.Y ω))

def Study.standing (S : Study Ω) : Prop :=
  S.monotone ∧ S.noLiarsDesign ∧ S.treatmentIndependent ∧ S.nondegenerate

def Study.mu (S : Study Ω) : ℝ := S.law.prob fun ω => S.X ω = true

def Study.truthRate (S : Study Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.X ω = true)

def Study.gamma (S : Study Ω) : ℝ := S.law.prob fun ω => S.Z ω = true

def Study.listMean (S : Study Ω) (z y : Bool) : ℝ :=
  S.law.ce (fun ω => (S.V ω : ℝ)) (S.cell z y)

def Study.beta (S : Study Ω) : ℝ := S.listMean true true - S.listMean false true

def Study.delta (S : Study Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) -
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false)

end
end SAP.P019a
