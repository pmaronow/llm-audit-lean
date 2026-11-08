import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b

open scoped BigOperators
noncomputable section
open Classical

/-- A finite probability law with arbitrary real atom masses. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

variable {Ω : Type*} [Fintype Ω]

def FiniteLaw.mean (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * f ω

def FiniteLaw.prob (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.mean fun ω => if D ω then 1 else 0

/-- Conditional means are used only with positive conditioning probability. -/
def FiniteLaw.ce (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop)
    [DecidablePred D] : ℝ :=
  (P.mean fun ω => if D ω then f ω else 0) / P.prob D

def FiniteLaw.variance (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω ^ 2) - (P.mean f) ^ 2

def FiniteLaw.cv (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop)
    [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω ^ 2) D - (P.ce f D) ^ 2

def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- One-subject observable law; W and V are list counts. -/
structure Study (Ω : Type*) [Fintype Ω] where
  law : FiniteLaw Ω
  W : Ω → ℕ
  X : Ω → Bool
  Y : Ω → Bool
  Z : Ω → Bool
  V : Ω → ℕ

/-- Assumption 1, on atoms of positive mass. -/
def Study.monotone (S : Study Ω) : Prop :=
  ∀ ω, 0 < S.law.mass ω → S.Y ω = true → S.X ω = true

/-- Assumption 2. -/
def Study.noLiarsDesign (S : Study Ω) : Prop :=
  ∀ ω, 0 < S.law.mass ω →
    (S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω) * bitVal (S.Z ω)

/-- Assumption 3: full factorization for every function of (W,X,Y). -/
def Study.treatmentIndependent (S : Study Ω) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    S.law.mean (fun ω => if S.Z ω = z then f (S.W ω) (S.X ω) (S.Y ω) else 0) =
      S.law.prob (fun ω => S.Z ω = z) *
        S.law.mean (fun ω => f (S.W ω) (S.X ω) (S.Y ω))

def Study.cell (S : Study Ω) (z y : Bool) (ω : Ω) : Prop :=
  S.Z ω = z ∧ S.Y ω = y

/-- Assumption 4, including existence of each conditional distribution. -/
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

/-- Equation (1), the combined population functional. -/
def Study.combined (S : Study Ω) : ℝ :=
  S.law.mean (fun ω => bitVal (S.Y ω)) +
  S.law.mean (fun ω => 1 - bitVal (S.Y ω)) *
    (S.listMean true false - S.listMean false false)

def Study.beta (S : Study Ω) : ℝ :=
  S.listMean true true - S.listMean false true

def Study.delta (S : Study Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) -
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false)

def tripleIndependent (P : FiniteLaw Ω) (W : Ω → ℕ) (R Q Z : Ω → Bool) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    P.mean (fun ω => if Z ω = z then f (W ω) (R ω) (Q ω) else 0) =
      P.prob (fun ω => Z ω = z) * P.mean (fun ω => f (W ω) (R ω) (Q ω))

end
end SAP.P019b
