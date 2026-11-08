import Mathlib
import SAP.P027a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

def fourPhase (low high : ℝ) (hl : 0 ≤ low) (hh : 0 ≤ high)
    (hn : 2*low+2*high = 1) : Design (Fin 8) (Fin 4) where
  weight g := if g.val % 2 = 0 then low else high
  selected g k := decide (k.val % 4 = g.val)

def periodic8 : Design (Fin 8) (Fin 4) :=
  fourPhase (1/12) (5/12) (by norm_num) (by norm_num) (by norm_num)

def random8 : Design (Fin 8) (Fin 4) :=
  fourPhase (1/8) (3/8) (by norm_num) (by norm_num) (by norm_num)

def alternating8 (k : Fin 8) : ℝ := if k.val % 2 = 0 then -1 else 1

def periodicSize8 (k : Fin 8) : ℝ := if k.val % 2 = 0 then 2 else 10

def randomSize8 (k : Fin 8) : ℝ := if k.val % 2 = 0 then 1 else 3

def randomOutcome8 (k : Fin 8) : ℝ := -alternating8 k

def cluster3 : Design (Fin 3) (Fin 2) where
  weight _ := 1/2
  selected g k := decide (if g.val = 0 then k.val < 2 else k.val = 2)

def cluster2 : Design (Fin 2) (Fin 2) where
  weight _ := 1/2
  selected g k := decide (g = k)

def allOnes3 (_ : Fin 3) : ℝ := 1

def totalledOnes (k : Fin 2) : ℝ := if k = 0 then 2 else 1

def mixed3 (k : Fin 3) : ℝ := if k = 2 then -1/4 else 1

def totalledMixed (k : Fin 2) : ℝ := if k = 0 then 2 else -1/4

def liftDesign {G Ω : Type} (D : Design G Ω) (n : G → ℕ) :
    Design (Σ g, Fin (n g)) Ω where
  weight := D.weight
  selected ω k := D.selected ω k.1

def groupTotal {G : Type} (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (g : G) : ℝ :=
  ∑ j, y ⟨g,j⟩

def groupSquares {G : Type} (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (g : G) : ℝ :=
  ∑ j, y ⟨g,j⟩ ^ 2

def phaseProb (r : ℕ) (g : Fin r × Fin 2) : ℝ :=
  if g.2 = 0 then 1/(6*r) else 5/(6*r)

def oneDraw {G : Type} (p : G → ℝ) : Design G G where
  weight := p
  selected g k := decide (g = k)

def phaseGrouped (r : ℕ) (hr : 0 < r) : Design (Fin r × Fin 2) (Fin r × Fin 2) :=
  oneDraw (phaseProb r)

def phaseOriginal (r m : ℕ) (hr : 0 < r) := liftDesign (phaseGrouped r hr) (fun _ => m)

def phaseSize {r m : ℕ} (k : Σ _ : Fin r × Fin 2, Fin m) : ℝ :=
  if k.1.2 = 0 then 2 else 10

def phaseIndex {r m : ℕ} (k : Σ _ : Fin r × Fin 2, Fin m) : ℕ :=
  2*k.1.1.val+k.1.2.val+2*r*k.2.val

def phaseStartLeft {r : ℕ} (g : Fin r × Fin 2) : ℝ :=
  12*(g.1:ℝ)+(if g.2 = 0 then 0 else 2)

def cumulativeLeft {N : ℕ} (x : Fin N → ℝ) (k : Fin N) : ℝ :=
  ∑ a, if a.val < k.val then x a else 0

def systematicSelected {N : ℕ} (x : Fin N → ℝ) (m : ℕ) (u : ℝ) (k : Fin N) : Prop :=
  ∃ j : Fin m, cumulativeLeft x k ≤ u+(j:ℝ)*((∑ a, x a)/m) ∧
    u+(j:ℝ)*((∑ a, x a)/m) < cumulativeLeft x k+x k

def fourLeft (a b : ℝ) (g : Fin 4) : ℝ :=
  if g = 0 then 0 else if g = 1 then a else if g = 2 then a+b else 2*a+b

end
end SAP.P027a
