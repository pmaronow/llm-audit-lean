import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Complete randomization uses all subsets of the fixed treatment size. Binary outcomes represent
the same fixed potential outcome in both arms under the sharp null. The integer table records
treated successes/failures and control successes/failures. Floor only extends the explicit
inverse outside attainable statistic values. Ordered samples use increasing unit labels.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

def support {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) : Finset (Finset ι) :=
  Finset.univ.powersetCard k

def successes {ι : Type*} [DecidableEq ι] (y : ι → Bool) (s : Finset ι) : ℕ :=
  (s.filter (fun i => y i = true)).card

def totalSuccesses {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → Bool) : ℕ :=
  successes y Finset.univ

def countTable (n1 n0 M a : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  ((a : ℤ), (n1 : ℤ) - a, (M : ℤ) - a, (n0 : ℤ) - M + a)

def binaryTau {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (y : ι → Bool) (s : Finset ι) : ℝ :=
  (successes y s : ℝ) / n1 -
    ((totalSuccesses y : ℝ) - successes y s) / n0

def reconstruct (n1 n0 M : ℕ) (t : ℝ) : ℝ :=
  ((n1 : ℝ) * n0 * t + n1 * M) / ((n1 : ℝ) + n0)

def tableFactor {S : Type*} (n1 n0 M : ℕ) (h : (ℤ × ℤ × ℤ × ℤ) → S) : ℝ → S :=
  fun t =>
    let a := Int.floor (reconstruct n1 n0 M t)
    h (a,(n1 : ℤ)-a,(M : ℤ)-a,(n0 : ℤ)-M+a)

def canonical (n k : ℕ) : Fin n → Bool := fun i => decide (i.val < k)

def orderedBinarySample {N n : ℕ} (y : Fin N → Bool) (s : Finset (Fin N))
    (hs : s.card=n) : Fin n → Bool := fun j => y (s.orderEmbOfFin hs j)

def fourY : Fin 4 → Bool := ![true, true, false, false]

def fourX : Fin 4 → Bool := ![true, false, true, false]

def fourA : Finset (Fin 4) := {0, 2}

def fourB : Finset (Fin 4) := {1, 2}

def labelStatistic (s : Finset (Fin 4)) : ℝ := if 0 ∈ s then 1 else 0

noncomputable def upperP {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (T : Finset ι → ℝ) (z : Finset ι) : ℝ :=
  by
  classical
  exact ((support (ι := ι) k).filter (fun w => T z ≤ T w)).card /
    ((support (ι := ι) k).card : ℝ)

def sixY : Fin 6 → Bool := ![true,true,true,false,false,false]

def sixTop : Finset (Fin 6) := {0,1,2}

def fourTop : Finset (Fin 4) := {0,1}

def fourBottom : Finset (Fin 4) := {2,3}

def repeatY (m : ℕ) : Fin m × Fin 4 → Bool := fun i => fourY i.2

def repeatX (m : ℕ) : Fin m × Fin 4 → Bool := fun i => fourX i.2

def repeatA (m : ℕ) : Finset (Fin m × Fin 4) := Finset.univ.product fourA

def repeatB (m : ℕ) : Finset (Fin m × Fin 4) := Finset.univ.product fourB

def repeatLabel (m : ℕ) (hm : 0 < m) (s : Finset (Fin m × Fin 4)) : ℝ :=
  if (⟨0, hm⟩, (0 : Fin 4)) ∈ s then 1 else 0

def binaryReal (b : Bool) : ℝ := if b=true then 1 else 0

end
end SAP.P053
