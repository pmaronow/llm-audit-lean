import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

/-! Exact empirical inputs and ordinary finite-sample trimming formulas.
The three arms are ordered 90–90, 90–70, 90–45. Counts are supplied inputs.
These definitions do not assert a connection to a raw data file. -/

def sampleSize : Fin 3 → ℕ := ![544, 538, 533]

def failures : Fin 3 → ℕ := ![35, 182, 40]

def passers (a : Fin 3) : ℕ := sampleSize a - failures a

def preferCount : Fin 3 → ℕ := ![61, 162, 327]

def approveCount : Fin 3 → ℕ := ![192, 188, 324]

def failureShare (a : Fin 3) : ℚ := (failures a : ℚ) / sampleSize a

def trimShare (a : Fin 3) : ℚ :=
  (∑ b : Fin 3, if b ≠ a then failureShare b else 0) / (1 - failureShare a)

def keptLower (a : Fin 3) : ℕ :=
  (⌈(passers a : ℚ) * (1 - trimShare a)⌉ - 1).toNat

def keptUpper (a : Fin 3) : ℕ :=
  passers a - (⌊(passers a : ℚ) * trimShare a⌋).toNat

def sampleBounds (ones : Fin 3 → ℕ) (a : Fin 3) : ℚ × ℚ :=
  ((keptLower a - (passers a - ones a) : ℕ) / (keptLower a : ℚ),
   (min (keptUpper a) (ones a) : ℕ) / (keptUpper a : ℚ))

noncomputable def sampleInterval (ones : Fin 3 → ℕ) (a : Fin 3) : Set ℝ :=
  Set.Icc ((sampleBounds ones a).1 : ℝ) ((sampleBounds ones a).2 : ℝ)

def minAlwaysShare : ℚ := 1 - ∑ a : Fin 3, failureShare a

def fractionalPreference (a : Fin 3) : ℚ × ℚ :=
  let az : ℚ := (preferCount a : ℚ) / sampleSize a
  (max 0 ((az - ∑ b : Fin 3, if b ≠ a then failureShare b else 0) /
    minAlwaysShare), min 1 (az / minAlwaysShare))

end SAP.P010
