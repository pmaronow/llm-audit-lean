import Mathlib
import SAP.P013b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

def shiftPopulation {N K : ℕ} {P : Design Ω} (F : Population P N K) (c : ℝ) :
    Population P N K where
  exposure := F.exposure
  outcome i d := F.outcome i d + c

def exposureWeight {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (z : Ω) (i : Fin N) : ℝ := indicator F.exposure i d z / pi F i d

def differenceEffect {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (gk gl : Fin N → ℝ) (z : Ω) : ℝ :=
  (differenceTotal F d gk z - differenceTotal F e gl z) / (N : ℝ)

def translationError {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (h : Fin N → ℝ) (c : ℝ) (z : Ω) : ℝ :=
  ∑ i, (1 - exposureWeight F d z i) * (h i - c)

def locationDesign : Design (Fin 3) where
  weight z := if z = 2 then 1/2 else 1/4
  positive z := by split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def locationPrediction (i : Fin 3) : ℝ := if i = 0 then 2 else if i = 1 then 3 else 5

def locationPopulation : Population locationDesign 3 2 where
  exposure z i := if z = i then 1 else 0
  outcome i _ := locationPrediction i

abbrev Recording (N K : ℕ) := Fin N → Fin K → Bool

def recordedPopulation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) : Population P N K where
  exposure := F.exposure
  outcome i d := if R i d then F.outcome i d else 0

def lostMean {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) (d : Fin K) : ℝ :=
  (∑ i, if R i d then 0 else F.outcome i d) / (N : ℝ)

def recordedNumerator {N K : ℕ} (D : Fin N → Fin K) (w G : Fin N → ℝ)
    (d : Fin K) (T : Finset (Fin N)) : ℝ :=
  ∑ i ∈ T, if D i = d then w i * G i else 0

def recordedDenominator {N K : ℕ} (D : Fin N → Fin K) (w : Fin N → ℝ)
    (d : Fin K) (T : Finset (Fin N)) : ℝ :=
  ∑ i ∈ T, if D i = d then w i else 0

def twoReportDesign : Design (Fin 2 × Fin 2) where
  weight _ := 1/4
  positive _ := by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]

def twoWearPopulation (world : Fin 3) : Population twoReportDesign 2 2 where
  exposure z i := if i = 0 then z.1 else z.2
  outcome i d := if i = 0 then (if d = 1 then 1 else 0)
    else if world = 1 then (if d = 1 then 1 else 0)
    else if world = 2 then (if d = 0 then 1 else 0) else 0

def twoRecording : Recording 2 2 := fun i _ => if i = 0 then true else false

def recordedData {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) (z : Ω) (i : Fin N) : Fin K × ℝ × Bool :=
  (F.exposure z i, observed (recordedPopulation F R) z i, R i (F.exposure z i))

def twoRespondentPopulation : Population twoReportDesign 1 2 where
  exposure z _ := z.1
  outcome _ d := if d = 1 then 1 else 0

def section10Exposure (host own peer : Bool) : Fin 5 :=
  if host then (if own then (if peer then 4 else 3) else (if peer then 2 else 1)) else 0

def section10Population {N M : ℕ} (P : Design Ω) (analysed : Fin N → Fin M)
    (school : Fin M → Fin 56) (hosts : Ω → Fin 56 → Bool) (assigned : Ω → Fin M → Bool)
    (neighbors : Fin M → Finset (Fin M)) (y : Fin N → Fin 5 → ℝ) : Population P N 5 where
  exposure z i := section10Exposure (hosts z (school (analysed i))) (assigned z (analysed i))
    (decide ((neighbors (analysed i)).filter (fun j => assigned z j)).Nonempty)
  outcome := y

/-- A fair one-treated two-unit design for the calibration case of T22(f). -/
def calibrationDesign : Design (Fin 2) where
  weight _ := 1/2
  positive _ := by norm_num
  total := by norm_num [Fin.sum_univ_two]

def calibrationPopulation : Population calibrationDesign 2 2 where
  exposure z i := if z = i then 1 else 0
  outcome _ _ := 0

end
end SAP.P013b
