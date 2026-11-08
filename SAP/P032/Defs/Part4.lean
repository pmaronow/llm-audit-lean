import SAP.P032.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

/-! Fixed-factor Rubin operations, completed binary data and printed table entries. -/

def estimateAverage {m : ℕ} (b : Fin m → P → ℝ) : P → ℝ :=
  fun i => (m : ℝ)⁻¹ * ∑ t, b t i

def betweenCovariance {m : ℕ} (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  fun i j => ((m : ℝ)-1)⁻¹ *
    ∑ t, (b t i-estimateAverage b i)*(b t j-estimateAverage b j)

def rubinContribution {m : ℕ} (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  (1+(m : ℝ)⁻¹) • betweenCovariance b

def componentAverage {J : Type*} {m : ℕ} (U : J → Fin m → Matrix P P ℝ)
    (j : J) : Matrix P P ℝ := (m : ℝ)⁻¹ • ∑ t, U j t

def poolBeforeCombining {J : Type*} [Fintype J] {m : ℕ}
    (s a : J → ℝ) (U : J → Fin m → Matrix P P ℝ) (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  ∑ j, (s j*a j) • ((a j)⁻¹ • componentAverage U j + rubinContribution b)

def combineBeforePooling {J : Type*} [Fintype J] {m : ℕ}
    (s : J → ℝ) (U : J → Fin m → Matrix P P ℝ) (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  (m : ℝ)⁻¹ • (∑ t, ∑ j, s j • U j t) + rubinContribution b

def decompositionWeight (k : ℕ) : (Fin k ⊕ Fin 2) → ℝ :=
  Sum.elim (fun _ => 1) (fun j => if j = 0 then -1 else -((k : ℝ)-2))

def undoFactors (k : ℕ) (Gi : Fin k → ℝ) (GD n : ℝ) : (Fin k ⊕ Fin 2) → ℝ :=
  Sum.elim (fun i => 1-1/Gi i) (fun j => if j = 0 then 1-1/GD else 1-1/n)

def imputationSuccesses (B : Bool) : Fin 6 → ℕ := if B then ![4,3,3,3,3,2] else ![4,2,2,2,2,0]

def imputationOutcome (B : Bool) (r : Fin 6 × Fin 4) : ℝ :=
  if r.2.val < imputationSuccesses B r.1 then 1 else 0

def imputationProbability (B : Bool) : ℝ := (1/24 : ℝ)*∑ r, imputationOutcome B r

def imputationEstimate (B : Bool) : ℝ := Real.log (imputationProbability B/(1-imputationProbability B))

def imputationInformation (B : Bool) : ℝ := 24*imputationProbability B*(1-imputationProbability B)

def imputationScore (B : Bool) (r : Fin 6 × Fin 4) : ℝ := imputationOutcome B r - imputationProbability B

def imputationRecordCovariance (B : Bool) : ℝ := (imputationInformation B)^(-2 : ℤ)*recordScalarCovariance (imputationScore B)

def imputationDyadCovariance (B : Bool) : ℝ :=
  (imputationInformation B)^(-2 : ℤ)*clusterScalarCovariance Prod.fst (imputationScore B)

def imputationMemberCovariance (B : Bool) (i : Fin 4) : ℝ :=
  (imputationInformation B)^(-2 : ℤ)*memberScalarCovariance (fun r => sixDyadData r.1) i (imputationScore B)

def fiveEstimates : Fin 5 → Fin 1 → ℝ := fun t _ => ![0,0,0,Real.log 3,Real.log 3] t

def averageMemberCovariance (i : Fin 4) : ℝ := (3*imputationMemberCovariance false i+2*imputationMemberCovariance true i)/5

def averageDyadCovariance : ℝ := (3*imputationDyadCovariance false+2*imputationDyadCovariance true)/5

def averageRecordCovariance : ℝ := (3*imputationRecordCovariance false+2*imputationRecordCovariance true)/5

def correctPooledVariance : ℝ :=
  (∑ i, averageMemberCovariance i)-averageDyadCovariance-2*averageRecordCovariance + rubinContribution fiveEstimates 0 0

def codePooledVariance : ℝ :=
  (∑ i : Fin 4, (12/13 : ℝ)*(averageMemberCovariance i/(12/13)+rubinContribution fiveEstimates 0 0)) -
    (5/6 : ℝ)*(averageDyadCovariance/(5/6)+rubinContribution fiveEstimates 0 0) -
    2*(23/24 : ℝ)*(averageRecordCovariance/(23/24)+rubinContribution fiveEstimates 0 0)

structure StudyEntry where
  n : ℕ
  loss : ℕ
  lossMilli : ℕ
  serMilli : ℕ

/-- Supplementary Table A.2 in printed order, indexed from zero.
The weak-threshold rows 4, 8, 9 and 20 are respectively Colgan (2014),
Efrat and Newman (2016), Fang, Johnson and Leeds (2014), and Weisiger (2016).
Row 8 is the equality case excluded by the strict threshold. -/
def studyData : Fin 22 → StudyEntry :=
  ![⟨6,1,167,2739⟩, ⟨173,43,249,2187⟩, ⟨29,6,207,2200⟩,
    ⟨8,3,375,1099⟩, ⟨9,8,889,3269⟩, ⟨24,0,0,1526⟩,
    ⟨45,5,111,898⟩, ⟨36,5,139,1511⟩, ⟨4,2,500,4158⟩,
    ⟨1,1,1000,1691⟩, ⟨170,7,41,955⟩, ⟨3,0,0,1895⟩,
    ⟨6,0,0,1301⟩, ⟨41,8,195,1432⟩, ⟨16,0,0,908⟩,
    ⟨18,4,222,1426⟩, ⟨20,1,50,1291⟩, ⟨18,0,0,999⟩,
    ⟨9,0,0,1071⟩, ⟨15,0,0,1212⟩, ⟨28,17,607,3268⟩, ⟨12,2,167,1311⟩]

abbrev roundingFits (row : StudyEntry) (k : ℕ) : Prop :=
  |2000*(k : ℤ)-2*(row.n : ℤ)*(row.lossMilli : ℤ)| ≤ (row.n : ℤ)

end
end SAP.P032
