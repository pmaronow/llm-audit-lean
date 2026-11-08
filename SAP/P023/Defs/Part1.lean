import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! Election designs, population laws, and estimator definitions. -/

def dot (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

def predict (X : ι → κ → ℝ) (c : κ → ℝ) (i : ι) : ℝ := ∑ j, X i j * c j

def IsOLS (X : ι → κ → ℝ) (y : ι → ℝ) (c : κ → ℝ) : Prop :=
  ∀ j, dot (fun i => X i j) (fun i => y i - predict X c i) = 0

def FullRank (X : ι → κ → ℝ) : Prop :=
  ∀ c, (∀ i, predict X c i = 0) → c = 0

def olsCoefficients (X : ι → κ → ℝ) (y : ι → ℝ) : κ → ℝ :=
  Classical.epsilon (fun c => IsOLS X y c)

def polynomialDesign (J : ℕ) (x d : ι → ℝ) : ι → Fin (J + 2) → ℝ :=
  fun i j => if j.val = 0 then 1 else if j.val = 1 then d i else x i ^ (j.val - 1)

def polynomialOLS (J : ℕ) (x d y : ι → ℝ) : ℝ :=
  olsCoefficients (polynomialDesign J x d) y ⟨1, by omega⟩

def close (k : ℝ) (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => -k < x i ∧ x i ≤ k)

def rd (k : ℝ) (x d y : ι → ℝ) : ℝ :=
  (∑ i ∈ close k x, d i * y i) / (∑ i ∈ close k x, d i) -
  (∑ i ∈ close k x, (1 - d i) * y i) / (∑ i ∈ close k x, (1 - d i))

def Condition1 (k : ℝ) (x : ι → ℝ) : Prop :=
  (∃ i, 0 < x i ∧ x i < k) ∧ (∃ i, -k < x i ∧ x i < 0)

def TwoParty (x d : ι → ℝ) : Prop :=
  (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ (∀ i, d i = 0 ∨ d i = 1) ∧
  (∀ i, 0 < x i → d i = 1) ∧ (∀ i, x i < 0 → d i = 0)

def binCount (k : ℝ) : ℕ := 2 * Nat.ceil ((1 - k) / (2 * k))

def inBin (k : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  if j = 0 then -(binCount k : ℝ) - 1 ≤ x / k ∧ x / k ≤ -(binCount k : ℝ) + 1
  else 2 * (j : ℝ) - binCount k - 1 < x / k ∧ x / k ≤ 2 * (j : ℝ) - binCount k + 1

def binIndicator (k : ℝ) (j : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if inBin k j x then 1 else 0

def coarsenedDesign (k : ℝ) (x d : ι → ℝ) : ι → Fin (binCount k + 2) → ℝ :=
  fun i j => if j.val = 0 then 1 else if j.val = 1 then d i
    else binIndicator k (j.val - 1) (x i)

def Localized (k : ℝ) (x : ι → ℝ) (est : (ι → ℝ) → ℝ) : Prop :=
  ∀ y y', (∀ i ∈ close k x, y i = y' i) → est y = est y'

def linearX : Fin 6 → ℝ := ![(-3 / 4 : ℝ), (-1 / 4 : ℝ), (-1 / 400 : ℝ), (1 / 400 : ℝ), (1 / 4 : ℝ), (3 / 4 : ℝ)]

def linearD : Fin 6 → ℝ := ![0, 0, 0, 1, 1, 1]

def linearY : Fin 6 → ℝ := ![(37 / 80 : ℝ), (39 / 80 : ℝ), (3999 / 8000 : ℝ), (4801 / 8000 : ℝ), (49 / 80 : ℝ), (51 / 80 : ℝ)]

def linearYprime : Fin 6 → ℝ := ![(37 / 80 : ℝ), (39 / 80 : ℝ), (3999 / 8000 : ℝ), (4801 / 8000 : ℝ), (49 / 80 : ℝ), (259 / 400 : ℝ)]

def linearW : Fin 6 → ℝ := ![(20299 / 139202 : ℝ), (-59901 / 139202 : ℝ), (-49800 / 69601 : ℝ), (49800 / 69601 : ℝ), (59901 / 139202 : ℝ), (-20299 / 139202 : ℝ)]

def linearExact : Fin 3 → ℝ := ![(1 / 2 : ℝ), (1 / 10 : ℝ), (1 / 20 : ℝ)]

def degree7X : Fin 16 → ℝ := ![-1, (-7 / 8 : ℝ), (-3 / 4 : ℝ), (-5 / 8 : ℝ), (-1 / 2 : ℝ), (-3 / 8 : ℝ), (-1 / 4 : ℝ), (-1 / 8 : ℝ), (1 / 8 : ℝ), (1 / 4 : ℝ), (3 / 8 : ℝ), (1 / 2 : ℝ), (5 / 8 : ℝ), (3 / 4 : ℝ), (7 / 8 : ℝ), 1]

def degree7D : Fin 16 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]

def degree7Y : Fin 16 → ℝ := ![(11 / 25 : ℝ), (94859017 / 209715200 : ℝ), (755573 / 1638400 : ℝ), (3929035 / 8388608 : ℝ), (6079 / 12800 : ℝ), (100923253 / 209715200 : ℝ), (798719 / 1638400 : ℝ), (103546879 / 209715200 : ℝ), (127139841 / 209715200 : ℝ), (1003521 / 1638400 : ℝ), (129763467 / 209715200 : ℝ), (8001 / 12800 : ℝ), (26492169 / 41943040 : ℝ), (1046667 / 1638400 : ℝ), (135827703 / 209715200 : ℝ), (33 / 50 : ℝ)]

def degree7Yprime : Fin 16 → ℝ := ![(11 / 25 : ℝ), (94859017 / 209715200 : ℝ), (755573 / 1638400 : ℝ), (3929035 / 8388608 : ℝ), (6079 / 12800 : ℝ), (100923253 / 209715200 : ℝ), (798719 / 1638400 : ℝ), (103546879 / 209715200 : ℝ), (127139841 / 209715200 : ℝ), (1003521 / 1638400 : ℝ), (129763467 / 209715200 : ℝ), (8001 / 12800 : ℝ), (26492169 / 41943040 : ℝ), (1046667 / 1638400 : ℝ), (135827703 / 209715200 : ℝ), (67 / 100 : ℝ)]

def degree7W : Fin 16 → ℝ := ![(-175 / 1607 : ℝ), (725 / 1607 : ℝ), (-685 / 1607 : ℝ), (-643 / 1607 : ℝ), (554 / 1607 : ℝ), (1289 / 1607 : ℝ), (239 / 1607 : ℝ), (-2911 / 1607 : ℝ), (2911 / 1607 : ℝ), (-239 / 1607 : ℝ), (-1289 / 1607 : ℝ), (-554 / 1607 : ℝ), (643 / 1607 : ℝ), (685 / 1607 : ℝ), (-725 / 1607 : ℝ), (175 / 1607 : ℝ)]

def degree7Exact : Fin 9 → ℝ := ![(1 / 2 : ℝ), (1 / 10 : ℝ), (1 / 20 : ℝ), 0, 0, 0, 0, 0, (1 / 100 : ℝ)]

def binLabel (k x : ℝ) : Fin (binCount k + 1) :=
  ⟨min (binCount k) (Nat.ceil ((x / k + (binCount k : ℝ) - 1) / 2)),
    Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

def centralLabel (k : ℝ) : Fin (binCount k + 1) :=
  ⟨Nat.ceil ((1 - k) / (2 * k)), by unfold binCount; omega⟩

def IsBinOLS {η : Type*} [Fintype η] [DecidableEq η]
    (B : ι → η) (d y : ι → ℝ) (a : η → ℝ) (β : ℝ) : Prop :=
  (∀ j, (∑ i, if B i = j then y i - a (B i) - β * d i else 0) = 0) ∧
  (∑ i, d i * (y i - a (B i) - β * d i)) = 0

def CoarsenedOLS (k : ℝ) (x d y : ι → ℝ) (β : ℝ) : Prop :=
  ∃ a, IsBinOLS (fun i => binLabel k (x i)) d y a β

def ProbabilityLaw {E : Type*} [MeasurableSpace E] (μ : Measure E) : Prop := μ univ = 1

def MarginSupport (μ : Measure ℝ) : Prop := μ (Set.Icc (-1) 1)ᶜ = 0

def party (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

def expectation (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, f x ∂μ

def IsProjection (μ : Measure ℝ) (J : ℕ) (q : Polynomial ℝ) : Prop :=
  q.natDegree ≤ J ∧ ∀ j ≤ J, expectation μ (fun x => (party x - q.eval x) * x^j) = 0

def projection (μ : Measure ℝ) (J : ℕ) : Polynomial ℝ :=
  Classical.epsilon (IsProjection μ J)

def popResidual (μ : Measure ℝ) (J : ℕ) (x : ℝ) : ℝ := party x - (projection μ J).eval x

def residualVariance (μ : Measure ℝ) (J : ℕ) : ℝ := expectation μ (fun x => popResidual μ J x ^ 2)

def amplification (μ : Measure ℝ) (J : ℕ) : ℝ :=
  expectation μ (fun x => |popResidual μ J x|) / residualVariance μ J

def biasFunctional (μ : Measure ℝ) (J : ℕ) (h : ℝ → ℝ) : ℝ :=
  expectation μ (fun x => popResidual μ J x * h x) / residualVariance μ J

def MomentPositiveDefinite (μ : Measure ℝ) (J : ℕ) : Prop :=
  ∀ c : Fin (J + 2) → ℝ, c ≠ 0 →
    0 < expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) c x ^ 2)

def PopNormal (μ : Measure ℝ) (J : ℕ) (m : ℝ → ℝ) (c : Fin (J + 2) → ℝ) : Prop :=
  ∀ j, expectation μ (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
    (m x - predict (polynomialDesign J (fun x : ℝ => x) party) c x)) = 0

def populationCoefficient (μ : Measure ℝ) (J : ℕ) (m : ℝ → ℝ) : ℝ :=
  (Classical.epsilon (PopNormal μ J m)) ⟨1, by omega⟩

def uniformMargins : Measure ℝ := (1 / 2 : ℝ≥0∞) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)

def populationRD (μ : Measure ℝ) (m : ℝ → ℝ) (k : ℝ) : ℝ :=
  (∫ x in Set.Ioc 0 k, m x ∂μ) / (μ (Set.Ioc 0 k)).toReal -
  (∫ x in Set.Ioo (-k) 0, m x ∂μ) / (μ (Set.Ioo (-k) 0)).toReal
end
end SAP.P023
