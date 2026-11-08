import SAP.P037a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

noncomputable def uniformDraw : Measure ℝ := volume.restrict (Ioo 0 1)

noncomputable def normalizedWeights {n : ℕ} (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i / ∑ j, w j

def openSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i < 1}

noncomputable def appendSimplex (m : ℕ) (p : Fin m → ℝ) : Fin (m+1) → ℝ :=
  fun i => if hi : i.val < m then p ⟨i.val, hi⟩ else 1 - ∑ j, p j

noncomputable def simplexLaw (m : ℕ) : Measure (Fin (m+1) → ℝ) :=
  Measure.map (appendSimplex m)
    ((m.factorial : ℝ≥0∞) • (volume.restrict (openSimplex m)))

noncomputable def uniformWeightLaw (n : ℕ) : Measure (Fin (n+2) → ℝ) :=
  Measure.map normalizedWeights
    (Measure.pi (fun _ : Fin (n+2) => uniformDraw))

def ratioEvent (n : ℕ) : Set (Fin (n+2) → ℝ) :=
  {p | p 0 / (p 0 + p 1) < 1/4}

def WLS {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : I → K → ℝ) (y : I → ℝ) (b : K → ℝ) : Prop :=
  ∀ k, ∑ i, w i * X i k * (y i - ∑ l, X i l*b l) = 0

noncomputable def gramWeighted {I K : Type*} [Fintype I]
    (w : I → ℝ) (X : Matrix I K ℝ) : Matrix K K ℝ :=
  fun k l => ∑ i, w i * X i k * X i l

noncomputable def rhsWeighted {I K : Type*} [Fintype I]
    (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) : K → ℝ :=
  fun k => ∑ i, w i * X i k * y i

noncomputable def wlsCoefficient {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) : K → ℝ :=
  (gramWeighted w X)⁻¹.mulVec (rhsWeighted w X y)

structure RetainedRow (B : ℕ) where
  students : Fin B → ℕ
  assignments : Fin B → ℕ
  law : (b : Fin B) → Design (Fin (assignments b))
  exposed : (b : Fin B) → Fin (assignments b) → Fin (students b) → Bool
  y : (b : Fin B) → Fin (students b) → ℝ
  g : (b : Fin B) → Fin (students b) → ℝ
  pi : (b : Fin B) → Fin (students b) → ℝ
  pi_def : ∀ b i, pi b i = mean (law b)
    (fun z => if exposed b z i then (1:ℝ) else 0)
  pi_pos : ∀ b i, 0 < pi b i

def populationSize {B : ℕ} (r : RetainedRow B) : ℕ := ∑ b, r.students b

abbrev RowAssignment {B : ℕ} (r : RetainedRow B) := (b : Fin B) → Fin (r.assignments b)

noncomputable def rowProbability {B : ℕ} (r : RetainedRow B)
    (event : RowAssignment r → Prop) : ℝ := by
  classical
  exact ∑ w, (∏ b, (r.law b).weight (w b)) * if event w then 1 else 0

noncomputable def blockTotal {B : ℕ} (r : RetainedRow B)
    (b : Fin B) (z : Fin (r.assignments b)) : ℝ :=
  ∑ i, contribution (if r.exposed b z i then 1 else 0)
    (r.pi b i) (r.y b i) (r.g b i)

noncomputable def oracleMean {B : ℕ} (r : RetainedRow B) (w : RowAssignment r) : ℝ :=
  (∑ b, blockTotal r b (w b)) / populationSize r

noncomputable def potentialMean {B : ℕ} (r : RetainedRow B) : ℝ :=
  (∑ b, ∑ i, r.y b i) / populationSize r

noncomputable def totalBlockVariance {B : ℕ} (r : RetainedRow B) : ℝ :=
  ∑ b, variance (r.law b) (blockTotal r b)

def BlockBounds (r : ∀ B, RetainedRow (B+1)) (m : ℕ) (c eta K : ℝ) : Prop :=
  0 < c ∧ 0 < eta ∧ 0 ≤ K ∧
  ∀ B, c*(B+1) ≤ populationSize (r B) ∧
    ∀ b, (r B).students b ≤ m ∧
      ∀ i, eta ≤ (r B).pi b i ∧ |(r B).y b i| ≤ K ∧ |(r B).g b i| ≤ K

structure PairedExposure {B : ℕ} (r : RetainedRow B) where
  exposed : (b : Fin B) → Fin (r.assignments b) → Fin (r.students b) → Bool
  y : (b : Fin B) → Fin (r.students b) → ℝ
  g : (b : Fin B) → Fin (r.students b) → ℝ
  pi : (b : Fin B) → Fin (r.students b) → ℝ
  pi_def : ∀ b i, pi b i = mean (r.law b)
    (fun z => if exposed b z i then (1:ℝ) else 0)
  pi_pos : ∀ b i, 0 < pi b i

abbrev pairedRow {B : ℕ} (r : RetainedRow B)
    (s : PairedExposure r) : RetainedRow B where
  students := r.students
  assignments := r.assignments
  law := r.law
  exposed := s.exposed
  y := s.y
  g := s.g
  pi := s.pi
  pi_def := s.pi_def
  pi_pos := s.pi_pos

noncomputable def contrastBlockTotal {B : ℕ} (r : RetainedRow B)
    (s : PairedExposure r) (b : Fin B) (z : Fin (r.assignments b)) : ℝ :=
  blockTotal r b z - ∑ i, contribution
    (if s.exposed b z i then 1 else 0) (s.pi b i) (s.y b i) (s.g b i)

noncomputable def populationContrast {B : ℕ} (r : RetainedRow B)
    (s : PairedExposure r) : ℝ :=
  (∑ b, ∑ i, (r.y b i-s.y b i)) / populationSize r

noncomputable def oracleContrast {B : ℕ} (r : RetainedRow B)
    (s : PairedExposure r) (w : RowAssignment r) : ℝ :=
  (∑ b, contrastBlockTotal r s b (w b)) / populationSize r

abbrev Covariates {B : ℕ} (r : RetainedRow B) (q : ℕ) :=
  (b : Fin B) → Fin (r.students b) → Fin q → ℝ

noncomputable def fittedMean {B q : ℕ} (r : RetainedRow B)
    (x : Covariates r q) (beta : Fin q → ℝ)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : RowAssignment r) : ℝ :=
  (∑ b, ∑ i, contribution (if r.exposed b (w b) i then 1 else 0)
    (p b i) (r.y b i) (∑ k, x b i k*beta k)) / populationSize r

noncomputable def fittedCoefficient {B q : ℕ} (r : RetainedRow B)
    (x : Covariates r q)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : RowAssignment r) : Fin q → ℝ :=
  let G : Matrix (Fin q) (Fin q) ℝ := fun k l => ∑ b, ∑ i,
    (if r.exposed b (w b) i then 1 else 0)/p b i * x b i k*x b i l
  let v : Fin q → ℝ := fun k => ∑ b, ∑ i,
    (if r.exposed b (w b) i then 1 else 0)/p b i * x b i k*r.y b i
  G⁻¹.mulVec v

noncomputable def covariateGram {B q : ℕ} (r : RetainedRow B)
    (x : Covariates r q) : Matrix (Fin q) (Fin q) ℝ :=
  fun k l => (∑ b, ∑ i, x b i k*x b i l) / populationSize r

noncomputable def covariateRhs {B q : ℕ} (r : RetainedRow B)
    (x : Covariates r q) : Fin q → ℝ :=
  fun k => (∑ b, ∑ i, x b i k*r.y b i) / populationSize r

end SAP.P037a
