import Mathlib
import SAP.P025b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

/-! A finite sampling law and its countable iid replication experiment.
Endpoint functions are total at initially empty samples; the statements below
explicitly provide eventual nonemptiness or require a positive replicate count. -/

structure FiniteDesign (ι κ : Type*) [Fintype κ] where
  sample : κ → Finset ι
  probability : κ → ℝ
  nonnegative : ∀ ω, 0 ≤ probability ω
  total : ∑ ω, probability ω = 1

def designExpectation {ι κ : Type*} [Fintype κ] (d : FiniteDesign ι κ) (X : κ → ℝ) : ℝ :=
  ∑ ω, d.probability ω * X ω

def inclusion {ι κ : Type*} [Fintype κ] (d : FiniteDesign ι κ) (i : ι) : ℝ := by
  classical
  exact designExpectation d (fun ω => if i ∈ d.sample ω then 1 else 0)

def classTotal {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (j : Fin J) : ℝ :=
  ∑ i with cls i = j, inclusion d i

def classCount {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (j : Fin J) (ω : κ) : ℝ := by
  classical
  exact ∑ i, if cls i = j ∧ i ∈ d.sample ω then 1 else 0

def designPMF {ι κ : Type*} [Fintype κ] (d : FiniteDesign ι κ) : PMF κ :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (d.probability ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => d.nonnegative ω),d.total]
    norm_num)

def jointLaw {ι κ : Type*} [Fintype κ] [MeasurableSpace κ] (d : FiniteDesign ι κ) :
    Measure (ℕ → κ) := Measure.infinitePi (fun _ : ℕ => (designPMF d).toMeasure)

def pooledIndicator {ι κ : Type*} [Fintype κ]
    (d : FiniteDesign ι κ) (h : ℕ) (ω : ℕ → κ) : Fin h × ι → ℝ := by
  classical
  exact fun ri => if ri.2 ∈ d.sample (ω ri.1.val) then 1 else 0

def pooledLower {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (h : ℕ) (ω : ℕ → κ) : ℝ :=
  lowerEndpoint (fun ri : Fin h × ι => y (cls ri.2)) (pooledIndicator d h ω) α β

def pooledUpper {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (h : ℕ) (ω : ℕ → κ) : ℝ :=
  upperEndpoint (fun ri : Fin h × ι => y (cls ri.2)) (pooledIndicator d h ω) α β

def pooledNonempty {ι κ : Type*} [Fintype κ]
    (d : FiniteDesign ι κ) (h : ℕ) (ω : ℕ → κ) : Prop :=
  ∃ r : Fin h, (d.sample (ω r.val)).Nonempty

def censusDesign : FiniteDesign (Fin 2) (Fin 1) where
  sample := fun _ => Finset.univ
  probability := fun _ => 1
  nonnegative := fun _ => by norm_num
  total := by simp

def omitOneDesign : FiniteDesign (Fin 3) (Fin 3) where
  sample := fun ω => Finset.univ.erase ω
  probability := fun _ => 1/3
  nonnegative := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_three]

def integralityOutcomes : Fin 3 → ℝ := ![0,1,1]

def integralityClass : Fin 3 → Fin 2 := ![0,1,1]

def threeOutcomes : Fin 3 → ℝ := ![0,2,3]

def pairChoice (ω : Fin 2 × Fin 2 × Fin 2) : Fin 3 → Fin 2 := ![ω.1,ω.2.1,ω.2.2]

def pairDesign : FiniteDesign (Fin 3 × Fin 2) (Fin 2 × Fin 2 × Fin 2) where
  sample := fun ω => Finset.univ.image (fun j => (j,pairChoice ω j))
  probability := fun _ => 1/8
  nonnegative := fun _ => by norm_num
  total := by norm_num [Fintype.sum_prod_type,Fin.sum_univ_two]

end
end SAP.P025b
