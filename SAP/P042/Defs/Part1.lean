import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

def precisionWeight {ι : Type*} (v : ι → ℝ) (j : ι) : ℝ := (v j)⁻¹

def totalWeight {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ j, precisionWeight v j

def normalizedWeight {ι : Type*} [Fintype ι] (v : ι → ℝ) (j : ι) : ℝ :=
  precisionWeight v j / totalWeight v

def pooled {ι Ω : Type*} [Fintype ι] (a : ι → ℝ) (D : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, a j * D j ω

def diagonalVariance {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ∑ j, (normalizedWeight v j)^2 * v j

def covarianceForm {ι : Type*} [Fintype ι] (a : ι → ℝ) (Sigma : ι → ι → ℝ) : ℝ :=
  ∑ j, ∑ k, a j * a k * Sigma j k

def offDiagonal {J : ℕ} (a : Fin J → ℝ) (Sigma : Fin J → Fin J → ℝ) : ℝ :=
  ∑ j, ∑ k ∈ Finset.univ.filter (fun k => j < k), a j * a k * Sigma j k

noncomputable def subsetWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ι) (v : ι → ℝ) (j : ι) : ℝ :=
  if j ∈ P then (v j)⁻¹ / (∑ k ∈ P, (v k)⁻¹) else 0

def armSampleMean {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => (∑ i, X i ω)/(n:ℝ)

noncomputable def effectCorrelation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  covariance X Y μ / (Real.sqrt (variance X μ) * Real.sqrt (variance Y μ))

def finiteExpectation {Ω : Type*} (s : Finset Ω) (X : Ω → ℝ) : ℝ :=
  (∑ ω ∈ s, X ω)/(s.card:ℝ)

def finiteCovariance {Ω : Type*} (s : Finset Ω) (X Y : Ω → ℝ) : ℝ :=
  finiteExpectation s (fun ω =>
    (X ω - finiteExpectation s X)*(Y ω - finiteExpectation s Y))

def completeThreeAllocations (N : ℕ) (n : Fin 3 → ℕ) : Finset (Fin N → Fin 4) :=
  Finset.univ.filter (fun z => ∀ g : Fin 3,
    (Finset.univ.filter (fun i => z i = Fin.castLE (by decide : 3 ≤ 4) g)).card = n g)

def populationMean {N : ℕ} (Y : Fin N → ℝ) : ℝ := (∑ i, Y i)/(N:ℝ)

def populationCovariance {N : ℕ} (Y V : Fin N → ℝ) : ℝ :=
  (∑ i, (Y i-populationMean Y)*(V i-populationMean V))/((N-1:ℕ):ℝ)

def randomizedArmMean {N : ℕ} (n : Fin 3 → ℕ) (Y : Fin N → Fin 3 → ℝ)
    (g : Fin 3) (z : Fin N → Fin 4) : ℝ :=
  (∑ i, if z i = Fin.castLE (by decide : 3 ≤ 4) g then Y i g else 0)/(n g:ℝ)

end
end SAP.P042
