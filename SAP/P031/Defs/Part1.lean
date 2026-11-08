import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/- Finite means, divisor-N moments, and scalar contractions of the
two-column regression covariance estimators. Legal assignments have
at least two units per arm. Expectations are uniform finite averages. -/

def Admissible (s : Finset ι) : Prop := 1 < s.card ∧ 1 < sᶜ.card

def treatment (s : Finset ι) (i : ι) : ℝ := if i ∈ s then 1 else 0

def observed (s : Finset ι) (y1 y0 : ι → ℝ) (i : ι) : ℝ :=
  treatment s i * y1 i + (1 - treatment s i) * y0 i

def groupMean (s : Finset ι) (v : ι → ℝ) : ℝ := (∑ i ∈ s, v i) / s.card

def popVariance (v : ι → ℝ) : ℝ :=
  (∑ i, (v i - groupMean univ v) ^ 2) / Fintype.card ι

def popCovariance (v w : ι → ℝ) : ℝ :=
  (∑ i, (v i - groupMean univ v) * (w i - groupMean univ w)) / Fintype.card ι

def averageEffect (y1 y0 : ι → ℝ) : ℝ := groupMean univ y1 - groupMean univ y0

def estimate (s : Finset ι) (Y : ι → ℝ) : ℝ := groupMean s Y - groupMean sᶜ Y

def intercept (s : Finset ι) (Y : ι → ℝ) : ℝ := groupMean sᶜ Y

def designMatrix (s : Finset ι) : Matrix ι (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else treatment s i

def gramInverse (s : Finset ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (sᶜ.card : ℝ), -(1 / (sᶜ.card : ℝ));
     -(1 / (sᶜ.card : ℝ)), 1 / (s.card : ℝ) + 1 / (sᶜ.card : ℝ)]

def residual (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i - intercept s Y - treatment s i * estimate s Y

def leverage (s : Finset ι) (i : ι) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    designMatrix s i a * gramInverse s a b * designMatrix s i b

def coefficientWeight (s : Finset ι) (i : ι) : ℝ :=
  ∑ a : Fin 2, gramInverse s 1 a * designMatrix s i a

def sampleVariance (s : Finset ι) (v : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (v i - groupMean s v) ^ 2) / ((s.card : ℝ) - 1)

def neyman (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  sampleVariance s Y / s.card + sampleVariance sᶜ Y / sᶜ.card

def hr (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  ∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2

def hc2 (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  ∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i)

def hc1 (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  Fintype.card ι / ((Fintype.card ι : ℝ) - 2) * hr s Y

def hc3 (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  ∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) ^ 2

def imputed0 (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i - treatment s i * estimate s Y

def imputed1 (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i + (1 - treatment s i) * estimate s Y

def varianceExpression (M K : ℝ) (y1 y0 : ι → ℝ) : ℝ :=
  Fintype.card ι / ((Fintype.card ι : ℝ) - 1) *
      (popVariance y1 / M + popVariance y0 / K) +
    (2 * popCovariance y1 y0 - popVariance y1 - popVariance y0) /
      ((Fintype.card ι : ℝ) - 1)

def constantEffects (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  varianceExpression s.card sᶜ.card (imputed1 s Y) (imputed0 s Y)

def ols (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  (∑ i, residual s Y i ^ 2) / ((Fintype.card ι : ℝ) - 2) * gramInverse s 1 1

def expectation (M : ℕ) (f : Finset ι → ℝ) : ℝ :=
  (∑ s ∈ (univ : Finset ι).powersetCard M, f s) /
    ((univ : Finset ι).powersetCard M).card

def randomizationVariance (M : ℕ) (y1 y0 : ι → ℝ) : ℝ :=
  expectation M (fun s =>
    (estimate s (observed s y1 y0) -
      expectation M (fun t => estimate t (observed t y1 y0))) ^ 2)

def proofExampleOutcomes : Fin 4 → ℝ := ![0, 2, 5, 9]

def proofExampleTreated : Finset (Fin 4) := {0, 1}

end
end SAP.P031
