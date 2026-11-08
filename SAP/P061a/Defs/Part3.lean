import SAP.P061a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- The finite witness, including all unit margins and both raw hybrid readings. -/
def VersionFacts (N : ℕ) (D : AtomicDesign (Fin N → Fin 3)) : Prop :=
    (mutuallyIndependent D versionExposure ∧
    (∀ (i : Fin N) (z : Fin N → Fin 3), 0 ≤ versionResponse i z ∧ versionResponse i z ≤ 2) ∧
    (∀ (i : Fin N) (z z' : Fin N → Fin 3), z i = z' i → versionResponse i z = versionResponse i z') ∧
    positiveExposure D versionExposure 1 ∧
    positiveExposure D versionExposure 0 ∧
    (∀ i : Fin N,
      eventProbability D (fun z => z i = 1 ∧ versionExposure i z = 1) /
        exposureProbability D versionExposure i 1 = 1/2 ∧
      eventProbability D (fun z => z i = 2 ∧ versionExposure i z = 1) /
        exposureProbability D versionExposure i 1 = 1/2) ∧
    populationContrast D versionExposure versionResponse 1 0 = 3/2 ∧
    (∀ (i : Fin N) (z : Fin N → Fin 3), versionResponse i (Function.update z i 1) -
        versionResponse i (Function.update z i 0) = 1 ∧
      versionResponse i (Function.update (versionExposureAssignment z) i 1) -
        versionResponse i (Function.update (versionExposureAssignment z) i 0) = 1) ∧
    (N : ℝ)⁻¹ * ∑ i, mean D (fun z =>
      versionResponse i (Function.update z i 1) - versionResponse i (Function.update z i 0)) = 1 ∧
    populationContrast D versionExposure versionResponse 1 0 - 1 = 1/2) ∧
    (∀ i : Fin N, exposureProbability D versionExposure i 1 = 2/3 ∧
    exposureProbability D versionExposure i 0 = 1/3 ∧
    exposureMean D versionExposure versionResponse i 1 = 3/2 ∧
    exposureMean D versionExposure versionResponse i 0 = 0) ∧
    (∀ i : Fin N, unitContrast D versionExposure versionResponse i 1 0 = 3/2) ∧
    (((N : ℝ)⁻¹ * ∑ i, mean D (fun z =>
      versionResponse i (Function.update (versionExposureAssignment z) i 1) -
        versionResponse i (Function.update (versionExposureAssignment z) i 0))) = 1 ∧
    ((N : ℝ)⁻¹ * ∑ i, mean D (fun z =>
      versionResponse i (Function.update z i 1) - versionResponse i (Function.update z i 0))) = 1) ∧
    ((∀ z : Fin N → Fin 3, estimateContrast D versionExposure versionResponse 1 0 z =
      (3 / (2 * N : ℝ)) * ∑ i, ((z i).val : ℝ)) ∧
    mean D (estimateContrast D versionExposure versionResponse 1 0) = 3/2 ∧
    designVariance D (estimateContrast D versionExposure versionResponse 1 0) = 3/(2*N : ℝ) ∧
    (∀ ε : ℝ, 0 < ε → eventProbability D (fun z =>
      |estimateContrast D versionExposure versionResponse 1 0 z - 3/2| ≥ ε) ≤
        3/(2 * N * ε^2 : ℝ)))

/-- A family of independent uniform version assignments contradicts the raw-coordinate reading. -/
def T1Statement : Prop :=
  ∃ D : ∀ N, AtomicDesign (Fin N → Fin 3),
    (∀ N z, (D N).mass z = (3 : ℝ)⁻¹ ^ N) ∧
    (∀ N, 0 < N → VersionFacts N (D N)) ∧
    (¬∃ H : (Fin 2 → ℝ) → ℝ, ∀ z : Fin 2 → Fin 3,
      versionResponse 0 z = H (fun i => versionExposure i z)) ∧
    (∀ i : Fin 2, versionExposure i ![1,0] = versionExposure i ![2,0]) ∧
    versionResponse 0 ![1,0] = 1 ∧ versionResponse 0 ![2,0] = 2 ∧
    (Tendsto (fun n : ℕ =>
      populationContrast (D (n+1)) versionExposure versionResponse 1 0 - 1) atTop (𝓝 (1/2 : ℝ)) ∧
    ¬Tendsto (fun n : ℕ =>
      populationContrast (D (n+1)) versionExposure versionResponse 1 0 - 1) atTop (𝓝 0))


end SAP.P061a
