import SAP.P027b.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

/-- Exact mean-scale design identities, including the with-replacement estimator. -/
def PeriodicFixed : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ), (∑ k, z k) = 0 →
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
    let Q := ∑ k, z k^2
    let N : ℝ := m*(2*r)
    let V := periodicMeanV hr z
    let H := periodicMeanH hr z
    let C := periodicMeanC hr z
    let W := periodicMeanW hr z
    V = (∑ g, Y g^2/phaseProb r g)/N^2 ∧
    H = V-(∑ g, Y g^2)/N^2 ∧ 0 ≤ (∑ g, Y g^2)/N^2 ∧
    C-H = (N-m)*Q/N^2 ∧
    W = ((m:ℝ)*(∑ g, Qg g/phaseProb r g)-N^2*V)/(N^2*((m:ℝ)-1))

/-- Actual model moments on the original population-mean scale. -/
def PeriodicModel : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m) (β σ2 : ℝ), 0 ≤ σ2 →
    ∀ ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ, NoiseMoments μ ε σ2 →
    let z := centeredOutcomes phaseSize β ε
    let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
    let q : ℝ := 2*r
    let N : ℝ := m*q
    let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
    let B := fun ξ => (∑ g, Y ξ g^2)/N^2
    let V := outcomeE μ (fun ξ => periodicMeanV hr (z ξ))
    let H := outcomeE μ (fun ξ => periodicMeanH hr (z ξ))
    let C := outcomeE μ (fun ξ => periodicMeanC hr (z ξ))
    let W := outcomeE μ (fun ξ => periodicMeanW hr (z ξ))
    let Q := outcomeE μ (fun ξ => ∑ k, z ξ k^2)
    (∀ g, outcomeE μ (fun ξ => Y ξ g^2) = L) ∧
    outcomeE μ B = 16*β^2/q+σ2*(N-m)/N^2 ∧
    V = (9*q/5)*outcomeE μ B ∧ H = V-outcomeE μ B ∧
    (0 < V → (H-V)/V = -5/(9*q)) ∧
    Q = 16*N*β^2+(N-1)*σ2 ∧ C = H+(N-m)/N^2*Q ∧ W = (9/5)*σ2/m ∧
    (∀ ρ : ℝ, σ2 = 900*(1-ρ^2) → β^2 = 900*ρ^2*(N-1)/(16*N) →
      (V,H,C,W) = periodicModelPredictions N m ρ ∧ Q = 900*(N-1))

/-- The orthogonal decomposition, its dimensions, and exact cancellation of signal. -/
def PeriodicDiagonalization : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ), (∑ k, z k) = 0 →
    Module.finrank ℝ (phaseCenteredSpace r m) = m*(2*r)-1 ∧
    Module.finrank ℝ (phaseWithinSpace r m) = m*(2*r)-2*r ∧
    Module.finrank ℝ (phaseSignalSpace r m) = 1 ∧
    Module.finrank ℝ (phaseParitySpace r m false) = r-1 ∧
    Module.finrank ℝ (phaseParitySpace r m true) = r-1 ∧
    (∀ (i j : Fin 4) (v w : (Σ _ : Fin r × Fin 2, Fin m) → ℝ),
      i ≠ j → v ∈ phaseComponentSpace r m i → w ∈ phaseComponentSpace r m j →
      (∑ k, v k*w k) = 0) ∧
    Nonempty (PhaseDecomposition r m z) ∧
    (∀ d₁ d₂ : PhaseDecomposition r m z,
      d₁.within = d₂.within ∧ d₁.signal = d₂.signal ∧ d₁.low = d₂.low ∧ d₁.high = d₂.high) ∧
    (∀ d : PhaseDecomposition r m z, periodicContrast hr z =
      (((m:ℝ)*(2*r)-m)/((m:ℝ)*(2*r))^2)*
        (populationSquareNorm d.within+contrastCoefficient (2*r)*
          (populationSquareNorm d.high-populationSquareNorm d.low)) ∧
      -(((m:ℝ)*(2*r)-m)*contrastCoefficient (2*r)/((m:ℝ)*(2*r))^2)*
        populationSquareNorm d.low ≤ periodicContrast hr z) ∧
    (∀ β : ℝ, periodicContrast hr (fun k => β*(phaseSize k-6)+z k) = periodicContrast hr z)

/-- Independent chi-square representation and strictly positive contrast mean. -/
def PeriodicGaussian : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m) (β σ2 : ℝ), 0 < σ2 →
    ∀ ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ, GaussianNoise μ ε σ2 →
    let z := centeredOutcomes phaseSize β ε
    let N : ℝ := m*(2*r)
    let a := (N-m)*σ2/N^2
    let c := contrastCoefficient (2*r)
    (∃ X : Fin 3 → Ξ → ℝ, iIndepFun X μ ∧
      μ.map (X 0) = chiSquaredLaw (m*(2*r)-2*r) ∧
      μ.map (X 1) = chiSquaredLaw (r-1) ∧ μ.map (X 2) = chiSquaredLaw (r-1) ∧
      (∀ᵐ ξ ∂μ, periodicContrast hr (z ξ) = a*(X 0 ξ+c*(X 1 ξ-X 2 ξ)))) ∧
    outcomeE μ (fun ξ => periodicContrast hr (z ξ)) = a*(N-2*r) ∧
    0 < outcomeE μ (fun ξ => periodicContrast hr (z ξ))

/-- The lower-tail bound for any positive number of generated populations. -/
def PeriodicTail : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (r m K : ℕ) (hr : 0 < r) (hm : 2 ≤ m) (hK : 0 < K) (β σ2 ℓ : ℝ),
    0 < σ2 → 0 < ℓ →
    ∀ ε : Fin K → (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ,
    (∀ i, GaussianNoise μ (ε i) σ2) →
    let z := fun i => centeredOutcomes phaseSize β (ε i)
    let N : ℝ := m*(2*r)
    let a := (N-m)*σ2/N^2
    let c := contrastCoefficient (2*r)
    let k := a*c
    let d : ℝ := r-1
    let Tbar := fun ξ => (∑ i, periodicContrast hr (z i ξ))/(K:ℝ)
    let prob := (μ {ξ | Tbar ξ ≤ -ℓ}).toReal
    let J : ℤ := ⌊ℓ/(4*k)⌋
    let h : ℤ := ⌈d/2⌉
    prob ≤ Real.exp (-ℓ/(4*k))*(2:ℝ)^(d/2) ∧
    (h < J → Real.exp (-ℓ/(4*k))*(2:ℝ)^(d/2) ≤ (2:ℝ)^(-((J-h):ℝ)))

/-- Rounding-compatible simultaneous printed HT and C2 means are very unlikely. -/
def PeriodicRows : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (row : Fin 4) (K : ℕ) (hK : 0 < K) (β : ℝ)
    (ε : Fin K → (Σ _ : Fin (a3HighR row) × Fin 2, Fin (a3HighM row)) → Ξ → ℝ),
    (∀ i, GaussianNoise μ (ε i) 17.91) →
    let hr : 0 < a3HighR row := by fin_cases row <;> norm_num [a3HighR]
    let z := fun i => centeredOutcomes phaseSize β (ε i)
    let Hbar := fun ξ => (∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)
    let Cbar := fun ξ => (∑ i, periodicMeanC hr (z i ξ))/(K:ℝ)
    (μ {ξ | |Hbar ξ-a3HighH row| ≤ 0.005 ∧ |Cbar ξ-a3HighC row| ≤ 0.005}).toReal ≤
      ((2:ℝ)^(a3HighExponent row))⁻¹

/-- Calibrated moment predictions and exact arithmetic for all four printed rows. -/
def PeriodicNumerics : Prop :=
  periodicModelPredictions 120 30 0.99 = (1575.3366,1356.53985,2025.91485,1.0746) ∧
  periodicModelPredictions 600 30 0.99 = (1586.1366,1542.07725,2395.65225,1.0746) ∧
  periodicModelPredictions 240 60 0.99 = (1581.5493,1361.889675,2034.077175,0.5373) ∧
  periodicModelPredictions 1200 60 0.99 = (1586.9493,1542.867375,2397.154875,0.5373) ∧
  (-5/(9*4):ℝ) = -5/36 ∧ (-5/(9*20):ℝ) = -1/36 ∧
  (∀ row : Fin 4,
    a3HighC row-(1+contrastR (2*a3HighR row))*a3HighH row = a3HighContrast row ∧
    (0.005:ℝ)*(2+contrastR (2*a3HighR row)) =
      (if a3HighR row = 2 then 77/6200 else 89/7000) ∧
    ((2:ℝ)^(a3HighExponent row))⁻¹ ≤
      (if row = 0 then (10:ℝ)^(-56:ℤ) else if row = 1 then (10:ℝ)^(-64:ℤ)
       else if row = 2 then (10:ℝ)^(-157:ℤ) else (10:ℝ)^(-111:ℤ)))

/-- Rowwise positivity, contrast, rounding, and integer tail-exponent certificates
for the four printed Table A3 means. -/
def PeriodicRowCertificates : Prop :=
  ∀ row : Fin 4,
    let R := contrastR (2*a3HighR row)
    let N : ℝ := a3HighM row*(2*a3HighR row)
    let ℓ := -a3HighContrast row-(0.005:ℝ)*(2+R)
    let k := ((N-a3HighM row)*17.91/N^2)*contrastCoefficient (2*a3HighR row)
    0 < ℓ ∧ 0 < k ∧
    R = (if a3HighR row = 2 then 15/31 else 19/35) ∧
    (⌊ℓ/(4*k)⌋-⌈((a3HighR row:ℝ)-1)/2⌉ : ℤ) = (a3HighExponent row:ℤ) ∧
    (∀ H C : ℝ, |H-a3HighH row| ≤ 0.005 → |C-a3HighC row| ≤ 0.005 →
      C-(1+R)*H ≤ -ℓ)

/-- The complete corrected claim, including the rowwise rounding certificates. -/
def T19Statement : Prop :=
  PeriodicFixed ∧ PeriodicModel ∧ PeriodicDiagonalization ∧ PeriodicGaussian ∧
  PeriodicTail ∧ PeriodicRows ∧ PeriodicNumerics ∧ PeriodicRowCertificates

end
end SAP.P027b
