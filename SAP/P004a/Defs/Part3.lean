import SAP.P004a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P004a
universe u v
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

def T1Statement : Prop :=
  (∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
      LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat ∧
      threeTypeTheta ∈ interior threeTypeParameterSet ∧
      SpatialLocalConditions threeTypePopulation ∧
      Overlap (fun N => propensities (threeTypeONat N) threeTypeTheta) ∧
      (∀ N : ℕ, 0 < N → WellDefined (threeTypePopulation N) 0) ∧
      (∀ N, homophilyQ (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0) (fun i => {i})
        (printedFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) = 0) ∧
      Nondegenerate (fun N => variance (propensities (threeTypeONat N) threeTypeTheta)
        (augmented (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0)
          (printedFits (propensities (threeTypeONat N) threeTypeTheta)
            (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)))) ∧
      ¬ LittleOp (fun N => propensities (threeTypeONat N) threeTypeTheta)
        (fun N z => augmented (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0)
          (printedFits (propensities (threeTypeONat N) threeTypeTheta)
            (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) z -
          fittedIPW (circleAverage (threeTypePopulation N) 0)
            (threeTypeONat N) (θhat N) z)
        (fun N => (Real.sqrt N)⁻¹)) ∧
  (let w : Fin 3 → ℝ := ![2/9,1/4,2/9]
    let a : Fin 3 → ℝ := ![27/250,-24/125,27/250]
    let b : Fin 3 → ℝ := ![-81/1000,16/125,-81/1000]
    (∑ t, w t*(a t)^2)/3 = (3/625 : ℝ) ∧
    (∑ t, w t*(b t)^2)/3 = (1753/750000 : ℝ) ∧
    (∑ t, w t*(a t-b t)^2)/3 = (10369/750000 : ℝ) ∧
    (0 : ℝ) < 10369/750000)


def T2AsymptoticStatement : Prop :=
  ∀ {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ)
    (hd : 0 ≤ d) (hh : 0 ≤ h) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) (hinterior : θ₀ ∈ interior Θ)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀)),
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    let B := spatialNeighborhoods P h
    let V := fun N => variance (p N) (augmented (p N) (R N) (scoreFits (p N) (R N) (O N)))
    BigOp p (fun N z => fittedIPW (R N) (O N) (θhat N) z -
      (ht (p N) (R N) z - (∑ i, (bit (z i)-p N i)*dot (O N i) (scoreGamma (p N) (R N) (O N)))/N))
      (fun N => (N : ℝ)⁻¹) ∧
    LittleOp p (fun N z => augmented (p N) (R N) (scoreFits (p N) (R N) (O N)) z -
      fittedIPW (R N) (O N) (θhat N) z) (fun N => (Real.sqrt N)⁻¹) ∧
    (Nondegenerate V →
      NormalLimit p (fun N z => (fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N))/Real.sqrt (V N)) ∧
      ∀ α : ℝ, 0 < α → α < 1 →
        Conservative (fun N => prob (p N) (fun z =>
          let phat := propensities (O N) (θhat N z)
          |fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)| ≤ normalQuantile (1-α/2) *
            Real.sqrt (rawSAH phat (R N) (B N) (fittedScoreFits phat (R N) (O N) z) z))) α ∧
        ((∀ N, 0 ≤ homophilyQ (p N) (R N) (B N) (printedFits (p N) (R N) (O N))) →
          Conservative (fun N => prob (p N) (fun z =>
            let phat := propensities (O N) (θhat N z)
            |fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)| ≤ normalQuantile (1-α/2) *
              Real.sqrt (max (oracleHAC phat (R N) (B N) (fittedScoreFits phat (R N) (O N) z) z) 0))) α))


def T2FiniteStatement : Prop :=
  ∀ {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (B : Fin N → Finset (Fin N)),
    0 < N → (∀ i, 0 < p i ∧ p i < 1) → IsUnit (information p O).det →
    (∀ i, i ∈ B i) → (∀ i j, j ∈ B i ↔ i ∈ B j) →
    (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
    (∀ i, scoreFits p R O i true - scoreFits p R O i false =
      printedFits p R O i true - printedFits p R O i false ∧
      scoreFits p R O i true / p i + scoreFits p R O i false / (1-p i) =
        dot (O i) (scoreGamma p R O)) ∧
    (∀ z, augmented p R (scoreFits p R O) z = ht p R z -
      (∑ i, (bit (z i)-p i)*dot (O i) (scoreGamma p R O)) / N) ∧
    (∀ i, expect p (residualContrast p R (scoreFits p R O) i) =
      residualEffect p R (printedFits p R O) i) ∧
    expect p (augmented p R (scoreFits p R O)) = ame p R ∧
    variance p (augmented p R (scoreFits p R O)) =
      secondMomentBound p R B (scoreFits p R O) - homophilyQ p R B (scoreFits p R O) / N ∧
    expect p (oracleHAC p R B (scoreFits p R O)) =
      variance p (augmented p R (scoreFits p R O)) + homophilyQ p R B (printedFits p R O) / N ∧
    variance p (augmented p R (scoreFits p R O)) ≤ expect p (rawSAH p R B (scoreFits p R O))


def T2Statement : Prop :=
  T2AsymptoticStatement (Space := Space) ∧ T2FiniteStatement


def T3Statement : Prop :=
  ∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
      LogisticConditions activeO activeTheta activeParameterSet θhat ∧
      activeTheta ∈ interior activeParameterSet ∧ SpatialLocalConditions activePopulation ∧
      (∀ N, 0 ≤ homophilyQ (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
        (fun i => {i}) (printedFits (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0) (activeO N))) ∧
      Overlap (fun N => propensities (activeO N) activeTheta) ∧
      (∀ N : ℕ, 0 < N → WellDefined (activePopulation N) 0) ∧
      Nondegenerate (fun N => variance (propensities (activeO N) activeTheta)
        (augmented (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
          (printedFits (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0) (activeO N)))) ∧
      (∀ᶠ N in atTop, 0 < variance (propensities (activeO N) activeTheta)
        (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (θhat N))) ∧
      InProb (fun N => propensities (activeO N) activeTheta) (fun N z =>
        let R := circleAverage (activePopulation N) 0
        let phat := propensities (activeO N) (θhat N z)
        let g := fun i a => dot (activeO N i) (fittedBeta phat R (activeO N) a z)
        printedSAH phat R (fun i => {i}) g z /
          variance (propensities (activeO N) activeTheta) (fittedIPW R (activeO N) (θhat N)) - 8/25)


def T4Statement : Prop :=
  (∀ {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N)
    (hN : 0 < N) (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (hp : ∀ i, 0 < phat i ∧ phat i < 1),
    rawSAH phat R B g z =
      (∑ i, bit (z i) * (B i).card * (weightedEpsilon phat R g z i)^2) / (armCount z true)^2 +
      (∑ i, (1-bit (z i)) * (B i).card * (weightedEpsilon phat R g z i)^2) / (armCount z false)^2 ∧
    printedSAH phat R B g z =
      (∑ i, (B i).card * ((armCount z true / N)^2 * bit (z i) * (R i z-g i true)^2 / (phat i)^4 +
        (armCount z false / N)^2 * (1-bit (z i)) * (R i z-g i false)^2 / (1-phat i)^4)) / (N : ℝ)^2) ∧
  (∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hself : ∀ i, i ∈ B i) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i →
      cov p (residualContrast p R g i) (residualContrast p R g j) = 0),
    variance p (fun z => (∑ i, residualContrast p R g i z) / N) ≤ sahLimit p R B g ∧
    sahLimit p R B g = expect p (rawSAH p R B g))


def T5Statement : Prop :=
  armCount areaWitnessAssignment true = 1 ∧ armCount areaWitnessAssignment false = 1 ∧
    (∀ j : Fin 6, circleAverage areaBinaryPopulation (j : ℝ) = areaWitnessTable j) ∧
    (∀ i : Fin 2, region areaBinaryPopulation i 6 =
      ⋃ j : Fin 6, region areaBinaryPopulation i (j : ℝ)) ∧
    (∀ i : Fin 2, Pairwise (fun j k : Fin 6 =>
      Disjoint (region areaBinaryPopulation i (j : ℝ))
        (region areaBinaryPopulation i (k : ℝ)))) ∧
    (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
    (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧
    WellDefined areaBinaryPopulation 6 ∧
    (∀ i (j : Fin 6), (volume (region areaBinaryPopulation i j)).toReal =
      Real.pi * (2 * (j : ℝ) + 1)) ∧
    (∑ j : Fin 6, hajek (circleAverage areaBinaryPopulation j) areaWitnessAssignment) =
      -(17 / 500 : ℝ) ∧
    (∑ j : Fin 6, ame (fun _ => 1 / 2) (circleAverage areaBinaryPopulation j)) =
      -(17 / 500 : ℝ) ∧
    ame (fun _ => 1 / 2) (circleAverage areaBinaryPopulation 6) = (121 / 18000 : ℝ) ∧
    (0 : ℝ) < 121 / 18000 ∧ -(17 / 500 : ℝ) ≠ 121 / 18000


def T6AggregationStatement : Prop :=
  ∀ {A : Type*} [MeasurableSpace A] {N m : ℕ}
    (ζ : Measure A) (B : Fin N → Fin m → Set A) (Y : A → Assignment N → ℝ)
    (p : Fin N → ℝ), 0 < N → 0 < m →
    (∀ i k, MeasurableSet (B i k)) →
    (∀ i, Pairwise (fun j k => Disjoint (B i j) (B i k))) →
    (∀ i k, 0 < ζ (B i k) ∧ ζ (B i k) < ⊤) →
    (∀ i k z, IntegrableOn (fun x => Y x z) (B i k) ζ) →
    (∀ i, 0 < p i ∧ p i < 1) →
    let a := fun i k => (ζ (B i k)).toReal
    let R := fun k i z => (∫ x in B i k, Y x z ∂ζ) / a i k
    let whole := fun i z => (∫ x in ⋃ k, B i k, Y x z ∂ζ) / (ζ (⋃ k, B i k)).toReal
    (∀ i z, whole i z = finiteAverage (a i) (fun k => R k i z)) ∧
    (∀ i arm, marginal p whole i arm = finiteAverage (a i) (fun k => marginal p (R k) i arm)) ∧
    (∀ i, nodeEffect p whole i = finiteAverage (a i) (fun k => nodeEffect p (R k) i)) ∧
    ame p whole = (∑ i, finiteAverage (a i) (fun k => nodeEffect p (R k) i))/N ∧
    (∀ i lo hi, (∀ k, lo ≤ nodeEffect p (R k) i ∧ nodeEffect p (R k) i ≤ hi) →
      lo ≤ nodeEffect p whole i ∧ nodeEffect p whole i ≤ hi) ∧
    (∀ i c, (∀ k, a i k = c) → nodeEffect p whole i = (∑ k, nodeEffect p (R k) i)/m)


def T6Statement : Prop :=
  T6AggregationStatement.{u} ∧
  (∀ (c s t : ℝ) (hc : 0 < c),
    |c * s| ≥ |c * t| ↔ |s| ≥ |t|) ∧
  (∀ {N : ℕ} (w : Assignment N → ℝ) (T : Assignment N → ℝ)
    (obs : Assignment N) (c : ℝ), 0 < c →
    (∑ z, w z * (if |c * T z| ≥ |c * T obs| then (1 : ℝ) else 0)) =
      ∑ z, w z * (if |T z| ≥ |T obs| then (1 : ℝ) else 0))


def T7FiniteStatement : Prop :=
  (armCount starAssignment20 true = 10 ∧ armCount starAssignment20 false = 10 ∧
    armMean (starBlockTable 4) starAssignment20 true = 0 ∧
    armMean (starBlockTable 4) starAssignment20 false = 0 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 false) = 4/25 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 true) = 4/25 ∧
    adjustmentMu starAssignment20 (starBlockKernel 4 false) = 41/50 ∧
    adjustmentMu starAssignment20 (starBlockKernel 4 true) = 101/100 ∧
    (16/101 : ℝ) < 8/41) ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 true) /
      adjustmentMu starAssignment20 (starBlockKernel 4 true) = 16/101 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 false) /
      adjustmentMu starAssignment20 (starBlockKernel 4 false) = 8/41


def T7Statement : Prop :=
  T7FiniteStatement ∧
    SpatialLocalConditions starPopulation ∧
    (∀ N : ℕ, 0 < N → WellDefined (starPopulation N) 0) ∧
    (∀ N, homophilyQ (fun _ => 1/2) (circleAverage (starPopulation N) 0)
      (spatialNeighborhoods starPopulation (6/5) N)
      (fun _ a => barMu (fun _ => 1/2) (circleAverage (starPopulation N) 0) a) = 0) ∧
    Nondegenerate (fun N => variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (circleAverage (starPopulation N) 0))) ∧
    (∀ m, uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5) = starBlockKernel m false) ∧
    (∀ N, LocalAt (circleAverage (starPopulation N) 0) (nodeSeparation (starPopulation N)) (6/5)) ∧
    (∀ m : ℕ, 0 < m → (5*m : ℝ) * variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (starBlockTable m)) = 16/5) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
        let Q := starBlockKernel m true
        let μ := adjustmentMu z Q
        let ν := adjustmentNu z Q
        0 < armCount z true ∧ 0 < armCount z false ∧ 0 < μ ∧ 0 < ν ∧
        |hajek (starBlockTable m) z| ≤ studentQuantile (2*μ^2/ν) (39/40) *
          Real.sqrt (kernelVariance z (residual (starBlockTable m) z) Q/μ)) <
        2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1+ε) ∧
    2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1 < 19/20


def T8FiniteStatement : Prop :=
  ∀ {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (horth : vectors.transpose * vectors = 1)
    (z : Assignment N) (e : Fin N → ℝ)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (critical c err : ℝ) (hc : 0 ≤ critical ∧ critical ≤ c),
    let K := spectralKernel values vectors false
    let Q := spectralKernel values vectors true
    let V := cappedVariance (kernelVariance z e Q) (adjustmentMu z Q)
    kernelVariance z e Q ≤ V ∧ max (kernelVariance z e K) 0 ≤ kernelVariance z e Q ∧
    (0 ≤ kernelVariance z e K → |err| ≤ critical*Real.sqrt (kernelVariance z e K) →
      |err| ≤ c*Real.sqrt V)


def T8AsymptoticStatement : Prop :=
  ∀ (P : PopulationSequence Space) (p d h α : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hh : 0 ≤ h) (hα : 0 < α ∧ α < 1)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hv : Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))
    (values : ∀ N, Fin N → ℝ) (vectors : ∀ N, Matrix (Fin N) (Fin N) ℝ)
    (horth : ∀ N, (vectors N).transpose * vectors N = 1)
    (heigen : ∀ N, spectralKernel (values N) (vectors N) false = uniformDistanceKernel (nodeSeparation (P N)) h)
    (hhom : ∀ᶠ N in atTop, 0 ≤ homophilyQ (fun _ => p) (circleAverage (P N) d) (spatialNeighborhoods P h N)
      (fun _ a => barMu (fun _ => p) (circleAverage (P N) d) a))
    (c : ∀ N, Assignment N → ℝ) (hc : ∀ N z, normalQuantile (1-α/2) ≤ c N z),
    Conservative (fun N => prob (fun _ => p) (fun z =>
      let R := circleAverage (P N) d
      let Q := spectralKernel (values N) (vectors N) true
      0 < armCount z true → 0 < armCount z false →
      |hajek R z-ame (fun _ => p) R| ≤ c N z *
        Real.sqrt (cappedVariance (kernelVariance z (residual R z) Q) (adjustmentMu z Q)))) α


def T8Statement : Prop :=
  T8FiniteStatement ∧ T8AsymptoticStatement (Space := Space)

end
end SAP.P004a
