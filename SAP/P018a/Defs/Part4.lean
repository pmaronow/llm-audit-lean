import Mathlib
import SAP.P018a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-- The packaged mathematical content of P018-T5. -/
def T5Statement : Prop :=
    (∀ t1 t2 σ : ℝ, sharedCov3 1 1 = !![3,1,1;1,3,1;1,1,3] ∧
    twoRoleCov3 t1 t2 σ = !![t1+t2+σ,t1,0;t1,t1+t2+σ,t2;0,t2,t1+t2+σ] ∧
    sharedCov3 1 1 ≠ twoRoleCov3 t1 t2 σ) ∧
    (glsWinv * twoRoleCov3 1 1 1 = 1 ∧
    glsR * (glsF.transpose * glsWinv * glsF) = 1 ∧
    glsR * glsF.transpose * glsWinv = glsL ∧ glsL * glsF = 1 ∧
    glsL * sharedCov3 1 1 * glsL.transpose = (1/64 : ℝ) • !![379,-135;-135,67] ∧
    glsR 0 0 / (glsL * sharedCov3 1 1 * glsL.transpose) 0 0 = 284/379 ∧
    (284/379 : ℝ) < 1) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (N : ℕ), 1 ≤ N → ∀ (a : Fin N → Ω → ℝ), iIndepFun a μ →
      (∀ i, HasLaw (a i) (gaussianReal 0 1) μ) →
      ∀ {D : ℕ} (yc : Ω → Vec D) (estimate : Vec D → ℝ),
      (∀ y c, estimate (y+c • (fun _ => 1)) = estimate y+c) →
      IndepFun yc (fun ω => (∑ i, a i ω)/(N : ℝ)) μ → Measurable estimate →
      MemLp (fun ω => estimate (yc ω)) 2 μ →
      MemLp (fun ω => estimate (yc ω+(2*(∑ i,a i ω)/(N : ℝ)) • (fun _ => 1))) 2 μ →
      ProbabilityTheory.variance
      (fun ω => estimate (yc ω+(2*(∑ i,a i ω)/(N : ℝ)) • (fun _ => 1))) μ =
        ProbabilityTheory.variance (fun ω => estimate (yc ω)) μ + 4/(N : ℝ) ∧
    4/(N : ℝ) ≤ ProbabilityTheory.variance
      (fun ω => estimate (yc ω+(2*(∑ i,a i ω)/(N : ℝ)) • (fun _ => 1))) μ)

/-- The packaged mathematical content of P018-T6. -/
def T6Statement : Prop :=
    (∀ N : ℕ, 2 ≤ N → (∀ d f : Dyad N,
      (endpointZ1 N * (endpointZ1 N).transpose) d f = (if firstUnit d = firstUnit f then 1 else 0) ∧
      (endpointZ2 N * (endpointZ2 N).transpose) d f = (if secondUnit d = secondUnit f then 1 else 0) ∧
      (endpointZ1 N * (endpointZ2 N).transpose) d f = (if firstUnit d = secondUnit f then 1 else 0) ∧
      (endpointZ2 N * (endpointZ1 N).transpose) d f = (if secondUnit d = firstUnit f then 1 else 0) ∧
      ((endpointZ1 N + endpointZ2 N) * (endpointZ1 N + endpointZ2 N).transpose) d f =
        ((members d ∩ members f).card : ℝ)) ∧
    (∀ τ σ : ℝ, sharedCov N τ σ =
      τ • (endpointZ1 N * (endpointZ1 N).transpose + endpointZ2 N * (endpointZ2 N).transpose +
        endpointZ1 N * (endpointZ2 N).transpose + endpointZ2 N * (endpointZ1 N).transpose) + σ • 1) ∧
    (3 ≤ N → ∀ τ σ : ℝ, 0 < τ → ∀ t1 t2 s : ℝ, sharedCov N τ σ ≠ twoRoleCov N t1 t2 s)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {m N : ℕ} (Z : Matrix (Fin m) (Fin N) ℝ) (a : Ω → Vec N) (ν : Ω → Vec m),
      (∀ i, MemLp (fun ω => a ω i) 2 μ) → (∀ d, MemLp (fun ω => ν ω d) 2 μ) →
      IndepFun a ν μ → ∀ τ σ : ℝ, varMat μ a = τ • 1 → varMat μ ν = σ • 1 →
      varMat μ (fun ω => Z.mulVec (a ω)+ν ω) = τ • (Z*Z.transpose) + σ • 1) ∧
    (∀ {m k : ℕ} (C : Mat m) (F : Matrix (Fin m) (Fin k) ℝ),
      IsUnit C.det → C.transpose = C → IsUnit (F.transpose * C⁻¹ * F).det →
      let G := F.transpose * C⁻¹ * F
    let L := G⁻¹ * F.transpose * C⁻¹
    L * F = 1 ∧ L * C * L.transpose = G⁻¹)

/-- The packaged mathematical content of P018-T7. -/
def T7Statement : Prop :=
    (Standing signPairKernel ∧ Proposition1Extra signPairKernel ∧
    populationGram signPairKernel = !![1,1;1,2] ∧ populationBeta signPairKernel = 0 ∧
    projectionGamma signPairKernel = !![1,1;1,1] ∧ limitingTarget signPairKernel = !![4,0;0,0] ∧
    (∀ N : ℕ, 3 ≤ N → trueTarget signPairKernel N =
      !![4*(N : ℝ)/((N : ℝ)-1),-4/((N : ℝ)-1);-4/((N : ℝ)-1),4/((N : ℝ)-1)]) ∧
    Tendsto (fun N : ℕ => (unitSampleLaw signPairKernel N {ω |
      (sampleVariance members (design signPairKernel ω) (response signPairKernel ω)) 1 1 < 0}).toReal)
      atTop (𝓝 (1-Real.exp (-1/2))) ∧
    inProbability (unitSampleLaw signPairKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design signPairKernel ω) (response signPairKernel ω) - (!![4,0;0,0] : Mat 2))) ∧
    (sampleGram degeneracyX = !![28,24;24,48] ∧
    (sampleGram degeneracyX).det = 768 ∧ sampleOLS degeneracyX degeneracyY = 0 ∧
    sampleVariance eightMembers degeneracyX degeneracyY = !![3/8,-1/48;-1/48,-13/288] ∧
    (sampleVariance eightMembers degeneracyX degeneracyY) 1 1 < 0)

/-- The packaged mathematical content of P018-T8. -/
def T8Statement : Prop :=
    ∀ {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k), Standing K →
    ((∃ ν : Measure (Vec k), centeredNormalLaw ν (limitingTarget K) ∧
      weakLimit (unitSampleLaw K) (fun N ω => Real.sqrt N • coefficientError K ω) ν) ∧
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K)) ∧
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - limitingTarget K) ∧
    ∀ c : Vec k, 0 < dot c ((limitingTarget K).mulVec c) →
      ((∀ᶠ N : ℕ in atTop, ∀ᵐ ω ∂ unitSampleLaw K N,
        0 < dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)) →
      weakLimit (unitSampleLaw K) (fun N ω =>
        dot c (coefficientError K ω) /
          Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)))
        (gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
        dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ≤ 0}).toReal)
        atTop (𝓝 0)) ∧
    (∀ (c : Vec k), 0 < dot c ((limitingTarget K).mulVec c) →
      ∀ α : ℝ, (0 < α ∧ α < 1) → Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
      0 ≤ dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ∧
      |dot c (coefficientError K ω)| ≤ normalQuantile (1-α/2) *
        Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c))}).toReal)
      atTop (𝓝 (1-α)))

/-- The packaged mathematical content of P018-T9. -/
def T9Statement : Prop :=
    ((∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < concentratedWeight d ∧ concentratedWeight d ≤ 1/8) ∧
    (∀ N : ℕ, 2 ≤ N → (9/16 : ℝ) ≤ ProbabilityTheory.variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)) ∧
    Tendsto (fun N : ℕ => ProbabilityTheory.variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N))
      atTop (𝓝 (36/35)) ∧
    (∀ N : ℕ, 8 ≤ N → (1/256 : ℝ) ≤ (unitSampleLaw signKernel N {ω |
      (N : ℝ)/2 ≤ |(N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 -
        (N : ℝ)*ProbabilityTheory.variance (fun u => weightedOLS signKernel concentratedWeight u 0)
          (unitSampleLaw signKernel N)|}).toReal) ∧
    ¬(∃ V : ℕ → ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)*ProbabilityTheory.variance
        (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)-V N)
        atTop (𝓝 0) ∧
      inProbability (unitSampleLaw signKernel) (fun N ω =>
        (N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 - V N))) ∧
    (∀ N : ℕ, 2 ≤ N → IdentDistrib (fun ω => (weightedOLS signKernel concentratedWeight ω,
      weightedVariance signKernel concentratedWeight ω))
      (fun ω => (repeatedOLS concentratedRepeated ω, repeatedVariance concentratedRepeated ω))
      (unitSampleLaw signKernel N) (repeatedLaw concentratedRepeated N))

/-- The packaged mathematical content of P018-T10. -/
def T10Statement : Prop :=
    (∀ {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k), RepeatedStanding R →
    (∃ fX : ℕ → U → U → Vec k, ∃ fY : ℕ → U → U → ℝ,
      ∀ N d (t : Fin (R.T N d)) u v,
        R.X N d t u v = fX t.val u v ∧ R.Y N d t u v = fY t.val u v) →
    (∃ T0 : ℕ, ∀ N d, R.T N d ≤ T0) → ∀ H : Mat k, H.PosDef →
    Tendsto (repeatedH R) atTop (𝓝 H) →
    Tendsto (fun N : ℕ => ((N : ℝ) / (repeatedL R N)^2) • meat members
      (fun d : Dyad N => meanVec (repeatedLaw R N)
        (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d))) atTop (𝓝 0) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • repeatedVariance R ω - repeatedTarget R N)) ∧
    (∀ {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K →
      ∀ (w : ∀ N : ℕ, Dyad N → ℝ) (a : ℕ → ℝ), (∀ N, 0 < a N) →
      (∃ C : ℝ, ∀ N d, 0 < w N d / a N ∧ w N d / a N ≤ C) →
      ∀ H : Mat k, H.PosDef →
      Tendsto (fun N : ℕ => weightedPopulationGram K (fun d => w N d / a N)) atTop (𝓝 H) →
      inProbability (unitSampleLaw K) (fun N ω =>
        (N : ℝ) • weightedVariance K (w N) ω - weightedTarget K (w N))) ∧
    (∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
      (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
      (a : ℝ), 0 < a → 2 ≤ N → ∀ ω : Fin N → U,
      (recordWeightedGram R w ω).det ≠ 0 → (recordWeightedH R w).det ≠ 0 →
      recordWeightedOLS R (fun d t => a*w d t) ω = recordWeightedOLS R w ω ∧
    recordWeightedVariance R (fun d t => a*w d t) ω = recordWeightedVariance R w ω ∧
    recordWeightedTarget R (fun d t => a*w d t) = recordWeightedTarget R w) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < concentratedWeight d ∧ concentratedWeight d ≤ 1/8) ∧
    Standing signKernel ∧ SampleRank signKernel ∧
    ¬(∃ V : ℕ → ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)*ProbabilityTheory.variance
        (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)-V N)
        atTop (𝓝 0) ∧
      inProbability (unitSampleLaw signKernel) (fun N ω =>
        (N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 - V N))

/-- The packaged mathematical content of P018-T11. -/
def T11Statement : Prop :=
    ((∀ N : ℕ, 3 ≤ N → (N : ℝ)*ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) = 4) ∧
    Tendsto (fun N : ℕ => 4/Dreal N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ)*(sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 - 4)) ∧
    (∀ N : ℕ, 3 ≤ N → (N : ℝ)*(2*(N : ℝ)-2)/(Dreal N)^2 = 4 / Dreal N ∧
    (N : ℝ)*((N : ℝ)*((N : ℝ)-1)^2)/(Dreal N)^2 = 4 ∧
    (N : ℝ)*(2*(N : ℝ)-2)/(Dreal N)^2 ≠ 4)

/-- The packaged mathematical content of P018-T12. -/
def T12Statement : Prop :=
    (∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k), RepeatedAtSize R N → 2 ≤ N →
    0 < repeatedL R N → (repeatedH R N).det ≠ 0 →
    let S := fun ω => ∑ d : Dyad N, repeatedBlockScore R (repeatedBeta R N) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    meanMat (repeatedLaw R N) (fun ω => (repeatedL R N)⁻¹ • repeatedGram R ω) = repeatedH R N ∧
    repeatedTarget R N = varMat (repeatedLaw R N) (fun ω =>
      (repeatedH R N)⁻¹.mulVec ((Real.sqrt N/repeatedL R N) • S ω)) ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (repeatedGram R ω).det ≠ 0 →
      Real.sqrt N • (repeatedOLS R ω - repeatedBeta R N) =
        ((repeatedL R N)⁻¹ • repeatedGram R ω)⁻¹.mulVec ((Real.sqrt N/repeatedL R N) • S ω))) ∧
    (∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
      (R : RepeatedKernel U k), RepeatedAtSize R N → 2 ≤ N →
      ∀ w : (d : Dyad N) → Fin (R.T N d) → ℝ, (recordWeightedH R w).det ≠ 0 →
      let S := fun ω => ∑ d : Dyad N, recordWeightedBlockScore R w (recordWeightedBeta R w) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    meanMat (repeatedLaw R N) (fun ω => (Dreal N)⁻¹ • recordWeightedGram R w ω) = recordWeightedH R w ∧
    recordWeightedTarget R w = varMat (repeatedLaw R N) (fun ω =>
      (recordWeightedH R w)⁻¹.mulVec ((Real.sqrt N / Dreal N) • S ω)) ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (recordWeightedGram R w ω).det ≠ 0 →
      Real.sqrt N • (recordWeightedOLS R w ω - recordWeightedBeta R w) =
      ((Dreal N)⁻¹ • recordWeightedGram R w ω)⁻¹.mulVec
        ((Real.sqrt N / Dreal N) • S ω))) ∧
    (∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
      (K : Kernel U k), Standing K → 2 ≤ N →
      repeatedTarget (singleRecord K) N = trueTarget K N ∧
    weightedTarget K (fun _ : Dyad N => 1) = trueTarget K N) ∧
    (∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
      (R : RepeatedKernel U k), 2 ≤ N → 0 < repeatedL R N →
      (meanMat (repeatedLaw R N) (repeatedGram R)).det ≠ 0 →
      repeatedTarget R N = ((N : ℝ)/(Dreal N)^2) •
      sandwich ((Dreal N)⁻¹ • meanMat (repeatedLaw R N) (repeatedGram R))⁻¹
        (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          repeatedBlockScore R (repeatedBeta R N) ω d)))

/-- The packaged mathematical content of P018-T13. -/
def T13Statement : Prop :=
    ((∀ d, logitY d=0 ∨ logitY d=1) ∧
    (∀ β : Vec 2, (∑ d,logLikelihood (logitX d) (logitY d) β) ≤
      ∑ d,logLikelihood (logitX d) (logitY d) 0) ∧
    (∀ β : Vec 2, (∑ d,logLikelihood (logitX d) (logitY d) β) =
      (∑ d,logLikelihood (logitX d) (logitY d) 0) → β=0) ∧
    (logisticBread logitX 0).det = 35/4 ∧
    sandwich (logisticBread logitX 0)⁻¹ (printedLogisticMeat sixMembers logitX logitR) =
      !![8/5,-2/5;-2/5,6/35] ∧
    logisticVariance sixMembers logitX logitY 0 = !![38/25,-64/175;-64/175,192/1225] ∧
    sandwich (logisticBread logitX 0)⁻¹ (printedLogisticMeat sixMembers logitX logitR) ≠
      logisticVariance sixMembers logitX logitY 0) ∧
    ((∑ d, score (logitX d) (logitR d)) = 0 ∧
    (∑ d, (1/4 : ℝ) • outer (logitX d) (logitX d)) = logitH ∧
    logitH.det = 35/4 ∧ logitHinv * logitH = 1 ∧
    printedLogisticMeat sixMembers logitX logitR = logitH ∧
    meat sixMembers (fun d => score (logitX d) (logitR d)) = !![3/2,7/2;7/2,27/2] ∧
    sandwich logitHinv logitH = logitHinv ∧
    sandwich logitHinv (!![3/2,7/2;7/2,27/2]) = !![38/25,-64/175;-64/175,192/1225] ∧
    sandwich logitHinv logitH ≠ sandwich logitHinv (!![3/2,7/2;7/2,27/2])) ∧
    (logitHinv.PosDef ∧ (!![38/25,-64/175;-64/175,192/1225] : Mat 2).PosDef) ∧
    (∀ d, logisticScore (logitX d) (logitY d) 0 = score (logitX d) (logitR d)) ∧
    (meat sixMembers (fun d => logisticScore (logitX d) (logitY d) 0) =
      (∑ i, outer (unitScore sixMembers (fun d => logisticScore (logitX d) (logitY d) 0) i)
        (unitScore sixMembers (fun d => logisticScore (logitX d) (logitY d) 0) i)) -
        dyadMeat (fun d => logisticScore (logitX d) (logitY d) 0)) ∧
    sandwich (logisticBread logitX 0)⁻¹ (printedLogisticMeat sixMembers logitX logitR) -
      logisticVariance sixMembers logitX logitY 0 = !![2/25,-6/175;-6/175,18/1225] ∧
    (∀ d, expit (dot (logitX d) 0) = 1/2 ∧
      logitY d - expit (dot (logitX d) 0) = logitR d) ∧
    logisticBread logitX 0 = logitH ∧ (logisticBread logitX 0)⁻¹ = logitHinv ∧
    (sampleGram logitX).det = 140 ∧
    (∀ d, (∑ f, if f ≠ d ∧ (sixMembers d ∩ sixMembers f).Nonempty then logitR f else 0) = 0)

end SAP.P018a
