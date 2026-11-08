import SAP.P010.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

def T3Statement : Prop :=
    (∀ upper : Bool, let μ := missingPassingPopulation upper
      populationAssumptions μ ∧ μ allPass = 1/4 ∧ noAtoms (μ.map response) ∧
      fullRealSupport μ response ∧ allMoments μ response ∧
      passRate μ 0 = 1/2 ∧ passRate μ 1 = 3/4 ∧ trimmingRatio μ 0 = 1/2 ∧
      passerDistribution μ 0 = laplaceDistribution 1 ∧ leftQuantile (passerDistribution μ 0) (1/2) = 0 ∧
      meanOn μ response ({ω | response ω ≤ 0} ∩ assigned 0) = -3/4 ∧
      meanOn μ response ({ω | 0 ≤ response ω} ∩ assigned 0) = 3/4 ∧
      meanOn μ (potentialOutcome 0) allPass = (if upper then 1 else -1) ∧
      ¬ (meanOn μ response ({ω | response ω ≤ 0} ∩ assigned 0) ≤
          meanOn μ (potentialOutcome 0) allPass ∧
        meanOn μ (potentialOutcome 0) allPass ≤
          meanOn μ response ({ω | 0 ≤ response ω} ∩ assigned 0)) ∧
      lowerEndpoint μ 0 = -1 ∧ upperEndpoint μ 0 = 1) ∧
    (missingPassingPopulation false).map (fun ω => (response ω, check ω, arm ω)) =
      (missingPassingPopulation true).map (fun ω => (response ω, check ω, arm ω))

def T4Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (h : populationAssumptions μ) (a : Fin K) (hA : 0 < μ allPass)
    (hc : noAtoms (passerDistribution μ a))
    (hi : Integrable response (μ.restrict (passed ∩ assigned a)))
    (hr : trimmingRatio μ a < 1),
    lowerEndpoint μ a ≤ meanOn μ (potentialOutcome a) allPass ∧
    meanOn μ (potentialOutcome a) allPass ≤ upperEndpoint μ a ∧
    lowerEndpoint μ a ∈ compatibleMeans μ a ∧ upperEndpoint μ a ∈ compatibleMeans μ a ∧
    (∀ m ∈ compatibleMeans μ a, lowerEndpoint μ a ≤ m ∧ m ≤ upperEndpoint μ a) ∧
    passRate μ a * (1 - trimmingRatio μ a) = 1 - ∑ b : Fin K, (1 - passRate μ b) ∧
    ((trimmingRatio μ a < 1) ↔ 0 < 1 - ∑ b : Fin K, (1 - passRate μ b)) ∧
    (trimmingRatio μ a = 0 → lowerEndpoint μ a = meanOn μ response (passed ∩ assigned a) ∧
      upperEndpoint μ a = meanOn μ response (passed ∩ assigned a)) ∧
    (let L := 1 - ∑ b : Fin K, (1 - passRate μ b)
     lowerEndpoint μ a = passRate μ a / L *
       ∫ u in (0 : ℝ)..(L / passRate μ a), realQuantile (passerDistribution μ a) u) ∧
    (let L := 1 - ∑ b : Fin K, (1 - passRate μ b)
     upperEndpoint μ a = passRate μ a / L *
       ∫ u in (1 - L / passRate μ a)..(1 : ℝ), realQuantile (passerDistribution μ a) u)

def T5Statement : Prop :=
    populationAssumptions boundedPasserPopulation ∧ boundedPasserPopulation allPass = 1/3 ∧
    noAtoms (boundedPasserPopulation.map response) ∧ fullRealSupport boundedPasserPopulation response ∧
    (∫ ω, response ω ∂boundedPasserPopulation) = 1/6 ∧
    (∫ ω, response ω ^ 2 ∂boundedPasserPopulation) = 13/63 ∧
    (∫ ω, |response ω| ^ 3 ∂boundedPasserPopulation) = 19/84 ∧
    Integrable (fun ω => |response ω| ^ 3) boundedPasserPopulation ∧
    (∀ R : ℝ, 1 ≤ R →
      (boundedPasserPopulation {ω | R < response ω}).toReal = 1/(3*(1+R)^5) ∧
      (boundedPasserPopulation {ω | response ω < -R}).toReal = 1/(3*(1+R)^5)) ∧
    (∀ a : Fin 2, passRate boundedPasserPopulation a = 1/3 ∧ trimmingRatio boundedPasserPopulation a = 2 ∧
      (∀ m ∈ compatibleMeans boundedPasserPopulation a, 0 < m ∧ m < 1) ∧
      IsGLB (extendedCompatibleMeans boundedPasserPopulation a) 0 ∧ IsLUB (extendedCompatibleMeans boundedPasserPopulation a) 1 ∧
      ¬ IsGLB (extendedCompatibleMeans boundedPasserPopulation a) ⊥ ∧ ¬ IsLUB (extendedCompatibleMeans boundedPasserPopulation a) ⊤) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      (betaPasserDistribution (Ioo 0 t)).toReal = 10*t^3 - 15*t^4 + 6*t^5 ∧
      (∀ upper : Bool, compatiblePopulations boundedPasserPopulation (betaEndpointPopulation t upper)) ∧
      (∀ a : Fin 2,
        meanOn (betaEndpointPopulation t false) (potentialOutcome a) allPass =
          t*(15/2-12*t+5*t^2)/(10-15*t+6*t^2) ∧
        0 < meanOn (betaEndpointPopulation t false) (potentialOutcome a) allPass ∧
        meanOn (betaEndpointPopulation t false) (potentialOutcome a) allPass < t ∧
        meanOn (betaEndpointPopulation t true) (potentialOutcome a) allPass =
          1 - meanOn (betaEndpointPopulation t false) (potentialOutcome a) allPass))

def T6Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (h : populationAssumptions μ) (a : Fin K) (hA : 0 < μ allPass)
    (hc : noAtoms (μ.map response))
    (hi : Integrable response (μ.restrict (passed ∩ assigned a)))
    (hr : 1 ≤ trimmingRatio μ a),
    ((1 ≤ trimmingRatio μ a) ↔ (∑ b : Fin K, passRate μ b) ≤ (K:ℝ)-1) ∧
    (passerEssentialInf μ a ≤ (meanOn μ (potentialOutcome a) allPass : EReal) ∧
      (meanOn μ (potentialOutcome a) allPass : EReal) ≤ passerEssentialSup μ a) ∧
    (∀ l : ℝ, passerEssentialInf μ a = (l : EReal) → l < meanOn μ (potentialOutcome a) allPass) ∧
    (∀ u : ℝ, passerEssentialSup μ a = (u : EReal) → meanOn μ (potentialOutcome a) allPass < u) ∧
    IsGLB (extendedCompatibleMeans μ a) (passerEssentialInf μ a) ∧ IsLUB (extendedCompatibleMeans μ a) (passerEssentialSup μ a) ∧
    (∀ l : ℝ, passerEssentialInf μ a = (l : EReal) → l ∉ compatibleMeans μ a) ∧
    (∀ u : ℝ, passerEssentialSup μ a = (u : EReal) → u ∉ compatibleMeans μ a) ∧
    ((IsGLB (extendedCompatibleMeans μ a) ⊥ ∧ IsLUB (extendedCompatibleMeans μ a) ⊤) ↔
      ((∀ M : ℝ, 0 < passerDistribution μ a (Iio M)) ∧
       (∀ M : ℝ, 0 < passerDistribution μ a (Ioi M))))

def T7Statement : Prop :=
    populationAssumptions jointDependencePopulation ∧ jointDependencePopulation sameCheck = 1 ∧
    jointDependencePopulation allPass = 1 ∧
    ¬ IndepFun (fun ω : Population 2 0 => (ω.1, check ω)) arm jointDependencePopulation ∧
    jointDependencePopulation {ω | potentialOutcome 0 ω = 0 ∧ potentialOutcome 1 ω = 0 ∧
      check ω = true ∧ arm ω = 0} = 1/4 ∧
    jointDependencePopulation {ω | potentialOutcome 0 ω = 0 ∧ potentialOutcome 1 ω = 0 ∧ check ω = true} *
      jointDependencePopulation (assigned 0) = 1/8 ∧
    meanOn jointDependencePopulation response (passed ∩ assigned 0) = 1/2 ∧
    meanOn jointDependencePopulation response (passed ∩ assigned 1) = 1/2 ∧
    meanOn jointDependencePopulation (fun ω => potentialOutcome 0 ω - potentialOutcome 1 ω) allPass = 0

def T9Statement : Prop :=
    (∀ ρ ∈ ({(1/4 : ℝ), 1/2} : Set ℝ), let μ := simulationPopulation (4/5) (4/5) ρ 1 1
      populationAssumptions μ ∧ 0 < μ allPass ∧ noAtoms (μ.map response) ∧
      fullRealSupport μ response ∧ checkCorrelation μ 0 1 = ρ ∧
      passRate μ 0 = 4/5 ∧ passRate μ 1 = 4/5 ∧ trimmingRatio μ 0 = 1/4 ∧ trimmingRatio μ 1 = 1/4) ∧
    (simulationPopulation (4/5) (4/5) (1/4) 1 1) allPass = 17/25 ∧
    (simulationPopulation (4/5) (4/5) (1/2) 1 1) allPass = 18/25 ∧
    passerDistribution (simulationPopulation (4/5) (4/5) (1/4) 1 1) 0 = normalMixture (3/20) ∧
    passerDistribution (simulationPopulation (4/5) (4/5) (1/2) 1 1) 0 = normalMixture (1/10) ∧
    passerDistribution (simulationPopulation (4/5) (4/5) (1/4) 1 1) 1 = (normalMixture (3/20)).map (fun y => -y) ∧
    passerDistribution (simulationPopulation (4/5) (4/5) (1/2) 1 1) 1 = (normalMixture (1/10)).map (fun y => -y) ∧
    (∫ y, y ∂normalMixture (3/20)) = -3/20 ∧
    (∫ y, y ∂normalMixture (1/10)) = -1/10 ∧
    (∫ y, (y+3/20)^2 ∂normalMixture (3/20)) = 451/400 ∧
    (∫ y, (y+1/10)^2 ∂normalMixture (1/10)) = 109/100 ∧
    effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/4) 1 1) =
      2*(mixtureUpperMean (3/20)-mixtureLowerMean (3/20)) ∧
    effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/2) 1 1) =
      2*(mixtureUpperMean (1/10)-mixtureLowerMean (1/10)) ∧
    effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/4) 1 1) ∈
      Icc (1798577298898/1000000000000) (1798577299027/1000000000000) ∧
    effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/2) 1 1) ∈
      Icc (1767983385194/1000000000000) (1767983385319/1000000000000) ∧
    30593913580/1000000000000 <
      effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/4) 1 1) -
      effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/2) 1 1)

def T10Statement : Prop :=
    ∀ (p₁ p₂ ρ lam σ : ℝ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hσ : 0 ≤ σ)
    (ha₀ : 0 ≤ 1-p₁-p₂+(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))))
    (ha₁ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₁)
    (ha₂ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₂)
    (ha : 0 ≤ p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))),
    (∀ (K d : ℕ) (μ ν : Measure (Population K d)), populationAssumptions μ → populationAssumptions ν →
      ∀ a : Fin K, passRate μ = passRate ν → passerDistribution μ a = passerDistribution ν a →
        correctedEndpoints μ a = correctedEndpoints ν a) ∧
    (let a := p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))
     let w₁ := 1-a/p₁
     let w₂ := 1-a/p₂
     let μ := simulationPopulation p₁ p₂ ρ lam σ
     populationAssumptions μ ∧ (μ allPass).toReal = a ∧ checkCorrelation μ 0 1 = ρ ∧
     passRate μ 0 = p₁ ∧ passRate μ 1 = p₂ ∧
     passerDistribution μ 0 = ENNReal.ofReal (1-w₁) • gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩ +
       ENNReal.ofReal w₁ • gaussianReal (-lam) ⟨σ^2,sq_nonneg σ⟩ ∧
     passerDistribution μ 1 = ENNReal.ofReal (1-w₂) • gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩ +
       ENNReal.ofReal w₂ • gaussianReal lam ⟨σ^2,sq_nonneg σ⟩ ∧
     meanOn μ response (passed ∩ assigned 0) = -lam*w₁ ∧
     meanOn μ response (passed ∩ assigned 1) = lam*w₂) ∧
    (lam ≠ 0 → ∀ ρ' : ℝ, ρ' ≠ ρ →
      -lam*(1-(p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁) ≠
      -lam*(1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁) ∧
      lam*(1-(p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂) ≠
      lam*(1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂)) ∧
    effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/4) 1 1) ≠
      effectIntervalWidth (simulationPopulation (4/5) (4/5) (1/2) 1 1)

def T13Statement : Prop :=
    populationAssumptions normalCommonPopulation ∧ normalCommonPopulation allPass = 4/5 ∧
    noAtoms (normalCommonPopulation.map response) ∧ fullRealSupport normalCommonPopulation response ∧
    (∀ a : Fin 2, passRate normalCommonPopulation a = 4/5 ∧
      passerDistribution normalCommonPopulation a = gaussianReal 0 1) ∧
    potentialTrimShare normalCommonPopulation 0 = 1/4 ∧ trimmingRatio normalCommonPopulation 0 = 1/4 ∧
    meanOn normalCommonPopulation (potentialOutcome 0) allPass = 0 ∧
    meanOn normalCommonPopulation (potentialOutcome 0) (otherArmsPass 0 ∩ wouldPass 0) = 0 ∧
    (let q := (leftQuantile (gaussianReal 0 1) (3/4)).toReal
     meanOn normalCommonPopulation (potentialOutcome 0) {ω | potentialOutcome 0 ω ≤ q} =
       -gaussianPDFReal 0 1 q / (3/4) ∧
     meanOn normalCommonPopulation (potentialOutcome 0) {ω | potentialOutcome 0 ω ≤ q} < 0 ∧
     ¬ (meanOn normalCommonPopulation (potentialOutcome 0) allPass ≤
       meanOn normalCommonPopulation (potentialOutcome 0) {ω | potentialOutcome 0 ω ≤ q})) ∧
    upperEndpoint normalCommonPopulation 0 =
      gaussianPDFReal 0 1 ((leftQuantile (gaussianReal 0 1) (1/4)).toReal) / (3/4) ∧
    0 < upperEndpoint normalCommonPopulation 0

def T14Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (hp : IsProbabilityMeasure μ) (a : Fin K) (hA : 0 < μ allPass)
    (hc : noAtoms (conditionalLaw μ (potentialOutcome a) (wouldPass a)))
    (hi : Integrable (potentialOutcome a) (μ.restrict (wouldPass a))),
    (∀ p : ℝ, 0 ≤ p → p < 1 →
      (∀ γ : Measure (ℝ × Bool), tailCoupling (conditionalLaw μ (potentialOutcome a) (wouldPass a)) p γ →
        meanOn γ Prod.fst {ω | ω.2 = true} ≤
          upperTailMean (conditionalLaw μ (potentialOutcome a) (wouldPass a)) p) ∧
      (let γ := (conditionalLaw μ (potentialOutcome a) (wouldPass a)).map
          (fun y : ℝ => (y, decide (leftQuantile (conditionalLaw μ (potentialOutcome a) (wouldPass a)) p ≤ (y : EReal))))
       tailCoupling (conditionalLaw μ (potentialOutcome a) (wouldPass a)) p γ ∧
       meanOn γ Prod.fst {ω | ω.2 = true} = upperTailMean (conditionalLaw μ (potentialOutcome a) (wouldPass a)) p)) ∧
    (∀ p q : ℝ, 0 ≤ p → p ≤ q → q < 1 →
      upperTailMean (conditionalLaw μ (potentialOutcome a) (wouldPass a)) p ≤
      upperTailMean (conditionalLaw μ (potentialOutcome a) (wouldPass a)) q) ∧
    (μ ((otherArmsPass a)ᶜ ∩ wouldPass a)).toReal / (μ (wouldPass a)).toReal ≤ potentialTrimShare μ a ∧
    (potentialTrimShare μ a < 1 → meanOn μ (potentialOutcome a) allPass ≤
      upperTailMean (conditionalLaw μ (potentialOutcome a) (wouldPass a)) (potentialTrimShare μ a))

def T15Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (h : populationAssumptions μ) (a : Fin K) (hA : 0 < μ allPass)
    (hc : noAtoms (μ.map response))
    (hi : Integrable response (μ.restrict (passed ∩ assigned a))),
    conditionalLaw μ (potentialOutcome a) (wouldPass a) = passerDistribution μ a ∧
    (∀ b, (μ (wouldPass b)).toReal = passRate μ b) ∧
    potentialTrimShare μ a = trimmingRatio μ a ∧
    (trimmingRatio μ a < 1 →
      upperTailMean (conditionalLaw μ (potentialOutcome a) (wouldPass a)) (trimmingRatio μ a) = upperEndpoint μ a ∧
      meanOn μ (potentialOutcome a) allPass = meanOn μ (potentialOutcome a) (otherArmsPass a ∩ wouldPass a) ∧
      meanOn μ (potentialOutcome a) allPass ≤ upperEndpoint μ a)

def T16Statement : Prop :=
    ∀ (q : ℝ) (hq : 0 < q) (hq1 : q < 1),
    populationAssumptions (selectionPopulation q) ∧
    covariateRandomAssignment (selectionPopulation q) ∧ covariateBalance (selectionPopulation q) ∧
    selectionPopulation q allPass = 1/3 ∧
    (∀ a, passRate (selectionPopulation q) a = 2/3) ∧
    IndepFun check arm (selectionPopulation q) ∧
    (∀ᵐ ω ∂selectionPopulation q, potentialOutcome 1 ω - potentialOutcome 0 ω = 0) ∧
    (∫ ω, (if potentialCheck 1 ω then (1:ℝ) else 0) -
      (if potentialCheck 0 ω then (1:ℝ) else 0) ∂selectionPopulation q) = 0 ∧
    meanOn (selectionPopulation q) (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω) allPass = 0 ∧
    meanOn (selectionPopulation q) (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω)
      {ω | potentialCheck 0 ω = true ∧ potentialCheck 1 ω = false} = 0 ∧
    meanOn (selectionPopulation q) (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω)
      {ω | potentialCheck 0 ω = false ∧ potentialCheck 1 ω = true} = 0 ∧
    meanOn (selectionPopulation q) response (passed ∩ assigned 0) = 0 ∧
    meanOn (selectionPopulation q) response (passed ∩ assigned 1) = 1/2 ∧
    meanOn (selectionPopulation q) response (passed ∩ assigned 1) -
      meanOn (selectionPopulation q) response (passed ∩ assigned 0) = 1/2 ∧
    (1/2 : ℝ) ≠ 0

end SAP.P010
