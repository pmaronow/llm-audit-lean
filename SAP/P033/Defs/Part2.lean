import SAP.P033.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

noncomputable section

/-- Exported deterministic certificate for the specified witness. -/
def M1Certificate : Prop :=
  m1Gram 1 = !![2,4/5;4/5,2/5] ∧
    Matrix.det (m1Gram 1) = 4/25 ∧
    m1Gram 2 = !![2,4/5,2/5;4/5,2/5,146/625;2/5,146/625,94/625] ∧
    Matrix.det (m1Gram 2) = 168/390625 ∧
    (∀ i, m1Linear i = m1Kernel i * ((5/2 : ℝ)-5*m1Distance i)) ∧
    (∀ i, m1Curvature i = m1Kernel i *
      ((125/2 : ℝ)-(14375/42)*m1Distance i+(15625/42)*m1Distance i^2)) ∧
    (∀ i, m1Corrected i = m1Kernel i *
      ((13 : ℝ)-(125/2)*m1Distance i+(125/2)*m1Distance i^2)) ∧
    (∑ i, m1Linear i) = 1 ∧ (∑ i, m1Linear i*m1Distance i) = 0 ∧
    (∑ i, m1Linear i*m1Distance i^2) = m1BiasMoment ∧
    (∑ i, m1Curvature i) = 0 ∧ (∑ i, m1Curvature i*m1Distance i) = 0 ∧
    (∑ i, m1Curvature i*m1Distance i^2) = 1 ∧
    (∑ i, m1Corrected i) = 1 ∧ (∑ i, m1Corrected i*m1Distance i) = 0 ∧
    (∑ i, m1Corrected i*m1Distance i^2) = 0 ∧
    (2*∑ i, m1Linear i^2) = 83/25 ∧ (2*∑ i, m1Corrected i^2) = 82/5 ∧
    (∑ i, m1Bias i^2) = 243/50 ∧ (∑ i, m1Linear i*m1Bias i) = -21/25 ∧
    ((83/50 : ℝ)+(243/50)-2*(-21/25) = 41/5) ∧
    (∑ i, m1Linear i*m1Observed (0,i)) = 211/100 ∧
    (∑ i, m1Linear i*m1Observed (1,i)) = 611/100 ∧
    (∑ i, m1Corrected i*m1Observed (0,i)) = 52/25 ∧
    (∑ i, m1Corrected i*m1Observed (1,i)) = 152/25 ∧
    rdEstimator m1Linear m1Observed = 4 ∧ rdEstimator m1Corrected m1Observed = 4 ∧
    ((16 : ℝ)/(83/25) = 400/83 ∧ (16 : ℝ)/(82/5) = 40/41 ∧
      (40/41 : ℝ) < (49/25)^2 ∧ (49/25 : ℝ)^2 < 400/83)

/-- Exported deterministic certificate for the specified witness. -/
def M2Certificate : Prop :=
  (∀ x, m2Perturbation x = 20-(625/3)*x+(4375/6)*x^2-(3125/3)*x^3+(3125/6)*x^4) ∧
    Continuous m2Treated ∧
    (∀ i, m2Perturbation (m1Distance i) = 0) ∧
    m2Perturbation 0 = 20 ∧ rdEffect m2Treated m1Control 0 = 24 ∧
    (∀ i, m2Treated (m1Distance i) = m1Treated (m1Distance i))

/-- Exported deterministic certificate for the specified witness. -/
def ClusterCertificate : Prop :=
  clusterGram 1 = !![25/2,175/6;175/6,175/2] ∧
    Matrix.det (clusterGram 1) = 4375/18 ∧
    clusterGram 2 = !![25/2,175/6,175/2;175/6,175/2,1855/6;175/2,1855/6,2415/2] ∧
    Matrix.det (clusterGram 2) = 61250/9 ∧
    (∑ g, clusterLinear g^2) = 62/25 ∧
    (∑ g, clusterCorrected g^2) = 10 ∧
    (6/5 : ℝ)*(62/25) = 372/125 ∧ (6/5 : ℝ)*10 = 12 ∧
    (∀ ω g i, nnResidual (clusterOutcome ω g) i = 0)

/-- Exported deterministic certificate for the specified witness. -/
def M1WLSCertificate : Prop :=
  (∀ p : Fin 2, (∑ q : Fin 2, ![(5/2:ℝ),-5] q*m1Gram 1 q p) =
      if p=0 then 1 else 0) ∧
    (∀ p : Fin 3, (∑ q : Fin 3, ![(125/2:ℝ),-14375/42,15625/42] q*m1Gram 2 q p) =
      if p=2 then 1 else 0) ∧
    (∀ p : Fin 3, (∑ q : Fin 3, ![(13:ℝ),-125/2,125/2] q*m1Gram 2 q p) =
      if p=0 then 1 else 0)

/-- Exported deterministic certificate for the specified witness. -/
def ClusterWLSCertificate : Prop :=
  (∀ g, clusterKernel g = ![(1/6:ℝ),1/3,1/2,2/3,5/6,5/6,2/3,1/2,1/3,1/6] g) ∧
    (∀ p : Fin 2, (∑ q : Fin 2, ![(9/25:ℝ),-3/25] q*clusterGram 1 q p) =
      if p=0 then 1 else 0) ∧
    (∀ p : Fin 3, (∑ q : Fin 3, ![(37/25:ℝ),-6/5,1/5] q*clusterGram 2 q p) =
      if p=0 then 1 else 0) ∧
    (∀ j : Fin 5, clusterLinear ⟨j.val+5,by omega⟩ =
      5*(1-((j:ℝ)+1)/6)*(9/25-(3/25)*((j:ℝ)+1))) ∧
    (∀ j : Fin 5, clusterCorrected ⟨j.val+5,by omega⟩ =
      5*(1-((j:ℝ)+1)/6)*(37/25-(6/5)*((j:ℝ)+1)+(1/5)*((j:ℝ)+1)^2))

/-- Mathematical content packaged for P033-T1. -/
def T1CoreStatement : Prop :=
  Continuous m1Control ∧ Continuous m1Treated ∧
    rdEffect m1Treated m1Control 0 = 4 ∧
    (∫ Y, rdEstimator m1Linear Y ∂rdConditionalLaw m1Treated m1Control) = 4 ∧
    (∫ Y, rdEstimator m1Corrected Y ∂rdConditionalLaw m1Treated m1Control) = 4 ∧
    variance (rdEstimator m1Linear) (rdConditionalLaw m1Treated m1Control) = 83/25 ∧
    variance (rdEstimator m1Corrected) (rdConditionalLaw m1Treated m1Control) = 82/5 ∧
    m1SELinear = Real.sqrt (variance (rdEstimator m1Linear)
      (rdConditionalLaw m1Treated m1Control)) ∧
    m1SECorrected = Real.sqrt (variance (rdEstimator m1Corrected)
      (rdConditionalLaw m1Treated m1Control)) ∧
    HasLaw (fun Y => (rdEstimator m1Linear Y-4)/m1SELinear)
      (gaussianReal 0 1) (rdConditionalLaw m1Treated m1Control) ∧
    HasLaw (fun Y => (rdEstimator m1Corrected Y-4)/m1SECorrected)
      (gaussianReal 0 1) (rdConditionalLaw m1Treated m1Control) ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
      4 (normalCritical*m1SELinear) = 19/20 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Corrected)
      4 (normalCritical*m1SECorrected) = 19/20 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
      4 ((49/25)*m1SELinear) = 2*normalCDF (49/25)-1 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Corrected)
      4 ((49/25)*m1SECorrected) = 2*normalCDF (49/25)-1 ∧
    0 < m1SELinear ∧ m1SELinear < m1SECorrected ∧
    rdEstimator m1Linear m1Observed = 4 ∧ rdEstimator m1Corrected m1Observed = 4 ∧
    absoluteT (rdEstimator m1Corrected m1Observed) m1SECorrected < 49/25 ∧
    (49/25 : ℝ) < absoluteT (rdEstimator m1Linear m1Observed) m1SELinear

/-- Mathematical content packaged for P033-T2. -/
def T2CoreStatement : Prop :=
  (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A B : Ω → ℝ) (τ σA σB c : ℝ), 0 < σA → 0 < σB → 0 < c →
      HasLaw A (gaussianReal τ ⟨σA^2, sq_nonneg σA⟩) μ →
      HasLaw B (gaussianReal τ ⟨σB^2, sq_nonneg σB⟩) μ →
      intervalCoverage μ A τ (c*σA) = 2*normalCDF c-1 ∧
      intervalCoverage μ B τ (c*σB) = 2*normalCDF c-1) ∧
    rdConditionalLaw m2Treated m1Control = rdConditionalLaw m1Treated m1Control ∧
    (∀ (E : Type*) [MeasurableSpace E] (F : ((Fin 2 × Fin 4) → ℝ) → E),
      Measurable F → (rdConditionalLaw m2Treated m1Control).map F =
        (rdConditionalLaw m1Treated m1Control).map F) ∧
    (∫ Y, rdEstimator m1Linear Y ∂rdConditionalLaw m2Treated m1Control) -
      rdEffect m2Treated m1Control 0 = -20 ∧
    (∀ κ : ℝ, 0 < κ → {Y | 24 ∈ Icc (rdEstimator m1Linear Y-κ*m1SELinear)
      (rdEstimator m1Linear Y+κ*m1SELinear)} ⊆
      {Y | 20/m1SELinear-κ ≤ (rdEstimator m1Linear Y-4)/m1SELinear}) ∧
    ((20/m1SELinear)^2 = (10000/83 : ℝ) ∧
      (5+(49/25 : ℝ))^2 = 30276/625 ∧ (30276/625 : ℝ) < 10000/83) ∧
    (0 < normalCritical ∧ normalCritical < 5 ∧ (10:ℝ) < 20/m1SELinear) ∧
    intervalCoverage (rdConditionalLaw m2Treated m1Control) (rdEstimator m1Linear)
      24 ((49/25)*m1SELinear) ≤ 1/25 ∧
    intervalCoverage (rdConditionalLaw m2Treated m1Control) (rdEstimator m1Linear)
      24 (normalCritical*m1SELinear) ≤ 1/25 ∧
    (1776/2401 : ℝ) ≤ intervalCoverage (rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) 4 ((49/25)*m1SELinear) ∧
    (1/25 : ℝ) < 1776/2401 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
      4 (normalCritical*m1SELinear) = 19/20 ∧
    (∀ N : ℕ, 1 ≤ N →
      (∀ S : Finset (Fin N), studyDataLaw N S = studyDataLaw N ∅) ∧
      (∀ S : Finset (Fin N),
        (Finset.univ.filter (fun j => intervalCoverage
          (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
          (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) ≤ 1/25)).card = S.card ∧
        (Finset.univ.filter (fun j => intervalCoverage
          (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
          (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) = 19/20)).card = N-S.card) ∧
      ¬ ∃ F : (Fin N → (Fin 2 × Fin 4) → ℝ) → ℕ, Measurable F ∧
        ∀ S : Finset (Fin N), ∀ᵐ Y ∂studyDataLaw N S, F Y = S.card) ∧
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (L βhat : Ω → ℝ), MemLp L 2 μ → MemLp βhat 2 μ →
      variance (fun ω => L ω-βhat ω) μ = variance L μ + variance βhat μ -
        2*covariance L βhat μ)

/-- Mathematical content packaged for P033-T3. -/
def T3CoreStatement : Prop :=
  Continuous (fun _ : ℝ => (0:ℝ)) ∧
    (∀ g i, finiteMean (fun ω => clusterOutcome ω g i) = 0) ∧
    rdEffect (fun _ => 0) (fun _ => 0) 0 = 0 ∧
    (∀ data g i, clusterOutcome data g i ∈ Icc (-1) 1) ∧
    finiteMean (clusterEstimator clusterLinear) = 0 ∧
    finiteMean (clusterEstimator clusterCorrected) = 0 ∧
    finiteVariance (clusterEstimator clusterLinear) = 62/25 ∧
    finiteVariance (clusterEstimator clusterCorrected) = 10 ∧
    (∀ f : ℝ, ∀ ω : Fin 10 → Bool,
      clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (clusterOutcome ω g) i) = 0 ∧
      clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (clusterOutcome ω g) i) = 0) ∧
    Fintype.card (Fin 10 → Bool) = 1024 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω ≠ 0)).card = 912 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω ≠ 0)).card = 968 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω = 0)).card = 112 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω = 0)).card = 56 ∧
    (∀ g i j, finiteCovariance (fun ω => noisyClusterOutcome ω g i)
      (fun ω => noisyClusterOutcome ω g j) = (if i=j then 1 else 0)+1) ∧
    (∀ v : Fin 5 → ℝ, v ≠ 0 → 0 < (∑ i, v i^2)+(∑ i, v i)^2) ∧
    (∀ g, finiteVariance (fun ω => noisyClusterMean ω g) = 6/5) ∧
    finiteVariance (noisyClusterEstimator clusterLinear) = 372/125 ∧
    finiteVariance (noisyClusterEstimator clusterCorrected) = 12 ∧
    (∀ f : ℝ, ∀ ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool,
      clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (noisyClusterOutcome ω g) i) = 0 ∧
      clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (noisyClusterOutcome ω g) i) = 0)

/-- Mathematical content packaged for P033-T4. -/
def T4Statement : Prop :=
  (∀ m : ℕ, 2 ≤ m → ∀ y : Fin m → ℝ,
      (∀ i, nnResidual y i = Real.sqrt ((m:ℝ)/((m:ℝ)-1)) *
        (y i-(∑ j, y j)/(m:ℝ))) ∧ (∑ i, nnResidual y i) = 0) ∧
    (∀ C G : ℕ, ∀ m : Fin C → ℕ, (∀ c, 4 ≤ m c) →
      ∀ owner : Fin C → Fin G, ∀ ell : Fin C → ℝ,
      ∀ y : (c : Fin C) → Fin (m c) → ℝ, ∀ f : ℝ,
      (∀ g, nestedClusterScore m owner ell y g = 0) ∧
      clusterScoreVariance f (nestedClusterScore m owner ell y) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      shrinkingMoment n 0 = (n:ℝ)/2 ∧
      shrinkingMoment n 1 = (n:ℝ)*((n:ℝ)+2)/(6*((n:ℝ)+1)) ∧
      shrinkingMoment n 2 = (n:ℝ)*((n:ℝ)+2)/(12*((n:ℝ)+1)) ∧
      shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 =
        (n:ℝ)^2*((n:ℝ)+2)*((n:ℝ)-1)/(72*((n:ℝ)+1)^2) ∧
      0 < shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 ∧
      (∀ j, shrinkingIntercept n j = 6*((n:ℝ)-(j:ℝ))*((n:ℝ)-1-2*(j:ℝ))/
        ((n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1))) ∧
      (∑ j : Fin n, ((n:ℝ)-(j:ℝ))^2*((n:ℝ)-1-2*(j:ℝ))^2) =
        (n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)*(4*(n:ℝ)^2+5*(n:ℝ)-1)/30 ∧
      shrinkingVariance n = 12*(4*(n:ℝ)^2+5*(n:ℝ)-1)/
        (5*(n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)) ∧
      0 < shrinkingVariance n ∧
      finiteMean (shrinkingEstimator n) = 0 ∧
      finiteVariance (shrinkingEstimator n) = shrinkingVariance n ∧
      finiteMean (shrinkingNoisyEstimator n) = 0 ∧
      finiteVariance (shrinkingNoisyEstimator n) = (6/5)*shrinkingVariance n ∧
      (∀ f : ℝ, ∀ y : (Fin 2 × Fin n) → Fin 5 → ℝ,
        f*(∑ g, ((shrinkingIntercept n g.2/5)*∑ i, nnResidual (y g) i)^2) = 0)) ∧
    Tendsto (fun n : ℕ => (n:ℝ)*shrinkingVariance n) atTop (𝓝 (48/5)) ∧
    (∀ G : ℕ, 2 ≤ G → ∀ (Ω : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Fin G → Ω → ℝ) (a : Fin G → ℝ)
      (mean varZ : ℝ), (∀ g, MemLp (Z g) 2 μ) → iIndepFun Z μ →
      (∀ g, (∫ ω, Z g ω ∂μ) = mean) → (∀ g, variance (Z g) μ = varZ) →
      (∀ g, (∫ ω, (Z g ω-sampleMean (fun j => Z j ω))^2 ∂μ) = (1-1/(G:ℝ))*varZ) ∧
      (∫ ω, clusterPlugin a (fun j => Z j ω) ∂μ) = varZ*∑ g, a g^2 ∧
      variance (fun ω => ∑ g, a g*Z g ω) μ = varZ*∑ g, a g^2) ∧
    (∀ (Ω : Type*) [Fintype Ω] (Z : Fin 10 → Ω → ℝ),
      (∀ g, finiteMean (fun ω => (Z g ω-sampleMean (fun j => Z j ω))^2) = (9/10:ℝ)) →
      finiteMean (fun ω => clusterPlugin clusterLinear (fun j => Z j ω)) = 62/25 ∧
      finiteMean (fun ω => clusterPlugin clusterCorrected (fun j => Z j ω)) = 10) ∧
    finiteMean (fun ω => clusterPlugin clusterLinear (fun g => clusterOutcome ω g 0)) = 62/25 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (fun g => clusterOutcome ω g 0)) = 10 ∧
    finiteMean (fun ω => clusterPlugin clusterLinear (noisyClusterMean ω)) = 372/125 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (noisyClusterMean ω)) = 12 ∧
    ((1/6 : ℝ)-1/36 = 5/36) ∧ ((11/72 : ℝ)-1/36 = 1/8) ∧
    ((5/48 : ℝ)-1/36 = 11/144) ∧ ((1/13 : ℝ)-1/26 = 1/26) ∧
    ((1/26 : ℝ)-1/26 = 0)

end
end SAP.P033
