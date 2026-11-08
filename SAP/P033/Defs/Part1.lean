import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

noncomputable section

def rdEffect (μ₁ μ₀ : ℝ → ℝ) (c : ℝ) : ℝ := μ₁ c - μ₀ c

def normalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)

def normalQuantile (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ normalCDF x}

def normalCritical : ℝ := normalQuantile (39/40)

def normalDensity (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

def normalPower (a : ℝ) : ℝ := normalCDF (a - normalCritical) +
  normalCDF (-a - normalCritical)

def finiteMean {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) : ℝ :=
  (∑ ω, Y ω) / (Fintype.card Ω : ℝ)

def finiteVariance {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) : ℝ :=
  finiteMean (fun ω => (Y ω - finiteMean Y)^2)

def sampleMean {n : ℕ} (Y : Fin n → ℝ) : ℝ := (∑ i, Y i) / n

def sampleVariance {n : ℕ} (Y : Fin n → ℝ) : ℝ :=
  (∑ i, (Y i - sampleMean Y)^2) / ((n : ℝ) - 1)

def sampleSD {n : ℕ} (Y : Fin n → ℝ) : ℝ := Real.sqrt (sampleVariance Y)

def funnelPoint (β se s₀ : ℝ) : ℝ × ℝ := (|β| / s₀, se / s₀)

def upperSE (β U q : ℝ) : ℝ := (U - β) / q

def widthSE (L U q : ℝ) : ℝ := (U - L) / (2 * q)

def absoluteT (β se : ℝ) : ℝ := |β| / se

def reconstructedP (β L U q : ℝ) : ℝ :=
  2 * normalCDF (-absoluteT β (widthSE L U q))

def binarySampleVariance (n k : ℝ) : ℝ :=
  (k * (1 - k/n)^2 + (n-k) * (k/n)^2) / (n-1)

def m1Control (x : ℝ) : ℝ := 2+x

def m1Treated (x : ℝ) : ℝ := 6+x

def m1Distance : Fin 4 → ℝ := ![1/5,2/5,3/5,4/5]

def m1Kernel (i : Fin 4) : ℝ := 1-m1Distance i

def m1Gram (degree : ℕ) : Matrix (Fin (degree+1)) (Fin (degree+1)) ℝ :=
  fun p q => ∑ i, m1Kernel i * m1Distance i ^ (p.val+q.val)

def m1Linear : Fin 4 → ℝ := ![6/5,3/10,-1/5,-3/10]

def m1Curvature : Fin 4 → ℝ := ![50/7,-125/14,-25/7,75/14]

def m1BiasMoment : ℝ := -21/125

def m1Bias (i : Fin 4) : ℝ := m1BiasMoment * m1Curvature i

def m1Corrected (i : Fin 4) : ℝ := m1Linear i - m1Bias i

def rdEstimator (w : Fin 4 → ℝ) (Y : (Fin 2 × Fin 4) → ℝ) : ℝ :=
  ∑ i, w i * (Y (1,i) - Y (0,i))

def rdConditionalLaw (μ₁ μ₀ : ℝ → ℝ) : Measure ((Fin 2 × Fin 4) → ℝ) :=
  Measure.pi (fun si => gaussianReal
    (if si.1 = 0 then μ₀ (-m1Distance si.2) else μ₁ (m1Distance si.2)) 1)

def m1SELinear : ℝ := Real.sqrt 83 / 5

def m1SECorrected : ℝ := Real.sqrt 410 / 5

def intervalCoverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (θ halfLength : ℝ) : ℝ :=
  μ.real {ω | θ ∈ Icc (T ω-halfLength) (T ω+halfLength)}

def m1Observed (si : Fin 2 × Fin 4) : ℝ :=
  if si.1 = 0 then ![19/10,3/2,8/5,1] si.2 else ![63/10,63/10,34/5,33/5] si.2

def m2Perturbation (x : ℝ) : ℝ :=
  20*(1-5*x)*(1-(5/2)*x)*(1-(5/3)*x)*(1-(5/4)*x)

def m2Treated (x : ℝ) : ℝ := m1Treated x + m2Perturbation x

def studyDataLaw (N : ℕ) (S : Finset (Fin N)) :
    Measure (Fin N → (Fin 2 × Fin 4) → ℝ) :=
  Measure.pi (fun j => if j ∈ S then rdConditionalLaw m2Treated m1Control
    else rdConditionalLaw m1Treated m1Control)

def studyEffect {N : ℕ} (S : Finset (Fin N)) (j : Fin N) : ℝ := if j ∈ S then 24 else 4

def nnResidual {m : ℕ} (y : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (((m:ℝ)-1)/m) * (y i - ((∑ j, y j)-y i)/((m:ℝ)-1))

def clusterScoreVariance {G : ℕ} (f : ℝ) (score : Fin G → ℝ) : ℝ :=
  f * ∑ g, score g ^ 2

def nestedClusterScore {C G : ℕ} (m : Fin C → ℕ) (owner : Fin C → Fin G)
    (ell : Fin C → ℝ) (y : (c : Fin C) → Fin (m c) → ℝ) (g : Fin G) : ℝ :=
  ∑ c, if owner c = g then ell c * ∑ i, nnResidual (y c) i else 0

def signShock (u : Bool) : ℝ := if u then 1 else -1

def clusterRunning : Fin 10 → ℝ := ![-5,-4,-3,-2,-1,1,2,3,4,5]

def clusterKernel (g : Fin 10) : ℝ := 1-|clusterRunning g|/6

def clusterGram (degree : ℕ) : Matrix (Fin (degree+1)) (Fin (degree+1)) ℝ :=
  fun p q => ∑ j : Fin 5, 5*(1-((j:ℝ)+1)/6)*((j:ℝ)+1)^(p.val+q.val)

def clusterLinear : Fin 10 → ℝ := ![1/5,1/5,0,-2/5,-1,1,2/5,0,-1/5,-1/5]

def clusterCorrected : Fin 10 → ℝ := ![-2/5,1/5,4/5,2/5,-2,2,-2/5,-4/5,-1/5,2/5]

def clusterEstimator (a : Fin 10 → ℝ) (ω : Fin 10 → Bool) : ℝ :=
  ∑ g, a g * signShock (ω g)

def clusterOutcome (ω : Fin 10 → Bool) (g : Fin 10) (_i : Fin 5) : ℝ := signShock (ω g)

def noisyClusterOutcome (ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool)
    (g : Fin 10) (i : Fin 5) : ℝ := signShock (ω (.inl g)) + signShock (ω (.inr (g,i)))

def noisyClusterMean (ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool) (g : Fin 10) : ℝ :=
  (∑ i, noisyClusterOutcome ω g i)/5

def noisyClusterEstimator (a : Fin 10 → ℝ)
    (ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool) : ℝ := ∑ g, a g * noisyClusterMean ω g

def finiteCovariance {Ω : Type*} [Fintype Ω] (X Y : Ω → ℝ) : ℝ :=
  finiteMean (fun ω => (X ω-finiteMean X)*(Y ω-finiteMean Y))

def shrinkingDistance (n : ℕ) (j : Fin n) : ℝ := ((j:ℝ)+1)/((n:ℝ)+1)

def shrinkingKernel (n : ℕ) (j : Fin n) : ℝ := 1-shrinkingDistance n j

def shrinkingMoment (n power : ℕ) : ℝ :=
  ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ power

def shrinkingIntercept (n : ℕ) (j : Fin n) : ℝ :=
  shrinkingKernel n j * (shrinkingMoment n 2-shrinkingMoment n 1*shrinkingDistance n j) /
    (shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2)

def shrinkingVariance (n : ℕ) : ℝ := 2 * ∑ j : Fin n, shrinkingIntercept n j ^ 2

def shrinkingEstimator (n : ℕ) (ω : (Fin 2 × Fin n) → Bool) : ℝ :=
  ∑ j, shrinkingIntercept n j*(signShock (ω (1,j))-signShock (ω (0,j)))

def shrinkingNoisyEstimator (n : ℕ)
    (ω : ((Fin 2 × Fin n) ⊕ ((Fin 2 × Fin n) × Fin 5)) → Bool) : ℝ :=
  ∑ j, shrinkingIntercept n j *
    ((∑ i : Fin 5, (signShock (ω (.inl (1,j)))+signShock (ω (.inr ((1,j),i)))))/5 -
     (∑ i : Fin 5, (signShock (ω (.inl (0,j)))+signShock (ω (.inr ((0,j),i)))))/5)

def clusterPlugin {G : ℕ} (a Z : Fin G → ℝ) : ℝ :=
  (G:ℝ)/((G:ℝ)-1) * ∑ g, a g^2 * (Z g-sampleMean Z)^2

def waldRatio (yE yI dE dI : ℝ) : ℝ := (yE-yI)/(dE-dI)

def binaryIndicator {n : ℕ} (k : ℕ) (i : Fin n) : ℝ := if i.val < k then 1 else 0

def eligibleBaseline : Fin 2 → ℕ := ![5,45]

def ineligibleBaseline : Fin 2 → ℕ := ![10,40]

def countToyPotential (eligible treated : Bool) (cell : Fin 2) (i : Fin 100) : ℝ :=
  binaryIndicator ((if eligible then eligibleBaseline cell else ineligibleBaseline cell) +
    (if treated then 5 else 0)) i

def countToyTreatment (eligible : Bool) (i : Fin 100) : ℝ :=
  if eligible then binaryIndicator 50 i else 0

def countToyObserved (eligible : Bool) (cell : Fin 2) (i : Fin 100) : ℝ :=
  if countToyTreatment eligible i = 1 then countToyPotential eligible true cell i
  else countToyPotential eligible false cell i

def binaryPopulationVariance (p : ℝ) : ℝ := p*(1-p)

def binaryStudySE : ℝ := 154987506828555/10^16

def caliperCutoff : ℝ := 49/25

def caliperAbove (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ x in caliperCutoff..caliperCutoff+h, f x

def caliperBelow (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ x in caliperCutoff-h..caliperCutoff, f x

def caliperProbability (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  caliperAbove f h/(caliperAbove f h+caliperBelow f h)

def binomialTail (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k n, (n.choose j:ℝ)*p^j*(1-p)^(n-j)

def caliperDataLaw (M : ℕ) (f : ℝ → ℝ) : Measure (Fin M → ℝ) :=
  Measure.pi (fun _ => volume.withDensity (fun x => ENNReal.ofReal (f x)))

def caliperCount {M : ℕ} (h : ℝ) (X : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => X i ∈ Icc (caliperCutoff-h) (caliperCutoff+h))).card

def caliperSuccesses {M : ℕ} (h : ℝ) (X : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => X i ∈ Icc caliperCutoff (caliperCutoff+h))).card

def linearCaliperDensity (x : ℝ) : ℝ := if x ∈ Icc 0 4 then x/8 else 0

def powerCaliperDensity (m : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Icc 0 4 then ((m:ℝ)+1)*x^m/4^(m+1) else 0

def foldedNormalCDF (θ x : ℝ) : ℝ := normalCDF (x-θ)-normalCDF (-x-θ)

def foldedCaliperProbability (θ h : ℝ) : ℝ :=
  (foldedNormalCDF θ (caliperCutoff+h)-foldedNormalCDF θ caliperCutoff) /
  (foldedNormalCDF θ (caliperCutoff+h)-foldedNormalCDF θ (caliperCutoff-h))

def clusterCountRatio {α : Type*} [DecidableEq α] (L R : Finset α) : ℝ :=
  ((L ∪ R).card:ℝ)/((L.card:ℝ)+(R.card:ℝ))

def pseudoP (estimate halfLength : ℝ) : ℝ :=
  2*normalCDF (-normalCritical*|estimate|/halfLength)

def biasModelLaw (θ b : ℝ) : Measure ℝ := gaussianReal (θ+b) 1

def biasCoverage (b H : ℝ) : ℝ := normalCDF (H-b)-normalCDF (-H-b)

def honestHalfLength (B : ℝ) : ℝ := sInf {H : ℝ | 0 ≤ H ∧ 19/20 ≤ biasCoverage B H}

def ValidBiasP (B : ℝ) (P : ℝ → ℝ) : Prop :=
  ∀ b : ℝ, |b| ≤ B → ∀ α : ℝ, 0 < α → α < 1 →
    (biasModelLaw 0 b).real {t | P t ≤ α} ≤ α

def biasAwareP (B t : ℝ) : ℝ := normalCDF (B-|t|)+normalCDF (-B-|t|)

end
end SAP.P033
