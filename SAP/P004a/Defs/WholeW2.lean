import Mathlib
import SAP.P004a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section

/-- The spectral positive part of a real symmetric matrix. The other branch is
irrelevant to every assertion below. No spectral data are additional inputs. -/
def positiveKernel {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  if hK : K.IsHermitian then
    spectralKernel hK.eigenvalues (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) true
  else 0

/-- The sandwich in (19)/(22), with the residual vector supplied explicitly. -/
def wholeSandwich {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (K : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((designMatrix z).transpose * designMatrix z)⁻¹ *
    ((designMatrix z).transpose * Matrix.of (fun i j => e i * e j * K i j) * designMatrix z) *
    ((designMatrix z).transpose * designMatrix z)⁻¹

def ValidArms {N : ℕ} (z : Assignment N) : Prop :=
  0 < armCount z true ∧ 0 < armCount z false

def T8StudentComparison : Prop :=
  ∀ ν a : ℝ, 0 < ν → 1/2 < a → a < 1 →
    {x : ℝ | a ≤ studentCDF ν x}.Nonempty ∧
    BddBelow {x : ℝ | a ≤ studentCDF ν x} ∧
    normalQuantile a ≤ studentQuantile ν a

def T8FiniteWhole : Prop :=
  ∀ {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ), K.IsSymm →
    ∀ (z : Assignment N) (e : Fin N → ℝ), ValidArms z →
    let Q := positiveKernel K
    let V := cappedVariance (kernelVariance z e Q) (adjustmentMu z Q)
    wholeSandwich z e K 1 1 = kernelVariance z e K ∧
    wholeSandwich z e Q 1 1 = kernelVariance z e Q ∧
    kernelVariance z e Q ≤ V ∧
    max (kernelVariance z e K) 0 ≤ kernelVariance z e Q ∧
    (∀ α c err : ℝ, 0 < α ∧ α < 1 → normalQuantile (1-α/2) ≤ c →
      0 ≤ kernelVariance z e K →
      |err| ≤ normalQuantile (1-α/2) * Real.sqrt (kernelVariance z e K) →
      |err| ≤ c * Real.sqrt V) ∧
    (∀ α ν err : ℝ, 0 < α ∧ α < 1 → 0 < ν →
      0 ≤ kernelVariance z e K →
      |err| ≤ normalQuantile (1-α/2) * Real.sqrt (kernelVariance z e K) →
      |err| ≤ studentQuantile ν (1-α/2) * Real.sqrt V)

def T8Coverage {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space)
    (p d h : ℝ) (c : ∀ N, Assignment N → ℝ) (N : ℕ) : ℝ :=
  prob (fun _ => p) (fun z : Assignment N =>
    let R := circleAverage (P N) d
    let Q := positiveKernel (uniformDistanceKernel (nodeSeparation (P N)) h)
    ValidArms z ∧ |hajek R z - ame (fun _ => p) R| ≤ c N z *
      Real.sqrt (cappedVariance (kernelVariance z (residual R z) Q) (adjustmentMu z Q)))

def T8AsymptoticWhole {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] : Prop :=
  ∀ (P : PopulationSequence Space) (p d h α : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hh : 0 ≤ h) (hα : 0 < α ∧ α < 1)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hv : Nondegenerate (fun N => variance (fun _ => p)
      (linearHajek (fun _ => p) (circleAverage (P N) d))))
    (hhom : ∀ᶠ N in atTop, 0 ≤ homophilyQ (fun _ => p) (circleAverage (P N) d)
      (spatialNeighborhoods P h N) (fun _ a => barMu (fun _ => p) (circleAverage (P N) d) a)),
    (∀ c : ∀ N, Assignment N → ℝ,
      (∀ N z, ValidArms z → normalQuantile (1-α/2) ≤ c N z) →
      Conservative (T8Coverage P p d h c) α) ∧
    (∀ ν : ∀ N, Assignment N → ℝ, (∀ N z, ValidArms z → 0 < ν N z) →
      Conservative (T8Coverage P p d h (fun N z => studentQuantile (ν N z) (1-α/2))) α)

def T8UncappedWhole : Prop :=
  SpatialLocalConditions starPopulation ∧
  (∀ N, WellDefined (starPopulation N) 0) ∧
  (∀ N, LocalAt (circleAverage (starPopulation N) 0) (nodeSeparation (starPopulation N)) (6/5)) ∧
  (∀ N, homophilyQ (fun _ => 1/2) (circleAverage (starPopulation N) 0)
    (spatialNeighborhoods starPopulation (6/5) N)
    (fun _ a => barMu (fun _ => 1/2) (circleAverage (starPopulation N) 0) a) = 0) ∧
  Nondegenerate (fun N => variance (fun _ => 1/2)
    (linearHajek (fun _ => 1/2) (circleAverage (starPopulation N) 0))) ∧
  (∀ m, circleAverage (starPopulation (5*m)) 0 = starBlockTable m) ∧
  (∀ m, ame (fun _ => 1/2) (starBlockTable m) = 0) ∧
  (∀ m, positiveKernel (uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5)) =
    starBlockKernel m true) ∧
  Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
    let Q := positiveKernel (uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5))
    ¬ (ValidArms z ∧ 0 < adjustmentMu z Q ∧ 0 < adjustmentNu z Q))) atTop (nhds 0) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
    prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      let Q := positiveKernel (uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5))
      let μ := adjustmentMu z Q
      let ν := adjustmentNu z Q
      ValidArms z ∧ 0 < μ ∧ 0 < ν ∧
      |hajek (starBlockTable m) z| ≤ studentQuantile (2*μ^2/ν) (39/40) *
        Real.sqrt (kernelVariance z (residual (starBlockTable m) z) Q / μ)) <
      2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1+ε) ∧
  2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1 < 19/20

/-- P004-T8; p. 761 (PDF p. 18), Section 7; p. 756 (PDF p. 13),
eqs. (21)-(22), footnote 15; Supplement A p. 17 (A.7).
Capping the positive-semidefinite HAC adjustment preserves variance ordering and
interval inclusion for every symmetric kernel. Every positive-degree Student
upper quantile dominates the normal quantile. Under C1-C5 and the variance floor,
the capped intervals have asymptotic coverage at least one minus alpha, including
arbitrary assignment-dependent positive Student degrees of freedom. Coverage
counts only draws with both arms nonempty. The repeated-star design has
well-defined uncapped intervals with probability tending to one and shows
that the uncapped rule has no such universal guarantee. -/
def T8WholeStatement : Prop :=
  T8StudentComparison ∧ T8FiniteWhole ∧
    (∀ (Space : ℕ → Type*) [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
      T8AsymptoticWhole (Space := Space)) ∧
    T8UncappedWhole

def boundaryO (N : ℕ) (_ : Fin N) (_ : Fin 1) : ℝ := 1
def boundaryTheta : Fin 1 → ℝ := fun _ => 0
def boundaryParameterSet : Set (Fin 1 → ℝ) := {θ | 0 ≤ θ 0 ∧ θ 0 ≤ 1}
def boundarySignSum {N : ℕ} (z : Assignment N) : ℝ := ∑ i, (2*bit (z i)-1)
def boundaryLikelihood {N : ℕ} (z : Assignment N) (t : ℝ) : ℝ :=
  armCount z true * t - N * Real.log (1 + Real.exp t)
def boundaryLeading {N : ℕ} (z : Assignment N) : ℝ := 4*(armCount z true / N - 1/2)
def boundaryRemainder {N : ℕ} (z : Assignment N) : ℝ := boundaryMLE z - boundaryLeading z

def T9ModelWhole : Prop :=
  LogisticConditions boundaryO boundaryTheta boundaryParameterSet (fun _ z _ => boundaryMLE z) ∧
  Overlap (fun N => propensities (boundaryO N) boundaryTheta) ∧
  IsCompact boundaryParameterSet ∧ boundaryTheta ∈ boundaryParameterSet ∧
  (∀ N i j, |boundaryO N i j| ≤ 1) ∧
  (∀ N i, propensities (boundaryO N) boundaryTheta i = 1/2 ∧
    1/4 < propensities (boundaryO N) boundaryTheta i ∧
    propensities (boundaryO N) boundaryTheta i < 1-1/4) ∧
  (∀ N : ℕ, 0 < N →
    (∑ i : Fin N, boundaryO N i 0 * boundaryO N i 0) / N = 1 ∧
    information (fun _ => 1/2) (boundaryO N) = (1/4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))

def T9LikelihoodWhole : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ z : Assignment N,
    (∀ t : ℝ, boundaryLikelihood z t =
      ∑ i, (bit (z i)*t - Real.log (1 + Real.exp t))) ∧
    (∀ t : ℝ,
      HasDerivAt (boundaryLikelihood z) (armCount z true - N*logistic t) t ∧
      HasDerivAt (fun s => armCount z true - N*logistic s)
        (-(N : ℝ)*Real.exp t/(1+Real.exp t)^2) t ∧
      -(N : ℝ)*Real.exp t/(1+Real.exp t)^2 < 0) ∧
    (boundaryMLE z ∈ Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, boundaryLikelihood z t ≤ boundaryLikelihood z (boundaryMLE z) ∧
      (boundaryLikelihood z t = boundaryLikelihood z (boundaryMLE z) → t = boundaryMLE z)) ∧
    (armCount z true ≤ (N : ℝ)/2 → boundaryMLE z = 0) ∧
    (armCount z true = 0 → boundaryMLE z = 0) ∧
    (armCount z true = N → boundaryMLE z = 1) ∧
    (0 < armCount z true → armCount z true < N → boundaryMLE z =
      min 1 (max 0 (Real.log ((armCount z true / N) / (1-armCount z true / N)))))

def T9AlgebraWhole : Prop :=
  ∀ N : ℕ, 0 < N → ∀ z : Assignment N,
    boundarySignSum z = 2*armCount z true - N ∧
    ((information (fun _ => 1/2) (boundaryO N))⁻¹ *ᵥ
      logisticScore (fun _ => 1/2) (boundaryO N) z) 0 = boundaryLeading z ∧
    boundaryLeading z = 2*boundarySignSum z/N ∧
    (boundarySignSum z < 0 → boundaryRemainder z = -2*boundarySignSum z/N) ∧
    (boundarySignSum z < 0 ∧ (N : ℝ)/4 < (boundarySignSum z)^2 →
      1 < Real.sqrt N * |boundaryRemainder z|)

def T9TailsWhole : Prop :=
  ∀ N : ℕ, 0 < N →
    expect (fun _ : Fin N => 1/2) (fun z => (boundarySignSum z)^2) = N ∧
    expect (fun _ : Fin N => 1/2) (fun z => (boundarySignSum z)^4) = 3*(N : ℝ)^2-2*N ∧
    0 < 3*(N : ℝ)^2-2*N ∧
    9*(N : ℝ)^2/(16*(3*(N : ℝ)^2-2*N)) ≤
      prob (fun _ => 1/2) (fun z : Assignment N => (N : ℝ)/4 < (boundarySignSum z)^2) ∧
    prob (fun _ => 1/2) (fun z : Assignment N =>
      boundarySignSum z < 0 ∧ (N : ℝ)/4 < (boundarySignSum z)^2) =
      prob (fun _ => 1/2) (fun z : Assignment N => (N : ℝ)/4 < (boundarySignSum z)^2) / 2 ∧
    9*(N : ℝ)^2/(32*(3*(N : ℝ)^2-2*N)) ≤
      prob (fun _ => 1/2) (fun z : Assignment N => 1 < Real.sqrt N * |boundaryRemainder z|) ∧
    (3/32 : ℝ) ≤ 9*(N : ℝ)^2/(32*(3*(N : ℝ)^2-2*N))

/-- CDF formulation of the two weak limits. The positive-part normal has a
jump at zero; the CDF convergence assertion therefore excludes zero. The last
clause separately records its limiting atom, rather than calling it folded normal. -/
def T9LimitLaws : Prop :=
  (∀ x : ℝ, Tendsto (fun N => prob (fun _ => 1/2) (fun z : Assignment N =>
    Real.sqrt N * boundaryLeading z ≤ x)) atTop (nhds (normalCDF (x/2)))) ∧
  (∀ x : ℝ, x ≠ 0 → Tendsto (fun N => prob (fun _ => 1/2) (fun z : Assignment N =>
    Real.sqrt N * boundaryMLE z ≤ x)) atTop
      (nhds (if x < 0 then 0 else normalCDF (x/2)))) ∧
  Tendsto (fun N => prob (fun _ => 1/2) (fun z : Assignment N => boundaryMLE z = 0))
    atTop (nhds (1/2 : ℝ))

/-- P004-T9; Supplement A pp. 13-14, C 1(iv),(vi) and Lemma A.6.
The boundary-constrained one-dimensional logistic MLE over [0,1], with constant
confounder one and true coefficient zero, satisfies all stated premises. Its
likelihood has the stated derivatives and unique clipped-logit maximizer; its
information, score remainder, exact moments and explicit finite tail lower bounds have
the displayed values. The score remainder fails to be smaller than root-N.
The scaled MLE converges to twice the positive part of a standard normal, while
the leading score term converges to twice a standard normal. Consistency and
the root-N rate hold. Thus the printed universal score expansion is false. -/
def T9WholeStatement : Prop :=
  T9ModelWhole ∧ T9LikelihoodWhole ∧ T9AlgebraWhole ∧ T9TailsWhole ∧
  (¬ LittleOp (fun _ _ => 1/2) (fun _ z => boundaryRemainder z)
    (fun N => (Real.sqrt N)⁻¹)) ∧ T9LimitLaws ∧
  InProb (fun _ _ => 1/2) (fun _ z => |boundaryMLE z|) ∧
  BigOp (fun _ _ => 1/2) (fun _ z => |boundaryMLE z|) (fun N => (Real.sqrt N)⁻¹)

def oneShellAtom (x : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  if x = 0 then planePoint 1 0 else if x = 1 then planePoint 0 2 else planePoint (-2) 0

def oneShellPopulation (D : Set ℝ) : SpatialPopulation 1 (EuclideanSpace ℝ (Fin 2)) where
  node := fun _ => {0}
  node_nonempty := fun _ => singleton_nonempty _
  zeta := ∑ x : Fin 3, Measure.dirac (oneShellAtom x)
  outcome := fun y z => if y = oneShellAtom 1 ∨ y = oneShellAtom 2 then bit (z 0) else 0
  bands := fun _ => D

def shellMass {N : ℕ} (P : SpatialPopulation N (EuclideanSpace ℝ (Fin 2))) (i : Fin N) : ℝ :=
  (P.zeta (region P i 0)).toReal

def T14OneNodeWhole : Prop :=
  (∀ D ∈ ({({1} : Set ℝ), {2}, Icc 0 2, Icc 1 2} : Set (Set ℝ)),
    WellDefined (oneShellPopulation D) 0) ∧
  (∀ x z, |(oneShellPopulation {1}).outcome x z| < 2) ∧
  (∀ x : Fin 3, nodeDistance (oneShellPopulation {1}) 0 (oneShellAtom x) =
    if x = 0 then 1 else 2) ∧
  ame (fun _ => 1/2) (circleAverage (oneShellPopulation {1}) 0) = 0 ∧
  ame (fun _ => 1/2) (circleAverage (oneShellPopulation {2}) 0) = 1 ∧
  (ame (fun _ => 1/2) (circleAverage (oneShellPopulation {1}) 0) +
    ame (fun _ => 1/2) (circleAverage (oneShellPopulation {2}) 0))/2 = 1/2 ∧
  ame (fun _ => 1/2) (circleAverage (oneShellPopulation (Icc 0 2)) 0) = 2/3 ∧
  ame (fun _ => 1/2) (circleAverage (oneShellPopulation (Icc 1 2)) 0) = 2/3 ∧
  shellMass (oneShellPopulation {1}) 0 / shellMass (oneShellPopulation (Icc 1 2)) 0 = 1/3 ∧
  shellMass (oneShellPopulation {2}) 0 / shellMass (oneShellPopulation (Icc 1 2)) 0 = 2/3 ∧
  (1/3 : ℝ)*ame (fun _ => 1/2) (circleAverage (oneShellPopulation {1}) 0) +
    (2/3 : ℝ)*ame (fun _ => 1/2) (circleAverage (oneShellPopulation {2}) 0) =
      ame (fun _ => 1/2) (circleAverage (oneShellPopulation (Icc 1 2)) 0)

def T14TwoNodeWhole : Prop :=
  T14Statement ∧
  (∀ i : Fin 2, ∀ x : Fin 3, nodeDistance (shellSpatialPopulation {4}) i (shellAtomPoint x) =
    if i = 0 then (if x = 0 then 4 else 5) else (if x = 0 then 5 else 4)) ∧
  (∀ i : Fin 2,
    nodeEffect (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) i = 0 ∧
    nodeEffect (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) i =
      (if i = 0 then 1 else -1) ∧
    nodeEffect (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Icc 4 5)) 0) i =
      (if i = 0 then 2/3 else -1/3) ∧
    nodeEffect (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Icc 0 5)) 0) i =
      (if i = 0 then 2/3 else -1/3) ∧
    shellMass (shellSpatialPopulation {4}) i / shellMass (shellSpatialPopulation (Icc 4 5)) i =
      (if i = 0 then 1/3 else 2/3) ∧
    shellMass (shellSpatialPopulation {5}) i / shellMass (shellSpatialPopulation (Icc 4 5)) i =
      (if i = 0 then 2/3 else 1/3)) ∧
  (∀ w4 w5 : ℝ,
    w4*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) +
    w5*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) ≠
      ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Icc 0 5)) 0))

/-- Area on the closed disk. The zero extension of the outcome outside the
disk is immaterial to this measure, and makes boundedness global. -/
def radialAreaPopulation (D : Set ℝ) : SpatialPopulation 1 (EuclideanSpace ℝ (Fin 2)) where
  node := fun _ => {0}
  node_nonempty := fun _ => singleton_nonempty _
  zeta := volume.restrict (Metric.closedBall 0 1)
  outcome := fun x z => if ‖x‖ ≤ 1 then bit (z 0)*‖x‖ else 0
  bands := fun _ => D

/-- The defining moment property for a version of the conditional mean given
radius. Integrability and measurability are part of the certificate. -/
def IsRadiusConditionalMean (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ Integrable f μ ∧ Integrable (fun x => g ‖x‖) μ ∧
  ∀ B : Set ℝ, MeasurableSet B →
    (∫ x in {x | ‖x‖ ∈ B}, f x ∂μ) = (∫ x in {x | ‖x‖ ∈ B}, g ‖x‖ ∂μ)

def radialUniform (a b : ℝ) : ℝ := (∫ r in Icc a b, r) / (b-a)
def radialAreaIntegral (a b : ℝ) : ℝ := ∫ r in Icc a b, r*(2*r/(b^2-a^2))

def T14AreaExistence : Prop :=
  (∀ x z, |(radialAreaPopulation (Icc 0 1)).outcome x z| < 2) ∧
  (∀ x z, ‖x‖ ≤ 1 → (radialAreaPopulation (Icc 0 1)).outcome x z = bit (z 0)*‖x‖) ∧
  (∀ x, ‖x‖ ≤ 1 → pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => 1/2) 0 x = ‖x‖) ∧
  Continuous (fun r : ℝ => r) ∧
  IsRadiusConditionalMean (radialAreaPopulation (Icc 0 1)).zeta
    (pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => 1/2) 0) (fun r => r) ∧
  (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    WellDefined (radialAreaPopulation (Icc a b)) 0 ∧
    (radialAreaPopulation (Icc a b)).zeta (region (radialAreaPopulation (Icc a b)) 0 0) =
      ENNReal.ofReal (Real.pi*(b^2-a^2)))

def T14AreaTransport : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    (ENNReal.ofReal (1/(Real.pi*(b^2-a^2)))) •
      Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖)
        ((radialAreaPopulation (Icc a b)).zeta.restrict
          (region (radialAreaPopulation (Icc a b)) 0 0)) =
      volume.withDensity (fun r : ℝ => ENNReal.ofReal
        (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)) ∧
    IntegrableOn (fun r : ℝ => r*(2*r/(b^2-a^2))) (Icc a b) ∧
    ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc a b)) 0) = radialAreaIntegral a b

def T14AreaWhole : Prop :=
  T14AreaExistence ∧ T14AreaTransport ∧
  (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    IntegrableOn (fun r : ℝ => r) (Icc a b) ∧
    radialUniform a b = (a+b)/2 ∧
    radialAreaIntegral a b = 2*(b^3-a^3)/(3*(b^2-a^2))) ∧
  radialUniform 0 1 = 1/2 ∧
  ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc 0 1)) 0) = 2/3 ∧
  radialUniform (1/2) 1 = 3/4 ∧
  ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc (1/2) 1)) 0) = 7/9 ∧
  radialUniform 0 1 ≠ ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc 0 1)) 0) ∧
  radialUniform (1/2) 1 ≠
    ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc (1/2) 1)) 0)

/-- P004-T14; p. 757 (PDF p. 14), sentence after eq. (26); eq. (2),
p. 747 (PDF p. 4), and eqs. (4)-(9), pp. 749-750.
All three explicit Euclidean witnesses refute the printed uniform-radius
disk/donut identity. The one-node atomic witness has radius effects zero and
one, uniform-radius mean one half, and band effects two thirds, with shell
weights one third and two thirds. The two-node witness has zero circle AMEs,
band AMEs one sixth, the stated individual effects and unequal shell weights,
and defeats every common pair of weights. For area on the unit disk the
continuous conditional circle-effect version is radius itself; radial area
has density 2r/(b squared minus a squared). Disk averages are two thirds versus
one half, and annulus averages seven ninths versus three quarters. Every atomic
and positive-area band average exists; singleton area circles are conditional
means. -/
def T14WholeStatement : Prop := T14OneNodeWhole ∧ T14TwoNodeWhole ∧ T14AreaWhole

end
end SAP.P004a
