import Mathlib
import SAP.P004b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

/-- The fixed population information matrix in Supplement A.6. -/
def projectionInformation {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => (∑ i, p i * (1-p i) * O i a * O i b) / N

/-- Population projection coefficients, used only with an invertible information matrix. -/
def projectionBeta {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) : Fin k → ℝ :=
  (projectionInformation p O)⁻¹ *ᵥ
    (fun j => (∑ i, marginal p R i a * p i * (1-p i) * O i j) / N)

def covariateFits {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (β : Bool → Fin k → ℝ) (i : Fin N) (a : Bool) : ℝ := ∑ j, O i j * β a j

def projectionFits {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) : Fin N → Bool → ℝ :=
  covariateFits O (projectionBeta p R O)

/-- The paper's deterministic projection-fit linear form, before any asymptotic assertion. -/
def projectionLinearIPW {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) : ℝ :=
  ((∑ i, (projectionFits p R O i true - projectionFits p R O i false)) +
    ∑ i, residualContrast p R (projectionFits p R O) i z) / N

def armSecondMoment {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (a : Bool) : ℝ :=
  (∑ i, marginal p (fun j z => (R j z-g j a)^2) i a / coin (p i) a) / (N : ℝ)^2

def diagonalEffectSquare {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) : ℝ := (∑ i, (residualEffect p R g i)^2) / (N : ℝ)^2

def signedPairSecondMoment {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
    armSign a * armSign b * pairMarginal p
      (fun z => (R i z-g i a)*(R j z-g j b)) i j a b) / (N : ℝ)^2

def signedPairMeanProduct {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
    armSign a * armSign b * (marginal p R i a-g i a) *
      (marginal p R j b-g j b)) / (N : ℝ)^2

def fiveTermVariance {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  armSecondMoment p R g true + armSecondMoment p R g false -
    diagonalEffectSquare p R g + signedPairSecondMoment p R B g - signedPairMeanProduct p R B g

def literalPairSecondMoment {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
    pairMarginal p (fun z => (R i z-g i a)*(R j z-g i b)) i j a b) / (N : ℝ)^2

def literalPairMeanProduct {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool, armSign a*armSign b *
    (marginal p R i a-g i a)*(marginal p R j b-g i b)) / (N : ℝ)^2

/-- The literal unsigned pair term and repeated i-index of the contextual printed formula. -/
def literalVariance {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z-g i true)^2) i true/p i +
      marginal p (fun i z => (R i z-g i false)^2) i false/(1-p i) - (residualEffect p R g i)^2)) +
    (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      pairMarginal p (fun z => (R i z-g i a)*(R j z-g i b)) i j a b) -
    (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool, armSign a*armSign b *
      (marginal p R i a-g i a)*(marginal p R j b-g i b))) / (N : ℝ)^2

def varianceExpansion {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : Prop :=
  variance p (augmented p R g) = fiveTermVariance p R B g ∧
  -diagonalEffectSquare p R g - signedPairMeanProduct p R B g =
    -(∑ i, ∑ j ∈ B i, residualEffect p R g i * residualEffect p R g j) / (N : ℝ)^2 ∧
  (0 ≤ homophilyQ p R B g → variance p (augmented p R g) ≤
    armSecondMoment p R g true + armSecondMoment p R g false + signedPairSecondMoment p R B g)

def threeNodeVarianceTable : CircleTable 3 :=
  fun i z => if i = 2 then 0 else bit (z 2)-1/2

def threeNodeVarianceWitness : Prop :=
  let p := fun _ : Fin 3 => (1/2 : ℝ)
  let R := threeNodeVarianceTable
  let O := fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)
  let B := fun _ : Fin 3 => (Finset.univ : Finset (Fin 3))
  let g := projectionFits p R O
  IsUnit (projectionInformation p O).det ∧
  (∀ a, projectionBeta p R O a = 0) ∧
  (∀ i a, g i a = 0) ∧
  (∀ z, projectionLinearIPW p R O z =
    (2/3 : ℝ)*((2*bit (z 0)-1)+(2*bit (z 1)-1))*(bit (z 2)-1/2)) ∧
  variance p (projectionLinearIPW p R O) = 2/9 ∧
  armSecondMoment p R g true + armSecondMoment p R g false = 2/9 ∧
  diagonalEffectSquare p R g = 0 ∧ signedPairSecondMoment p R B g = 0 ∧
  signedPairMeanProduct p R B g = 0 ∧
  literalPairSecondMoment p R B g = 2/9 ∧ literalPairMeanProduct p R B g = 0 ∧
  literalVariance p R B g = 4/9 ∧ fiveTermVariance p R B g = 2/9

/-- P004-T22; Supplement A pp. 15–16, equations (37)–(40) and the bound under C 2.
The corrected five-term variance formula has both pair signs and the neighbour's own fit.
Its third and fifth terms form the full negative residual-effect quadratic, yielding the
corrected homophily bound. This includes the population projection-fit linear estimator
and the three-node witness: true and corrected variance 2/9, printed sum 4/9. -/
def T22WholeStatement : Prop :=
  (∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ),
    0 < N → (∀ i, 0 < p i ∧ p i < 1) → (∀ i, i ∈ B i) →
    (∀ i j, j ∉ B i → ¬ sharesSource R i j) → varianceExpansion p R B g) ∧
  (∀ {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (O : Fin N → Fin k → ℝ),
    0 < N → (∀ i, 0 < p i ∧ p i < 1) → IsUnit (projectionInformation p O).det →
    (∀ i, i ∈ B i) → (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
    projectionLinearIPW p R O = augmented p R (projectionFits p R O) ∧
    varianceExpansion p R B (projectionFits p R O)) ∧ threeNodeVarianceWitness

def treatmentSelector : Fin 2 → ℝ := ![0,1]

def treatmentQuadratic (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  dotProduct treatmentSelector (A *ᵥ treatmentSelector)

def neighborhoodMatrix {N : ℕ} (B : Fin N → Finset (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j ∈ B i then 1 else 0

def logisticPropensity {N k : ℕ} (O : Fin N → Fin k → ℝ) (θ : Fin k → ℝ) (i : Fin N) : ℝ :=
  Real.exp (∑ j, O i j * θ j) / (1 + Real.exp (∑ j, O i j * θ j))

/-- All three presentations of the corrected, IPW-labelled event at variance V. -/
def correctedIPWEvents {N : ℕ} (p phat : Fin N → ℝ) (R : CircleTable N)
    (z : Assignment N) (α V : ℝ) : Prop :=
  let t := (ht phat R z-ame p R)/Real.sqrt V
  ((normalQuantile (α/2) ≤ |t| ∧ |t| ≤ normalQuantile (1-α/2)) ↔
    |t| ≤ normalQuantile (1-α/2)) ∧
  ((|t| ≤ normalQuantile (1-α/2)) ↔
    (normalQuantile (α/2) ≤ t ∧ t ≤ normalQuantile (1-α/2)))

/-- P004-T23; Supplement A pp. 14–16, C 2, observational HAC, and Proposition 4(i)–(ii).
The corrected homophily uses O_j at the neighbour, and the residual uses its own fitted
propensity. The actual inverse-Gram treatment row yields the scalar treatment sandwich
entry and the inverse-propensity residual quadratic. The numerator is the fitted IPW
estimator. Genuine normal quantiles have opposite signs and give all three equivalent
event presentations, for both SAH and HAC. These are exact identities, without a coverage claim. -/
def T23WholeStatement : Prop :=
  (∀ {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N),
    0 < N → ValidArms z → (∀ i, 0 < phat i ∧ phat i < 1) →
    (∀ i, (((designMatrix z).transpose * designMatrix z)⁻¹ * (designMatrix z).transpose) 1 i = lambda z i) ∧
    (∀ i, lambda z i * weightedEpsilon phat R g z i = residualContrast phat R g i z / N) ∧
    treatmentQuadratic (sandwich z (weightedEpsilon phat R g z) (neighborhoodMatrix B)) =
      sandwich z (weightedEpsilon phat R g z) (neighborhoodMatrix B) 1 1 ∧
    sandwich z (weightedEpsilon phat R g z) (neighborhoodMatrix B) 1 1 =
      (∑ i, ∑ j ∈ B i, lambda z i * lambda z j *
        weightedEpsilon phat R g z i * weightedEpsilon phat R g z j) ∧
    sandwich z (weightedEpsilon phat R g z) (neighborhoodMatrix B) 1 1 = oracleHAC phat R B g z) ∧
  (∀ {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (B : Fin N → Finset (Fin N))
    (O : Fin N → Fin k → ℝ) (θ : Fin k → ℝ) (β : Bool → Fin k → ℝ) (z : Assignment N),
    0 < N → (∀ i, 0 < p i ∧ p i < 1) →
    (∀ i, 0 < logisticPropensity O θ i ∧ logisticPropensity O θ i < 1) ∧
    homophilyQ p R B (covariateFits O β) =
      (∑ i, (nodeEffect p R i-(covariateFits O β i true-covariateFits O β i false)) *
        ∑ j ∈ B i, (nodeEffect p R j-(covariateFits O β j true-covariateFits O β j false))) / N ∧
    (∀ i, weightedEpsilon (logisticPropensity O θ) R (covariateFits O β) z i =
      armCount z true / N * bit (z i) / logisticPropensity O θ i * (R i z-covariateFits O β i true) +
      armCount z false / N * (1-bit (z i)) / (1-logisticPropensity O θ i) *
        (R i z-covariateFits O β i false)) ∧
    ht (logisticPropensity O θ) R z =
      (∑ i, (bit (z i)*R i z/logisticPropensity O θ i -
        (1-bit (z i))*R i z/(1-logisticPropensity O θ i))) / N) ∧
  (∀ α : ℝ, 0 < α → α < 1 →
    FiniteQuantile (α/2) ∧ FiniteQuantile (1-α/2) ∧
    normalQuantile (α/2) = -normalQuantile (1-α/2) ∧
    normalQuantile (α/2) < 0 ∧ 0 < normalQuantile (1-α/2) ∧
    (∀ t : ℝ,
      ((normalQuantile (α/2) ≤ |t| ∧ |t| ≤ normalQuantile (1-α/2)) ↔
        |t| ≤ normalQuantile (1-α/2)) ∧
      ((|t| ≤ normalQuantile (1-α/2)) ↔
        (normalQuantile (α/2) ≤ t ∧ t ≤ normalQuantile (1-α/2)))) ∧
    (∀ {N : ℕ} (p phat : Fin N → ℝ) (R : CircleTable N) (z : Assignment N)
      (Vsah Vhac : ℝ), 0 < N → (∀ i, 0 < p i ∧ p i < 1) →
      (∀ i, 0 < phat i ∧ phat i < 1) →
      0 < Vsah → 0 < Vhac →
      correctedIPWEvents p phat R z α Vsah ∧ correctedIPWEvents p phat R z α Vhac))

def leverageKernel {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => Q i j * (lambda z i * lambda z j)

def traceAdjustment {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (armCount z true * armCount z false / N) • (residualMaker z * leverageKernel z Q * residualMaker z)

def traceMu {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  Matrix.trace (traceAdjustment z Q)

def traceNu {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  2 * Matrix.trace (traceAdjustment z Q * traceAdjustment z Q)

/-- Defined on its ordinary mathematical domain traceNu ≠ 0. -/
def effectiveDegreesOfFreedom {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (Matrix.trace (traceAdjustment z Q))^2 /
    Matrix.trace (traceAdjustment z Q * traceAdjustment z Q)

/-- Shapes record row and column counts; this predicate avoids assigning values to ill-typed products. -/
def ShapeCompatible (A B : ℕ × ℕ) : Prop := A.2 = B.1

/-- P004-T24; Supplement A p. 17, Appendix A.7 and equations (44)–(45).
The corrected leverage and residual-maker matrices satisfy all projection, treatment-row,
norm, reciprocal normalization and sandwich identities. The uniform kernel gives the
stated residual quadratic. The trace adjustment uses degrees of freedom 2 mu²/nu on its
domain nu ≠ 0. Each printed defective product has compatible dimensions exactly when N=2. -/
def T24WholeStatement : Prop :=
  (∀ {N : ℕ} (z : Assignment N), ValidArms z →
    (∀ (e : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) ℝ),
      (residualMaker z).transpose = residualMaker z ∧
      residualMaker z * residualMaker z = residualMaker z ∧ residualMaker z * designMatrix z = 0 ∧
      (∀ i, (((designMatrix z).transpose * designMatrix z)⁻¹ * (designMatrix z).transpose) 1 i = lambda z i) ∧
      treatmentQuadratic (((designMatrix z).transpose * designMatrix z)⁻¹) = N/(armCount z true*armCount z false) ∧
      (∑ i, (lambda z i)^2) = N/(armCount z true*armCount z false) ∧
      armCount z true*armCount z false/N =
        1/treatmentQuadratic (((designMatrix z).transpose * designMatrix z)⁻¹) ∧
      treatmentQuadratic (sandwich z e Q) = kernelVariance z e Q ∧
      (traceNu z Q ≠ 0 → effectiveDegreesOfFreedom z Q = 2*(traceMu z Q)^2/traceNu z Q)) ∧
    (∀ (e : Fin N → ℝ) (D : Fin N → Fin N → ℝ) (h : ℝ),
      (∀ i j, 0 ≤ D i j) → 0 < h →
      let Ω := neighborhoodMatrix (fun i => ball D i h)
      distanceKernel D uniformKernel h = Ω ∧
      treatmentQuadratic (sandwich z e (distanceKernel D uniformKernel h)) =
        dotProduct e (leverageKernel z Ω *ᵥ e))) ∧
  (∀ N : ℕ, (ShapeCompatible (1,2) (N,2) ↔ N = 2) ∧
    (ShapeCompatible (2,N) (2,2) ↔ N = 2))

def expandedCenteredSummand {N : ℕ} (p : ℝ) (R : CircleTable N)
    (μ1 μ0 : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  (bit (z i)/(N*p)-(1-bit (z i))/(N*(1-p)))*R i z + (μ1-μ0)/N -
    (bit (z i)*μ1/(N*p)-(1-bit (z i))*μ0/(N*(1-p))) - nodeEffect (fun _ => p) R i/N

def expandedPrintedSummand {N : ℕ} (p : ℝ) (R : CircleTable N)
    (μ1 μ0 : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  (bit (z i)/(N*p)-(1-bit (z i))/(N*(1-p)))*R i z + (μ1-μ0)/N -
    (bit (z i)*μ1/(N*p)-(1-bit (z i))*μ0/(N*(1-p))) - nodeEffect (fun _ => p) R i

/-- Uniform L2-NED of size -4, expressed through exact finite-cylinder conditional expectations. -/
def TableNED (p : ℝ) (D : ∀ N, Fin N → Fin N → ℝ) (R : ∀ N, CircleTable N) : Prop :=
  ∃ ψ : ℝ → ℝ, ∃ g : ∀ N, Fin N → ℝ, ∃ G : ℝ,
    (∀ s, 0 ≤ s → 0 ≤ ψ s) ∧ AntitoneOn ψ (Set.Ici 0) ∧ Tendsto ψ atTop (nhds 0) ∧
    (∃ exponent : ℝ, 4 < exponent ∧ ∃ C S : ℝ, 0 < S ∧
      ∀ s, S ≤ s → ψ s ≤ C*s^(-exponent)) ∧
    (∀ N i, 0 < g N i ∧ g N i ≤ G) ∧
    (∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => R N i z-conditionOn (fun _ => p) (ball (D N) i s) (R N i) z) ≤ g N i*ψ s)

/-- P004-T25; Supplement A p. 26, the summands preceding Lemma C.2 and equation (57).
Subtracting tau_i/N gives mean zero, the exact augmented-estimator sum and its HT
specialization. Conditioning on a ball containing the own coin gives corrected (57).
The printed summand has mean (1/N-1)tau_i; the eight-node example gives -7/8 instead
of zero. The own-coin affine transformation also preserves uniform L2-NED of size -4. -/
def T25WholeStatement : Prop :=
  (∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ),
    0 < N → (0 < p ∧ p < 1) →
    (∀ i, expandedCenteredSummand p R μ1 μ0 i = centeredSummand (fun _ => p) R μ1 μ0 i) ∧
    (∀ i, expect (fun _ => p) (expandedCenteredSummand p R μ1 μ0 i) = 0) ∧
    (∀ z, (∑ i, expandedCenteredSummand p R μ1 μ0 i z) =
      augmented (fun _ => p) R (fun _ a => if a then μ1 else μ0) z-ame (fun _ => p) R) ∧
    (∀ z, (∑ i, expandedCenteredSummand p R 0 0 i z) = ht (fun _ => p) R z-ame (fun _ => p) R) ∧
    (∀ i, expect (fun _ => p) (expandedPrintedSummand p R μ1 μ0 i) =
      (1/(N : ℝ)-1)*nodeEffect (fun _ => p) R i) ∧
    (∀ (D : Fin N → Fin N → ℝ), (∀ i, D i i = 0) → ∀ i s, 0 ≤ s → ∀ z,
      conditionOn (fun _ => p) (ball D i s) (expandedCenteredSummand p R μ1 μ0 i) z =
        (bit (z i)/(N*p)-(1-bit (z i))/(N*(1-p))) *
          conditionOn (fun _ => p) (ball D i s) (R i) z + (μ1-μ0)/N -
          (bit (z i)*μ1/(N*p)-(1-bit (z i))*μ0/(N*(1-p))) - nodeEffect (fun _ => p) R i/N)) ∧
  (let R : CircleTable 8 := fun i z => bit (z i)
   ∀ i, nodeEffect (fun _ => 1/2) R i = 1 ∧
     expect (fun _ => 1/2) (expandedPrintedSummand (1/2) R 0 0 i) = -7/8 ∧
     expect (fun _ => 1/2) (expandedCenteredSummand (1/2) R 0 0 i) = 0) ∧
  (∀ (p μ1 μ0 : ℝ) (D : ∀ N, Fin N → Fin N → ℝ) (R : ∀ N, CircleTable N),
    (0 < p ∧ p < 1) → (∀ N i, D N i i = 0) → TableNED p D R →
    TableNED p D (fun N i => expandedCenteredSummand p (R N) μ1 μ0 i))

/-- S3 marginalization, also defined for a zero-probability own arm at p=0 or p=1. -/
def forcedMarginal {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) (a : Bool) : ℝ :=
  expect p (fun z => R i (Function.update z i a))

def forcedEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  forcedMarginal p R i true-forcedMarginal p R i false

def forcedAME {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : ℝ := (∑ i, forcedEffect p R i)/N

def forcedCentered {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  forcedEffect p R i-forcedAME p R

/-- Maximum of a finite row array; the empty sample's irrelevant prefix is explicitly zero. -/
def rowMaximum {N : ℕ} (f : Fin N → ℝ) : ℝ := if 0 < N then sSup (Set.range f) else 0

def arrayKernel (D : ∀ N, Fin N → Fin N → ℝ) (a : ∀ N, Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i, ∑ j, K (D N i j/b N)*a N i*a N j)/N

def exteriorEnvelope (D : ∀ N, Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  rowMaximum (fun i => ∑ j ∈ (ball (D N) i (r N))ᶜ, φ (D N i j))

def interiorEnvelope (D : ∀ N, Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  rowMaximum (fun i => ∑ j ∈ ball (D N) i (b N), φ (D N i j))

def arraySquareMaximum (a : ∀ N, Fin N → ℝ) (N : ℕ) : ℝ := rowMaximum (fun i => (a N i)^2)

def kernelLimitConclusion (D : ∀ N, Fin N → Fin N → ℝ) (a : ∀ N, Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℕ → ℝ) : Prop :=
  Tendsto (arrayKernel D a K b) atTop (nhds 0) ∧
  Filter.liminf (arrayKernel D a K b) atTop = 0 ∧ LiminfAtLeast (arrayKernel D a K b) 0

def printedInteriorConclusion (D : ∀ N, Fin N → Fin N → ℝ) (a : ∀ N, Fin N → ℝ)
    (K φ : ℝ → ℝ) (b : ℕ → ℝ) : Prop :=
  φ 0 = 0 ∧ (∀ᶠ N in atTop, ∀ i, a N i = 0) ∧
  (∀ᶠ N in atTop, arraySquareMaximum a N ≤ interiorEnvelope D φ b N) ∧
  Tendsto (arraySquareMaximum a) atTop (nhds 0) ∧
  (∀ L : ℝ, (∀ t, 0 ≤ t → |K t| < L) →
    ∀ᶠ N in atTop, |arrayKernel D a K b N| ≤ L*interiorEnvelope D φ b N) ∧
  kernelLimitConclusion D a K b

/-- P004-T26; Supplement A pp. 34–35, Lemma C.10, equation (122) and Remark 1.
The exterior-tail envelope, bounded outcomes, quadratic spacing and kernel conditions
give convergence of the centered-effect kernel form to zero, liminf zero and C 6.
The explicit radius b_N^(1/6) diverges and its cube divided by b_N tends to zero.
The printed inside-ball premise also implies the conclusion, bounds the diagonal
heterogeneity and the kernel form, and forces eventual exact homogeneity for fixed phi.
Effects use S3 marginalization, including Bernoulli endpoints; regularity is only eventual. -/
def T26WholeStatement : Prop :=
  (∀ b : ℕ → ℝ, Tendsto b atTop atTop →
    Tendsto (fun N => (b N)^(1/6 : ℝ)) atTop atTop ∧
    Tendsto (fun N => ((b N)^(1/6 : ℝ))^3/b N) atTop (nhds 0)) ∧
  (∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ) (K φ : ℝ → ℝ) (b : ℕ → ℝ),
    (0 ≤ p ∧ p ≤ 1) → 0 ≤ d → BoundedOutcomes P →
    (∀ᶠ N in atTop, WellDefined (P N) d) → MetricNodeDistances P →
    QuadraticSpacing P → KernelConditions K → Tendsto b atTop atTop →
    (∀ s, 0 ≤ s → 0 ≤ φ s) →
    let D := fun N => nodeSeparation (P N)
    let a := fun N => forcedCentered (fun _ => p) (circleAverage (P N) d)
    (∀ᶠ N in atTop, ∀ i j, |a N i| * |a N j| ≤ φ (D N i j)) →
    ((∀ r : ℕ → ℝ, Tendsto r atTop atTop →
        Tendsto (exteriorEnvelope D φ r) atTop (nhds 0)) → kernelLimitConclusion D a K b) ∧
    (Tendsto (interiorEnvelope D φ b) atTop (nhds 0) → printedInteriorConclusion D a K φ b)) ∧
  (∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N), (∀ i, 0 < p i ∧ p i < 1) →
    (∀ i a, forcedMarginal p R i a = marginal p R i a) ∧
    forcedAME p R = ame p R ∧ (∀ i, forcedCentered p R i = nodeEffect p R i-ame p R))

end
end SAP.P004b
