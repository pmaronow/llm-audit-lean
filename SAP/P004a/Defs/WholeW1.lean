import Mathlib
import SAP.P004a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
universe u v

/-- Convergence in probability for a sequence whose population size is `n k`. -/
def W1InProb (n : ℕ → ℕ) (p : ∀ k, Fin (n k) → ℝ)
    (X : ∀ k, Assignment (n k) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun k => prob (p k) (fun z => ε < |X k z|)) atTop (nhds 0)

/-- Order in probability on a sequence of possibly reindexed populations. -/
def W1BigOp (n : ℕ → ℕ) (p : ∀ k, Fin (n k) → ℝ)
    (X : ∀ k, Assignment (n k) → ℝ) (rate : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k in atTop, prob (p k) (fun z => C * |rate k| < |X k z|) < ε

/-- Standard normal distributional limit on reindexed populations. -/
def W1NormalLimit (n : ℕ → ℕ) (p : ∀ k, Fin (n k) → ℝ)
    (X : ∀ k, Assignment (n k) → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun k => prob (p k) (fun z => X k z ≤ x)) atTop (nhds (normalCDF x))

/-- Change only the distance band, preserving the field, nodes and spatial measure. -/
def w1WithBand {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (D : Set ℝ) : SpatialPopulation N X :=
  { P with bands := fun _ => D }

/-- Marginalization over the other independent coins, including endpoint probabilities. -/
def w1ForcedMarginal {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (i : Fin N) (a : Bool) : ℝ := expect p (fun z => R i (Function.update z i a))

def w1ForcedEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  w1ForcedMarginal p R i true - w1ForcedMarginal p R i false

def w1ForcedAME {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : ℝ :=
  (∑ i, w1ForcedEffect p R i) / N

def w1ForcedPointEffect {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (p : Fin N → ℝ) (i : Fin N) (x : X) : ℝ :=
  w1ForcedEffect p (fun _ z => P.outcome x z) i

/-- A radial effect is the signed pushforward density on the band. Positive atoms use their
actual shell means; no value is assigned by dividing by a zero shell mass. -/
def W1RadialDensity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (r : X → ℝ) (δ : X → ℝ) (t : ℝ → ℝ) : Prop :=
  Integrable t (Measure.map r μ) ∧
  (∀ B : Set ℝ, MeasurableSet B →
    (∫ s in B, t s ∂Measure.map r μ) = ∫ x in r ⁻¹' B, δ x ∂μ) ∧
  (∀ s : ℝ, 0 < (Measure.map r μ) {s} →
    t s = (∫ x in r ⁻¹' {s}, δ x ∂μ) / ((Measure.map r μ) {s}).toReal)

/-- T15(a), including the continuous-circle convention and the bridge to conditional means. -/
def T15BandStatement : Prop :=
  ∀ {N : ℕ} {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (p : Fin N → ℝ) (d : ℝ),
    0 < N → (∀ i, 0 ≤ p i ∧ p i ≤ 1) → WellDefined P d →
    (∀ i, Measurable (nodeDistance P i)) →
    (∀ i, IntegrableOn (w1ForcedPointEffect P p i) (region P i d) P.zeta) ∧
    (∀ i, w1ForcedEffect p (circleAverage P d) i =
      (∫ x in region P i d, w1ForcedPointEffect P p i x ∂P.zeta) /
        (P.zeta (region P i d)).toReal) ∧
    w1ForcedAME p (circleAverage P d) =
      (∑ i, (∫ x in region P i d, w1ForcedPointEffect P p i x ∂P.zeta) /
        (P.zeta (region P i d)).toReal) / N ∧
    (∀ i, ∃ t : ℝ → ℝ,
      W1RadialDensity (P.zeta.restrict (region P i d)) (nodeDistance P i)
        (w1ForcedPointEffect P p i) t ∧
      w1ForcedEffect p (circleAverage P d) i =
        (∫ r, t r ∂Measure.map (nodeDistance P i) (P.zeta.restrict (region P i d))) /
          (P.zeta (region P i d)).toReal) ∧
    ((∀ i, 0 < p i ∧ p i < 1) →
      (∀ i, w1ForcedEffect p (circleAverage P d) i = nodeEffect p (circleAverage P d) i) ∧
      w1ForcedAME p (circleAverage P d) = ame p (circleAverage P d))

/-- T15(b-c), with a finite enumeration of attained radii. Labels of zero mass are excluded
from every shell-mean expression, including the common-weight formula. -/
def T15FiniteStatement : Prop :=
  ∀ {A : Type v} [Fintype A] {m N : ℕ}
    (a : Fin N → A → ℝ) (shell : Fin N → A → Fin m) (δ : Fin N → A → ℝ),
    0 < N → (∀ i x, 0 ≤ a i x) → (∀ i, 0 < ∑ x, a i x) →
    (∀ i, finiteAverage (a i) (δ i) =
      ∑ k ∈ Finset.univ.filter (fun k => 0 < supportedShellMass (a i) shell i k),
        supportedShellMass (a i) shell i k / (∑ x, a i x) *
          ((∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k)) ∧
    (∑ i, finiteAverage (a i) (δ i)) / (N : ℝ) =
      (∑ i, ∑ k ∈ Finset.univ.filter (fun k => 0 < supportedShellMass (a i) shell i k),
        supportedShellMass (a i) shell i k / (∑ x, a i x) *
          ((∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k)) / (N : ℝ) ∧
    (∀ w : Fin m → ℝ,
      (∀ i k, supportedShellMass (a i) shell i k / (∑ x, a i x) = w k) →
      (∀ k, 0 < w k → ∀ i, 0 < supportedShellMass (a i) shell i k) ∧
      (∑ i, finiteAverage (a i) (δ i)) / (N : ℝ) =
        ∑ k ∈ Finset.univ.filter (fun k => 0 < w k), w k *
          ((∑ i, (∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k) / (N : ℝ)))

/-- A common radial kernel gives the identity for all bounded measurable radial effect
profiles exactly when every normalized node measure is that kernel. -/
def T15KernelStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (P : Fin N → Measure ℝ) (U : Measure ℝ),
    (∀ i, IsProbabilityMeasure (P i)) → IsProbabilityMeasure U →
    ((∀ f : Fin N → ℝ → ℝ, (∀ i, Measurable (f i)) →
      (∀ i, ∃ C : ℝ, ∀ r, |f i r| ≤ C) →
      (∑ i, ∫ r, f i r ∂P i) / N = ∫ r, (∑ i, f i r) / N ∂U) ↔ ∀ i, P i = U)

def w1ZeroShell (D : Set ℝ) : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) :=
  { shellSpatialPopulation D with outcome := fun _ _ => 0 }

/-- Non-identifiability allows every recovery function, not just linear combinations. -/
def T15NonidentificationStatement : Prop :=
  T14Statement ∧
  (∀ (i : Fin 2) (r : ℝ),
    0 < (shellSpatialPopulation {r}).zeta (region (shellSpatialPopulation {r}) i 0) ↔ r = 4 ∨ r = 5) ∧
  (∀ D ∈ ({({4} : Set ℝ), {5}, Set.Icc 4 5, Set.Icc 0 5} : Finset (Set ℝ)),
    WellDefined (w1ZeroShell D) 0 ∧ ame (fun _ => 1/2) (circleAverage (w1ZeroShell D) 0) = 0) ∧
  ¬ ∃ F : (Fin 2 → ℝ) → ℝ,
    F (fun j => ame (fun _ => 1/2)
      (circleAverage (shellSpatialPopulation (if j = 0 then {4} else {5})) 0)) =
        ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0) ∧
    F (fun j => ame (fun _ => 1/2)
      (circleAverage (w1ZeroShell (if j = 0 then {4} else {5})) 0)) =
        ame (fun _ => 1/2) (circleAverage (w1ZeroShell (Set.Icc 4 5)) 0)

def w1AreaRadial (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin 2))) : Measure ℝ :=
  ENNReal.ofReal (1 / (Real.pi * (b^2-a^2))) •
    Measure.map (fun x => dist x c)
      ((volume.restrict X).restrict {x | a ≤ dist x c ∧ dist x c ≤ b})

def w1UniformRadial (a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (b-a)) • volume.restrict (Set.Icc a b)

/-- T15(d), including ambient-set transport and a comparison on a set of positive measure. -/
def T15AreaStatement : Prop :=
  ∀ (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin 2))),
    0 ≤ a → a < b → Metric.closedBall c b ⊆ X →
    w1AreaRadial c a b X = volume.withDensity (fun r : ℝ =>
      ENNReal.ofReal (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)) ∧
    (w1AreaRadial c a b X) (Set.Iic ((a+b)/2)) =
      ENNReal.ofReal ((((a+b)/2)^2-a^2)/(b^2-a^2)) ∧
    w1UniformRadial a b (Set.Iic ((a+b)/2)) = ENNReal.ofReal (1/2) ∧
    (((a+b)/2)^2-a^2)/(b^2-a^2) < 1/2 ∧
    w1AreaRadial c a b X ≠ w1UniformRadial a b

/-- P004-T15; p. 757 (PDF p. 14), sentence after eq. (26); eqs. (2), (7)-(9).
Band effects average marginalized point effects using node-specific shell masses. Continuous
circle effects are signed pushforward densities, with the actual shell means at positive
atoms. Finite shell decompositions and their node mean hold without common weights; common
weights give a weighted sum of circle AMEs. A common kernel works for every bounded measurable
profile if and only if all normalized node measures equal it. Circle AMEs alone do not
determine the band AME. Full planar annuli have density 2r/(b²-a²), including disks at a=0,
and their radial measure differs from the uniform radial measure.
The usual measure-theoretic conditions are assumed. -/
def T15WholeStatement : Prop :=
  T15BandStatement.{u} ∧ T15FiniteStatement.{v} ∧ T15KernelStatement ∧
    T15NonidentificationStatement ∧ T15AreaStatement

/-! The balanced three-type witness. Locations use a common translation by ten of the
one-based paper coordinates; every distance, integral and statistical quantity is preserved. -/

def w1ThreeP (N : ℕ) : Fin N → ℝ := propensities (threeTypeONat N) threeTypeTheta

def w1ThreeA (t : ℕ) : ℝ := if t = 1 then -24/125 else 27/250
def w1ThreeB (t : ℕ) : ℝ := if t = 1 then 16/125 else -81/1000
def w1ThreeD (t : ℕ) : ℝ := w1ThreeA t - w1ThreeB t

def w1ThreeLinear (c : ℕ → ℝ) (N : ℕ) (z : Assignment N) : ℝ :=
  (∑ i, c (i.val % 3) * (bit (z i) - w1ThreeP N i)) / N

def w1ThreePrinted (N : ℕ) : Assignment N → ℝ :=
  augmented (w1ThreeP N) (circleAverage (threeTypePopulation N) 0)
    (printedFits (w1ThreeP N) (circleAverage (threeTypePopulation N) 0) (threeTypeONat N))

def w1ThreeIPW (θhat : ∀ N, Assignment N → Fin 2 → ℝ) (N : ℕ) : Assignment N → ℝ :=
  fittedIPW (circleAverage (threeTypePopulation N) 0) (threeTypeONat N) (θhat N)

/-- The explicit regularity constants of T1(W1), without assuming the certificates. -/
def T1SpatialStatement : Prop :=
  SpatialLocalConditions threeTypePopulation ∧
  threeTypeTheta ∈ interior threeTypeParameterSet ∧ 0 < Real.log 2 ∧ Real.log 2 < 1 ∧
  (∀ N x z, |(threeTypePopulation N).outcome x z| < 2) ∧
  (∀ N i j, |threeTypeONat N i j| ≤ 1) ∧
  (∀ N i, (1/10 : ℝ) < w1ThreeP N i ∧ w1ThreeP N i < 1-1/10) ∧
  (∀ N d, 0 ≤ d → WellDefined (threeTypePopulation N) d) ∧
  (∀ N, circleAverage (threeTypePopulation N) 0 = threeTypeTable N) ∧
  (∀ N d, 0 ≤ d → LocalAt (circleAverage (threeTypePopulation N) d)
    (nodeSeparation (threeTypePopulation N)) 0) ∧
  (∀ N i, ball (nodeSeparation (threeTypePopulation N)) i 0 = {i}) ∧
  (∀ N i r, 0 ≤ r → ((ball (nodeSeparation (threeTypePopulation N)) i r).card : ℝ) ≤ r/5+1)

/-- T1(W1-W2): balanced numerical population certificates. -/
def T1PopulationStatement : Prop :=
  ∀ K : ℕ, 0 < K →
  let N := 3*K
  let p := w1ThreeP N
  let R := circleAverage (threeTypePopulation N) 0
  let O := threeTypeONat N
  (∀ a b : Fin 2, (∑ i, O i a * O i b) / N = (!![1,0;0,2/3] : Matrix (Fin 2) (Fin 2) ℝ) a b) ∧
  information p O = !![25/108,0;0,4/27] ∧
  (∀ a : Bool, beta p R O a = ![509/500,0]) ∧
  (fun j => (∑ i, ((1-p i)*marginal p R i true + p i*marginal p R i false)*O i j) / N) = ![61/60,0] ∧
  scoreGamma p R O = ![549/125,0] ∧
  (∀ i, nodeEffect p R i = 0) ∧ ame p R = 0 ∧
  homophilyQ p R (fun i => {i}) (printedFits p R O) = 0 ∧
  ((∑ i, ∑ j ∈ ({i} : Finset (Fin N)),
    (nodeEffect p R i - dot (O i) (beta p R O true-beta p R O false)) *
    (nodeEffect p R j - dot (O i) (beta p R O true-beta p R O false))) / N = 0)

/-- T1(W3-W4): actual random variables and their design variances. -/
def T1LinearStatement : Prop :=
  ∀ K : ℕ, 0 < K →
  let N := 3*K
  let p := w1ThreeP N
  let R := circleAverage (threeTypePopulation N) 0
  (∀ z, w1ThreePrinted N z = w1ThreeLinear w1ThreeB N z) ∧
  (∀ z, ht p R z - (∑ i, (bit (z i)-p i)*dot (threeTypeONat N i)
    (scoreGamma p R (threeTypeONat N))) / N = w1ThreeLinear w1ThreeA N z) ∧
  (N : ℝ) * variance p (w1ThreeLinear w1ThreeA N) = 3/625 ∧
  (N : ℝ) * variance p (w1ThreePrinted N) = 1753/750000 ∧
  (N : ℝ) * variance p (fun z => w1ThreeLinear w1ThreeA N z-w1ThreePrinted N z) = 10369/750000

def w1ThreeBlockIndex {K : ℕ} (j : Fin K) (t : Fin 3) : Fin (3*K) :=
  ⟨3*j.val+t.val, by omega⟩

def w1ThreeBlock {K : ℕ} (z : Assignment (3*K)) (j : Fin K) : ℝ :=
  ∑ t : Fin 3, w1ThreeD t.val * (bit (z (w1ThreeBlockIndex j t)) - w1ThreeP 3 t)

def w1ThreeU (K : ℕ) (z : Assignment (3*K)) : ℝ :=
  (∑ j : Fin K, w1ThreeBlock z j) / Real.sqrt (3*K : ℕ)

def w1OneBlock (z : Assignment 3) : ℝ :=
  ∑ t : Fin 3, w1ThreeD t.val * (bit (z t)-w1ThreeP 3 t)

/-- Equality of the joint block law to the product of the one-block laws expresses both
independence and identical distribution, including the empty product. -/
def T1BlockLawStatement : Prop :=
  (∀ K : ℕ, ∀ F : (Fin K → ℝ) → ℝ,
    expect (w1ThreeP (3*K)) (fun z => F (w1ThreeBlock z)) =
      ∑ b : Fin K → Assignment 3, (∏ j, designWeight (w1ThreeP 3) (b j)) *
        F (fun j => w1OneBlock (b j))) ∧
  expect (w1ThreeP 3) w1OneBlock = 0 ∧
  expect (w1ThreeP 3) (fun z => (w1OneBlock z)^2) = 3*(10369/750000) ∧
  expect (w1ThreeP 3) (fun z => (w1OneBlock z)^4) = 915255049/250000000000

/-- T1(W5): exact block-sum moments and a uniform positive tail probability. -/
def T1MomentStatement : Prop :=
  ∀ K : ℕ, 0 < K →
    (∀ z, Real.sqrt (3*K : ℕ) *
      (w1ThreeLinear w1ThreeA (3*K) z-w1ThreeLinear w1ThreeB (3*K) z) = w1ThreeU K z) ∧
    expect (w1ThreeP (3*K)) (fun z => (w1ThreeU K z)^2) = 10369/750000 ∧
    expect (w1ThreeP (3*K)) (fun z => (w1ThreeU K z)^4) =
      (915255049/250000000000)/(9*(K : ℝ)) +
        3*((K : ℝ)-1)*(10369/750000)^2/(K : ℝ) ∧
    expect (w1ThreeP (3*K)) (fun z => (w1ThreeU K z)^4) ≤ 2205448981/2250000000000 ∧
    (107516161/2205448981 : ℝ) ≤
      prob (w1ThreeP (3*K)) (fun z => (10369/750000 : ℝ)/2 < (w1ThreeU K z)^2)

/-- T1(W6), along the balanced sequence N=3K. The variance-estimate assumption is precisely
consistency for the printed variance, not an assumption about the desired coverage. -/
def T1ExpansionStatement (θhat : ∀ N, Assignment N → Fin 2 → ℝ) : Prop :=
  W1BigOp (fun K => 3*K) (fun K => w1ThreeP (3*K))
    (fun K z => w1ThreeIPW θhat (3*K) z-w1ThreeLinear w1ThreeA (3*K) z)
    (fun K => ((3*K : ℕ) : ℝ)⁻¹)

def T1RemainderStatement (θhat : ∀ N, Assignment N → Fin 2 → ℝ) : Prop :=
 W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
    (fun K z => Real.sqrt (3*K : ℕ) * (w1ThreeIPW θhat (3*K) z-w1ThreePrinted (3*K) z)-w1ThreeU K z) ∧
  ¬ W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
    (fun K z => Real.sqrt (3*K : ℕ) * (w1ThreeIPW θhat (3*K) z-w1ThreePrinted (3*K) z))

def T1GaussianStatement (θhat : ∀ N, Assignment N → Fin 2 → ℝ) : Prop :=
 W1NormalLimit (fun K => 3*K) (fun K => w1ThreeP (3*K))
    (fun K z => Real.sqrt (3*K : ℕ) * w1ThreeIPW θhat (3*K) z / Real.sqrt (3/625)) ∧
  W1NormalLimit (fun K => 3*K) (fun K => w1ThreeP (3*K))
    (fun K z => w1ThreeIPW θhat (3*K) z /
      Real.sqrt (variance (w1ThreeP (3*K)) (w1ThreePrinted (3*K))) / Real.sqrt (3600/1753))

def T1CoverageStatement (θhat : ∀ N, Assignment N → Fin 2 → ℝ) : Prop :=
 (∀ Vhat : ∀ K, Assignment (3*K) → ℝ, (∀ K z, 0 ≤ Vhat K z) →
    W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => (3*K : ℕ)*Vhat K z-1753/750000) →
    ∀ α : ℝ, 0 < α → α < 1 →
    Tendsto (fun K => prob (w1ThreeP (3*K)) (fun z =>
      |w1ThreeIPW θhat (3*K) z-ame (w1ThreeP (3*K)) (circleAverage (threeTypePopulation (3*K)) 0)| ≤
        normalQuantile (1-α/2)*Real.sqrt (Vhat K z))) atTop
      (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (1753/3600))-1)) ∧
    2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (1753/3600))-1 < 1-α)


def T1LimitStatement (θhat : ∀ N, Assignment N → Fin 2 → ℝ) : Prop :=
  T1ExpansionStatement θhat ∧ T1RemainderStatement θhat ∧
    T1GaussianStatement θhat ∧ T1CoverageStatement θhat

/-- P004-T1; Supplement A pp. 13-17, Proposition 4, eqs. (36), (42)-(43).
The printed claim is false: the balanced three-type spatial design satisfies every stated
hypothesis, with the displayed exact information, coefficients, effects and variance
constants. Its independent blocks have the stated exact second and fourth moments and the
positive uniform tail bound. An actual constrained logistic MLE has the corrected order-N⁻¹
expansion, so the printed root-N remainder fails to converge to zero. The fitted estimator's
Gaussian variance is 3/625, its printed-variance standardization has limiting variance
3600/1753, and intervals consistent for the printed variance have the stated strict coverage
deficit for every 0<α<1. -/
def T1WholeStatement : Prop :=
  T1SpatialStatement ∧ T1PopulationStatement ∧ T1LinearStatement ∧
  T1BlockLawStatement ∧ T1MomentStatement ∧
  ∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
    LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat ∧ T1LimitStatement θhat

/-! The active-group witness, with the specified field on the unit disks, including points
outside the support of the counting measure. -/

def w1ActiveSign (N : ℕ) (i : Fin N) : ℝ :=
  if i.val % 8 = 0 then 1 else if i.val % 8 = 1 then -1 else 0

def w1ActiveDiskPopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) :=
  { activePopulation N with outcome := fun x z =>
      (∑ i : Fin N, if dist x (planePoint (10*(i : ℝ)) 0) ≤ 1 then
        w1ActiveSign N i * bit (z i) else 0) }

def w1ActiveP (N : ℕ) : Fin N → ℝ := propensities (activeO N) activeTheta

def w1ActiveNH (N : ℕ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin N => activeGroup N i)).card : ℝ)

def w1ActiveNL (N : ℕ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i)).card : ℝ)

def w1ActiveS (N : ℕ) (z : Assignment N) : ℝ := ∑ i, w1ActiveSign N i * bit (z i)
def w1ActiveK (N : ℕ) (z : Assignment N) : ℝ :=
  ∑ i, if activeGroup N i then bit (z i) else 0

def w1ActiveJ (N : ℕ) (z : Assignment N) : ℝ :=
  ∑ i, if activeGroup N i then 0 else bit (z i)

def w1Clip (q : ℝ) : ℝ := max (1/20) (min (19/20) q)
def w1Logit (q : ℝ) : ℝ := Real.log (q/(1-q))
def w1ActivePH (N : ℕ) (z : Assignment N) : ℝ := w1Clip (w1ActiveK N z/w1ActiveNH N)
def w1ActivePL (N : ℕ) (z : Assignment N) : ℝ := w1Clip (w1ActiveJ N z/w1ActiveNL N)

def w1ActiveMLE (N : ℕ) (z : Assignment N) : Fin 2 → ℝ :=
  ![if w1ActiveNH N = 0 then 0 else w1Logit (w1ActivePH N z),
    if w1ActiveNL N = 0 then -Real.log 9 else w1Logit (w1ActivePL N z)]

def w1ActiveR (N : ℕ) (z : Assignment N) : ℝ :=
  ∑ i, if activeGroup N i then bit (z i) *
    (w1ActiveSign N i-w1ActiveS N z/(w1ActiveNH N*w1ActivePH N z))^2 else 0

def w1ActiveIPW (N : ℕ) : Assignment N → ℝ :=
  fittedIPW (activeTable N) (activeO N) (w1ActiveMLE N)

def w1ActiveFits (N : ℕ) (z : Assignment N) : Fin N → Bool → ℝ :=
  fun i a => dot (activeO N i)
    (fittedBeta (propensities (activeO N) (w1ActiveMLE N z)) (activeTable N) (activeO N) a z)

def w1ActiveVPrinted (N : ℕ) (z : Assignment N) : ℝ :=
  printedSAH (propensities (activeO N) (w1ActiveMLE N z)) (activeTable N)
    (fun i => {i}) (w1ActiveFits N z) z

def w1ActiveVRaw (N : ℕ) (z : Assignment N) : ℝ :=
  rawSAH (propensities (activeO N) (w1ActiveMLE N z)) (activeTable N)
    (fun i => {i}) (w1ActiveFits N z) z

/-- T3 spatial, logistic and numerical regularity. The count measure is supported at the
node centers; the field itself has the prescribed values on entire unit disks. -/
def T3SpatialStatement : Prop :=
  LogisticConditions activeO activeTheta activeParameterSet w1ActiveMLE ∧
  activeTheta ∈ interior activeParameterSet ∧ SpatialLocalConditions w1ActiveDiskPopulation ∧
  (∀ N x z, |(w1ActiveDiskPopulation N).outcome x z| < 2) ∧
  (∀ N (i : Fin N) x z, dist x (planePoint (10*(i : ℝ)) 0) ≤ 1 →
    (w1ActiveDiskPopulation N).outcome x z = w1ActiveSign N i*bit (z i)) ∧
  (∀ N x z, (∀ i : Fin N, 1 < dist x (planePoint (10*(i : ℝ)) 0)) →
    (w1ActiveDiskPopulation N).outcome x z = 0) ∧
  (∀ N d, 0 ≤ d → WellDefined (w1ActiveDiskPopulation N) d) ∧
  (∀ N d, circleAverage (w1ActiveDiskPopulation N) d = circleAverage (activePopulation N) d) ∧
  (∀ N, circleAverage (w1ActiveDiskPopulation N) 0 = activeTable N) ∧
  (∀ N d, 0 ≤ d → LocalAt (circleAverage (w1ActiveDiskPopulation N) d)
    (nodeSeparation (w1ActiveDiskPopulation N)) (2*(d+1))) ∧
  (∀ N i, ball (nodeSeparation (w1ActiveDiskPopulation N)) i 0 = {i}) ∧
  (∀ N i r, 0 ≤ r → ((ball (nodeSeparation (w1ActiveDiskPopulation N)) i r).card : ℝ) ≤ r/5+1) ∧
  (∀ N i, (1/25 : ℝ) < w1ActiveP N i ∧ w1ActiveP N i < 1-1/25) ∧
  (∀ N i j, |activeO N i j| ≤ 1)

/-- T3(W1-W2) on every N=8r, r>0; every fitted inverse and variance is certified here. -/
def T3FiniteStatement : Prop :=
  ∀ r : ℕ, 0 < r →
  let N := 8*r
  (w1ActiveNH N = (N : ℝ)/4 ∧ w1ActiveNL N = 3*(N : ℝ)/4) ∧
  (∀ a b : Fin 2, (∑ i, activeO N i a*activeO N i b)/N =
    (!![1/4,0;0,3/4] : Matrix (Fin 2) (Fin 2) ℝ) a b) ∧
  (∀ i, w1ActiveP N i = if activeGroup N i then 1/2 else 1/10) ∧
  (∀ a : Bool, beta (w1ActiveP N) (activeTable N) (activeO N) a = 0) ∧
  ame (w1ActiveP N) (activeTable N) = 0 ∧
  homophilyQ (w1ActiveP N) (activeTable N) (fun i => {i}) (printedFits (w1ActiveP N) (activeTable N) (activeO N)) = 1/4 ∧
  (∀ z, w1ActiveIPW N z = w1ActiveS N z/(N*w1ActivePH N z)) ∧
  (∀ z, augmented (w1ActiveP N) (activeTable N)
    (printedFits (w1ActiveP N) (activeTable N) (activeO N)) z = 2*w1ActiveS N z/N) ∧
  expect (w1ActiveP N) (w1ActiveS N) = 0 ∧ variance (w1ActiveP N) (w1ActiveS N) = (N : ℝ)/16 ∧
  variance (w1ActiveP N) (fun z => 2*w1ActiveS N z/N) = 1/(4*N) ∧
  (∀ z, fittedBeta (propensities (activeO N) (w1ActiveMLE N z)) (activeTable N) (activeO N) true z =
      ![w1ActiveS N z/(w1ActiveNH N*w1ActivePH N z),0]) ∧
  (∀ z, fittedBeta (propensities (activeO N) (w1ActiveMLE N z)) (activeTable N) (activeO N) false z = 0) ∧
  (∀ z, (1/20 : ℝ) ≤ w1ActivePH N z ∧ w1ActivePH N z ≤ 19/20 ∧
    IsUnit (information (propensities (activeO N) (w1ActiveMLE N z)) (activeO N)).det) ∧
  (∀ z, w1ActiveVPrinted N z = (armCount z true/N)^2*w1ActiveR N z/((N : ℝ)^2*(w1ActivePH N z)^4)) ∧
  0 < variance (w1ActiveP N) (w1ActiveIPW N)

/-- The two high-group signed counts, and the low-group count. -/
def w1ActiveCount (N : ℕ) (z : Assignment N) (a : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => i.val % 8 = a ∧ z i = true)).card

def w1ActiveLowCount (N : ℕ) (z : Assignment N) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i ∧ z i = true)).card

/-- Finite binomial fiber formula; the ranges guarantee that each exponent subtraction is
ordinary nonnegative subtraction. This identifies expectations, not just entered constants. -/
def T3CountStatement : Prop :=
  ∀ r : ℕ, 0 < r → ∀ F : ℕ → ℕ → ℕ → ℝ,
    expect (w1ActiveP (8*r)) (fun z => F (w1ActiveCount (8*r) z 0)
      (w1ActiveCount (8*r) z 1) (w1ActiveLowCount (8*r) z)) =
    ∑ u : Fin (r+1), ∑ v : Fin (r+1), ∑ j : Fin (6*r+1),
      ((Nat.choose r u.val : ℝ)*(Nat.choose r v.val : ℝ)/(2 : ℝ)^(2*r)) *
      ((Nat.choose (6*r) j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(6*r-j.val)) * F u.val v.val j.val

/-- T3(W3), with an exact N=64 expectation as well as certified rounding intervals. -/
def T3NumericalStatement : Prop :=
  variance (w1ActiveP 32) (w1ActiveIPW 32) = 18239/1505280 ∧
  expect (w1ActiveP 32) (w1ActiveVPrinted 32) = 412940740700292467/161486810505216000000 ∧
  variance (w1ActiveP 64) (w1ActiveIPW 64) = 1710440723/354248294400 ∧
  expect (w1ActiveP 64) (w1ActiveVPrinted 64) =
    17415062510218476553980121318471/12002159705791979639097262080000000 ∧
  |expect (w1ActiveP 64) (w1ActiveVPrinted 64)-(14510/10000000 : ℝ)| < 1/20000000 ∧
  |expect (w1ActiveP 32) (w1ActiveVPrinted 32)/variance (w1ActiveP 32) (w1ActiveIPW 32)-2110/10000| < 1/20000 ∧
  |expect (w1ActiveP 64) (w1ActiveVPrinted 64)/variance (w1ActiveP 64) (w1ActiveIPW 64)-3005/10000| < 1/20000 ∧
  expect (w1ActiveP 32) (w1ActiveVPrinted 32) < variance (w1ActiveP 32) (w1ActiveIPW 32) ∧
  expect (w1ActiveP 64) (w1ActiveVPrinted 64) < variance (w1ActiveP 64) (w1ActiveIPW 64)

/-- T3(W4), along N=8r. Coverage is an interval event defined on every draw, and the
standardized version is restricted to its positive-variance domain. -/
def T3AsymptoticStatement : Prop :=
  W1BigOp (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => w1ActiveIPW (8*r) z-2*w1ActiveS (8*r) z/(8*r : ℕ)) (fun r => ((8*r : ℕ) : ℝ)⁻¹) ∧
  W1NormalLimit (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => Real.sqrt (8*r : ℕ)*w1ActiveIPW (8*r) z/(1/2)) ∧
  Tendsto (fun r => (8*r : ℕ)*variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r))) atTop (nhds (1/4 : ℝ)) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r)) (fun r z => armCount z true/(8*r : ℕ)-1/5) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r)) (fun r z => w1ActiveR (8*r) z/(8*r : ℕ)-1/8) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r)) (fun r z => (8*r : ℕ)*w1ActiveVPrinted (8*r) z-2/25) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => w1ActiveVPrinted (8*r) z/variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r))-8/25) ∧
  Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0)) atTop (nhds 0)

def T3CoverageStatement : Prop :=
 (∀ α : ℝ, 0 < α → α < 1/2 →
    Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z =>
      |w1ActiveIPW (8*r) z| ≤ normalQuantile (1-α/2)*Real.sqrt (w1ActiveVPrinted (8*r) z))) atTop
      (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1)) ∧
    Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z =>
      0 < w1ActiveVPrinted (8*r) z ∧
      |w1ActiveIPW (8*r) z/Real.sqrt (w1ActiveVPrinted (8*r) z)| ≤ normalQuantile (1-α/2))) atTop
      (nhds (2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1)) ∧
    2*normalCDF (normalQuantile (1-α/2)*Real.sqrt (8/25))-1 < 1-α)


def T3LimitStatement : Prop := T3AsymptoticStatement ∧ T3CoverageStatement

/-- P004-T3; Supplement A pp. 15-16, observational residual, SAH variance and Proposition 4(i).
The printed claim is false: the specified N=8r two-group disk field and actual clipped
logistic MLE satisfy the stated assumptions, with singleton neighborhoods and zero AME.
The exact fitted estimator, coefficients, residual sum and double-weighted variance have
the stated formulas. The N=32 and N=64 variances and expectations give the stated strict
finite underestimation. The root-N Gaussian variance and scaled actual variance tend to
1/4, the pooled treatment fraction N₁/N and normalized residual sum R/N tend in probability
to 1/5 and 1/8, and the printed scaled variance and variance ratio tend to 2/25 and 8/25.
Every 0<α<1/2 has the stated exact limiting coverage strictly below 1-α. -/
def T3WholeStatement : Prop :=
  T3SpatialStatement ∧ T3FiniteStatement ∧ T3NumericalStatement ∧ T3LimitStatement

/-- T4(c), on precisely the fitted-MLE witness used for T3. -/
def T4WitnessStatement : Prop :=
  (∀ r : ℕ, 0 < r → ∀ z : Assignment (8*r),
    w1ActiveVRaw (8*r) z = w1ActiveR (8*r) z/(((8*r : ℕ) : ℝ)^2*(w1ActivePH (8*r) z)^2)) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => (8*r : ℕ)*w1ActiveVRaw (8*r) z-1/2) ∧
  Tendsto (fun r => (8*r : ℕ)*variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r))) atTop (nhds (1/4 : ℝ)) ∧
  (1/4 : ℝ) ≤ 1/2 ∧
  expect (w1ActiveP 32) (w1ActiveVRaw 32) = 493725989/38038425600 ∧
  variance (w1ActiveP 32) (w1ActiveIPW 32) = 18239/1505280 ∧
  variance (w1ActiveP 32) (w1ActiveIPW 32) < expect (w1ActiveP 32) (w1ActiveVRaw 32)

/-- P004-T4; Supplement A p. 15, definitions of the observational residual and SAH variance.
Use raw fitted residuals with squared inverse propensities. With both arms nonempty this
has the stated equivalent arm-count form; the printed weighted residual instead produces
fourth powers. Under independent assignment, symmetric self-containing neighborhoods and
zero covariance outside them, the variance of the residual contrast mean is bounded by
the stated conditional second moments, exactly the expectation of the raw SAH estimator.
In the T3 design its N-scaled limit is 1/2, compared with actual variance limit 1/4, and its
N=32 expectation is exactly 493725989/38038425600, above 18239/1505280. General fitted-IPW
intervals use the residuals of the corrected linearization as specified in T2. -/
def T4WholeStatement : Prop := T4Statement ∧ T4WitnessStatement

/-! Parameterized binary area fields for all three T5 cases. -/

def w1AreaBin (c : EuclideanSpace ℝ (Fin 2)) (j : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  if j = 0 then Metric.closedBall c 1 else {x | (j : ℝ) < dist x c ∧ dist x c ≤ (j : ℝ)+1}

def w1AreaPopulation (q : Fin 6 → Bool → ℝ) : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) :=
  { areaBinaryPopulation with outcome := fun x z =>
      (∑ i : Fin 2, ∑ j : Fin 6, if x ∈ w1AreaBin (areaBinaryCenter i) j.val then
        (if angularFraction (areaBinaryCenter i) x < q j (z i) then 1 else 0) else 0) }

def w1AreaShares (c : Fin 3) (j : Fin 6) (a : Bool) : ℝ :=
  if a then if c = 0 then 283/3000 else if c = 1 then
    (if j = 0 then 1/50 else 273/2500) else
    (![90,91,94,95,97,99] : Fin 6 → ℝ) j / 1000
  else 1/10

def w1AreaCase (c : Fin 3) : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) :=
  w1AreaPopulation (w1AreaShares c)

def w1AreaCaseEffect (c : Fin 3) : ℝ := (![(-17/3000),121/18000,(-7/1800)] : Fin 3 → ℝ) c

/-- The geometry, existence, and all-assignment integral interpretation for a six-bin field. -/
def W1AreaGeometry (q : Fin 6 → Bool → ℝ) : Prop :=
  let P := w1AreaPopulation q
  (∀ x z, P.outcome x z = 0 ∨ P.outcome x z = 1) ∧
  (∀ z, Measurable (fun x => P.outcome x z)) ∧
  (∀ i (j : Fin 6) x z, x ∈ region P i j →
    P.outcome x z = if angularFraction (areaBinaryCenter i) x < q j (z i) then 1 else 0) ∧
  (∀ x z, (∀ i : Fin 2, x ∉ region P i 6) → P.outcome x z = 0) ∧
  (∀ j : Fin 6, WellDefined P j) ∧ WellDefined P 6 ∧
  (∀ i (j : Fin 6), region P i j = w1AreaBin (areaBinaryCenter i) j.val) ∧
  (∀ i, region P i 6 = ⋃ j : Fin 6, region P i j) ∧
  (∀ i, Pairwise (fun j k : Fin 6 => Disjoint (region P i j) (region P i k))) ∧
  (∀ i (j : Fin 6), P.zeta (region P i j) = ENNReal.ofReal (Real.pi*(2*(j : ℝ)+1))) ∧
  (∀ i, P.zeta (region P i 6) = ENNReal.ofReal (36*Real.pi))

def W1AreaMeans (q : Fin 6 → Bool → ℝ) : Prop :=
  let P := w1AreaPopulation q
 (∀ (j : Fin 6) i z, circleAverage P j i z = q j (z i)) ∧
  (∀ i z, circleAverage P 6 i z = ∑ j : Fin 6, (2*(j : ℝ)+1)/36*q j (z i))


def W1AreaRealization (q : Fin 6 → Bool → ℝ) : Prop := W1AreaGeometry q ∧ W1AreaMeans q

/-- Finite statistical consequences for the three actual area fields. -/
def T5CaseStatement : Prop :=
  armCount areaWitnessAssignment true = 1 ∧ armCount areaWitnessAssignment false = 1 ∧
  (∀ c : Fin 3, ∀ j : Fin 6, ∀ a : Bool, 0 ≤ w1AreaShares c j a ∧ w1AreaShares c j a ≤ 1) ∧
  (∀ c : Fin 3, W1AreaRealization (w1AreaShares c)) ∧
  (∀ (c : Fin 3) (j : Fin 6),
    hajek (circleAverage (w1AreaCase c) j) areaWitnessAssignment = w1AreaShares c j true-1/10 ∧
    ame (fun _ => 1/2) (circleAverage (w1AreaCase c) j) = w1AreaShares c j true-1/10) ∧
  (∀ c : Fin 3,
    (∑ j : Fin 6, hajek (circleAverage (w1AreaCase c) j) areaWitnessAssignment) = -17/500 ∧
    (∑ j : Fin 6, ame (fun _ => 1/2) (circleAverage (w1AreaCase c) j)) = -17/500 ∧
    hajek (circleAverage (w1AreaCase c) 6) areaWitnessAssignment = w1AreaCaseEffect c ∧
    ame (fun _ => 1/2) (circleAverage (w1AreaCase c) 6) = w1AreaCaseEffect c ∧
    (-17/500 : ℝ) ≠ w1AreaCaseEffect c) ∧
  (0 : ℝ) < w1AreaCaseEffect 1 ∧
  (∀ j : Fin 6, (-17/500 : ℝ) < w1AreaShares 2 j true-1/10)

def w1RefinedBand (j : Fin 11) : Set ℝ :=
  if j = 0 then {0} else Set.Ioc (((j : ℝ)-1)/2) ((j : ℝ)/2)

def w1RefinedArea (j : Fin 11) : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) :=
  w1WithBand (w1AreaCase 0) (w1RefinedBand j)

/-- Grid dependence uses exactly the same Case A outcome field and the same union. -/
def T5RefinementStatement : Prop :=
  (∀ j : Fin 11, WellDefined (w1RefinedArea j) 0) ∧
  (∀ i : Fin 2, region (w1AreaCase 0) i 6 = ⋃ j : Fin 11, region (w1RefinedArea j) i 0) ∧
  (∀ i : Fin 2, Pairwise (fun j k : Fin 11 =>
    Disjoint (region (w1RefinedArea j) i 0) (region (w1RefinedArea k) i 0))) ∧
  (∀ (j : Fin 11) i z, circleAverage (w1RefinedArea j) 0 i z = w1AreaShares 0 0 (z i)) ∧
  (∀ j : Fin 11, hajek (circleAverage (w1RefinedArea j) 0) areaWitnessAssignment = -17/3000 ∧
    ame (fun _ => 1/2) (circleAverage (w1RefinedArea j) 0) = -17/3000) ∧
  (∑ j : Fin 11, hajek (circleAverage (w1RefinedArea j) 0) areaWitnessAssignment) = -187/3000 ∧
  (∑ j : Fin 11, ame (fun _ => 1/2) (circleAverage (w1RefinedArea j) 0)) = -187/3000 ∧
  ame (fun _ => 1/2) (circleAverage (w1AreaCase 0) 6) = -17/3000

/-- P004-T5; pp. 763-764 (PDF pp. 20-21), interpretation of the sum of point Hajek estimates;
eqs. (2), (8)-(9), (16).
These examples refute the reading that an unweighted sum of point Hajek contrasts over a
partition equals the change in the normalized deforested area share of the union. Three
specified binary area fields on the two radius-one disk nodes realize Cases A, B and C.
All six bin areas, positive finite averages, all-assignment
shares and whole-region weighted averages have the stated values. At assignment (1,0),
each bin Hajek contrast is its AME and each six-bin sum is -17/500; the actual whole-region
contrasts and AMEs are -17/3000, 121/18000 and -7/1800. Case B reverses the sign and Case C's
sum is below every bin effect. Refining the same Case A field into eleven bins changes the
sum to -187/3000 while preserving its whole-region effect -17/3000.
No corrected empirical area effect is asserted for the application. -/
def T5WholeStatement : Prop := T5CaseStatement ∧ T5RefinementStatement

end
end SAP.P004a
