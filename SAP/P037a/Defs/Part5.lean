import SAP.P037a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

def stratifiedSeedMoments : Prop :=
  ∀ {H : ℕ} (N n : Fin H → ℕ)
      (refs : (h : Fin H) → Finset (Fin (N h)))
      (hN : ∀ h, 0<N h) (hn : ∀ h, n h≤N h) (ht : 0<∑ h, n h),
    let K := fun h => (refs h).card
      let μ := seedCompositionMean N K n
      let mass := (∏ h, (Nat.choose (N h) (n h):ℝ))⁻¹
      (∑ z : SeedAssignment N n, mass)=1 ∧
      (∑ z : SeedAssignment N n, mass*seedComposition N n refs z)=μ ∧
      (∑ z : SeedAssignment N n, mass*(seedComposition N n refs z-μ)^2)=
        (∑ h, if N h=1 then 0 else
          (n h:ℝ)*((K h:ℝ)/N h)*(1-(K h:ℝ)/N h)*
            (((N h:ℝ)-n h)/((N h:ℝ)-1)))/(∑ h, (n h:ℝ))^2

def equalFractionMean : Prop :=
  ∀ {H : ℕ} (N K n : Fin H → ℕ)
      (f : ℝ) (hN : ∀ h, N h≠0) (hn : (∑ h, (n h:ℝ))≠0)
      (hfraction : ∀ h, (n h:ℝ)=f*(N h:ℝ)),
    seedCompositionMean N K n=eligibleShare N K

def unequalFractionExample : Prop :=
  eligibleShare ![13,14,14,14] ![2,1,0,0]=3/55 ∧
      seedCompositionMean ![13,14,14,14] ![2,1,0,0] ![7,7,7,7]=41/728 ∧
      (41/728:ℝ)-3/55=71/40040 ∧ (41/728:ℝ)≠3/55

def responseIdentification : Prop :=
  ∀ {Ω K : Type}
      [Fintype Ω] [Fintype K] {B : ℕ}
      (d : Design Ω) (X : K → Ω → (Fin B × Fin 4) → ℝ)
      (alpha : Fin B → ℝ) (theta : K → ℝ)
      (err Y : Ω → (Fin B × Fin 4) → ℝ)
      (hY : ∀ w i, Y w i = alpha i.1 + (∑ k, theta k*X k w i) + err w i)
      (he : ∀ k, mean d (fun w => centeredBlockCross (X k w) (err w)) = 0),
    NormalEquations d X Y theta ∧
      (Function.Injective (fun v : K → ℝ => fun k =>
        ∑ l, v l * mean d (fun w => centeredBlockCross (X k w) (X l w))) →
        ∀ v, NormalEquations d X Y v → v=theta)

def compositionDecomposition : Prop :=
  ∀ (a t b D C μ : ℝ),
    a+D*t+b*D*C = a+D*(t+b*μ)+b*(D*(C-μ))

def compositionOrthogonality : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {B : ℕ}
      (d : Design Ω) (D : Ω → (Fin B × Fin 4) → Bool)
      (R : Ω → (Fin B × Fin 4) → ℝ) (hR : CompositionRandomized d D R)
      (V : ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ),
    mean d (fun w => centeredBlockCross (R w) (V (D w))) = 0

def centeredIdentification : Prop :=
  ∀ {Ω K : Type} [Fintype Ω] [Fintype K]
      {B : ℕ} (d : Design Ω) (D : Ω → (Fin B × Fin 4) → Bool)
      (C : Ω → (Fin B × Fin 4) → ℝ) (μ a t : (Fin B × Fin 4) → ℝ)
      (W : K → ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ)
      (b beta : ℝ) (delta : K → ℝ)
      (hR : CompositionRandomized d D (fun w i => (if D w i then (1:ℝ) else 0)*(C w i-μ i)))
      (hN : ExtendedNormalEquations d (fun k w => W k (D w))
        (fun w i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))
        (fun w i => a i+(if D w i then (1:ℝ) else 0)*t i+
          b*(if D w i then (1:ℝ) else 0)*C w i) delta beta)
      (hv : 0 < mean d (fun w => centeredBlockCross
        (fun i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))
        (fun i => (if D w i then (1:ℝ) else 0)*(C w i-μ i)))),
    beta=b

def augmentationEquivalence : Prop :=
  ∀ {Ω K : Type}
      [Fintype Ω] [Fintype K] [DecidableEq K] {B : ℕ}
      (d : Design Ω) (W : K → Ω → (Fin B × Fin 4) → ℝ)
      (R Z Y : Ω → (Fin B × Fin 4) → ℝ) (e : K)
      (hZ : ∀ w i, Z w i=R w i+W e w i)
      (delta : K → ℝ) (beta : ℝ),
    ExtendedNormalEquations d W Z Y delta beta ↔
      ExtendedNormalEquations d W R Y
        (fun k => delta k + if k=e then beta else 0) beta

def eligibleCentering : Prop :=
  ∀ (D C μ q : ℝ),
    D*(C-q)=D*(C-μ)+D*(μ-q) ∧
      (μ=q → D*(C-μ)=D*(C-q) ∧ D*μ=D*q)

def compositionRegressionComparisons : Prop :=
  compositionMean (fun w => centeredCross (innovation w) (innovation w)) = 1/160 ∧
      (∀ theta, CompositionEquations expandedColumns observedOutcome theta ↔
        theta = ![0,0,0,-1]) ∧
      (∀ theta, CompositionEquations centeredColumns observedOutcome theta ↔
        theta = ![-1/5,-1/2,0]) ∧
      (∀ theta, CompositionEquations regressionColumns
        (fun w i => observedOutcome w i+(1/5)*compositionColumn w i) theta ↔
        theta = ![-3/31,-15/62,-49/155]) ∧
      (∀ theta, CompositionEquations centeredColumns
        (fun w i => observedOutcome w i+(1/5)*compositionColumn w i) theta ↔
        theta = ![-4/25,-2/5,1/5]) ∧
      (∀ theta, CompositionEquations expandedColumns
        (fun w i => observedOutcome w i+(1/5)*compositionColumn w i) theta ↔
        theta = ![0,0,1/5,-1]) ∧
      (∀ theta, CompositionEquations regressionColumns
        (fun w i => 3/10-(1/5)*treatment w.1 i-(1/2)*eligibleFraction i+
          (1/5)*compositionColumn w i) theta ↔ theta = ![-1/5,-1/2,1/5])

def uncenteredOrthogonality : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {B : ℕ} (d : Design Ω)
    (D : Ω → (Fin B × Fin 4) → Bool) (R : Ω → (Fin B × Fin 4) → ℝ),
    CompositionRandomized d D R →
    ∀ V : ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ,
      mean d (fun w => ∑ i, V (D w) i * R w i) = 0

def centeredSlopeMoment : Prop :=
  ∀ {Ω K : Type} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : Design Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (R : Ω → (Fin B × Fin 4) → ℝ), CompositionRandomized d D R →
    ∀ (A : ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ)
      (W : K → ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ)
      (b beta : ℝ) (delta : K → ℝ),
    ExtendedNormalEquations d (fun k w => W k (D w)) R
      (fun w i => A (D w) i + b*R w i) delta beta →
    beta * mean d (fun w => centeredBlockCross (R w) (R w)) =
      b * mean d (fun w => centeredBlockCross (R w) (R w))

def augmentedSlopeIdentification : Prop :=
  ∀ {Ω K : Type} [Fintype Ω] [Fintype K] [DecidableEq K] {B : ℕ}
    (d : Design Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (C : Ω → (Fin B × Fin 4) → ℝ) (μ a t : (Fin B × Fin 4) → ℝ)
    (W : K → ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ) (e : K)
    (b beta : ℝ) (delta : K → ℝ),
    (∀ w i, W e (D w) i = (if D w i then (1:ℝ) else 0)*μ i) →
    CompositionRandomized d D (fun w i => (if D w i then (1:ℝ) else 0)*(C w i-μ i)) →
    ExtendedNormalEquations d (fun k w => W k (D w))
      (fun w i => (if D w i then (1:ℝ) else 0)*C w i)
      (fun w i => a i+(if D w i then (1:ℝ) else 0)*t i+
        b*(if D w i then (1:ℝ) else 0)*C w i) delta beta →
    0 < mean d (fun w => centeredBlockCross
      (fun i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))
      (fun i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))) → beta=b

def T2Statement : Prop :=
  stratifiedSeedMoments ∧ equalFractionMean ∧ unequalFractionExample ∧
  responseIdentification ∧ compositionDecomposition ∧ compositionOrthogonality ∧
  centeredIdentification ∧ augmentationEquivalence ∧ eligibleCentering ∧
  compositionRegressionComparisons ∧ uncenteredOrthogonality ∧ centeredSlopeMoment ∧
  augmentedSlopeIdentification

end SAP.P037a
