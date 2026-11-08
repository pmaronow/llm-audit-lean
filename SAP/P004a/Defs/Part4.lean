import SAP.P004a.Defs.Part3

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

def T9Statement : Prop :=
  LogisticConditions (fun N (_ : Fin N) (_ : Fin 1) => 1)
      (fun _ => 0) {θ : Fin 1 → ℝ | 0 ≤ θ 0 ∧ θ 0 ≤ 1}
      (fun _ z _ => boundaryMLE z) ∧
    (∀ N : ℕ, 0 < N → prob (fun _ : Fin N => 1/2)
      (fun z => 1 < Real.sqrt N * |boundaryMLE z - 4*(armCount z true/N-1/2)|) ≥ 3/32) ∧
    ¬ LittleOp (fun _ _ => 1/2) (fun N z => boundaryMLE z-4*(armCount z true/N-1/2))
      (fun N => (Real.sqrt N)⁻¹)


def T10Statement : Prop :=
  ∀ {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ)
    (hlog : LogisticConditions O θ₀ Θ θhat)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀)),
    let p := fun N => propensities (O N) θ₀
    InProb p (fun N z => ‖θhat N z - θ₀‖) ∧
    BigOp p (fun N z => ‖θhat N z - θ₀‖) (fun N => (Real.sqrt N)⁻¹) ∧
    (θ₀ ∈ interior Θ →
      BigOp p (fun N z => ‖θhat N z-θ₀-(information (p N) (O N))⁻¹ *ᵥ logisticScore (p N) (O N) z‖)
        (fun N => (N : ℝ)⁻¹) ∧
      LittleOp p (fun N z => ‖θhat N z-θ₀-(information (p N) (O N))⁻¹ *ᵥ logisticScore (p N) (O N) z‖)
        (fun N => (Real.sqrt N)⁻¹))


def T11Statement : Prop :=
  (∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N),
    0 < N → (∀ i, 0 < p i ∧ p i < 1) →
    expect p (ht p R) = ame p R ∧
    expect p (printedObsHT p R) =
      (∑ i, (marginal p R i true-(1-p i)/p i*marginal p R i false)) / N ∧
    (expect p (printedObsHT p R) = ame p R ↔
      (∑ i, (1-2*p i)/p i*marginal p R i false) / N = 0)) ∧
    (∀ N : ℕ, 0 < N →
      ame (fun _ : Fin N => 1/4) (fun _ _ => 1) = 0 ∧
      expect (fun _ : Fin N => 1/4) (printedObsHT (fun _ => 1/4) (fun _ _ => 1)) = -2 ∧
      expect (fun _ : Fin N => 1/4) (ht (fun _ => 1/4) (fun _ _ => 1)) = 0)


def T12Statement : Prop :=
  (SharpNull eightNodeNullPopulation ∧ WellDefined eightNodeNullPopulation 0 ∧
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) eightNodeObserved = -255/512 ∧
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) eightNodeResampled = -1/512 ∧
    mcDrawWeight (fun _ => 1/2) eightNodeMCDraws = (256 : ℝ)^(-101 : ℤ) ∧
    0 < mcDrawWeight (fun _ => 1/2) eightNodeMCDraws ∧
    ((Finset.univ.filter (fun r : Fin 101 => r ≠ 0 ∧
      ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws 0) ≤
        |ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws r)|)).card : ℝ)/100 = 1 ∧
    mcExceedances (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0)) eightNodeMCDraws = 0 ∧
    mcPlusPvalue (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0)) eightNodeMCDraws = 1/101) ∧
  (SharpNull eightNodeNullPopulation ∧ WellDefined eightNodeNullPopulation 0 ∧
    (∑ draws : Fin 101 → Assignment 8, mcDrawWeight (fun _ => 1/2) draws *
      (if (mcExceedances (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0)) draws : ℝ)/100 ≤ 1/20
        then 1 else 0)) = eightNodeMCSize ∧ eightNodeMCSize > 1/20)


def T13Statement : Prop :=
  (∀ {N P : ℕ}
    (w : Assignment N → ℝ) (T : Assignment N → ℝ)
    (hwn : ∀ z, 0 ≤ w z) (hw : (∑ z, w z) = 1)
    (hP : 0 < P) (α : ℝ) (hα : 0 < α ∧ α < 1),
    (∑ draws : Fin (P + 1) → Assignment N,
      (∏ r, w (draws r)) *
        (if mcPlusPvalue T draws ≤ α then (1 : ℝ) else 0)) ≤ α ∧
    (∑ draws : Fin (P + 1) → Assignment N,
      (∏ r, w (draws r)) *
        (if (mcExceedances T draws : ℝ) / (P : ℝ) ≤ α then (1 : ℝ) else 0)) ≤
      ((Int.floor (α * (P : ℝ)) : ℝ) + 1) / ((P : ℝ) + 1) ∧
    ((Int.floor (α * (P : ℝ)) : ℝ) + 1) / ((P : ℝ) + 1) ≤
      α + (1 - α) / ((P : ℝ) + 1)) ∧
  (∀ {N P : ℕ} (T : Assignment N → ℝ) (draws : Fin (P+1) → Assignment N), 0 < P →
    mcPlusPvalue T draws - (mcExceedances T draws : ℝ)/P =
      (1-(mcExceedances T draws : ℝ)/P)/(P+1) ∧
    0 ≤ mcPlusPvalue T draws - (mcExceedances T draws : ℝ)/P ∧
    mcPlusPvalue T draws - (mcExceedances T draws : ℝ)/P ≤ 1/(P+1)) ∧
    (((Int.floor ((1/20 : ℝ)*100) : ℝ)+1)/(100+1) > (1/20 : ℝ))


def T14Statement : Prop :=
  WellDefined (shellSpatialPopulation {4}) 0 ∧
    WellDefined (shellSpatialPopulation {5}) 0 ∧
    WellDefined (shellSpatialPopulation (Set.Icc 4 5)) 0 ∧
    WellDefined (shellSpatialPopulation (Set.Icc 0 5)) 0 ∧
    (∀ x z, |(shellSpatialPopulation {4}).outcome x z| < 3) ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) = 0 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) = 0 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0) = 1/6 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 0 5)) 0) = 1/6 ∧
    (∀ w4 w5 : ℝ,
      w4*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) +
      w5*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) ≠
        ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0))


def T15GeneralStatement : Prop :=
  ∀ {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (p : Fin N → ℝ) (d : ℝ)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1) (hWD : WellDefined P d),
    (∀ i, nodeEffect p (circleAverage P d) i =
      (∫ x in region P i d, pointEffect P p i x ∂P.zeta) / (P.zeta (region P i d)).toReal) ∧
    ame p (circleAverage P d) = (∑ i,
      (∫ x in region P i d, pointEffect P p i x ∂P.zeta) / (P.zeta (region P i d)).toReal) / N


def T15DiscreteStatement : Prop :=
  ∀ {A : Type*} [Fintype A] {m N : ℕ}
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
    (∀ w : Fin m → ℝ, (∀ k, 0 < w k) →
      (∀ i k, supportedShellMass (a i) shell i k / (∑ x, a i x) = w k) →
      (∑ i, finiteAverage (a i) (δ i)) / (N : ℝ) =
        ∑ k, w k * ((∑ i, (∑ x, if shell i x = k then a i x * δ i x else 0) /
          supportedShellMass (a i) shell i k) / (N : ℝ)))


def T15Statement : Prop :=
  T15GeneralStatement.{u} ∧ T15DiscreteStatement.{v} ∧
  (∀ (center : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b),
    (ENNReal.ofReal (1 / (Real.pi * (b^2-a^2)))) •
      Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => dist x center)
        (volume.restrict {x | a ≤ dist x center ∧ dist x center ≤ b}) =
      volume.withDensity (fun r : ℝ => ENNReal.ofReal
        (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)))

end
end SAP.P004a
