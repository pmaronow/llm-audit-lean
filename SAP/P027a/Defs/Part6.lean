import Mathlib
import SAP.P027a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

def AEAggregationPreservation : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω]
      (n : G → ℕ) (hn : ∀ g, 0 < n g)
      (D : Design (Σ g, Fin (n g)) Ω), Valid D → Positive D →
      (∀ (g : G) (i j : Fin (n g)),
        expect D (fun ω =>
          if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then 0 else 1) = 0) →
      ∀ (y : (Σ g, Fin (n g)) → ℝ),
      let Dc : Design G Ω :=
        { weight := D.weight
          selected := fun ω g => D.selected ω ⟨g,⟨0, hn g⟩⟩ }
      Positive Dc ∧
      (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi Dc g) ∧
      (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
        joint D ⟨g,i⟩ ⟨h,j⟩ = joint Dc g h) ∧
      (∀ ω : Ω, 0 < D.weight ω →
        htTotal D y ω = htTotal Dc (groupTotal n y) ω ∧
        htVarianceEstimator D y ω =
          htVarianceEstimator Dc (groupTotal n y) ω) ∧
      variance D (htTotal D y) =
        variance Dc (htTotal Dc (groupTotal n y)) ∧
      biasA D y = biasA Dc (groupTotal n y)

def AggregationClaim : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (D : Design G Ω),
  Valid D → Positive D → ∀ (n : G → ℕ), (∀ g, 0 < n g) →
  ∀ (y : (Σ g, Fin (n g)) → ℝ),
((∀ ω, htTotal (liftDesign D n) y ω = htTotal D (groupTotal n y) ω) ∧
    variance (liftDesign D n) (htTotal (liftDesign D n) y) =
      variance D (htTotal D (groupTotal n y)) ∧
    (∀ ω, htVarianceEstimator (liftDesign D n) y ω =
      htVarianceEstimator D (groupTotal n y) ω) ∧
    biasA (liftDesign D n) y = biasA D (groupTotal n y)) ∧
  (quadraticA (liftDesign D n) y =
      (∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then
        (n h : ℝ)*groupSquares n y g+(n g : ℝ)*groupSquares n y h else 0)/2) ∧
  (let Y := groupTotal n y
    let S := groupSquares n y
    let Δ := (expect (liftDesign D n) (c2Estimator (liftDesign D n) y) -
      variance (liftDesign D n) (htTotal (liftDesign D n) y)) -
      (expect D (c2Estimator D Y) - variance D (htTotal D Y))
    Δ = (∑ g, ∑ h', if g ≠ h' ∧ joint D g h' = 0 then
      (n h' : ℝ)*S g + (n g : ℝ)*S h' - Y g^2 - Y h'^2 else 0)/2 ∧
    ((∀ g h', g ≠ h' ∧ joint D g h' = 0 → n g = n h') → 0 ≤ Δ) ∧
    (∀ v : ℝ, (∀ k, y k = v) →
      Δ = -v^2 * (∑ g, ∑ h', if g ≠ h' ∧ joint D g h' = 0 then
        ((n g : ℝ) - n h')^2 else 0)/2) ∧
    0 ≤ expect D (c2Estimator D Y) - variance D (htTotal D Y) ∧
    0 ≤ expect (liftDesign D n) (c2Estimator (liftDesign D n) y) -
      variance (liftDesign D n) (htTotal (liftDesign D n) y)) ∧
  ((∑ g, (zeroNeighborSize D n g-(zeroNeighborCount D g:ℝ)*(n g:ℝ))*groupSquares n y g) ≤
      (expect (liftDesign D n) (c2Estimator (liftDesign D n) y)-
        variance (liftDesign D n) (htTotal (liftDesign D n) y)) -
      (expect D (c2Estimator D (groupTotal n y))-
        variance D (htTotal D (groupTotal n y))))

def ConstantAggregationStrict : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (D : Design G Ω),
  Valid D → Positive D → ∀ (n : G → ℕ), (∀ g, 0 < n g) →
  ∀ (v : ℝ), v ≠ 0 → (∃ g h, g ≠ h ∧ joint D g h = 0 ∧ n g ≠ n h) →
expect (liftDesign D n) (c2Estimator (liftDesign D n) (fun _ => v))-
      variance (liftDesign D n) (htTotal (liftDesign D n) (fun _ => v)) <
    expect D (c2Estimator D (groupTotal n (fun _ => v)))-
      variance D (htTotal D (groupTotal n (fun _ => v)))

def AggregationSquaredBias : Prop :=
  
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (D : Design G Ω),
  Valid D → Positive D → ∀ (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ),
  (expect (liftDesign D n) (c2Estimator (liftDesign D n) y)-
    variance (liftDesign D n) (htTotal (liftDesign D n) y) = squaredZeroPairs (liftDesign D n) y) ∧
  (expect D (c2Estimator D (groupTotal n y))-
    variance D (htTotal D (groupTotal n y)) = squaredZeroPairs D (groupTotal n y))

def T4Statement : Prop :=
  AEAggregationPreservation ∧ AggregationClaim ∧ ConstantAggregationStrict ∧ AggregationSquaredBias

def TableBoundViolation : Prop :=
  ∀ (row : Fin 4) (V G : ℝ),
  |V-a3LowTrue row| ≤ 0.005 → |G-a3LowC2 row| ≤ 0.005 →
0 < V ∧ ¬ G ≤ (1+5*(a3LowQ row-2)/(3*a3LowQ row))*V

def Row21Witness : Prop :=
  let D := phaseOriginal 2 30 (by norm_num)
    let Dc := phaseGrouped 2 (by norm_num)
    let Y := groupTotal (fun _ : Fin 2 × Fin 2 => 30) row21Fibre
    (∑ k, row21Fibre k) = 0 ∧ (∑ g, Y g^2) = 57600 ∧
    (∑ k, row21Fibre k^2) = 37880 ∧
    variance D (htTotal D row21Fibre) = 414720 ∧
    expect D (htVarianceEstimator D row21Fibre) = 357120 ∧
    expect D (c2Estimator D row21Fibre) = 3766320 ∧
    expect Dc (c2Estimator Dc Y) = 529920

def Row21MeanValues : Prop :=
  
  let D := phaseOriginal 2 30 (by norm_num)
  let Dc := phaseGrouped 2 (by norm_num)
  let Y := groupTotal (fun _ : Fin 2 × Fin 2 => 30) row21Fibre
  let V := variance D (htTotal D row21Fibre)
  V/14400 = 144/5 ∧ expect D (htVarianceEstimator D row21Fibre)/14400 = 124/5 ∧
  expect D (c2Estimator D row21Fibre)/14400 = 5231/20 ∧
  expect Dc (c2Estimator Dc Y)/14400 = 184/5 ∧
  (expect D (c2Estimator D row21Fibre)-V)/V = 4655/576 ∧
  (expect Dc (c2Estimator Dc Y)-V)/V = 5/18

def T5Statement : Prop :=
  TableBoundViolation ∧ Row21Witness ∧ Row21MeanValues
end
end SAP.P027a
