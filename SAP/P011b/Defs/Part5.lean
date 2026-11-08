import SAP.P011b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

def starCore : Prop :=
  Scaling (starFamily false) 1 3 (27/128) 2 ∧ Valid (starFamily false) ∧
  (∀ k, Homoskedastic ((starFamily false).model k) ∧
    (∀ᵐ y ∂((starFamily false).model k).law, ∀ i, y i=0 ∨ y i=1) ∧
    (∀ i, expectation ((starFamily false).model k) (fun y => y i) =
      (![3/4,1/4,1/4,1/4] : Fin 4 → ℝ) (localIndex (by decide) i)) ∧
    (∀ i j, covariance ((starFamily false).model k) i j =
      ((3/16 : ℝ) • (1 : Matrix (Fin ((starFamily false).size k))
        (Fin ((starFamily false).size k)) ℝ) + (1/64 : ℝ) • adjacency ((starFamily false).model k).G) i j)) ∧
  (∀ k, beta ((starFamily false).model k) = 3/8 ∧ scaledTrue (starFamily false) k = 27/128 ∧
    meanBias ((starFamily false).model k) = -3/128 ∧
    (∀ A, Compatible ((starFamily false).model k).R ((starFamily false).model k).d A
      ↔ A = ((starFamily false).model k).G) ∧
    expectation ((starFamily false).model k) (scaledOracle (starFamily false) k) =
      3*(64*((k+1 : ℕ) : ℝ)-47)/(1024*((k+1 : ℕ) : ℝ))) ∧
  InProbability (starFamily false) (scaledOracle (starFamily false)) (fun _ => 3/16) ∧
  Tendsto (fun k => probability ((starFamily false).model k)
    {y | 27/128 - scaledOracle (starFamily false) k y > 3/256}) atTop (𝓝 1) ∧
  (∀ α : ℝ, 0 < α → α < 1 →
    Tendsto (fun k => coverage ((starFamily false).model k)
      (fun y => V1 ((starFamily false).model k).G (weighted ((starFamily false).model k) y)) α)
      atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1)) ∧
    2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1 < 1-α) ∧
  Scaling (starFamily true) 1 3 (47/192) 2 ∧ Valid (starFamily true) ∧
  (∀ k, beta ((starFamily true).model k) = 1/2 ∧ scaledTrue (starFamily true) k = 47/192) ∧
  InProbability (starFamily true) (scaledOracle (starFamily true)) (fun _ => 53/192) ∧
  (∀ upper : Bool,
    InProbability (starFamily upper)
      (fun k y => quadratic (oracleMatrix ((starFamily upper).model k).G)
        (fun i => y i - (if upper then (![1/2,3/4,1/4,1/2] : Fin 4 → ℝ)
          (localIndex (by decide) i) else (![3/4,1/4,1/4,1/4] : Fin 4 → ℝ)
          (localIndex (by decide) i))) / ((starFamily upper).size k : ℝ))
      (fun _ => if upper then 47/192 else 27/128))

/-- The same two-column designs and saturated real edge constraints as the
counterexample; no spectral or asymptotic premise is introduced here. -/
def starRegression : Prop :=
  ∀ upper : Bool, ∀ K : ℕ, 0 < K →
    let D : Matrix (Fin (4*K)) (Fin 2) ℝ := fun i j => if j=0 then 1 else
      (if upper then (![0,1,-1,0] : Fin 4 → ℝ) else ![3,-1,-1,-1]) (localIndex (by decide) i)
    MeanModel (starModel upper K) D (if upper then ![1/2,1/4] else ![3/8,1/8]) ∧
    (∀ y, ols D y 0 = average y)

def starRelaxation : Prop :=
  ∀ upper : Bool, ∀ k : ℕ, ∀ a : Edge (4*(k+1)) → ℝ,
    RelaxedFeasible (starModel upper (k+1)).R (starModel upper (k+1)).d a ↔
      a=fun e => adjacency (starModel upper (k+1)).G e.val.1 e.val.2

def starExtraFacts : Prop :=
  (∀ upper : Bool, ∀ k : ℕ,
    ∀ᵐ y ∂(starModel upper (k+1)).law, ∀ i, y i=0 ∨ y i=1) ∧
  (∀ upper : Bool, ∀ k : ℕ, ∀ A : Graph (4*(k+1)),
    Compatible (starModel upper (k+1)).R (starModel upper (k+1)).d A ↔
      A=(starModel upper (k+1)).G)

def T15Statement : Prop :=
  starCore ∧ starRegression ∧ starRelaxation ∧ starExtraFacts ∧
  quadratic (oracleMatrix starGraph) (![3/8,-1/8,-1/8,-1/8] : Fin 4 → ℝ) = -3/32 ∧
  quadratic (oracleMatrix starGraph) (![0,1/4,-1/4,0] : Fin 4 → ℝ) = 1/8 ∧
  (3/16 : ℝ)/(27/128) = 8/9

end
end SAP.P011b
