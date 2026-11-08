import SAP.P061a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

def PairInferenceFacts (D : ∀ m, AtomicDesign (Fin (m^8) → BitPair)) (m : ℕ) : Prop :=
    ((∀ z, supported (D m) z) ∧
    (∀ i, exposureProbability (D m) (pairedOwnBit (m^8)) i 1 = 1/2 ∧
      exposureProbability (D m) (pairedOwnBit (m^8)) i 0 = 1/2) ∧
    (∀ i z, 1 ≤ pairResponses m i z ∧ pairResponses m i z ≤ 3/2) ∧
    (∀ i, independent (D m) (pairedOwnBit (m^8) i)
      (fun z => fun k : {k : Fin (m^8) // k ≠ (finProdFinEquiv.symm i).1} => z k.val)) ∧
    (∀ k : Fin (m^8), designCovariance (D m) (fun z => ownBit 0 (z k))
      (fun z => ownBit 1 (z k)) = 1/(4*m : ℝ)) ∧
    pairDirectContrast m (D m) = 0 ∧
    (∀ i, exposureMean (D m) (pairedOwnBit (m^8)) (pairResponses m) i 1 =
      1+(1/(m : ℝ))*((1+1/(m : ℝ))/2) ∧
      exposureMean (D m) (pairedOwnBit (m^8)) (pairResponses m) i 0 =
      1+(1/(m : ℝ))*((1-1/(m : ℝ))/2)) ∧
    populationContrast (D m) (pairedOwnBit (m^8)) (pairResponses m) 1 0 = 1/(m : ℝ)^2 ∧
    mean (D m) (pairEstimator m (D m)) = 1/(m : ℝ)^2 ∧
    designVariance (D m) (pairEstimator m (D m)) = variancePolynomial m/(4*(m : ℝ)^8) ∧
    8 ≤ variancePolynomial m ∧ variancePolynomial m < 20 ∧
    (1/(m : ℝ)^2/pairStandardError m (D m))^2 = 4*(m : ℝ)^4/variancePolynomial m ∧
    (m : ℝ)^4/5 ≤ (1/(m : ℝ)^2/pairStandardError m (D m))^2 ∧
    24/25 ≤ eventProbability (D m) (fun z =>
      |pairEstimator m (D m) z - 1/(m : ℝ)^2| ≤ 5*pairStandardError m (D m)) ∧
    (5 ≤ m → eventProbability (D m) (fun z => |pairEstimator m (D m) z| ≤ 5*pairStandardError m (D m)) ≤
      4*designVariance (D m) (pairEstimator m (D m))/(1/(m : ℝ)^2)^2 ∧
      4*designVariance (D m) (pairEstimator m (D m))/(1/(m : ℝ)^2)^2 = variancePolynomial m/(m : ℝ)^4 ∧
      variancePolynomial m/(m : ℝ)^4 ≤ 20/(m : ℝ)^4)) ∧
    0 < pairStandardError m (D m)

/-- Exact finite and limiting coverage counterexample under independent correlated pairs. -/
def T4Statement : Prop :=
  ∃ D : ∀ m, AtomicDesign (Fin (m^8) → BitPair),
    (∀ m z, (D m).mass z = ∏ k : Fin (m^8),
      if (z k).1 = (z k).2 then (1+pairParameter m)/4 else (1-pairParameter m)/4) ∧
    (∀ m, 2 ≤ m → PairInferenceFacts D m) ∧
    (Tendsto (fun (index : ℕ) => populationContrast (D (index+2)) (pairedOwnBit ((index+2)^8)) (pairResponses (index+2)) 1 0 -
      pairDirectContrast (index+2) (D (index+2))) atTop (𝓝 0) ∧
    Tendsto (fun (index : ℕ) => ((index+2)^8*2 : ℝ)*designVariance (D (index+2)) (pairEstimator (index+2) (D (index+2)))) atTop (𝓝 4) ∧
    Tendsto (fun (index : ℕ) => ((populationContrast (D (index+2)) (pairedOwnBit ((index+2)^8)) (pairResponses (index+2)) 1 0 -
      pairDirectContrast (index+2) (D (index+2)))/pairStandardError (index+2) (D (index+2)))^2) atTop atTop ∧
    Tendsto (fun (index : ℕ) => eventProbability (D (index+2))
      (fun z => |pairEstimator (index+2) (D (index+2)) z - pairDirectContrast (index+2) (D (index+2))| ≤ 5*pairStandardError (index+2) (D (index+2)))) atTop (𝓝 0))


end SAP.P061a
