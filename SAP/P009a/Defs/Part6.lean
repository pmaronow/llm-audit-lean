import SAP.P009a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- Mathematical content retained for target P009-T13. -/
def T13Statement : Prop :=
  ProductDesign cancellingPopulation ∧ Regularity cancellingPopulation 2 4 1 ∧
    Affects cancellingPopulation 0 1 ∧
    expectedSpillover cancellingPopulation 1 0 false = 0 ∧
    expectedSpillover cancellingPopulation 1 0 true = 0 ∧
    weightedSpillover cancellingPopulation 1 0 = 0

/-- Mathematical content retained for target P009-T14. -/
def T14Statement : Prop :=
  (∀ {n : ℕ} (E : FiniteExperiment n) (i j : Fin n)
    (hij : i ≠ j) (hI : ¬ Affects E i j),
    (∀ a z, E.outcome j (Function.update (Function.update z j a) i true) =
      E.outcome j (Function.update (Function.update z j a) i false)) ∧
    expectedSpillover E j i false = 0 ∧ expectedSpillover E j i true = 0 ∧ weightedSpillover E j i = 0) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (h : NoSpillovers E)
    (hp : ∀ i, 0 < armProbability E i true ∧ 0 < armProbability E i false),
    (∀ i j, i ≠ j → expectedSpillover E i j false = 0 ∧ expectedSpillover E i j true = 0) ∧ directBias E = 0) ∧
  (Affects cancellingPopulation 0 1 ∧ weightedSpillover cancellingPopulation 1 0 = 0) ∧
  (∀ {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) (hij : i ≠ j),
    weightedSpillover E j i ≠ 0 → Affects E i j)

/-- Mathematical content retained for target P009-T15. -/
def T15Statement : Prop :=
  SequenceRegularity identitySequence 2 4 1 ∧ MaximalOrders identitySequence ⊤ ⊤ ∧
    (∀ t, ProductDesign (identitySequence.experiment t) ∧ NoSpillovers (identitySequence.experiment t) ∧
      averageDependence (identitySequence.experiment t) = 1) ∧ SparseDependence identitySequence ∧
    vanishingRelativeTo (fun t => externalMixing (identitySequence.experiment t) 1) (sampleSize identitySequence) ∧
    vanishingRelativeTo (fun t => internalMixing (identitySequence.experiment t) 1) (sampleSize identitySequence) ∧
    (∀ t, let E := identitySequence.experiment t
      4*(∑ i, ∑ j, covariance E.design (fun z => treatmentValue (z i)) (fun z => treatmentValue (z j))) = sampleSize identitySequence t ∧
      4*(∑ i, ∑ j, if j = i then 0 else mixingCoefficient E.design (fun z => z i) (fun z => z j)) = 0 ∧
      0 < sampleSize identitySequence t)

/-- Mathematical content retained for target P009-T16. -/
def T16Statement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n)
    (E : FiniteExperiment n) (b : Bool) (k : ℝ) (hk : 0 < k),
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, covariance E.design
      (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)) ≤
      k^2/(n:ℝ)^2 * (∑ i, ∑ j, mixingCoefficient E.design (fun z => z i) (fun z => z j)) ∧
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, mixingCoefficient E.design (fun z => z i) (fun z => z j)) ≤
      k^2*averageDependence E/(n:ℝ) + k^2/(n:ℝ)^2 *
        (∑ i, ∑ j, (1-dependenceIndicator E i j)*mixingCoefficient E.design (fun z => z i) (fun z => z j))

/-- Mathematical content retained for target P009-T17. -/
def T17Statement : Prop :=
  ∃ E : FiniteExperiment 4,
    (∀ z, E.design.mass z =
      if (∑ i, if z i then (1:ℕ) else 0) = 2 then 1/6 else 0) ∧
    (∀ i z, E.outcome i z = treatmentValue (z i) + if i = 0 then treatmentValue (z 1) else 0) ∧
    (∀ j, Affects E j 0 ↔ j = 0 ∨ j = 1) ∧
    FixedSizeDesign E 2 ∧ Regularity E 2 4 1 ∧ incomingCount E 0 = 2 ∧
    probability E.design (fun z => treatedIncomingCount E 0 z = 0) = 1/2 ∧
    conditionalMean E.design (fun z => z 0 = true)
      (fun z => if treatedIncomingCount E 0 z = 0 then 1 else 0) = 2/3 ∧
    printedHypergeomMass 4 2 2 0 = 1/6 ∧ printedHypergeomMass 3 1 2 0 = 1/3 ∧
    (1/2:ℝ) ≠ 1/6 ∧ (2/3:ℝ)/(1/2) ≠ (1/3)/(1/6)

end
end SAP.P009a
