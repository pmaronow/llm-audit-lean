import SAP.P061a.Defs.Part11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- The fixed four-unit sampling/treatment witness, with both supports and all EPOs. -/
def T9Statement : Prop :=
  ∃ D D' : AtomicDesign (Fin 4 → Fin 3),
    (∀ z, D.mass z = if samplingSupport 2 z then 1/12 else 0) ∧
    (∀ z, D'.mass z = if samplingSupport 3 z then 1/12 else 0) ∧
    (∀ z, supported D z ↔ samplingSupport 2 z) ∧
    (∀ z, supported D' z ↔ samplingSupport 3 z) ∧
    (∀ i, exposureProbability D (fun i z => (z i).val) i 2 = 1/4 ∧
      exposureProbability D (fun i z => (z i).val) i 1 = 1/4 ∧
      exposureProbability D' (fun i z => (z i).val) i 2 = 1/4 ∧
      exposureProbability D' (fun i z => (z i).val) i 1 = 1/2) ∧
    (∀ i, 0 < exposureProbability D (fun i z => (z i).val) i 2 ∧
      0 < exposureProbability D (fun i z => (z i).val) i 1 ∧
      0 < exposureProbability D' (fun i z => (z i).val) i 2 ∧
      0 < exposureProbability D' (fun i z => (z i).val) i 1) ∧
    supportStability D (fun i z => (z i).val) samplingResponse ∧
    supportStability D' (fun i z => (z i).val) samplingResponse ∧
    (∀ i, exposureMean D (fun i z => (z i).val) samplingResponse i 2 = 2 ∧
      exposureMean D (fun i z => (z i).val) samplingResponse i 1 = 0 ∧
      exposureMean D' (fun i z => (z i).val) samplingResponse i 2 = 3 ∧
      exposureMean D' (fun i z => (z i).val) samplingResponse i 1 = 0) ∧
    populationContrast D (fun i z => (z i).val) samplingResponse 2 1 = 2 ∧
    populationContrast D' (fun i z => (z i).val) samplingResponse 2 1 = 3 ∧
    ¬globalStability (fun i z => (z i).val) samplingResponse


end SAP.P061a
