import Mathlib
import SAP.P018a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-- The packaged mathematical content of P018-T14. -/
def T14Statement : Prop :=
    (∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (s : E → Finset V), (∀ d, (s d).card = 2) → Function.Injective s →
    ∀ {k : ℕ} (X : E → Vec k) (Y : E → ℝ) (β : Vec k),
    (∀ d, Y d = 0 ∨ Y d = 1) → (logisticBread X β).det ≠ 0 →
    let r := fun d => Y d - expit (dot (X d) β)
    let q := fun d => logisticScore (X d) (Y d) β
    (∀ d f, outer (q d) (q f) = (r d * r f) • outer (X d) (X f)) ∧
    meat s q = (∑ i, outer (unitScore s q i) (unitScore s q i)) - dyadMeat q ∧
    (meat s q).transpose = meat s q ∧
    (logisticVariance s X Y β).transpose = logisticVariance s X Y β ∧
    printedLogisticMeat s X r = ∑ d,
      (r d * ∑ f, if (s d ∩ s f).Nonempty then r f else 0) • outer (X d) (X d)) ∧
    printedLogisticMeat sixMembers logitX logitR ≠
      meat sixMembers (fun d => score (logitX d) (logitR d))

end SAP.P018a
