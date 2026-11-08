import SAP.P044.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.Bridge

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

@[simp] theorem marginal_fun_lift {Ω K : Type*} {N : ℕ} [Fintype Ω] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → SAP.P044.Exposure) :
    SAP.P044.marginal p (fun ω i => labels (f ω i)) =
      fun i a => SAP.P044.marginal p f i (labels.symm a) := by
  funext i a; exact marginal_lift p f i a

@[simp] theorem joint_fun_lift {Ω K : Type*} {N : ℕ} [Fintype Ω] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → SAP.P044.Exposure) :
    SAP.P044.joint p (fun ω i => labels (f ω i)) =
      fun i j a b => SAP.P044.joint p f i j (labels.symm a) (labels.symm b) := by
  funext i j a b; exact joint_lift p f i j a b

@[simp] theorem weight_fun_lift {K : Type*} [Field K] {R N : ℕ}
    (f : Fin R → Fin N → SAP.P044.Exposure) :
    (SAP.P044.smoothedWeight (fun r i => labels (f r i)) : Fin N → AronowAudit.P044.Exposure → K) =
      fun i a => SAP.P044.smoothedWeight f i (labels.symm a) := by
  funext i a; exact weight_lift f i a

@[simp] theorem joints_fun_lift {K : Type*} [Field K] {R N : ℕ}
    (f : Fin R → Fin N → SAP.P044.Exposure) :
    (SAP.P044.smoothedJoint (fun r i => labels (f r i)) :
      Fin N → Fin N → AronowAudit.P044.Exposure → AronowAudit.P044.Exposure → K) =
      fun i j a b => SAP.P044.smoothedJoint f i j (labels.symm a) (labels.symm b) := by
  funext i j a b; exact joints_lift f i j a b

@[simp] theorem mapped_pair_functions {I J : Type*} (f g : I → J → SAP.P044.Exposure) :
    (fun i j => labels (f i j)) = (fun i j => labels (g i j)) ↔ f = g := by
  constructor
  · intro h; funext i j; exact labels.injective (congrFun (congrFun h i) j)
  · intro h; rw [h]

/-- This is Mathlib's cardinality identity for fibers of a finite function. -/
theorem exposure_count_partition {R N : ℕ} {D : Type*} [Fintype D] [DecidableEq D]
    (f : Fin R → Fin N → D) (i : Fin N) : ∑ a, SAP.P044.exposureCount f i a = R := by
  simpa [SAP.P044.exposureCount] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin R))
      (Finset.univ : Finset D) (fun r => f r i))

end
end SAP.P044.Bridge
