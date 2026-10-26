import AronowAudit.P009.P009_CommonCompletion

namespace AronowAudit.P009.PaperDomains
open scoped BigOperators Topology
open Filter
noncomputable section

/-- Full T26 component on the actual growing common-assignment study: all finite
coefficients, the order-n normalized limit, and failure of Assumption 5. -/
theorem common_assignment_mixing (S : Study) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hNo : ∀ t, NoInterference (S.experiment t))
    (hCommon : ∀ t z, (S.experiment t).design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0) :
    (∀ t,
      (∀ i j, i ≠ j → alpha (S.experiment t).design
        (masked (S.experiment t) i) (masked (S.experiment t) j) = p*(1-p)) ∧
      (∀ θ : ℝ, alphaExt (S.experiment t) θ =
        (size S t-1)*Real.rpow (p*(1-p)) θ) ∧
      alphaExt (S.experiment t) 1 = (size S t-1)*p*(1-p)) ∧
    Tendsto (fun t => alphaExt (S.experiment t) 1/size S t)
      atTop (nhds (p*(1-p))) ∧
    ¬ LittleO (fun t => alphaExt (S.experiment t) 1) (size S) := by
  have hseq := CommonCompletion.common_assignment_mixing_sequence S p hp hNo hCommon
  refine ⟨?_,hseq.1,hseq.2⟩
  intro t
  have h := CommonCompletion.common_assignment_mixing_completed
    (S.positive t) (S.experiment t) p 0 hp (hNo t) (hCommon t)
  exact ⟨h.1,fun θ => (CommonCompletion.common_assignment_mixing_completed
    (S.positive t) (S.experiment t) p θ hp (hNo t) (hCommon t)).2.1,h.2.2⟩

end
end AronowAudit.P009.PaperDomains
