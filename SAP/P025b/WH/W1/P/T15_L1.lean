import SAP.P025b.WH.W1.Leaves
import AronowAudit.P037.P037_FiniteDesign

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1.P.T15_L1

open scoped BigOperators

noncomputable section

private def bernoulliLaw (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    AronowAudit.P037.FiniteDesign Bool where
  weight b := if b then q else 1 - q
  nonneg := by
    intro b
    cases b <;> simp_all
  total := by
    simp

private theorem bernoulli_true_mean (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    AronowAudit.P037.designMean (bernoulliLaw q hq) (fun b => if b then 1 else 0) = q := by
  simp [AronowAudit.P037.designMean, bernoulliLaw]

end
end SAP.P025b.WH.W1.P.T15_L1

open SAP.P025b.WH.W1.P.T15_L1

theorem SAP.P025b.WH.W1.T15_L1_proof : SAP.P025b.WH.W1.T15_L1 := by
  intro ι instF instD p hp
  classical
  let law : ∀ i : ι, AronowAudit.P037.FiniteDesign Bool := fun i => bernoulliLaw (p i) (hp i)
  let joint := AronowAudit.P037.productDesign law
  let d : SAP.P025b.FiniteDesign ι (ι → Bool) := {
    sample := fun ω => Finset.univ.filter (fun i => ω i = true)
    probability := fun ω => joint.weight ω
    nonnegative := fun ω => joint.nonneg ω
    total := joint.total }
  refine ⟨d, ?_, ?_, ?_⟩
  · intro ω
    rfl
  · intro ω
    simp [d, joint, law, AronowAudit.P037.productDesign, bernoulliLaw]
  · intro i
    unfold SAP.P025b.inclusion SAP.P025b.designExpectation
    simp only [d, Finset.mem_filter, Finset.mem_univ, true_and]
    change AronowAudit.P037.designMean joint (fun ω => if ω i then 1 else 0) = p i
    rw [AronowAudit.P037.product_design_coordinate_mean law i (fun b => if b then 1 else 0)]
    exact bernoulli_true_mean (p i) (hp i)

