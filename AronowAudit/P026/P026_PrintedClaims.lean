import AronowAudit.P026.P026_FiniteDesign
/- Printed assertions preserved solely as propositions; checked refutations are in P026_Refutations. -/
namespace AronowAudit.P026.PrintedClaims
open Finset
noncomputable section
def printed_cluster_claims {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I] (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hd : ∀ i j, i ≠ j → 0 < disagreement D i j)
    (N : ℕ) (hN : 0 < N) (x z : I → ℝ)  : Prop :=
crossSupport D ∧
    expectation D (printedCovariance D x z) ≤ covariance D (htTotal D true x) (htTotal D false z) ∧
    variance D (ht D N x z) ≤ expectation D (printedVariance D N x z) ∧
    ((∀ i, x i=z i) → expectation D (printedCovariance D x z) =
      covariance D (htTotal D true x) (htTotal D false z)) ∧
    ((∀ i, x i=z i) → (∀ i j, i ≠ j → 0 < joint D true true i j ∧ 0 < joint D false false i j) →
      expectation D (printedVariance D N x z) = variance D (ht D N x z))

def printed_pairwise_fitting {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I] {Θ : Type*} (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (i : I) (J : Finset I) (x z : I → ℝ)
    (G : (↥J → ℝ) → Θ) (P : Θ → ℝ)
    (h : ∀ j ∈ J, independent D (fun w => D.treatment w i) (fun w => D.treatment w j))  : Prop :=
independent D (fun w => D.treatment w i) (fun w => G (fittingOutcomes D J x z w)) ∧
    independent D (fun w => D.treatment w i) (fun w => P (G (fittingOutcomes D J x z w))) ∧
    covariance D (fun w => indicator D true w i) (fun w => P (G (fittingOutcomes D J x z w)))=0

def printed_table_columns  : Prop :=
(∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
    rounded3 (expectation tableDesign feEstimate) (-12/1000) ∧
    rounded3 (variance tableDesign feEstimate) (36/1000) ∧
    roundedSD3 (variance tableDesign feEstimate) (191/1000) ∧
    roundedSD3 (variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2) (191/1000) ∧
    roundedSD3 (variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)) (162/1000) ∧
    rounded3 (variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)) (26/1000) ∧
    rounded3 (expectation tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)) (26/1000) ∧
    roundedSD3 (variance tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)) (7/1000) ∧
    |Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual))-170/1000| ≤ 1/2000 ∧
    |variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)-29/1000| ≤ 1/2000 ∧
    |expectation realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)-29/1000| ≤ 1/2000 ∧
    |Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual))-7/1000| ≤ 1/2000

def printed_sharp_null_footnote {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I] (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hd : ∀ i j, i ≠ j → 0 < disagreement D i j)
    (N : ℕ) (hN : 0 < N) (x : I → ℝ) (G : (I → ℝ) → (I → ℝ))
    (hs : ∀ i j, i ≠ j → 0 < joint D true true i j ∧ 0 < joint D false false i j)  : Prop :=
expectation D (printedVariance D N (fun i => x i-G x i) (fun i => x i-G x i))=
      variance D (generalized D N x x (fun w => G (observed D x x w)))

end
end AronowAudit.P026.PrintedClaims
