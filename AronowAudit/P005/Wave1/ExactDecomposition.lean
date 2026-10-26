import AronowAudit.P005.Wave1.ExactDecompositionBlueprint
import AronowAudit.P005.Wave1.ExactDecomposition.N1
import AronowAudit.P005.Wave1.ExactDecomposition.N2
import AronowAudit.P005.Wave1.ExactDecomposition.N3
import AronowAudit.P005.Wave1.ExactDecomposition.N4
import AronowAudit.P005.Wave1.ExactDecomposition.N5
import AronowAudit.P005.Wave1.ExactDecomposition.N6
import AronowAudit.P005.Wave1.ExactDecomposition.N7

set_option autoImplicit false

namespace AronowAudit.P005.Wave1

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-- P005-T24: the finite-sample exact decomposition in Theorem 4.1.
This result is separate from the sign-identity and asymptotic-expansion counterexamples. -/
theorem interacted_exact_decomposition_completion :
    ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
      interactedRegular P m →
      (∀ S ∈ design n m,
        armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT +
            armNu3 P S P.yT ∧
        armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
          armNu2 P (control S) P.yC + armNu3 P (control S) P.yC) ∧
      expectation m (fun S => interactedATE P S - ate P) =
        expectation m (fun S => dot (xMean P (control S))
          (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
        expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT +
          armNu3 P S P.yT)) ∧
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT ∧
      expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
        (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
      expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) -
        expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
        (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC -
          ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT :=
  ExactDecomposition.assemble ExactDecomposition.n1_proof ExactDecomposition.n2_proof
    ExactDecomposition.n3_proof ExactDecomposition.n4_proof ExactDecomposition.n5_proof
    ExactDecomposition.n6_proof ExactDecomposition.n7_proof

end

end AronowAudit.P005.Wave1
