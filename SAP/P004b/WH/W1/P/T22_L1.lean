import SAP.P004b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W1.P.T22_L1

open SAP.P004b
open scoped BigOperators Matrix Classical
noncomputable section
set_option maxHeartbeats 1000000

def p3 : Fin 3 → ℝ := fun _ => 1/2

def O3 : Fin 3 → Fin 1 → ℝ := fun _ _ => 1

def B3 : Fin 3 → Finset (Fin 3) := fun _ => Finset.univ

theorem assignment_three_univ : (Finset.univ : Finset (Assignment 3)) =
    {![false,false,false], ![false,false,true], ![false,true,false],
     ![false,true,true], ![true,false,false], ![true,false,true],
     ![true,true,false], ![true,true,true]} := by
  decide

end
end SAP.P004b.WH.W1.P.T22_L1

open SAP.P004b.WH.W1.P.T22_L1
open SAP.P004b.WH.W1
open SAP.P004b
set_option maxHeartbeats 1000000

theorem SAP.P004b.WH.W1.T22_L1_proof : SAP.P004b.WH.W1.T22_L1 := by
  change IsUnit (projectionInformation p3 O3).det ∧
    (∀ a, projectionBeta p3 threeNodeVarianceTable O3 a = 0) ∧
    (∀ i a, projectionFits p3 threeNodeVarianceTable O3 i a = 0) ∧
    (∀ z, projectionLinearIPW p3 threeNodeVarianceTable O3 z =
      (2/3 : ℝ)*((2*bit (z 0)-1)+(2*bit (z 1)-1))*(bit (z 2)-1/2)) ∧
    variance p3 (projectionLinearIPW p3 threeNodeVarianceTable O3) = 2/9 ∧
    armSecondMoment p3 threeNodeVarianceTable (projectionFits p3 threeNodeVarianceTable O3) true +
      armSecondMoment p3 threeNodeVarianceTable (projectionFits p3 threeNodeVarianceTable O3) false = 2/9 ∧
    diagonalEffectSquare p3 threeNodeVarianceTable (projectionFits p3 threeNodeVarianceTable O3) = 0 ∧
    signedPairSecondMoment p3 threeNodeVarianceTable B3 (projectionFits p3 threeNodeVarianceTable O3) = 0 ∧
    signedPairMeanProduct p3 threeNodeVarianceTable B3 (projectionFits p3 threeNodeVarianceTable O3) = 0 ∧
    literalPairSecondMoment p3 threeNodeVarianceTable B3 (projectionFits p3 threeNodeVarianceTable O3) = 2/9 ∧
    literalPairMeanProduct p3 threeNodeVarianceTable B3 (projectionFits p3 threeNodeVarianceTable O3) = 0 ∧
    literalVariance p3 threeNodeVarianceTable B3 (projectionFits p3 threeNodeVarianceTable O3) = 4/9 ∧
    fiveTermVariance p3 threeNodeVarianceTable B3 (projectionFits p3 threeNodeVarianceTable O3) = 2/9
  have hp : ∀ i : Fin 3, 0 < p3 i ∧ p3 i < 1 := by
    intro i
    norm_num [p3]
  have hm : ∀ i : Fin 3, ∀ a : Bool,
      marginal p3 threeNodeVarianceTable i a = 0 := by
    intro i a
    fin_cases i <;> cases a <;>
      norm_num [marginal, expect, designWeight, coin, p3, threeNodeVarianceTable, bit,
        assignment_three_univ, Fin.sum_univ_succ]
  have hi : IsUnit (projectionInformation p3 O3).det := by
    norm_num [projectionInformation, p3, O3, Fin.sum_univ_succ, Matrix.det_fin_one]
  have hb : ∀ a : Bool, projectionBeta p3 threeNodeVarianceTable O3 a = 0 := by
    intro a
    funext j
    fin_cases j
    simp [projectionBeta, projectionInformation, p3, O3, hm, Fin.sum_univ_succ]
  have hg : ∀ i : Fin 3, ∀ a : Bool,
      projectionFits p3 threeNodeVarianceTable O3 i a = 0 := by
    intro i a
    simp [projectionFits, covariateFits, hb, Fin.sum_univ_succ]
  have hgf : projectionFits p3 threeNodeVarianceTable O3 = fun _ _ => 0 := by
    funext i a
    exact hg i a
  have hlin : ∀ z : Assignment 3,
      projectionLinearIPW p3 threeNodeVarianceTable O3 z =
        (2/3 : ℝ)*((2*bit (z 0)-1)+(2*bit (z 1)-1))*(bit (z 2)-1/2) := by
    intro z
    cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;>
      norm_num [projectionLinearIPW, residualContrast, p3, threeNodeVarianceTable,
        bit, hg, h0, h1, h2, Fin.sum_univ_succ]
  refine ⟨hi, hb, hg, hlin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : projectionLinearIPW p3 threeNodeVarianceTable O3 =
        fun z : Assignment 3 =>
          (2/3 : ℝ)*((2*bit (z 0)-1)+(2*bit (z 1)-1))*(bit (z 2)-1/2) := by
      funext z
      exact hlin z
    rw [heq]
    norm_num [variance, cov, expect, designWeight, coin, p3, bit,
      assignment_three_univ, Fin.sum_univ_succ]
  · rw [hgf]
    norm_num [armSecondMoment, marginal, expect, designWeight, coin, p3,
      threeNodeVarianceTable, bit, assignment_three_univ, Fin.sum_univ_succ]
  · rw [hgf]
    simp [diagonalEffectSquare, residualEffect, nodeEffect, hm]
  · rw [hgf]
    norm_num [signedPairSecondMoment, pairMarginal, expect, designWeight, coin,
      p3, threeNodeVarianceTable, bit, armSign, B3,
      assignment_three_univ, Fin.sum_univ_succ]
  · rw [hgf]
    norm_num [signedPairMeanProduct, hm, armSign, B3, Fin.sum_univ_succ]
  · rw [hgf]
    norm_num [literalPairSecondMoment, pairMarginal, expect, designWeight, coin,
      p3, threeNodeVarianceTable, bit, B3, assignment_three_univ,
      Fin.sum_univ_succ]
  · rw [hgf]
    norm_num [literalPairMeanProduct, hm, armSign, B3, Fin.sum_univ_succ]
  · rw [hgf]
    norm_num [literalVariance, marginal, pairMarginal, expect, designWeight,
      coin, p3, threeNodeVarianceTable, bit, residualEffect, nodeEffect, hm,
      armSign, B3, assignment_three_univ, Fin.sum_univ_succ]
  · rw [hgf]
    have ha : armSecondMoment p3 threeNodeVarianceTable (fun _ _ => 0) true +
        armSecondMoment p3 threeNodeVarianceTable (fun _ _ => 0) false = 2/9 := by
      norm_num [armSecondMoment, marginal, expect, designWeight, coin, p3,
        threeNodeVarianceTable, bit, assignment_three_univ, Fin.sum_univ_succ]
    have hd : diagonalEffectSquare p3 threeNodeVarianceTable (fun _ _ => 0) = 0 := by
      simp [diagonalEffectSquare, residualEffect, nodeEffect, hm]
    have hp : signedPairSecondMoment p3 threeNodeVarianceTable B3 (fun _ _ => 0) = 0 := by
      norm_num [signedPairSecondMoment, pairMarginal, expect, designWeight,
        coin, p3, threeNodeVarianceTable, bit, armSign, B3,
        assignment_three_univ, Fin.sum_univ_succ]
    have hmprod : signedPairMeanProduct p3 threeNodeVarianceTable B3 (fun _ _ => 0) = 0 := by
      norm_num [signedPairMeanProduct, hm, armSign, B3, Fin.sum_univ_succ]
    simp [fiveTermVariance, ha, hd, hp, hmprod]
