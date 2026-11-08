import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T15_L2

open SAP.P003a
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

lemma row1 (x : ℚ) :
    wholeEstimatorMass ⟨0,4,0,0⟩ 2 x = wholeTwoPointMass 1 1 x := by
  have hc : Nat.choose 4 2 = 6 := by decide
  have h42 : Nat.fast_choose 4 2 = 6 := by decide
  have h00 : Nat.fast_choose 0 0 = 1 := by decide
  have hs : randomStates ⟨0,4,0,0⟩ 2 = [⟨0,2,0,0⟩] := by decide
  by_cases h : x = 1
  · subst x
    norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
      observed, multiplicity, binomial, estimateQ, Counts.total, hc, h42, h00]
  · norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
      observed, multiplicity, binomial, estimateQ, Counts.total, hc, h42, h00, h, eq_comm]

lemma row2 (x : ℚ) :
    wholeEstimatorMass ⟨1,3,0,0⟩ 2 x = wholeTwoPointMass (1/2) 1 x := by
  have hc : Nat.choose 4 2 = 6 := by decide
  have h10 : Nat.fast_choose 1 0 = 1 := by decide
  have h11 : Nat.fast_choose 1 1 = 1 := by decide
  have h30 : Nat.fast_choose 3 0 = 1 := by decide
  have h31 : Nat.fast_choose 3 1 = 3 := by decide
  have h32 : Nat.fast_choose 3 2 = 3 := by decide
  have h00 : Nat.fast_choose 0 0 = 1 := by decide
  have hs : randomStates ⟨1,3,0,0⟩ 2 = [⟨0,2,0,0⟩,⟨1,1,0,0⟩] := by decide
  by_cases h₁ : x = 1/2
  · subst x
    norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
      observed, multiplicity, binomial, estimateQ, Counts.total,
      hc, h10, h11, h30, h31, h32, h00]
  · by_cases h₂ : x = 1
    · subst x
      norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
        observed, multiplicity, binomial, estimateQ, Counts.total,
        hc, h10, h11, h30, h31, h32, h00, h₁, eq_comm]
    · norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
        observed, multiplicity, binomial, estimateQ, Counts.total,
        hc, h10, h11, h30, h31, h32, h00, h₁, h₂, eq_comm]

lemma row3 (x : ℚ) :
    wholeEstimatorMass ⟨1,2,1,0⟩ 2 x = wholeTwoPointMass 0 (1/2) x := by
  have hc : Nat.choose 4 2 = 6 := by decide
  have h10 : Nat.fast_choose 1 0 = 1 := by decide
  have h11 : Nat.fast_choose 1 1 = 1 := by decide
  have h20 : Nat.fast_choose 2 0 = 1 := by decide
  have h21 : Nat.fast_choose 2 1 = 2 := by decide
  have h22 : Nat.fast_choose 2 2 = 1 := by decide
  have h00 : Nat.fast_choose 0 0 = 1 := by decide
  have hs : randomStates ⟨1,2,1,0⟩ 2 =
      [⟨0,1,1,0⟩,⟨0,2,0,0⟩,⟨1,0,1,0⟩,⟨1,1,0,0⟩] := by decide
  by_cases h₁ : x = 0
  · subst x
    norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
      observed, multiplicity, binomial, estimateQ, Counts.total,
      hc, h10, h11, h20, h21, h22, h00]
  · by_cases h₂ : x = 1/2
    · subst x
      norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
        observed, multiplicity, binomial, estimateQ, Counts.total,
        hc, h10, h11, h20, h21, h22, h00, h₁, eq_comm]
    · norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
        observed, multiplicity, binomial, estimateQ, Counts.total,
        hc, h10, h11, h20, h21, h22, h00, h₁, h₂, eq_comm]

lemma row4 (x : ℚ) :
    wholeEstimatorMass ⟨0,3,0,1⟩ 2 x = wholeTwoPointMass (1/2) 1 x := by
  have hc : Nat.choose 4 2 = 6 := by decide
  have h30 : Nat.fast_choose 3 0 = 1 := by decide
  have h31 : Nat.fast_choose 3 1 = 3 := by decide
  have h32 : Nat.fast_choose 3 2 = 3 := by decide
  have h10 : Nat.fast_choose 1 0 = 1 := by decide
  have h11 : Nat.fast_choose 1 1 = 1 := by decide
  have h00 : Nat.fast_choose 0 0 = 1 := by decide
  have h01 : Nat.fast_choose 0 1 = 0 := by decide
  have hs : randomStates ⟨0,3,0,1⟩ 2 = [⟨0,1,0,1⟩,⟨0,2,0,0⟩] := by decide
  by_cases h₁ : x = 1/2
  · subst x
    norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
      observed, multiplicity, binomial, estimateQ, Counts.total,
      hc, h30, h31, h32, h10, h11, h00, h01]
  · by_cases h₂ : x = 1
    · subst x
      norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
        observed, multiplicity, binomial, estimateQ, Counts.total,
        hc, h30, h31, h32, h10, h11, h00, h01, h₁, eq_comm]
    · norm_num [wholeEstimatorMass, wholeTwoPointMass, designProb, hs,
        observed, multiplicity, binomial, estimateQ, Counts.total,
        hc, h30, h31, h32, h10, h11, h00, h01, h₁, h₂, eq_comm]

end SAP.P003a.WH.W3.P.T15_L2

attribute [local instance 0] Classical.propDecidable

theorem SAP.P003a.WH.W3.T15_L2_proof : SAP.P003a.WH.W3.T15_L2 := by
  intro r hr x
  simp only [SAP.P003a.wholeWitnessRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact SAP.P003a.WH.W3.P.T15_L2.row1 x
  · exact SAP.P003a.WH.W3.P.T15_L2.row2 x
  · exact SAP.P003a.WH.W3.P.T15_L2.row3 x
  · exact SAP.P003a.WH.W3.P.T15_L2.row4 x
