import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T15_L1

open SAP.P003a
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

private theorem row₁ (x : ℚ) :
    wholeEstimatorMass ⟨1,1,0,0⟩ 1 x = wholeTwoPointMass 0 1 x := by
  have hs : randomStates ⟨1,1,0,0⟩ 1 = [⟨0,1,0,0⟩,⟨1,0,0,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h0 : x = 0
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · by_cases h1 : x = 1
    · subst x
      norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total]
    · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total, h0, h1, eq_comm]

private theorem row₂ (x : ℚ) :
    wholeEstimatorMass ⟨0,1,0,1⟩ 1 x = wholeTwoPointMass 0 1 x := by
  have hs : randomStates ⟨0,1,0,1⟩ 1 = [⟨0,0,0,1⟩,⟨0,1,0,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h0 : x = 0
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · by_cases h1 : x = 1
    · subst x
      norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total]
    · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total, h0, h1, eq_comm]

private theorem row₃ (x : ℚ) :
    wholeEstimatorMass ⟨1,0,1,0⟩ 1 x = wholeTwoPointMass (-1) 0 x := by
  have hs : randomStates ⟨1,0,1,0⟩ 1 = [⟨0,0,1,0⟩,⟨1,0,0,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h0 : x = -1
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · by_cases h1 : x = 0
    · subst x
      norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total]
    · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total, h0, h1, eq_comm]

private theorem row₄ (x : ℚ) :
    wholeEstimatorMass ⟨0,0,1,1⟩ 1 x = wholeTwoPointMass (-1) 0 x := by
  have hs : randomStates ⟨0,0,1,1⟩ 1 = [⟨0,0,0,1⟩,⟨0,0,1,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h0 : x = -1
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · by_cases h1 : x = 0
    · subst x
      norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total]
    · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
        binomial, Nat.fast_choose, Counts.total, h0, h1, eq_comm]

private theorem row₅ (x : ℚ) :
    wholeEstimatorMass ⟨0,2,0,0⟩ 1 x = wholeTwoPointMass 1 1 x := by
  have hs : randomStates ⟨0,2,0,0⟩ 1 = [⟨0,1,0,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h : x = 1
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total, h, eq_comm]

private theorem row₆ (x : ℚ) :
    wholeEstimatorMass ⟨0,0,2,0⟩ 1 x = wholeTwoPointMass (-1) (-1) x := by
  have hs : randomStates ⟨0,0,2,0⟩ 1 = [⟨0,0,1,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h : x = -1
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total, h, eq_comm]

private theorem row₇ (x : ℚ) :
    wholeEstimatorMass ⟨0,1,1,0⟩ 1 x = wholeTwoPointMass 0 0 x := by
  have hs : randomStates ⟨0,1,1,0⟩ 1 = [⟨0,0,1,0⟩,⟨0,1,0,0⟩] := by decide
  rw [wholeEstimatorMass, designProb, hs]
  by_cases h : x = 0
  · subst x
    norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total]
  · norm_num [wholeTwoPointMass, observed, estimateQ, multiplicity,
      binomial, Nat.fast_choose, Counts.total, h, eq_comm]

end SAP.P003a.WH.W3.P.T15_L1

theorem SAP.P003a.WH.W3.T15_L1_proof : SAP.P003a.WH.W3.T15_L1 := by
  intro r hr x
  simp [wholeBaseRows] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SAP.P003a.WH.W3.P.T15_L1.row₁ x
  · exact SAP.P003a.WH.W3.P.T15_L1.row₂ x
  · exact SAP.P003a.WH.W3.P.T15_L1.row₃ x
  · exact SAP.P003a.WH.W3.P.T15_L1.row₄ x
  · exact SAP.P003a.WH.W3.P.T15_L1.row₅ x
  · exact SAP.P003a.WH.W3.P.T15_L1.row₆ x
  · exact SAP.P003a.WH.W3.P.T15_L1.row₇ x
