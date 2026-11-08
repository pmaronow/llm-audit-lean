import SAP.P003b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1
open SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

lemma rankZero (K : ℕ) (o v : Counts) (samples : Fin K → Counts) :
    rankValue (fun _ _ => 0) o v samples = 1 := by
  simp [rankValue]
  field_simp
  ring

lemma t35Support : Possible ⟨0,1,0,1⟩ w1T35Population ∧
    w1LiteralVisited ⟨0,1,0,1⟩ = [⟨0,1,0,1⟩,⟨0,0,0,2⟩,⟨0,0,1,1⟩] ∧
    w1LiteralVisited ⟨1,0,1,0⟩ = [⟨1,1,0,0⟩,⟨0,1,1,0⟩,⟨1,0,1,0⟩] ∧
    w1T35Population ∉ w1LiteralVisited ⟨0,1,0,1⟩ := by
  decide +kernel

lemma t35Observations (z : Assignment 2 1) :
    canonicalObserved w1T35Population z.val = ⟨0,1,0,1⟩ ∨
    canonicalObserved w1T35Population z.val = ⟨1,0,1,0⟩ := by
  fin_cases z <;> decide +kernel

lemma t35ObservationProbability : uniformProb (fun z : Assignment 2 1 =>
    canonicalObserved w1T35Population z.val = ⟨1,0,1,0⟩) = 1/2 := by
  have hN : Fintype.card (Assignment 2 1) = 2 := by decide +kernel
  have hE : (Finset.univ.filter (fun z : Assignment 2 1 =>
      canonicalObserved w1T35Population z.val = ⟨1,0,1,0⟩)).card = 1 := by
    decide +kernel
  have hh := congrArg (fun k : ℕ => (k : ℝ)/(Fintype.card (Assignment 2 1) : ℝ)) hE
  rw [hN] at hh
  unfold uniformProb
  rw [hN]
  convert hh using 2
  · congr 2
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  · norm_num

end
end SAP.P003b.WH.W1
