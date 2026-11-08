import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P003a.WH.W1.P.T21_L1

open SAP.P003a

def observedCounts : Counts := ⟨1, 6, 0, 2⟩

def pValues (d : ℤ) : Finset ℚ :=
  (((possibleTables observedCounts).filter (fun v => v.effect = d)).map
    (fun v => pValue v observedCounts)).toFinset

lemma max_neg_six : (pValues (-6)).max = (1 / 36 : ℚ) := by decide +kernel
lemma max_neg_five : (pValues (-5)).max = (1 / 12 : ℚ) := by decide +kernel
lemma max_neg_four : (pValues (-4)).max = (1 / 6 : ℚ) := by decide +kernel
lemma max_neg_three : (pValues (-3)).max = (4 / 9 : ℚ) := by decide +kernel
lemma max_neg_two : (pValues (-2)).max = (1 / 2 : ℚ) := by decide +kernel
lemma max_neg_one : (pValues (-1)).max = (29 / 36 : ℚ) := by decide +kernel
lemma max_zero : (pValues 0).max = (1 : ℚ) := by decide +kernel
lemma max_one : (pValues 1).max = (1 : ℚ) := by decide +kernel
lemma max_two : (pValues 2).max = (2 / 3 : ℚ) := by decide +kernel
lemma max_three : (pValues 3).max = (1 / 12 : ℚ) := by decide +kernel

lemma fiber_max_attained (d : ℤ) (p : ℚ)
    (hmax : (pValues d).max = (p : WithBot ℚ)) :
    SAP.P003a.w1MaxP observedCounts d p := by
  constructor
  · intro v hv he
    have hm : pValue v observedCounts ∈ pValues d := by
      change v ∈ possibleTables observedCounts at hv
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, rfl⟩
      exact decide_eq_true_eq.mpr he
    have hle : (pValue v observedCounts : WithBot ℚ) ≤ (pValues d).max :=
      Finset.le_max hm
    rw [hmax] at hle
    exact WithBot.coe_le_coe.mp hle
  · have hp : p ∈ pValues d := Finset.mem_of_max hmax
    rcases List.mem_map.mp (List.mem_toFinset.mp hp) with ⟨v, hv, hpv⟩
    rcases List.mem_filter.mp hv with ⟨hv, he⟩
    exact ⟨v, hv, of_decide_eq_true he, hpv⟩

end SAP.P003a.WH.W1.P.T21_L1

theorem SAP.P003a.WH.W1.T21_L1_proof : SAP.P003a.WH.W1.T21_L1 := by
  classical
  rintro ⟨d, p⟩ hdp
  simp only [SAP.P003a.w1FootnoteMaxima, List.mem_cons, List.not_mem_nil, or_false] at hdp
  rcases hdp with hdp | hdp | hdp | hdp | hdp | hdp | hdp | hdp | hdp | hdp
  all_goals
    rcases Prod.mk.inj hdp with ⟨rfl, rfl⟩
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained (-6) (1 / 36)
      SAP.P003a.WH.W1.P.T21_L1.max_neg_six
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained (-5) (1 / 12)
      SAP.P003a.WH.W1.P.T21_L1.max_neg_five
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained (-4) (1 / 6)
      SAP.P003a.WH.W1.P.T21_L1.max_neg_four
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained (-3) (4 / 9)
      SAP.P003a.WH.W1.P.T21_L1.max_neg_three
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained (-2) (1 / 2)
      SAP.P003a.WH.W1.P.T21_L1.max_neg_two
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained (-1) (29 / 36)
      SAP.P003a.WH.W1.P.T21_L1.max_neg_one
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained 0 1
      SAP.P003a.WH.W1.P.T21_L1.max_zero
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained 1 1
      SAP.P003a.WH.W1.P.T21_L1.max_one
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained 2 (2 / 3)
      SAP.P003a.WH.W1.P.T21_L1.max_two
  · exact SAP.P003a.WH.W1.P.T21_L1.fiber_max_attained 3 (1 / 12)
      SAP.P003a.WH.W1.P.T21_L1.max_three
