import SAP.P037b.WH.W1.Leaves
import AronowAudit.P037.Wave1.Gap.GP037B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b.WH.W1.P.T22_L3

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def seedA : Finset (Fin 12) := {6,7,8,9,10,11}
def seedB : Finset (Fin 12) := {1,6,7,8,9,10}
def seedC : Finset (Fin 12) := {0,6,7,8,9,10}

def seedChoice (j : Fin 10000) : Bool × Finset (Fin 12) :=
  if j.val < 2500 then (false, {0,1,2,3,4,5})
  else if j.val < 5000 then (true, seedA)
  else if j.val < 7500 then (true, seedB)
  else (true, seedC)

theorem seedChoice_legal (j : Fin 10000) :
    (seedChoice j).2 ∈ seedSubsets 12 6 := by
  unfold seedChoice seedSubsets seedA seedB seedC
  split_ifs <;> norm_num [Finset.mem_powersetCard]

theorem seedA_label_bg :
    localTreatedLabel (∅ : Finset (Fin 12)) {0,1,2,3,4,5} {0} seedA = 1 := by
  have hp : Disjoint seedA ({0,1,2,3,4,5} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [seedA, Finset.mem_insert, Finset.mem_singleton] at hx hy
    omega
  simp [localTreatedLabel, hp]

theorem seedA_label_eligible :
    localTreatedLabel ({2} : Finset (Fin 12)) {0,1} {0} seedA = 1 := by
  have hs : Disjoint seedA ({2} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_singleton] at hy
    subst x
    simp [seedA] at hx
  have hp : Disjoint seedA ({0,1} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [seedA, Finset.mem_insert, Finset.mem_singleton] at hx hy
    omega
  simp [localTreatedLabel, hs, hp]

theorem seedB_label_bg :
    localTreatedLabel (∅ : Finset (Fin 12)) {0,1,2,3,4,5} {0} seedB = 2 := by
  have hp : ¬ Disjoint seedB ({0,1,2,3,4,5} : Finset (Fin 12)) := by
    intro h
    have hs : (1 : Fin 12) ∈ seedB := by simp [seedB]
    have h' : (1 : Fin 12) ∉ ({0,1,2,3,4,5} : Finset (Fin 12)) :=
      Finset.disjoint_left.mp h hs
    exact h' (by simp)
  have hr : Disjoint seedB ({0} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_singleton] at hy
    subst x
    simp [seedB] at hx
  simp [localTreatedLabel, hp, hr]

theorem seedB_label_eligible :
    localTreatedLabel ({2} : Finset (Fin 12)) {0,1} {0} seedB = 2 := by
  have hs : Disjoint seedB ({2} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_singleton] at hy
    subst x
    simp [seedB] at hx
  have hp : ¬ Disjoint seedB ({0,1} : Finset (Fin 12)) := by
    intro h
    have hs : (1 : Fin 12) ∈ seedB := by simp [seedB]
    have h' : (1 : Fin 12) ∉ ({0,1} : Finset (Fin 12)) :=
      Finset.disjoint_left.mp h hs
    exact h' (by simp)
  have hr : Disjoint seedB ({0} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_singleton] at hy
    subst x
    simp [seedB] at hx
  simp [localTreatedLabel, hs, hp, hr]

theorem seedC_label_bg :
    localTreatedLabel (∅ : Finset (Fin 12)) {0,1,2,3,4,5} {0} seedC = 3 := by
  have hp : ¬ Disjoint seedC ({0,1,2,3,4,5} : Finset (Fin 12)) := by
    intro h
    have hs : (0 : Fin 12) ∈ seedC := by simp [seedC]
    have h' : (0 : Fin 12) ∉ ({0,1,2,3,4,5} : Finset (Fin 12)) :=
      Finset.disjoint_left.mp h hs
    exact h' (by simp)
  have hr : ¬ Disjoint seedC ({0} : Finset (Fin 12)) := by
    intro h
    have hs : (0 : Fin 12) ∈ seedC := by simp [seedC]
    have h' : (0 : Fin 12) ∉ ({0} : Finset (Fin 12)) := Finset.disjoint_left.mp h hs
    exact h' (by simp)
  simp [localTreatedLabel, hp, hr]

theorem seedC_label_eligible :
    localTreatedLabel ({2} : Finset (Fin 12)) {0,1} {0} seedC = 3 := by
  have hs : Disjoint seedC ({2} : Finset (Fin 12)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_singleton] at hy
    subst x
    simp [seedC] at hx
  have hp : ¬ Disjoint seedC ({0,1} : Finset (Fin 12)) := by
    intro h
    have hs : (0 : Fin 12) ∈ seedC := by simp [seedC]
    have h' : (0 : Fin 12) ∉ ({0,1} : Finset (Fin 12)) :=
      Finset.disjoint_left.mp h hs
    exact h' (by simp)
  have hr : ¬ Disjoint seedC ({0} : Finset (Fin 12)) := by
    intro h
    have hs : (0 : Fin 12) ∈ seedC := by simp [seedC]
    have h' : (0 : Fin 12) ∉ ({0} : Finset (Fin 12)) := Finset.disjoint_left.mp h hs
    exact h' (by simp)
  simp [localTreatedLabel, hs, hp, hr]

def sequenceDraws (j : Fin 10000) : CutoffAssignmentsW1 :=
  liftCutoffAssignmentW1 (seedChoice j) (seedChoice_legal j)

theorem sequence_label (j : Fin 10000) (i : Fin 2) :
    cutoffNetworkW1 (sequenceDraws j) i =
      (if j.val < 2500 then (0 : Fin 5)
       else if j.val < 5000 then 1
       else if j.val < 7500 then 2 else 3) := by
  fin_cases i
  all_goals
    by_cases h0 : j.val < 2500
    · simp [sequenceDraws, seedChoice, cutoffNetworkW1, cutoffExposureW1,
        liftCutoffAssignmentW1, h0]
    · by_cases h1 : j.val < 5000
      · simp [sequenceDraws, seedChoice, cutoffNetworkW1, cutoffExposureW1,
          liftCutoffAssignmentW1, h0, h1, seedA_label_bg, seedA_label_eligible]
      · by_cases h2 : j.val < 7500
        · simp [sequenceDraws, seedChoice, cutoffNetworkW1, cutoffExposureW1,
            liftCutoffAssignmentW1, h0, h1, h2, seedB_label_bg, seedB_label_eligible]
        · simp [sequenceDraws, seedChoice, cutoffNetworkW1, cutoffExposureW1,
            liftCutoffAssignmentW1, h0, h1, h2, seedC_label_bg, seedC_label_eligible]

theorem labelCount (i : Fin 2) (k : Fin 4) :
    (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW1 (sequenceDraws j) i = k.castSucc)).card = 2500 := by
  classical
  have hi : ∀ j : Fin 10000,
      cutoffNetworkW1 (sequenceDraws j) i = cutoffNetworkW1 (sequenceDraws j) 0 := by
    intro j
    rw [sequence_label, sequence_label]
  rw [show (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW1 (sequenceDraws j) i = k.castSucc)) =
      Finset.univ.filter (fun j : Fin 10000 =>
        cutoffNetworkW1 (sequenceDraws j) 0 = k.castSucc) by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hi]]
  fin_cases k
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        cutoffNetworkW1 (sequenceDraws j) 0 = (0 : Fin 5))) =
      Finset.univ.filter (fun j => 0 ≤ j.val ∧ j.val < 2500) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sequence_label]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW1 (sequenceDraws j) 0 = (0 : Fin 5))).card = 2500
    rw [he, AronowAudit.P037.Wave1.cutoff_interval_card 0 2500 (by omega) (by omega)]
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        cutoffNetworkW1 (sequenceDraws j) 0 = (1 : Fin 5))) =
      Finset.univ.filter (fun j => 2500 ≤ j.val ∧ j.val < 5000) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sequence_label]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW1 (sequenceDraws j) 0 = (1 : Fin 5))).card = 2500
    rw [he, AronowAudit.P037.Wave1.cutoff_interval_card 2500 5000 (by omega) (by omega)]
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        cutoffNetworkW1 (sequenceDraws j) 0 = (2 : Fin 5))) =
      Finset.univ.filter (fun j => 5000 ≤ j.val ∧ j.val < 7500) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sequence_label]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW1 (sequenceDraws j) 0 = (2 : Fin 5))).card = 2500
    rw [he, AronowAudit.P037.Wave1.cutoff_interval_card 5000 7500 (by omega) (by omega)]
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        cutoffNetworkW1 (sequenceDraws j) 0 = (3 : Fin 5))) =
      Finset.univ.filter (fun j => 7500 ≤ j.val ∧ j.val < 10000) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sequence_label]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW1 (sequenceDraws j) 0 = (3 : Fin 5))).card = 2500
    rw [he, AronowAudit.P037.Wave1.cutoff_interval_card 7500 10000 (by omega) (by omega)]

end SAP.P037b.WH.W1.P.T22_L3

theorem SAP.P037b.WH.W1.T22_L3_proof : SAP.P037b.WH.W1.T22_L3 := by
  classical
  refine ⟨SAP.P037b.WH.W1.P.T22_L3.sequenceDraws, ?_⟩
  intro i k
  unfold SAP.P037b.estimatedExposureW1
  rw [SAP.P037b.WH.W1.P.T22_L3.labelCount]
  norm_num
