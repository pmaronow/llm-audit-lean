import SAP.P003b.WH.W2.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2
open scoped BigOperators
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

theorem example_candidates :
    candidateLattice wholeT25Data = ({-1/2,-1/4,0,1/4,1/2} : Set ℝ) := by
  ext t
  norm_num [candidateLattice,candidateNumerators,wholeT25Data,Counts.total,List.range_succ]

theorem example_maxima : wholeT25Maxima := by
  have hc : ([-2,-1,0,1,2] : List ℤ).all (fun e =>
      let p : ℚ := if e = -2 ∨ e = 2 then 1/3 else 1
      ((possibleTables wholeT25Data).all fun v =>
        decide (v.effect = e → pValue v wholeT25Data ≤ p)) &&
      ((possibleTables wholeT25Data).any fun v =>
        decide (v.effect = e ∧ pValue v wholeT25Data = p))) = true := by decide +kernel
  intro e he
  have h := List.all_eq_true.mp hc e he
  simp only [Bool.and_eq_true] at h
  constructor
  · intro v hv he
    exact (of_decide_eq_true (List.all_eq_true.mp h.1 v hv)) he
  · obtain ⟨v,hv,hv'⟩ := List.any_eq_true.mp h.2
    exact ⟨v,hv,(of_decide_eq_true hv').1,(of_decide_eq_true hv').2⟩

theorem example_unique (v : Counts) (hv : Possible wholeT25Data v) (he : tauQ v = -1/2) :
    v = ⟨0,0,2,2⟩ := by
  have hlist : possibleTables wholeT25Data =
      [⟨0,0,0,4⟩,⟨0,1,0,3⟩,⟨0,2,0,2⟩,
       ⟨0,0,1,3⟩,⟨0,1,1,2⟩,⟨0,2,1,1⟩,
       ⟨0,0,2,2⟩,⟨0,1,2,1⟩,⟨0,2,2,0⟩] := by decide +kernel
  rw [Possible,hlist] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [tauQ,Counts.effect,Counts.total] at he
  rfl

theorem example_endpoints :
    lower (1/2) wholeT25Data = -1/4 ∧ upper (1/2) wholeT25Data = 1/4 := by
  have hI : AronowAudit.P003.intervalQ (1/2) (toCounts wholeT25Data) = some (-1/4,1/4) :=
    AronowAudit.P003.lattice_interval_witness.2.1
  have h := AronowAudit.P003.ConfidenceFollowup.real_extrema_of_intervalQ _ _ _ _ hI
  simpa only [lower_eq,upper_eq,Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat] using h.2

theorem example_j : wholeJ (1/2) wholeT25Data = ({-1/4,0,1/4} : Set ℝ) := by
  rw [j_eq_accepted]
  have hc : (acceptedEffectsQ (1/2) wholeT25Data).toFinset = {-1,0,1} := by
    simpa only [acceptedEffects_any, fromCounts, wholeT25Data] using AronowAudit.P003.lattice_interval_witness.1
  ext t
  have hr := AronowAudit.P003.ConfidenceFollowup.accepted_real_iff (1/2)
    (toCounts wholeT25Data) t
  simp only [accepted_eq,acceptedEffects_eq,total_eq,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hr
  change (t ∈ accepted (1/2) wholeT25Data) ↔ _
  rw [hr]
  simp_rw [← List.mem_toFinset, hc]
  norm_num [wholeT25Data,Counts.total]

theorem example_interval : exactInterval (1/2) wholeT25Data = Set.Icc (-1/4) (1/4) := by
  have hj := example_j
  rw [j_eq_accepted] at hj
  ext t
  change (∃ l ∈ accepted (1/2) wholeT25Data, ∃ u ∈ accepted (1/2) wholeT25Data,
    l ≤ t ∧ t ≤ u) ↔ (-1/4 : ℝ) ≤ t ∧ t ≤ 1/4
  constructor
  · rintro ⟨l,hl,u,hu,hlt,htu⟩
    have hl' : l ∈ ({-1/4,0,1/4} : Set ℝ) := by rw [←hj]; exact hl
    have hu' : u ∈ ({-1/4,0,1/4} : Set ℝ) := by rw [←hj]; exact hu
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hl' hu'
    rcases hl' with rfl | rfl | rfl <;> rcases hu' with rfl | rfl | rfl <;>
      constructor <;> linarith
  · rintro ⟨hl,hu⟩
    refine ⟨-1/4,?_,1/4,?_,hl,hu⟩ <;>
      change _ ∈ (↑(accepted (1/2) wholeT25Data) : Set ℝ) <;> rw [hj] <;> simp

theorem example_printed : wholePrintedJ (1/2) wholeT25Data = candidateLattice wholeT25Data := by
  apply Set.Subset.antisymm (fun _ ht => ht.1)
  intro t ht
  refine ⟨ht,?_⟩
  rw [example_candidates] at ht
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨1,0,2,1⟩,rfl,?_,?_⟩
    · norm_num [tau,tauQ,Counts.total,Counts.effect]
    · have h : pValue ⟨1,0,2,1⟩ wholeT25Data = 2/3 := by decide +kernel
      rw [h]; norm_num
  · refine ⟨⟨0,0,1,3⟩,rfl,?_,?_⟩
    · norm_num [tau,tauQ,Counts.total,Counts.effect]
    · have h : pValue ⟨0,0,1,3⟩ wholeT25Data = 1 := by decide +kernel
      rw [h]; norm_num
  · refine ⟨⟨0,0,0,4⟩,rfl,?_,?_⟩
    · norm_num [tau,tauQ,Counts.total,Counts.effect]
    · have h : pValue ⟨0,0,0,4⟩ wholeT25Data = 1 := by decide +kernel
      rw [h]; norm_num
  · refine ⟨⟨0,1,0,3⟩,rfl,?_,?_⟩
    · norm_num [tau,tauQ,Counts.total,Counts.effect]
    · have h : pValue ⟨0,1,0,3⟩ wholeT25Data = 1 := by decide +kernel
      rw [h]; norm_num
  · refine ⟨⟨1,2,0,1⟩,rfl,?_,?_⟩
    · norm_num [tau,tauQ,Counts.total,Counts.effect]
    · have h : pValue ⟨1,2,0,1⟩ wholeT25Data = 2/3 := by decide +kernel
      rw [h]; norm_num

end
end SAP.P003b.WH.W2
