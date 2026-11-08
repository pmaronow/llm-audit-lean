import SAP.P003b.Defs.WholeW2
import SAP.P003b.Bridge
import AronowAudit.P003.Wave1.Gap.GP0031B2
import AronowAudit.P003.Wave1.Gap.GP0031B3b
import AronowAudit.P003.Wave1.Gap.GLP0032B1
import AronowAudit.P003.Wave1.Gap.GLP0032B2
import AronowAudit.P003.Wave1.Gap.GLP0032B6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2
open scoped BigOperators
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

theorem allCounts_mem (n : ℕ) (v : Counts) : v ∈ allCounts n ↔ v.total = n := by
  simpa only [allCounts_eq, Finset.mem_image, to_inj, exists_eq_right, total_eq] using
    AronowAudit.P003.Wave1.corrected_stratum_count_mem n (toCounts v)

theorem stratum_card (a b : ℕ) :
    (stratifiedCounts a b).card = (a+3).choose 3 * (b+3).choose 3 := by
  simpa only [stratified_card_eq] using
    (AronowAudit.P003.Wave1.corrected_stratum_count_proof a b).2.1

theorem four_card (n : ℕ) : (allCounts n).card = (n+3).choose 3 := by
  simpa only [allCounts_card_eq] using
    AronowAudit.P003.Wave1.corrected_stratum_count_card n

theorem countsOn_total {n : ℕ} (A : Finset (Fin n)) (w : PotentialTable n) :
    (wholeCountsOn A w).total = A.card := by
  have h (i : Fin n) :
      (if w i = (true,true) then 1 else 0) +
      (if w i = (true,false) then 1 else 0) +
      (if w i = (false,true) then 1 else 0) +
      (if w i = (false,false) then 1 else 0) = (1 : ℕ) := by
    rcases hw : w i with ⟨a,b⟩
    cases a <;> cases b <;> simp
  have hs := Finset.sum_congr (s₁ := A) (s₂ := A) rfl (fun i _ => h i)
  simpa [Finset.sum_add_distrib, wholeCountsOn, Counts.total] using hs

theorem stratum_sizes {n : ℕ} (X : Fin n → Bool) :
    wholeStratumSize X false + wholeStratumSize X true = n := by
  have h (i : Fin n) :
      (if X i = false then 1 else 0) + (if X i = true then 1 else 0) = (1 : ℕ) := by
    cases X i <;> simp
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => h i)
  simpa [Finset.sum_add_distrib, wholeStratumSize] using hs

theorem rows_independent : LinearIndependent ℝ wholeStratumRow := by
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have h := congrFun hc ((true,true),s)
  cases s <;> simpa [Fintype.sum_bool, wholeStratumRow] using h

theorem totalEight_mem (n : ℕ) (v : Counts × Counts) :
    v ∈ wholeTotalEight n ↔ v.1.total+v.2.total = n := by
  simp only [wholeTotalEight, Finset.mem_biUnion, Finset.mem_range,
    stratifiedCounts, Finset.product_eq_sprod, Finset.mem_product, allCounts_mem]
  constructor
  · rintro ⟨r,hr,h₀,h₁⟩
    omega
  · intro h
    exact ⟨v.1.total,by omega,rfl,by omega⟩

def assignmentEquiv (n m : ℕ) : Assignment n m ≃ wholeBinaryAssignments n m where
  toFun z := ⟨wholeAssignmentBits z, by
    simpa [wholeAssignmentBits] using z.property⟩
  invFun z := ⟨Finset.univ.filter (fun i => z.val i = true), by
    simpa using z.property⟩
  left_inv z := by
    apply Subtype.ext
    ext i
    simp [wholeAssignmentBits]
  right_inv z := by
    apply Subtype.ext
    funext i
    simp [wholeAssignmentBits]

theorem uniform_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (E : B → Prop) :
    uniformProb (fun a => E (e a)) = uniformProb E := by
  have hc := Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl) :
    {a : A // E (e a)} ≃ {b : B // E b})
  simp only [Fintype.card_subtype] at hc
  simp only [uniformProb, hc, Fintype.card_congr e]

theorem retained20 : T20Statement := by
  refine ⟨?_,?_,@AronowAudit.P003.symbol_corrections⟩
  · intro n m hm w w' hc
    exact AronowAudit.P003.Wave1.count_distribution_invariance_proof m hm w w'
      (congrArg toCounts hc)
  · intro v ha hd
    exact AronowAudit.P003.corrected_update (toCounts v) ha hd

theorem minimum_line (o u v : Counts) (hu : Possible o u)
    (hv : firstOnLine o u.effect (u.a+u.b) = some v) :
    0 ≤ (u.b : ℤ)-v.b ∧ (u ≠ v → 0 < (u.b : ℤ)-v.b) ∧
    wholeSignedLine o.total (u.a+u.b) v.b u.effect =
      ((u.a : ℤ)+((u.b : ℤ)-v.b),(u.b : ℤ)-((u.b : ℤ)-v.b),
       (u.c : ℤ)-((u.b : ℤ)-v.b),(u.d : ℤ)+((u.b : ℤ)-v.b)) := by
  have hv' : AronowAudit.P003.firstOnLine (toCounts o) u.effect (u.a+u.b) =
      some (toCounts v) := by rw [firstOnLine_eq, hv]; rfl
  have hs := AronowAudit.P003.first_on_line_spec (toCounts o) u.effect (u.a+u.b) (toCounts v) hv'
  have hp : Possible o v := (possible_eq o v).mp hs.1
  have ht := (AronowAudit.P003.possible_table_facts (toCounts o) (toCounts u)
    ((possible_eq o u).mpr hu)).1
  have hvt := (AronowAudit.P003.possible_table_facts (toCounts o) (toCounts v) hs.1).1
  have hb := hs.2.2.2 (toCounts u) ((possible_eq o u).mpr hu) rfl rfl
  have he := hs.2.1
  have hj := hs.2.2.1
  change v.b ≤ u.b at hb
  change v.effect = u.effect at he
  change v.a+v.b = u.a+u.b at hj
  change u.total = o.total at ht
  change v.total = o.total at hvt
  dsimp [Counts.total, Counts.effect] at he ht hvt
  refine ⟨by omega,?_,?_⟩
  · intro hne
    by_contra hn
    have heq : u = v := by ext <;> omega
    exact hne heq
  · ext <;> dsimp [wholeSignedLine, Counts.effect, Counts.total] <;> omega

theorem minimum_pvalue (o u v : Counts) (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hu : Possible o u) (hv : firstOnLine o u.effect (u.a+u.b) = some v)
    (hd : 1 ≤ v.b+v.c) : pValue u o ≤ pValue v o := by
  have h := AronowAudit.P003.corrected_general_loop (toCounts o) (toCounts u)
    ((possible_eq o u).mpr hu)
  obtain ⟨v',hv',k,hkn,hka,hkd,huv⟩ := h.2.2
  have he : v' = toCounts v := by
    have hv'' : AronowAudit.P003.firstOnLine (toCounts o) u.effect (u.a+u.b) =
        some (toCounts v) := by rw [firstOnLine_eq, hv]; rfl
    change AronowAudit.P003.firstOnLine (toCounts o) u.effect (u.a+u.b) = some v' at hv'
    rw [hv''] at hv'
    exact Option.some.inj hv'.symm
  subst v'
  have hs := AronowAudit.P003.first_on_line_spec (toCounts o) u.effect (u.a+u.b) (toCounts v) hv'
  have ht := (AronowAudit.P003.possible_table_facts (toCounts o) (toCounts v) hs.1).1
  have hp := AronowAudit.P003.Wave1.GLP0032B6_reuse_pvalue (toCounts o) (toCounts v) k ho ht hka hkd hd
  rw [←huv] at hp
  simpa only [pValue_eq] using hp

theorem balanced_membership (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1) :
    estimate o ∈ accepted α o ∧ estimate o ∈ exactInterval α o ∧
    lower α o ≤ estimate o ∧ estimate o ≤ upper α o := by
  simpa only [estimate_eq,accepted_eq,interval_eq,lower_eq,upper_eq] using
    AronowAudit.P003.balanced_estimate_in_interval (toCounts o) α ho hα

theorem balanced_vector (o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    Possible o (wholeBalancedVector o) ∧ tau (wholeBalancedVector o) = estimate o ∧
      pValue (wholeBalancedVector o) o = 1 := by
  let v := wholeBalancedVector o
  have hv : Possible o v := by
    simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
    refine ⟨0,by omega,o.b,by omega,0,by omega,o.d,by omega,?_⟩
    ext <;> dsimp [v, wholeBalancedVector] <;> omega
  have ht : v.total = o.total :=
    (AronowAudit.P003.possible_table_facts (toCounts o) (toCounts v) ((possible_eq o v).mpr hv)).1
  have hn : v.total = 2*(o.a+o.b) := by rw [ht]; dsimp [Counts.total]; omega
  have hQ : (o.a : ℚ)+o.b = (o.c : ℚ)+o.d := by exact_mod_cast ho.2
  have hden : (o.a : ℚ)+o.b ≠ 0 := by
    have hp : (0 : ℚ) < o.a+o.b := by exact_mod_cast ho.1
    exact ne_of_gt hp
  have heQ : tauQ v = estimateQ o := by
    dsimp [tauQ, estimateQ, v, wholeBalancedVector, Counts.effect, Counts.total]
    push_cast
    have htt : (o.a : ℚ)+o.d+(o.b+o.c) = 2*(o.a+o.b) := by linarith
    simp only [zero_add]
    rw [htt, ←hQ]
    field_simp [hden]
    linarith
  have he : tau v = estimate o := congrArg (fun x : ℚ => (x : ℝ)) heQ
  have hdev : deviationNumerator v o (o.a+o.b) = 0 := by
    have hd : (o.d : ℤ) = o.a+o.b-o.c := by
      have hb : (o.a : ℤ)+o.b = (o.c : ℤ)+o.d := by exact_mod_cast ho.2
      omega
    dsimp [deviationNumerator, v, wholeBalancedVector, Counts.total, Counts.effect]
    rw [hd]
    ring
  have htail : tailCount v o = v.total.choose (o.a+o.b) := by
    simp only [tailCount,hdev,Int.natAbs_zero,Nat.zero_le,ite_true]
    simpa only [randomStates_eq, List.map_map, multiplicity_eq, Function.comp_def, total_eq] using
      AronowAudit.P003.design_weight_total (toCounts v) (o.a+o.b) (by change o.a+o.b ≤ v.total; omega)
  refine ⟨hv,he,?_⟩
  rw [pValue,htail]
  rw [show binomial v.total (o.a+o.b) = v.total.choose (o.a+o.b) from
    AronowAudit.P003.binomial_eq_choose _ _]
  exact div_self (by exact_mod_cast (Nat.choose_pos (show o.a+o.b ≤ v.total by omega)).ne')

end
end SAP.P003b.WH.W2
