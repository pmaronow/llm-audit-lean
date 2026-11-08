import SAP.P003a.Defs.WholeW2
import SAP.P003a.Bridge
import AronowAudit.P003.P003_Audit
import AronowAudit.P003.Wave1.Gap.GP0032B1b
import AronowAudit.P003.Wave1.Gap.GLP0031B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2

open scoped BigOperators
open SAP.P003a.Bridge
attribute [local instance 0] Classical.propDecidable

theorem assignment_nonempty (n m : ℕ) (hm : m ≤ n) : Nonempty (Assignment n m) := by
  obtain ⟨z, _, hz⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using hm)
  exact ⟨⟨z,hz⟩⟩

theorem table_effect (n : ℕ) (y : PotentialTable n) (hn : 0 < n) :
    tableTau y = tau (tableCounts y) := by
  simpa only [to_tableTau, to_tableCounts, to_tau] using
    (AronowAudit.P003.corrected_sate y hn).2.2.2

theorem true_counts_possible (n m : ℕ) (y : PotentialTable n) (z : Assignment n m) :
    Possible (unitObserved (unitOutcomes y z.val) z.val) (tableCounts y) := by
  have he := AronowAudit.P003.Wave1.couplingB2_observed y z.val
  have ht : AronowAudit.P003.Wave1.couplingB2_treated y z.val =
      AronowAudit.P003.Wave1.neyman_treated y z.val := rfl
  rw [ht] at he
  have hq := AronowAudit.P003.Wave1.neyman_treated_mem y
    (toAudit (tableCounts y)) (to_tableCounts y) m z
  have hp := AronowAudit.P003.observed_population_possible _ m _ hq
  rw [← to_tableCounts, ← he] at hp
  have hout : AronowAudit.P003.unitOutcomes y z.val = unitOutcomes y z.val := by
    funext i
    by_cases hi : i ∈ z.val <;> simp [AronowAudit.P003.unitOutcomes, unitOutcomes, hi]
  simpa only [hout, to_unitObserved, to_tableCounts, to_possible] using hp

theorem uniform_event_sum {Ω : Type*} [Fintype Ω] (E : Ω → Prop) :
    uniformProb E = ∑ i, if E i then (1 : ℝ)/Fintype.card Ω else 0 := by
  simp only [uniformProb, ← Finset.sum_boole, Finset.sum_div, ite_div, zero_div]

theorem uniform_tail {Ω : Type*} [Fintype Ω] (D : Ω → ℝ) (x : ℝ) :
    uniformProb (fun i => x ≤ D i) = finiteTail (fun _ => 1/Fintype.card Ω) D x := by
  exact uniform_event_sum _

theorem uniform_weights_total {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    (∑ _i : Ω, (1 : ℝ)/Fintype.card Ω) = 1 := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [h]

theorem uniform_weights_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (_i : Ω) :
    0 < (1 : ℝ)/Fintype.card Ω := by
  have h : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  positivity

theorem uniform_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (p : Prop) :
    uniformProb (fun _ : Ω => p) = if p then 1 else 0 := by
  by_cases hp : p <;> simp [uniformProb, hp, Fintype.card_ne_zero]

theorem uniform_cover {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → ℝ) (E : Ω → Prop) (α : ℝ)
    (hpoint : ∀ i, α ≤ p i → E i)
    (hrej : uniformProb (fun i => p i < α) < α) :
    1-α ≤ uniformProb E := by
  let w : ℝ := 1/Fintype.card Ω
  have hpoint' (i : Ω) : w ≤ (if E i then w else 0)+(if p i < α then w else 0) := by
    have hw : 0 ≤ w := by dsimp [w]; positivity
    by_cases hr : p i < α
    · simp only [ite_eq_left hr]; split_ifs <;> linarith
    · have he := hpoint i (le_of_not_gt hr)
      simp only [ite_eq_right hr, ite_eq_left he, add_zero, le_refl]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Ω)) => hpoint' i)
  rw [Finset.sum_add_distrib] at hs
  change (∑ _i : Ω, (1 : ℝ)/Fintype.card Ω) ≤
    (∑ i, if E i then (1 : ℝ)/Fintype.card Ω else 0)+
    (∑ i, if p i < α then (1 : ℝ)/Fintype.card Ω else 0) at hs
  rw [uniform_weights_total, ← uniform_event_sum, ← uniform_event_sum] at hs
  linarith

theorem log_floor (d : ℕ) (hd : 0 < d) :
    ⌊logTwo (d : ℝ)⌋ = (Nat.log 2 d : ℤ) := by
  change ⌊Real.logb (2 : ℝ) (d : ℝ)⌋ = _
  simpa only [Nat.cast_ofNat, Int.log_natCast] using
    (Real.floor_logb_natCast (b := 2) (r := (d : ℝ)) (by positivity))

theorem log_floor_add (d : ℕ) (hd : 0 < d) (j : ℕ) :
    ⌊logTwo (d : ℝ)+(j : ℝ)⌋ = (Nat.log 2 d : ℤ)+j := by
  rw [Int.floor_add_natCast, log_floor d hd]

theorem two_budget (n : ℕ) (hn : 15 ≤ n) :
    2*((n+1 : ℕ) : ℝ)*((⌊logTwo (n+1 : ℕ)+3⌋ : ℤ) : ℝ) ≤
      4*n*logTwo n := by
  have h := AronowAudit.P003.Wave1.GP0032B1b_two_budget_le n hn
  rw [show ⌊logTwo (n+1 : ℕ)+3⌋ = (Nat.log 2 (n+1) : ℤ)+3 from
    log_floor_add (n+1) (by omega) 3]
  simpa only [AronowAudit.P003.testBudget, Nat.log2_eq_log_two,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Int.cast_add,
    Int.cast_natCast, Int.cast_ofNat, logTwo_eq, mul_assoc] using h

theorem static_search (fuel : ℕ) (f : ℤ → Bool) (t : ℕ) (a b : ℤ) :
    let s := w2Search fuel (fun _ c => f c) t a b
    sentinelSearch fuel f a b = (s.1.1, s.2.map w2Mid) := by
  induction fuel generalizing t a b with
  | zero => rfl
  | succ fuel ih =>
    simp only [w2Search, sentinelSearch]
    split
    · rfl
    · split <;> simp only [ih (t+1), List.map_cons, w2Mid]

theorem threshold_frames (fuel : ℕ) (f : ℤ → Bool) (t : ℕ) (a b r : ℤ)
    (hr : a ≤ r ∧ r < b)
    (hf : ∀ x, a < x → x < b → (f x = false ↔ x ≤ r)) :
    ∀ p ∈ (w2Search fuel (fun _ c => f c) t a b).2, p.1 ≤ r ∧ r < p.2 := by
  induction fuel generalizing t a b with
  | zero => simp [w2Search]
  | succ fuel ih =>
    by_cases hs : b ≤ a+1
    · simp [w2Search, hs]
    · have hl : a < (a+b)/2 := by omega
      have hu : (a+b)/2 < b := by omega
      by_cases hc : f ((a+b)/2) = true
      · have hrc : r < (a+b)/2 := by
          by_contra h
          have hfalse := (hf _ hl hu).mpr (by omega)
          simp [hc] at hfalse
        simp only [w2Search, ite_eq_right hs, ite_eq_left hc, List.mem_cons]
        intro p hp
        rcases hp with rfl | hp
        · exact hr
        · exact ih (t+1) a ((a+b)/2) ⟨hr.1,hrc⟩
            (fun x hx hxc => hf x hx (lt_trans hxc hu)) p hp
      · have hcr : (a+b)/2 ≤ r := (hf _ hl hu).mp (Bool.eq_false_iff.mpr hc)
        simp only [w2Search, ite_eq_right hs, ite_eq_right hc, List.mem_cons]
        intro p hp
        rcases hp with rfl | hp
        · exact hr
        · exact ih (t+1) ((a+b)/2) b ⟨hcr,hr.2⟩
            (fun x hcx hx => hf x (lt_trans hl hcx) hx) p hp

theorem point_bijective (k : ℕ) (hk : 0 < k) : Function.Bijective (w2Point k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  constructor
  · intro i j hij
    have h : (i : ℝ)/(k : ℝ) = (j : ℝ)/(k : ℝ) := congrArg Subtype.val hij
    have : (i : ℝ) = j := (div_left_inj' hkR).mp h
    exact_mod_cast this
  · rintro ⟨x,j,hj⟩
    exact ⟨j, Subtype.ext hj.symm⟩

theorem point_coordinate (k : ℕ) (hk : 0 < k) (x : W2Lattice k) (j : ℤ) :
    (k : ℝ)*x.val = (j : ℝ) ↔ x = w2Point k j := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  constructor
  · intro h
    apply Subtype.ext
    change x.val = (j : ℝ)/(k : ℝ)
    apply (eq_div_iff hkR).mpr
    simpa only [mul_comm] using h
  · intro h
    subst x
    dsimp [w2Point]
    field_simp

theorem cost_without_zero (B : ℕ) (cost : ℤ → ℕ) (qs : List ℤ)
    (hcost : ∀ x ∈ qs, cost x ≤ if x = 0 then 2*B else B) (hzero : 0 ∉ qs) :
    w2Cost cost qs ≤ B*qs.length := by
  induction qs with
  | nil => simp [w2Cost]
  | cons x xs ih =>
    have hx : x ≠ 0 := by intro h; subst x; simp at hzero
    have ht : 0 ∉ xs := fun h => hzero (by simp [h])
    have hc : cost x ≤ B := by simpa [hx] using hcost x (by simp)
    have hi := ih (fun y hy => hcost y (by simp [hy])) ht
    simp only [w2Cost, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem cost_with_zero (B : ℕ) (cost : ℤ → ℕ) (qs : List ℤ)
    (hcost : ∀ x ∈ qs, cost x ≤ if x = 0 then 2*B else B) (hqs : qs.Nodup) :
    w2Cost cost qs ≤ B*(qs.length+1) := by
  induction qs with
  | nil => simp [w2Cost]
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.nodup_cons.mp hqs
    by_cases hx0 : x = 0
    · subst x
      have hi := cost_without_zero B cost xs (fun y hy => hcost y (by simp [hy])) hx
      have hc : cost 0 ≤ 2*B := by simpa using hcost 0 (by simp)
      simp only [w2Cost, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith
    · have hi := ih (fun y hy => hcost y (by simp [hy])) ht
      have hc : cost x ≤ B := by simpa [hx0] using hcost x (by simp)
      simp only [w2Cost, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

theorem half_point_pmf : W2LatticePMF w2HalfPointMass := by
  let x : W2Lattice 2 := w2Point 2 1
  have he : w2HalfPointMass = fun t => if t = x then (1 : ℝ) else 0 := by
    funext t
    have ht : t.val = 1/2 ↔ t = x := by
      constructor
      · intro h; apply Subtype.ext; simpa [x, w2Point] using h
      · intro h; subst t; norm_num [x, w2Point]
    simp only [w2HalfPointMass, ht]
  have hs : HasSum w2HalfPointMass 1 := by rw [he]; exact hasSum_ite_eq x 1
  exact ⟨fun t => by simp only [he]; split_ifs <;> norm_num, hs.summable, hs.tsum_eq⟩

theorem half_point_correct (j : ℤ) :
    w2Rescale w2HalfPointMass j = if j = 1 then 1 else 0 := by
  have he : (j : ℝ)/2 = 1/2 ↔ j = 1 := by
    constructor
    · intro h
      have hjR : (j : ℝ) = 1 := by linarith
      exact_mod_cast hjR
    · intro h; subst j; norm_num
  simp only [w2Rescale, w2HalfPointMass, w2Point, Nat.cast_ofNat, he]

theorem half_point_wrong (j : ℤ) : w2PrintedRescale j = 0 := by
  change (if (((4*j : ℤ) : ℝ)/2 = (1 : ℝ)/2) then (1 : ℝ) else 0) = 0
  have h : ((4*j : ℤ) : ℝ)/2 ≠ 1/2 := by
    intro hj
    have hjR : (4*j : ℤ) = (1 : ℤ) := by exact_mod_cast (show ((4*j : ℤ) : ℝ) = 1 by linarith)
    omega
  exact ite_eq_right h

theorem b_joint (j : ℤ) :
    (∑ i : Fin 4, if w2BX i = j then w2BW i else 0) = w2ThreeMass j ∧
    (∑ i : Fin 4, if w2BY i = j then w2BW i else 0) = fairMass j ∧
    (∑ i : Fin 4, if w2BX i+w2BY i = j then w2BW i else 0) = w2BSumMass j := by
  by_cases hm : j = -1
  · subst j; norm_num [Fin.sum_univ_succ, w2BX, w2BY, w2BW, w2ThreeMass, w2BSumMass, fairMass]
  by_cases h0 : j = 0
  · subst j; norm_num [Fin.sum_univ_succ, w2BX, w2BY, w2BW, w2ThreeMass, w2BSumMass, fairMass]
  by_cases h1 : j = 1
  · subst j; norm_num [Fin.sum_univ_succ, w2BX, w2BY, w2BW, w2ThreeMass, w2BSumMass, fairMass]
  by_cases h2 : j = 2
  · subst j; norm_num [Fin.sum_univ_succ, w2BX, w2BY, w2BW, w2ThreeMass, w2BSumMass, fairMass]
  simp [Fin.sum_univ_succ, w2BX, w2BY, w2BW, w2ThreeMass, w2BSumMass, fairMass,
    hm, h0, h1, h2, Ne.symm hm, Ne.symm h0, Ne.symm h1, Ne.symm h2]

end SAP.P003a.WH.W2
