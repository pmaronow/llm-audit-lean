import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1.P.T7_L1

open SAP.P003b

theorem midpoint_step (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (a b : ℤ) (idx : ℕ) :
    w1Midpoints (fuel+1) o reject a b idx =
      if b ≤ a+1 then [] else
        let c := (a+b)/2
        let q := runTests reject idx (candidates o c)
        c :: w1Midpoints fuel o reject (if q.compatible then c else a)
          (if q.compatible then b else c) q.idx := by
  simp only [w1Midpoints]

theorem midpoint_invariants (q fuel : ℕ) (o : Counts)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ)
    (hab : a < b) (hw : b-a ≤ (2 : ℤ)^q) :
    (w1Midpoints fuel o reject a b idx).length ≤ q ∧
    (w1Midpoints fuel o reject a b idx).Nodup ∧
    (w1Midpoints fuel o reject a b idx).count 0 ≤ 1 ∧
    ∀ x ∈ w1Midpoints fuel o reject a b idx, a < x ∧ x < b := by
  induction q generalizing fuel a b idx with
  | zero =>
      have hs : b ≤ a+1 := by omega
      cases fuel <;> simp [w1Midpoints, hs]
  | succ q ih =>
      cases fuel with
      | zero => simp [w1Midpoints]
      | succ fuel =>
          rw [midpoint_step]
          by_cases hs : b ≤ a+1
          · simp [hs]
          · simp only [if_neg hs]
            let c : ℤ := (a+b)/2
            let r := runTests reject idx (candidates o c)
            have hac : a < c := by dsimp [c]; omega
            have hcb : c < b := by dsimp [c]; omega
            have hp : (2 : ℤ)^(q+1) = 2*(2 : ℤ)^q := by ring
            rw [hp] at hw
            have hl : c-a ≤ (2 : ℤ)^q := by dsimp [c]; omega
            have hr : b-c ≤ (2 : ℤ)^q := by dsimp [c]; omega
            cases hrc : r.compatible with
            | false =>
                have hi := ih fuel a c r.idx hac hl
                simp only [show (a+b)/2 = c from rfl, hrc]
                refine ⟨?_, ?_, ?_, ?_⟩
                · simpa [r, hrc] using hi.1
                · apply List.nodup_cons.mpr
                  refine ⟨?_, hi.2.1⟩
                  intro hc
                  have hh := hi.2.2.2 c hc
                  exact (lt_irrefl c) hh.2
                · by_cases hcz : c = 0
                  · have hnot : 0 ∉ w1Midpoints fuel o reject a c r.idx := by
                      intro hz
                      have hh := hi.2.2.2 0 hz
                      simpa [hcz] using hh.2
                    have hcount := List.count_eq_zero_of_not_mem hnot
                    have hcount' : (w1Midpoints fuel o reject a 0
                        (runTests reject idx (candidates o 0)).idx).count 0 = 0 := by
                      simpa [r, hcz] using hcount
                    simp [List.count_cons, hcz, hcount']
                  · simpa [List.count_cons, hcz] using hi.2.2.1
                · intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact ⟨hac,hcb⟩
                  · have hh := hi.2.2.2 x hx
                    exact ⟨hh.1,lt_trans hh.2 hcb⟩
            | true =>
                have hi := ih fuel c b r.idx hcb hr
                simp only [show (a+b)/2 = c from rfl, hrc]
                refine ⟨?_, ?_, ?_, ?_⟩
                · simpa [r, hrc] using hi.1
                · apply List.nodup_cons.mpr
                  refine ⟨?_, hi.2.1⟩
                  intro hc
                  have hh := hi.2.2.2 c hc
                  exact (lt_irrefl c) hh.1
                · by_cases hcz : c = 0
                  · have hnot : 0 ∉ w1Midpoints fuel o reject c b r.idx := by
                      intro hz
                      have hh := hi.2.2.2 0 hz
                      simpa [hcz] using hh.1
                    have hcount := List.count_eq_zero_of_not_mem hnot
                    have hcount' : (w1Midpoints fuel o reject 0 b
                        (runTests reject idx (candidates o 0)).idx).count 0 = 0 := by
                      simpa [r, hcz] using hcount
                    simp [List.count_cons, hcz, hcount']
                  · simpa [List.count_cons, hcz] using hi.2.2.1
                · intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact ⟨hac,hcb⟩
                  · have hh := hi.2.2.2 x hx
                    exact ⟨lt_trans hac hh.1,hh.2⟩

theorem search_step_native (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    adaptiveSearch (fuel+1) true o k₁ k₂ reject a b idx =
      if b ≤ a+1 then ⟨some a, []⟩ else
        let c := (a+b)/2
        let q := runTests reject idx (candidates o c)
        let r := if q.compatible then
          adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx
        ⟨r.value, q.trace ++ r.trace⟩ := by
  conv_lhs => unfold adaptiveSearch
  simp only [eq_self, true_and, not_true_eq_false, false_and, ite_false]
  by_cases hs : b ≤ a+1
  · simp only [if_pos hs]
  · simp only [if_neg hs]
    cases hq : (runTests reject idx (candidates o ((a+b)/2))).compatible <;>
      simp [hq]

theorem trace_midpoint_cost (fuel : ℕ) (o : Counts)
    (reject : Counts → ℕ → Bool) (k₁ k₂ a b : ℤ) (idx : ℕ) :
    (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace.length ≤
      (o.total+1) * ((w1Midpoints fuel o reject a b idx).length +
        (w1Midpoints fuel o reject a b idx).count 0) := by
  induction fuel generalizing a b idx with
  | zero =>
      by_cases hs : b ≤ a+1 <;> simp [adaptiveSearch, w1Midpoints, hs]
  | succ fuel ih =>
      rw [search_step_native]
      by_cases hs : b ≤ a+1
      · simp [hs, w1Midpoints]
      · simp only [if_neg hs]
        let c : ℤ := (a+b)/2
        let r := runTests reject idx (candidates o c)
        have hq : r.trace.length ≤ (o.total+1) * (1 + if c = 0 then 1 else 0) := by
          have h := SAP.P003b.WH.W1.queryCosts o c reject idx
          by_cases hc : c = 0 <;> simpa [r, hc] using h
        cases hrc : r.compatible with
        | false =>
            have hi := ih a c r.idx
            simp only [show (a+b)/2 = c from rfl, hrc, List.length_append,
              midpoint_step, if_neg hs, show (a+b)/2 = c from rfl,
              show r = runTests reject idx (candidates o c) from rfl]
            have hm := Nat.add_le_add hq hi
            simpa [List.length_cons, List.count_cons, r, hrc, Nat.mul_add,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hm
        | true =>
            have hi := ih c b r.idx
            simp only [show (a+b)/2 = c from rfl, hrc, List.length_append,
              midpoint_step, if_neg hs, show (a+b)/2 = c from rfl,
              show r = runTests reject idx (candidates o c) from rfl]
            have hm := Nat.add_le_add hq hi
            simpa [List.length_cons, List.count_cons, r, hrc, Nat.mul_add,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hm

end SAP.P003b.WH.W1.P.T7_L1

namespace SAP.P003b.WH.W1

open SAP.P003b

theorem T7_L1_proof : SAP.P003b.WH.W1.T7_L1 := by
  intro o reject idx ho
  dsimp [SAP.P003b.WH.W1.T7_L1]
  let k₁ : ℤ := 2*((o.a : ℤ)-o.c)
  let k₂ : ℤ := (o.a : ℤ)-o.c+(o.a+o.b)
  let a : ℤ := k₁-1
  let b : ℤ := k₂+1
  let qs := w1UpperMidpoints o reject idx
  have hab : a < b := by dsimp [a,b,k₁,k₂]; omega
  have hwidth : b-a ≤ (o.total : ℤ)+2 := by dsimp [a,b,k₁,k₂,Counts.total]; omega
  have hpowN : (o.total : ℕ)+2 ≤ 2^Nat.clog 2 (o.total+2) :=
    Nat.le_pow_clog (by norm_num) (o.total+2)
  have hpow : b-a ≤ (2 : ℤ)^Nat.clog 2 (o.total+2) := by
    have hpowZ : (o.total : ℤ)+2 ≤ (2 : ℤ)^Nat.clog 2 (o.total+2) := by
      exact_mod_cast hpowN
    exact le_trans hwidth hpowZ
  have hmid := SAP.P003b.WH.W1.P.T7_L1.midpoint_invariants
    (Nat.clog 2 (o.total+2)) (o.total+3)
    o reject a b idx hab hpow
  have hceil : ⌈logTwo ((o.total : ℝ)+2)⌉₊ = Nat.clog 2 (o.total+2) := by
    unfold logTwo
    rw [show Real.log ((o.total : ℝ)+2) / Real.log 2 =
      Real.logb (2 : ℝ) ((o.total : ℝ)+2) by rfl]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (Real.natCeil_logb_natCast 2 (o.total+2))
  have hqsLen : qs.length ≤ ⌈logTwo ((o.total : ℝ)+2)⌉₊ := by
    simpa [qs, w1UpperMidpoints, a, b, k₁, k₂, hceil] using hmid.1
  have hqsNodup : qs.Nodup := by
    simpa [qs, w1UpperMidpoints, a, b, k₁, k₂] using hmid.2.1
  have hqsZero : qs.count 0 ≤ 1 := by
    simpa [qs, w1UpperMidpoints, a, b, k₁, k₂] using hmid.2.2.1
  have hsearch := SAP.P003b.WH.W1.allStartBudget o reject idx ho
  have htrace :
      (upperRun true o reject idx).trace.length ≤ (o.total+1)*(qs.length+qs.count 0) := by
    have heq : upperRun true o reject idx =
        adaptiveSearch (o.total+3) true o k₁ k₂ reject a b idx := by
      rfl
    rw [heq]
    simpa [qs, w1UpperMidpoints, a, b, k₁, k₂] using
      SAP.P003b.WH.W1.P.T7_L1.trace_midpoint_cost (o.total+3) o reject k₁ k₂ a b idx
  have hlogPow : o.total+2 ≤ 2^(Nat.log2 (o.total+1)+1) := by
    have hp := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (o.total+1)
    rw [Nat.log2_eq_log_two]
    omega
  have hclog : Nat.clog 2 (o.total+2) ≤ Nat.log2 (o.total+1)+1 :=
    Nat.clog_le_of_le_pow hlogPow
  have hbudget : (o.total+1)*(⌈logTwo ((o.total : ℝ)+2)⌉₊+1) ≤ testBudget o.total := by
    unfold testBudget
    apply Nat.mul_le_mul_left
    rw [hceil]
    omega
  exact ⟨hsearch.1,hsearch.2,hqsLen,hqsNodup,hqsZero,htrace,hbudget⟩

end SAP.P003b.WH.W1
