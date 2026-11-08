import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T5_L2

open SAP.P003a

lemma w2Search_trace_length_le_pow (q fuel : ℕ) (reply : ℕ → ℤ → Bool)
    (t : ℕ) (a b : ℤ) (hw : b-a ≤ (2 : ℤ)^q) :
    (w2Search fuel reply t a b).2.length ≤ q := by
  induction q generalizing fuel t a b with
  | zero =>
      have hs : b ≤ a+1 := by simp only [pow_zero] at hw; omega
      cases fuel <;> simp [w2Search, hs]
  | succ q ih =>
      cases fuel with
      | zero => simp [w2Search]
      | succ fuel =>
          by_cases hs : b ≤ a+1
          · simp [w2Search, hs]
          · let c : ℤ := (a+b)/2
            have hp : (2 : ℤ)^(q+1) = 2*(2 : ℤ)^q := by ring
            rw [hp] at hw
            have hl : c-a ≤ (2 : ℤ)^q := by dsimp [c]; omega
            have hr : b-c ≤ (2 : ℤ)^q := by dsimp [c]; omega
            by_cases hf : reply t c
            · have hi := ih fuel (t+1) a c hl
              simp only [w2Search, ite_eq_right hs, show (a+b)/2 = c from rfl,
                ite_eq_left hf, List.length_cons]
              omega
            · have hi := ih fuel (t+1) c b hr
              simp only [w2Search, ite_eq_right hs, show (a+b)/2 = c from rfl,
                ite_eq_right hf, List.length_cons]
              omega

end SAP.P003a.WH.W2.P.T5_L2

theorem SAP.P003a.WH.W2.T5_L2_proof : SAP.P003a.WH.W2.T5_L2 := by
  intro k₁ k₂ hk reply
  let d : ℕ := (k₂-k₁+1).toNat
  have hd : 0 < d := by dsimp [d]; omega
  have hcast : (d : ℤ) = k₂-k₁+1 := by dsimp [d]; omega
  have hpN := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) d
  have hpN' : d+1 ≤ (2 : ℕ)^(Nat.log 2 d+1) := by omega
  have hp : (d : ℤ)+1 ≤ (2 : ℤ)^(Nat.log 2 d+1) := by exact_mod_cast hpN'
  have hw : (k₂+1)-(k₁-1) ≤ (2 : ℤ)^(Nat.log 2 d+1) := by
    have heq : (k₂+1)-(k₁-1) = (d : ℤ)+1 := by omega
    rw [heq]
    exact hp
  have hlen := SAP.P003a.WH.W2.P.T5_L2.w2Search_trace_length_le_pow
    (Nat.log 2 d+1) (d+1)
    reply 0 (k₁-1) (k₂+1) hw
  simp only [w2Queries, w2Run, List.length_map]
  simpa only [d] using hlen

