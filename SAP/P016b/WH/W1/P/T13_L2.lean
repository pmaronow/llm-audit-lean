import SAP.P016b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b.WH.W1.P.T13_L2

open SAP.P016b.WH.W1
open scoped Classical

theorem boundsPow_sound (hL1 : IntervalArithmeticSound)
    (scale : ℕ) (a : NatBounds) (x : ℝ) (n : ℕ) (hs : 0 < scale)
    (ha : Encloses scale a x) :
    Encloses scale (boundsPow scale a n) (x ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [boundsPow, boundsOne, Encloses]
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        let k := n / 2
        have hk : k < n := by
          dsimp [k]
          exact Nat.div_lt_self hpos (by decide)
        have hh := ih k hk
        have hsq := hL1.2.1 scale (boundsPow scale a k) (boundsPow scale a k)
          (x ^ k) (x ^ k) hs hh hh
        have hsq' : Encloses scale (boundsMul scale (boundsPow scale a k)
            (boundsPow scale a k)) (x ^ (2*k)) := by
          have hp : x^k*x^k = x^(2*k) := by
            calc
              x^k*x^k = x^(k+k) := by rw [← pow_add]
              _ = x^(2*k) := by congr 1; omega
          simpa only [hp] using hsq
        have hnmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rw [boundsPow]
        simp only [hn, ↓reduceDIte]
        split
        · rcases hnmod with hmod | hmod
          · have hnEq : n = 2*k := by dsimp [k]; omega
            simpa [hnEq] using hsq'
          · omega
        · rcases hnmod with hmod | hmod
          · omega
          · have hnEq : n = 2*k+1 := by omega
            have hdiv : (2*k+1)/2 = k := by omega
            have hmul := hL1.2.1 scale
              (boundsMul scale (boundsPow scale a k) (boundsPow scale a k)) a
              (x ^ (2*k)) x hs hsq' ha
            have hmul' : Encloses scale
                (boundsMul scale (boundsMul scale (boundsPow scale a k)
                  (boundsPow scale a k)) a) (x ^ (2*k+1)) := by
              simpa only [pow_succ] using hmul
            simpa [hnEq, hdiv] using hmul'

theorem boundsPowersFrom_sound (hL1 : IntervalArithmeticSound)
    (scale : ℕ) (a seed : NatBounds) (x y : ℝ) (count : ℕ) (hs : 0 < scale)
    (ha : Encloses scale a x) (hseed : Encloses scale seed y) :
    List.Forall₂ (Encloses scale) (boundsPowersFrom scale a seed count)
      ((List.range count).map fun j => y*x^j) := by
  induction count generalizing seed y with
  | zero => simp [boundsPowersFrom]
  | succ count ih =>
      rw [boundsPowersFrom]
      have hnext := hL1.2.1 scale seed a y x hs hseed ha
      have htail := ih (boundsMul scale seed a) (y*x) hnext
      have hrange : List.range (count+1) = 0 :: (List.range count).map Nat.succ :=
        List.range_succ_eq_map
      rw [hrange]
      simp only [List.map_cons, List.map_map]
      apply List.Forall₂.cons
      · simpa using hseed
      · change List.Forall₂ (Encloses scale)
          (boundsPowersFrom scale a (boundsMul scale seed a) count)
          (List.map (fun j => y*x^(Nat.succ j)) (List.range count))
        simpa [pow_succ', mul_assoc] using htail

end SAP.P016b.WH.W1.P.T13_L2

theorem SAP.P016b.WH.W1.T13_L2_proof : SAP.P016b.WH.W1.T13_L2 := by
  intro hL1
  constructor
  · intro scale a x n hs ha
    exact SAP.P016b.WH.W1.P.T13_L2.boundsPow_sound hL1 scale a x n hs ha
  · intro scale a seed x y count hs ha hseed
    exact SAP.P016b.WH.W1.P.T13_L2.boundsPowersFrom_sound hL1 scale a seed x y count hs ha hseed
