import SAP.P016b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b.WH.W1.P.T13_L1

open SAP.P016b.WH.W1
open scoped BigOperators

theorem nat_floor_quotient_le (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  have hn : n / d * d ≤ n := Nat.div_mul_le_self n d
  have hn' : ((n / d : ℕ) : ℝ) * (d : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact (le_div_iff₀ hd').2 (by simpa [Nat.cast_mul, mul_comm] using hn')

theorem nat_ceil_quotient_ge (n d : ℕ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ (((n + d - 1) / d : ℕ) : ℝ) := by
  let q : ℕ := (n + d - 1) / d
  have hlt : n + d - 1 < d * ((n + d - 1) / d + 1) :=
    Nat.lt_mul_div_succ (n + d - 1) hd
  have hlt' : n + d - 1 < ((n + d - 1) / d) * d + d := by
    simpa [Nat.mul_add, Nat.mul_comm] using hlt
  have hnle : n ≤ n + d - 1 := by omega
  have hn : n ≤ q * d := by dsimp [q]; omega
  have hn' : (n : ℝ) ≤ (q : ℝ) * (d : ℝ) := by exact_mod_cast hn
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hq : (n : ℝ) / (d : ℝ) ≤ (q : ℝ) :=
    (div_le_iff₀ hd').2 (by simpa [mul_comm] using hn')
  simpa [q] using hq

theorem encloses_nonneg {scale : ℕ} {a : NatBounds} {x : ℝ}
    (hs : 0 < scale) (h : Encloses scale a x) : 0 ≤ x := by
  have hs' : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hs
  have h0 : (0 : ℝ) ≤ (scale : ℝ) * x :=
    le_trans (Nat.cast_nonneg a.lo) h.1
  apply le_of_mul_le_mul_left (by simpa using h0) hs'

theorem ratio_sound (scale num den : ℕ) (hs : 0 < scale)
    (hd : 0 < den) :
    Encloses scale (boundsRatio scale num den) ((num : ℝ) / den) := by
  have hden : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have hscale : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hs
  have hlo := nat_floor_quotient_le (num * scale) den hd
  have hhi := nat_ceil_quotient_ge (num * scale) den hd
  constructor
  · change ((num * scale / den : ℕ) : ℝ) ≤ (scale : ℝ) * ((num : ℝ) / den)
    calc
      ((num * scale / den : ℕ) : ℝ) ≤ ((num * scale : ℕ) : ℝ) / (den : ℝ) := hlo
      _ = (scale : ℝ) * ((num : ℝ) / den) := by
        push_cast
        field_simp
  · change (scale : ℝ) * ((num : ℝ) / den) ≤
      (((num * scale + den - 1) / den : ℕ) : ℝ)
    calc
      (scale : ℝ) * ((num : ℝ) / den) = ((num * scale : ℕ) : ℝ) / (den : ℝ) := by
        push_cast
        field_simp
      _ ≤ (((num * scale + den - 1) / den : ℕ) : ℝ) := hhi

theorem mul_sound (scale : ℕ) (a b : NatBounds) (x y : ℝ)
    (hs : 0 < scale) (ha : Encloses scale a x) (hb : Encloses scale b y) :
    Encloses scale (boundsMul scale a b) (x * y) := by
  have hs' : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hs
  have hx0 : 0 ≤ x := encloses_nonneg hs ha
  have hy0 : 0 ≤ y := encloses_nonneg hs hb
  have hxlo : (a.lo : ℝ) ≤ (scale : ℝ) * x := ha.1
  have hylo : (b.lo : ℝ) ≤ (scale : ℝ) * y := hb.1
  have hxhi : (scale : ℝ) * x ≤ (a.hi : ℝ) := ha.2
  have hyhi : (scale : ℝ) * y ≤ (b.hi : ℝ) := hb.2
  have hprodlo : (a.lo : ℝ) * (b.lo : ℝ) ≤
      (scale : ℝ) * (scale : ℝ) * (x * y) := by
    calc
      (a.lo : ℝ) * (b.lo : ℝ) ≤ ((scale : ℝ) * x) * ((scale : ℝ) * y) :=
        mul_le_mul hxlo hylo (Nat.cast_nonneg b.lo)
          (mul_nonneg (le_of_lt hs') hx0)
      _ = (scale : ℝ) * (scale : ℝ) * (x * y) := by ring
  have hprodhi : (scale : ℝ) * (scale : ℝ) * (x * y) ≤
      (a.hi : ℝ) * (b.hi : ℝ) := by
    calc
      (scale : ℝ) * (scale : ℝ) * (x * y) =
          ((scale : ℝ) * x) * ((scale : ℝ) * y) := by ring
      _ ≤ (a.hi : ℝ) * (b.hi : ℝ) :=
        mul_le_mul hxhi hyhi (mul_nonneg (le_of_lt hs') hy0)
          (Nat.cast_nonneg a.hi)
  have hfloor := nat_floor_quotient_le (a.lo * b.lo) scale hs
  have hceil := nat_ceil_quotient_ge (a.hi * b.hi) scale hs
  constructor
  · change ((a.lo * b.lo / scale : ℕ) : ℝ) ≤ (scale : ℝ) * (x * y)
    calc
      ((a.lo * b.lo / scale : ℕ) : ℝ) ≤ ((a.lo * b.lo : ℕ) : ℝ) / (scale : ℝ) := hfloor
      _ ≤ (scale : ℝ) * (x * y) := (div_le_iff₀ hs').2 (by
        simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hprodlo)
  · change (scale : ℝ) * (x * y) ≤
      (((a.hi * b.hi + scale - 1) / scale : ℕ) : ℝ)
    calc
      (scale : ℝ) * (x * y) ≤ ((a.hi * b.hi : ℕ) : ℝ) / (scale : ℝ) :=
        (le_div_iff₀ hs').2 (by
          simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hprodhi)
      _ ≤ (((a.hi * b.hi + scale - 1) / scale : ℕ) : ℝ) := hceil

theorem natMul_sound (scale n : ℕ) (a : NatBounds) (x : ℝ)
    (hs : 0 < scale) (ha : Encloses scale a x) :
    Encloses scale (boundsNatMul n a) ((n : ℝ) * x) := by
  constructor
  · change ((n * a.lo : ℕ) : ℝ) ≤ (scale : ℝ) * ((n : ℝ) * x)
    calc
      ((n * a.lo : ℕ) : ℝ) = (n : ℝ) * (a.lo : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) * ((scale : ℝ) * x) :=
        mul_le_mul_of_nonneg_left ha.1 (Nat.cast_nonneg n)
      _ = (scale : ℝ) * ((n : ℝ) * x) := by ring
  · change (scale : ℝ) * ((n : ℝ) * x) ≤ ((n * a.hi : ℕ) : ℝ)
    calc
      (scale : ℝ) * ((n : ℝ) * x) = (n : ℝ) * ((scale : ℝ) * x) := by ring
      _ ≤ (n : ℝ) * (a.hi : ℝ) :=
        mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg n)
      _ = ((n * a.hi : ℕ) : ℝ) := by push_cast; ring

theorem foldl_boundsAdd (init : NatBounds) (as : List NatBounds) :
    as.foldl boundsAdd init = boundsAdd init (boundsSum as) := by
  change List.foldl boundsAdd init as =
    boundsAdd init (List.foldl boundsAdd boundsZero as)
  induction as generalizing init with
  | nil => simp [boundsZero, boundsAdd]
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih (boundsAdd init a)]
      have hz : boundsAdd boundsZero a = a := by
        cases a <;> simp [boundsAdd, boundsZero]
      rw [hz, ih a]
      cases init with
      | mk il ih =>
        cases a with
        | mk al ah =>
          cases List.foldl boundsAdd boundsZero as with
          | mk sl sh => simp [boundsAdd, Nat.add_assoc]

theorem sum_sound (scale : ℕ) (as : List NatBounds) (xs : List ℝ)
    (hs : 0 < scale) (h : List.Forall₂ (Encloses scale) as xs) :
    Encloses scale (boundsSum as) xs.sum := by
  induction h with
  | nil => simp [Encloses, boundsSum, boundsZero]
  | @cons a x as xs ha htail ih =>
      rw [show boundsSum (a :: as) = boundsAdd a (boundsSum as) by
        change List.foldl boundsAdd (boundsAdd boundsZero a) as =
          boundsAdd a (List.foldl boundsAdd boundsZero as)
        rw [show boundsAdd boundsZero a = a by
          cases a <;> simp [boundsAdd, boundsZero]]
        exact foldl_boundsAdd a as]
      rcases ha with ⟨hal, hau⟩
      rcases ih with ⟨ihl, ihu⟩
      constructor
      · change ((a.lo + (boundsSum as).lo : ℕ) : ℝ) ≤
          (scale : ℝ) * (x + xs.sum)
        calc
          ((a.lo + (boundsSum as).lo : ℕ) : ℝ) =
              (a.lo : ℝ) + ((boundsSum as).lo : ℝ) := by push_cast; rfl
          _ ≤ (scale : ℝ) * x + (scale : ℝ) * xs.sum := add_le_add hal ihl
          _ = (scale : ℝ) * (x + xs.sum) := by ring
      · change (scale : ℝ) * (x + xs.sum) ≤
          ((a.hi + (boundsSum as).hi : ℕ) : ℝ)
        calc
          (scale : ℝ) * (x + xs.sum) =
              (scale : ℝ) * x + (scale : ℝ) * xs.sum := by ring
          _ ≤ (a.hi : ℝ) + ((boundsSum as).hi : ℝ) := add_le_add hau ihu
          _ = ((a.hi + (boundsSum as).hi : ℕ) : ℝ) := by push_cast; rfl

theorem rescale_sound (scale outScale : ℕ) (a : NatBounds) (x : ℝ)
    (hs : 0 < scale) (ho : 0 < outScale) (ha : Encloses scale a x) :
    Encloses outScale (boundsRescale scale outScale a) x := by
  have hs' : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hs
  have ho' : (0 : ℝ) < (outScale : ℝ) := by exact_mod_cast ho
  have hlo := nat_floor_quotient_le (a.lo * outScale) scale hs
  have hhi := nat_ceil_quotient_ge (a.hi * outScale) scale hs
  constructor
  · change ((a.lo * outScale / scale : ℕ) : ℝ) ≤ (outScale : ℝ) * x
    calc
      ((a.lo * outScale / scale : ℕ) : ℝ) ≤
          ((a.lo * outScale : ℕ) : ℝ) / (scale : ℝ) := hlo
      _ ≤ (outScale : ℝ) * x := (div_le_iff₀ hs').2 (by
        have h := mul_le_mul_of_nonneg_right ha.1 (le_of_lt ho')
        simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h)
  · change (outScale : ℝ) * x ≤
      (((a.hi * outScale + scale - 1) / scale : ℕ) : ℝ)
    calc
      (outScale : ℝ) * x ≤ ((a.hi * outScale : ℕ) : ℝ) / (scale : ℝ) :=
        (le_div_iff₀ hs').2 (by
          have h := mul_le_mul_of_nonneg_right ha.2 (le_of_lt ho')
          simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h)
      _ ≤ (((a.hi * outScale + scale - 1) / scale : ℕ) : ℝ) := hhi

end SAP.P016b.WH.W1.P.T13_L1

theorem SAP.P016b.WH.W1.T13_L1_proof : SAP.P016b.WH.W1.T13_L1 := by
  change SAP.P016b.WH.W1.IntervalArithmeticSound
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact SAP.P016b.WH.W1.P.T13_L1.ratio_sound
  · exact SAP.P016b.WH.W1.P.T13_L1.mul_sound
  · exact SAP.P016b.WH.W1.P.T13_L1.natMul_sound
  · exact SAP.P016b.WH.W1.P.T13_L1.sum_sound
  · exact SAP.P016b.WH.W1.P.T13_L1.rescale_sound
