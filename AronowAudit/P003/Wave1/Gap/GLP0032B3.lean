import AronowAudit.P003.Wave1.Gap.GLP0032B1
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! Finite generating functions. The first exponent counts treated units;
the second counts their two potential-outcome bits. -/

abbrev bpm_Algebra := AddMonoidAlgebra ℝ (ℤ × ℤ)

noncomputable def bpm_monomial (i j : ℤ) : bpm_Algebra :=
  AddMonoidAlgebra.single (i,j) 1

@[simp] lemma bpm_monomial_mul (i j k l : ℤ) :
    bpm_monomial i j * bpm_monomial k l = bpm_monomial (i+k) (j+l) := by
  simp [bpm_monomial, AddMonoidAlgebra.single_mul_single]

@[simp] lemma bpm_monomial_zero : bpm_monomial 0 0 = 1 := rfl

@[simp] lemma bpm_monomial_coeff (i j k l : ℤ) :
    (bpm_monomial i j).coeff (k,l) = if i = k ∧ j = l then 1 else 0 := by
  simp [bpm_monomial, Finsupp.single_apply, Prod.ext_iff]

@[simp] lemma bpm_shift_coeff (i j : ℤ) (F : bpm_Algebra) (k l : ℤ) :
    (bpm_monomial i j * F).coeff (k,l) = F.coeff (k-i,l-j) := by
  simp [bpm_monomial, AddMonoidAlgebra.coeff_single_mul_apply, sub_eq_add_neg,
    add_comm]

noncomputable def bpm_unit (w : ℤ) : bpm_Algebra := 1 + bpm_monomial 1 w

noncomputable def bpm_population (a b z : ℕ) : bpm_Algebra :=
  bpm_unit 2 ^ a * bpm_unit 1 ^ b * bpm_unit 0 ^ z

noncomputable def bpm_mass (a b z m : ℕ) (k : ℤ) : ℝ :=
  (bpm_population a b z).coeff (m,(a : ℤ)+k)

noncomputable def bpm_degree (F : bpm_Algebra) : bpm_Algebra :=
  F.coeff.sum fun p r => AddMonoidAlgebra.single p ((p.1 : ℝ)*r)

@[simp] lemma bpm_degree_coeff (F : bpm_Algebra) (p : ℤ × ℤ) :
    (bpm_degree F).coeff p = (p.1 : ℝ)*F.coeff p := by
  simp only [bpm_degree, AddMonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single p]
  · simp
  · intro q hq hqp
    simp [hqp]
  · intro hp
    simp

@[simp] lemma bpm_degree_zero : bpm_degree 0 = 0 := by ext p; simp

@[simp] lemma bpm_degree_add (F G : bpm_Algebra) :
    bpm_degree (F+G) = bpm_degree F + bpm_degree G := by
  ext p
  simp [mul_add]

@[simp] lemma bpm_degree_smul (r : ℝ) (F : bpm_Algebra) :
    bpm_degree (r • F) = r • bpm_degree F := by
  ext p
  simp [mul_left_comm]

@[simp] lemma bpm_degree_single (p : ℤ × ℤ) (r : ℝ) :
    bpm_degree (AddMonoidAlgebra.single p r) =
      AddMonoidAlgebra.single p ((p.1 : ℝ)*r) := by
  ext q
  by_cases h : p = q
  · subst q; simp
  · simp [h]

lemma bpm_degree_shift (i j : ℤ) (F : bpm_Algebra) :
    bpm_degree (bpm_monomial i j * F) =
      (i : ℝ) • (bpm_monomial i j * F) + bpm_monomial i j * bpm_degree F := by
  ext ⟨k,l⟩
  simp only [bpm_degree_coeff, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, bpm_shift_coeff, Int.cast_sub]
  ring

lemma bpm_degree_mul (F G : bpm_Algebra) :
    bpm_degree (F*G) = bpm_degree F*G + F*bpm_degree G := by
  induction F using AddMonoidAlgebra.induction_on with
  | of p =>
    rcases p with ⟨i,j⟩
    change bpm_degree (bpm_monomial i j * G) =
      bpm_degree (bpm_monomial i j)*G + bpm_monomial i j*bpm_degree G
    rw [bpm_degree_shift]
    simp only [bpm_monomial, bpm_degree_single, mul_one]
    rw [← smul_mul_assoc, AddMonoidAlgebra.smul_single', mul_one]
  | add F H hF hH => simp only [add_mul, bpm_degree_add, hF, hH]; abel
  | smul r F hF => simp only [smul_mul_assoc, bpm_degree_smul, hF, smul_add]

@[simp] lemma bpm_degree_one : bpm_degree 1 = 0 := by
  change bpm_degree (AddMonoidAlgebra.single (0,0) 1) = 0
  simp

lemma bpm_degree_pow (F : bpm_Algebra) (r : ℕ) :
    bpm_degree (F^r) = (r : ℝ) • (F^(r-1)*bpm_degree F) := by
  cases r with
  | zero => simp
  | succ r =>
    simp only [Nat.add_sub_cancel]
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, bpm_degree_mul, ih]
      rw [smul_mul_assoc]
      have he : F^r * bpm_degree F * F = F^(r+1) * bpm_degree F := by
        rw [pow_succ]
        ring
      rw [he]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

noncomputable def bpm_binom (n : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k then (n.choose k.toNat : ℝ) else 0

lemma bpm_binom_nonneg (n : ℕ) (k : ℤ) : 0 ≤ bpm_binom n k := by
  unfold bpm_binom
  split_ifs <;> positivity

lemma bpm_binom_eq_zero (n : ℕ) (k : ℤ) (h : k < 0 ∨ (n : ℤ) < k) :
    bpm_binom n k = 0 := by
  rcases h with h | h
  · simp [bpm_binom, not_le.mpr h]
  · by_cases hk : 0 ≤ k
    · have hkn : n < k.toNat := by omega
      simp [bpm_binom, hk, Nat.choose_eq_zero_of_lt hkn]
    · simp [bpm_binom, hk]


lemma bpm_binom_symm (n : ℕ) (k : ℤ) : bpm_binom n ((n : ℤ)-k) = bpm_binom n k := by
  by_cases hk : 0 ≤ k ∧ k ≤ n
  · have hsub : ((n : ℤ)-k).toNat = n-k.toNat := by omega
    simp only [bpm_binom, if_pos hk.1, if_pos (show 0 ≤ (n : ℤ)-k by omega), hsub]
    exact_mod_cast Nat.choose_symm (show k.toNat ≤ n by omega)
  · rw [bpm_binom_eq_zero n k (by omega), bpm_binom_eq_zero n ((n : ℤ)-k) (by omega)]

lemma bpm_binom_right (n : ℕ) (k : ℤ) (hk : (n : ℤ) ≤ 2*k+1) :
    bpm_binom n (k+1) ≤ bpm_binom n k := by
  by_cases h0 : k < 0
  · omega
  · have hk0 : 0 ≤ k := by omega
    by_cases hkn : k < n
    · have hidx : (k+1).toNat = k.toNat+1 := by omega
      have hn : k.toNat ≤ n := by omega
      have hr := Nat.choose_succ_right_eq n k.toNat
      have hrR : (n.choose (k.toNat+1) : ℝ) * (k.toNat+1) =
          (n.choose k.toNat : ℝ)*(n-k.toNat) := by exact_mod_cast hr
      have hcomp : (n-k.toNat : ℝ) ≤ k.toNat+1 := by
        have hn' : n-k.toNat ≤ k.toNat+1 := by omega
        exact_mod_cast hn'
      have hpos : (0 : ℝ) < k.toNat+1 := by positivity
      have hb : (0 : ℝ) ≤ n.choose k.toNat := by positivity
      simp only [bpm_binom, if_pos hk0, if_pos (show 0 ≤ k+1 by omega), hidx]
      nlinarith
    · rw [bpm_binom_eq_zero n (k+1) (Or.inr (by omega))]
      exact bpm_binom_nonneg n k

lemma bpm_binom_left (n : ℕ) (k : ℤ) (hk : 2*k ≤ (n : ℤ)+1) :
    bpm_binom n (k-1) ≤ bpm_binom n k := by
  rw [← bpm_binom_symm n (k-1), ← bpm_binom_symm n k]
  convert bpm_binom_right n ((n : ℤ)-k) (by omega) using 1 <;> congr 1 <;> omega

lemma bpm_binom_right_back (n : ℕ) (k : ℤ) (hk : (n : ℤ)+1 ≤ 2*k) :
    bpm_binom n k ≤ bpm_binom n (k-1) := by
  convert bpm_binom_right n (k-1) (by omega) using 1 <;> congr 1 <;> omega

lemma bpm_binom_left_forward (n : ℕ) (k : ℤ) (hk : 2*k+1 ≤ (n : ℤ)) :
    bpm_binom n k ≤ bpm_binom n (k+1) := by
  convert bpm_binom_left n (k+1) (by omega) using 1 <;> congr 1 <;> omega

@[simp] lemma bpm_monomial_pow (i j : ℤ) (r : ℕ) :
    bpm_monomial i j ^ r = bpm_monomial ((r : ℤ)*i) ((r : ℤ)*j) := by
  induction r with
  | zero => simp
  | succ r ih => simp only [pow_succ, ih, bpm_monomial_mul, Nat.cast_add,
      Nat.cast_one]; congr 1 <;> ring

lemma bpm_unit_pow (w : ℤ) (n : ℕ) :
    bpm_unit w ^ n = ∑ i ∈ Finset.range (n+1),
      (n.choose i : ℝ) • bpm_monomial i ((i : ℤ)*w) := by
  rw [bpm_unit, add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one, bpm_monomial_pow, mul_one]
  rw [Algebra.smul_def]
  simp only [map_natCast]
  ring

lemma bpm_unit_pow_coeff (w : ℤ) (n : ℕ) (i j : ℤ) :
    (bpm_unit w ^ n).coeff (i,j) =
      if j = i*w then bpm_binom n i else 0 := by
  rw [bpm_unit_pow]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    bpm_monomial_coeff]
  by_cases hi : 0 ≤ i ∧ i ≤ n
  · have hn : i.toNat ∈ Finset.range (n+1) := by simp only [Finset.mem_range]; omega
    rw [Finset.sum_eq_single i.toNat]
    · have hc : (i.toNat : ℤ) = i := by omega
      simp [hc, bpm_binom, hi.1, eq_comm]
    · intro k hk hki
      have hc : (k : ℤ) ≠ i := by omega
      simp [hc]
    · exact fun h => (h hn).elim
  · rw [bpm_binom_eq_zero n i (by omega)]
    simp only [ite_self]
    apply Finset.sum_eq_zero
    intro k hk
    have hc : (k : ℤ) ≠ i := by simp only [Finset.mem_range] at hk; omega
    simp [hc]

lemma bpm_even_coeff (a z : ℕ) (m x : ℤ) :
    (bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff (m,2*x) =
      bpm_binom a x * bpm_binom z (m-x) := by
  rw [bpm_unit_pow]
  simp only [Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    smul_mul_assoc, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, bpm_shift_coeff, bpm_unit_pow_coeff, mul_zero]
  by_cases hx : 0 ≤ x ∧ x ≤ a
  · have hn : x.toNat ∈ Finset.range (a+1) := by simp only [Finset.mem_range]; omega
    rw [Finset.sum_eq_single x.toNat]
    · have hc : (x.toNat : ℤ) = x := by omega
      simp [hc, bpm_binom, hx.1, show 2*x-x*2 = 0 by ring]
    · intro i hi hix
      have hc : 2*x-(i : ℤ)*2 ≠ 0 := by omega
      simp [hc]
    · exact fun h => (h hn).elim
  · rw [bpm_binom_eq_zero a x (by omega), zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hc : 2*x-(i : ℤ)*2 ≠ 0 := by simp only [Finset.mem_range] at hi; omega
    simp [hc]

lemma bpm_odd_coeff (a z : ℕ) (m x : ℤ) :
    (bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff (m,2*x+1) = 0 := by
  rw [bpm_unit_pow]
  simp only [Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    smul_mul_assoc, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, bpm_shift_coeff, bpm_unit_pow_coeff, mul_zero]
  apply Finset.sum_eq_zero
  intro i hi
  have hc : 2*x+1-(i : ℤ)*2 ≠ 0 := by omega
  simp [hc]

def bpm_negEquiv : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun := fun p => -p
  invFun := fun p => -p
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add

noncomputable def bpm_flip : bpm_Algebra ≃+* bpm_Algebra :=
  AddMonoidAlgebra.mapDomainRingEquiv ℝ bpm_negEquiv

@[simp] lemma bpm_flip_coeff (F : bpm_Algebra) (i j : ℤ) :
    (bpm_flip F).coeff (i,j) = F.coeff (-i,-j) := by
  simp [bpm_flip, bpm_negEquiv]

@[simp] lemma bpm_flip_monomial (i j : ℤ) :
    bpm_flip (bpm_monomial i j) = bpm_monomial (-i) (-j) := by
  simp [bpm_flip, bpm_monomial, bpm_negEquiv]

lemma bpm_flip_unit (w : ℤ) :
    bpm_flip (bpm_unit w) = bpm_monomial (-1) (-w) * bpm_unit w := by
  simp [bpm_unit, mul_add, add_comm]

lemma bpm_population_flip (a b z : ℕ) :
    bpm_flip (bpm_population a b z) =
      bpm_monomial (-(a+b+z : ℕ)) (-(2*(a : ℤ)+b)) * bpm_population a b z := by
  simp only [bpm_population, map_mul, map_pow, bpm_flip_unit, mul_pow,
    bpm_monomial_pow]
  have he : bpm_monomial ((a : ℤ)*(-1)) ((a : ℤ)*(-2)) *
      bpm_monomial ((b : ℤ)*(-1)) ((b : ℤ)*(-1)) *
      bpm_monomial ((z : ℤ)*(-1)) ((z : ℤ)*(-0)) =
      bpm_monomial (-(a+b+z : ℕ)) (-(2*(a : ℤ)+b)) := by
    simp only [bpm_monomial_mul, Nat.cast_add]
    congr 1 <;> ring
  rw [← he]
  ring

lemma bpm_mass_symm (a b z m : ℕ) (hn : a+b+z = 2*m) (k : ℤ) :
    bpm_mass a b z m ((b : ℤ)-k) = bpm_mass a b z m k := by
  have he := congrArg (fun F : bpm_Algebra => F.coeff (-(m : ℤ),-((a : ℤ)+k)))
    (bpm_population_flip a b z)
  simp only [bpm_flip_coeff, neg_neg, bpm_shift_coeff] at he
  have hn' : ((a+b+z : ℕ) : ℤ) = 2*(m : ℤ) := by exact_mod_cast hn
  have hi : -(m : ℤ) - -((a+b+z : ℕ) : ℤ) = m := by omega
  have hj : -((a : ℤ)+k) - -(2*(a : ℤ)+b) = (a : ℤ)+(b-k) := by ring
  rw [hi,hj] at he
  exact he.symm

lemma bpm_mass_one_formula (a z m : ℕ) (k : ℤ) :
    bpm_mass a 1 z m k =
      (bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff (m,(a : ℤ)+k) +
      (bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff ((m : ℤ)-1,(a : ℤ)+k-1) := by
  have he : bpm_population a 1 z =
      bpm_unit 2 ^ a * bpm_unit 0 ^ z +
      bpm_monomial 1 1 * (bpm_unit 2 ^ a * bpm_unit 0 ^ z) := by
    simp only [bpm_population, pow_one, bpm_unit]
    ring
  simp only [bpm_mass, he, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    bpm_shift_coeff]

lemma bpm_mass_one_even (a z m : ℕ) (k x : ℤ) (hx : (a : ℤ)+k = 2*x) :
    bpm_mass a 1 z m k = bpm_binom a x * bpm_binom z ((m : ℤ)-x) := by
  rw [bpm_mass_one_formula, hx, bpm_even_coeff,
    show 2*x-1 = 2*(x-1)+1 by ring, bpm_odd_coeff, add_zero]

lemma bpm_mass_one_odd (a z m : ℕ) (k x : ℤ) (hx : (a : ℤ)+k = 2*x+1) :
    bpm_mass a 1 z m k = bpm_binom a x * bpm_binom z ((m : ℤ)-1-x) := by
  rw [bpm_mass_one_formula, hx, bpm_odd_coeff,
    show 2*x+1-1 = 2*x by ring, bpm_even_coeff, zero_add]

lemma bpm_shape_of_step (f : ℤ → ℝ) (c : ℤ)
    (hsym : ∀ k, f (c-k) = f k)
    (hstep : ∀ k, c ≤ 2*k → f (k+1) ≤ f k) : SDShape f c := by
  refine ⟨hsym, ?_⟩
  intro i j hi hij
  exact Int.leInduction (motive := fun j _ => f j ≤ f i) le_rfl
    (fun j hj ih => le_trans (hstep j (by omega)) ih) j hij

lemma bpm_shape_one (a z m : ℕ) (hn : a+1+z = 2*m) :
    SDShape (bpm_mass a 1 z m) 1 := by
  apply bpm_shape_of_step _ _ (bpm_mass_symm a 1 z m hn)
  intro k hk
  have hn' : (a : ℤ)+1+z = 2*(m : ℤ) := by exact_mod_cast hn
  let x : ℤ := ((a : ℤ)+k)/2
  by_cases heven : ((a : ℤ)+k)%2 = 0
  · have hx : (a : ℤ)+k = 2*x := by dsimp [x]; omega
    rw [bpm_mass_one_even a z m k x hx,
      bpm_mass_one_odd a z m (k+1) x (by omega)]
    have he : (m : ℤ)-1-x = (m : ℤ)-x-1 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (bpm_binom_left z ((m : ℤ)-x) (by omega)) (bpm_binom_nonneg a x)
  · have hx : (a : ℤ)+k = 2*x+1 := by dsimp [x]; omega
    rw [bpm_mass_one_odd a z m k x hx,
      bpm_mass_one_even a z m (k+1) (x+1) (by omega)]
    have he : (m : ℤ)-(x+1) = (m : ℤ)-1-x := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (bpm_binom_right a x (by omega))
      (bpm_binom_nonneg z _)

lemma bpm_mass_two_formula (a z m : ℕ) (k : ℤ) :
    bpm_mass a 2 z m k =
      (bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff (m,(a : ℤ)+k) +
      2*(bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff ((m : ℤ)-1,(a : ℤ)+k-1) +
      (bpm_unit 2 ^ a * bpm_unit 0 ^ z).coeff ((m : ℤ)-2,(a : ℤ)+k-2) := by
  have he : bpm_population a 2 z =
      bpm_unit 2 ^ a * bpm_unit 0 ^ z +
      bpm_monomial 1 1 * (bpm_unit 2 ^ a * bpm_unit 0 ^ z) +
      bpm_monomial 1 1 * (bpm_unit 2 ^ a * bpm_unit 0 ^ z) +
      bpm_monomial 2 2 * (bpm_unit 2 ^ a * bpm_unit 0 ^ z) := by
    have hmon : bpm_monomial 1 1 ^ 2 = bpm_monomial 2 2 := by
      rw [pow_two, bpm_monomial_mul]
      norm_num
    simp only [bpm_population, bpm_unit]
    rw [← hmon]
    ring
  simp only [bpm_mass, he, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    bpm_shift_coeff]
  ring

lemma bpm_mass_two_even (a z m : ℕ) (j x : ℤ) (hx : (a : ℤ)+j = 2*x) :
    bpm_mass a 2 z m (j+1) = 2*bpm_binom a x * bpm_binom z ((m : ℤ)-1-x) := by
  rw [bpm_mass_two_formula]
  rw [show (a : ℤ)+(j+1) = 2*x+1 by omega, bpm_odd_coeff,
    show 2*x+1-1 = 2*x by ring, bpm_even_coeff,
    show 2*x+1-2 = 2*(x-1)+1 by ring, bpm_odd_coeff]
  ring

lemma bpm_mass_two_odd (a z m : ℕ) (j x : ℤ) (hx : (a : ℤ)+j = 2*x+1) :
    bpm_mass a 2 z m (j+1) =
      bpm_binom a (x+1) * bpm_binom z ((m : ℤ)-1-x) +
      bpm_binom a x * bpm_binom z ((m : ℤ)-2-x) := by
  rw [bpm_mass_two_formula]
  rw [show (a : ℤ)+(j+1) = 2*(x+1) by omega, bpm_even_coeff,
    show 2*(x+1)-1 = 2*x+1 by ring, bpm_odd_coeff,
    show 2*(x+1)-2 = 2*x by ring, bpm_even_coeff]
  have he : (m : ℤ)-(x+1) = (m : ℤ)-1-x := by ring
  rw [he]
  ring

lemma bpm_shape_two (a z m : ℕ) (hn : a+2+z = 2*m) :
    SDShape (bpm_mass a 2 z m) 2 := by
  apply bpm_shape_of_step _ _ (bpm_mass_symm a 2 z m hn)
  intro k hk
  let j := k-1
  have hj : 0 ≤ j := by dsimp [j]; omega
  have hk' : k = j+1 := by dsimp [j]; omega
  rw [hk']
  have hn' : (a : ℤ)+2+z = 2*(m : ℤ) := by exact_mod_cast hn
  let x : ℤ := ((a : ℤ)+j)/2
  by_cases heven : ((a : ℤ)+j)%2 = 0
  · have hx : (a : ℤ)+j = 2*x := by dsimp [x]; omega
    rw [bpm_mass_two_even a z m j x hx,
      bpm_mass_two_odd a z m (j+1) x (by omega)]
    have h1 := mul_le_mul_of_nonneg_right (bpm_binom_right a x (by omega))
      (bpm_binom_nonneg z ((m : ℤ)-1-x))
    have h2 := mul_le_mul_of_nonneg_left
      (bpm_binom_left z ((m : ℤ)-1-x) (by omega)) (bpm_binom_nonneg a x)
    have he : (m : ℤ)-1-x-1 = (m : ℤ)-2-x := by ring
    rw [he] at h2
    linarith
  · have hx : (a : ℤ)+j = 2*x+1 := by dsimp [x]; omega
    rw [bpm_mass_two_odd a z m j x hx,
      bpm_mass_two_even a z m (j+1) (x+1) (by omega)]
    have h1 := mul_le_mul_of_nonneg_left
      (bpm_binom_left_forward z ((m : ℤ)-2-x) (by omega))
      (bpm_binom_nonneg a (x+1))
    have h2 := mul_le_mul_of_nonneg_right
      (bpm_binom_right_back a (x+1) (by omega))
      (bpm_binom_nonneg z ((m : ℤ)-2-x))
    have he1 : (m : ℤ)-2-x+1 = (m : ℤ)-1-x := by ring
    have he2 : (m : ℤ)-1-(x+1) = (m : ℤ)-2-x := by ring
    rw [he1] at h1
    rw [show x+1-1 = x by ring] at h2
    rw [he2]
    linarith

@[simp] lemma bpm_degree_unit (w : ℤ) : bpm_degree (bpm_unit w) = bpm_monomial 1 w := by
  simp [bpm_unit, bpm_monomial]

lemma bpm_degree_population (a b z : ℕ) :
    bpm_degree (bpm_population a b z) =
      (a : ℝ) • (bpm_monomial 1 2 * bpm_population (a-1) b z) +
      (b : ℝ) • (bpm_monomial 1 1 * bpm_population a (b-1) z) +
      (z : ℝ) • (bpm_monomial 1 0 * bpm_population a b (z-1)) := by
  simp only [bpm_population, bpm_degree_mul, bpm_degree_pow, bpm_degree_unit,
    Algebra.smul_def, add_mul]
  ring

lemma bpm_a_factor (a b z : ℕ) :
    (a : ℝ) • bpm_population a b z =
      (a : ℝ) • (bpm_unit 2 * bpm_population (a-1) b z) := by
  cases a with
  | zero => simp
  | succ a =>
    congr 1
    simp only [Nat.add_sub_cancel, bpm_population, pow_succ]
    ring

lemma bpm_b_factor (a b z : ℕ) :
    (b : ℝ) • bpm_population a b z =
      (b : ℝ) • (bpm_unit 1 * bpm_population a (b-1) z) := by
  cases b with
  | zero => simp
  | succ b =>
    congr 1
    simp only [Nat.add_sub_cancel, bpm_population, pow_succ]
    ring

lemma bpm_z_factor (a b z : ℕ) :
    (z : ℝ) • bpm_population a b z =
      (z : ℝ) • (bpm_unit 0 * bpm_population a b (z-1)) := by
  cases z with
  | zero => simp
  | succ z =>
    congr 1
    simp only [Nat.add_sub_cancel, bpm_population, pow_succ]
    ring

/- The coefficient of this identity at treatment size m, when the total is
2m, counts each assignment m times. The three terms on the right select
an opposite-arm partner of type 11, 10, or 00 for one distinguished 10. -/
lemma bpm_partner_identity (a b z : ℕ) :
    ((a+b+z : ℕ) : ℝ) • (bpm_monomial 1 1 * bpm_population a b z) +
      bpm_degree (bpm_population a b z) -
      bpm_monomial 1 1 * bpm_degree (bpm_population a b z) =
    (a : ℝ) • ((bpm_monomial 1 1 + bpm_monomial 1 2) * bpm_population (a-1) b z) +
      (b : ℝ) • ((2 : ℝ) • (bpm_monomial 1 1 * bpm_population a (b-1) z)) +
      (z : ℝ) • ((bpm_monomial 1 0 + bpm_monomial 1 1) * bpm_population a b (z-1)) := by
  have ha := congrArg (fun F : bpm_Algebra => bpm_monomial 1 1 * F) (bpm_a_factor a b z)
  have hb := congrArg (fun F : bpm_Algebra => bpm_monomial 1 1 * F) (bpm_b_factor a b z)
  have hz := congrArg (fun F : bpm_Algebra => bpm_monomial 1 1 * F) (bpm_z_factor a b z)
  simp only [mul_smul_comm] at ha hb hz
  simp only [Nat.cast_add, add_smul]
  rw [ha,hb,hz,bpm_degree_population]
  simp only [bpm_unit, Algebra.smul_def, map_ofNat]
  ring

lemma bpm_partner_recurrence (a b z m : ℕ) (hm : 0 < m)
    (hn : a+(b+1)+z = 2*m) (k : ℤ) :
    (m : ℝ)*bpm_mass a (b+1) z m k =
      (a : ℝ)*(bpm_mass (a-1) b z (m-1) k + bpm_mass (a-1) b z (m-1) (k-1)) +
      2*(b : ℝ)*bpm_mass a (b-1) z (m-1) (k-1) +
      (z : ℝ)*(bpm_mass a b (z-1) (m-1) k + bpm_mass a b (z-1) (m-1) (k-1)) := by
  have hmi : ((m-1 : ℕ) : ℤ) = (m : ℤ)-1 := by omega
  have he := congrArg (fun F : bpm_Algebra => F.coeff (m,(a : ℤ)+k))
    (bpm_partner_identity a b z)
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul, bpm_shift_coeff, bpm_degree_coeff,
    Int.cast_sub, Int.cast_natCast] at he
  have hp : bpm_population a (b+1) z =
      bpm_population a b z + bpm_monomial 1 1 * bpm_population a b z := by
    simp only [bpm_population, pow_succ, bpm_unit]
    ring
  have hfull : bpm_mass a (b+1) z m k =
      (bpm_population a b z).coeff (m,(a : ℤ)+k) +
      (bpm_population a b z).coeff ((m : ℤ)-1,(a : ℤ)+k-1) := by
    simp only [bpm_mass,hp,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,bpm_shift_coeff]
  have ha :
      (a : ℝ)*((bpm_monomial 1 1 + bpm_monomial 1 2)*bpm_population (a-1) b z).coeff
        (m,(a : ℤ)+k) =
      (a : ℝ)*(bpm_mass (a-1) b z (m-1) k + bpm_mass (a-1) b z (m-1) (k-1)) := by
    cases a with
    | zero => simp
    | succ a =>
      simp only [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        bpm_shift_coeff, bpm_mass, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hmi]
      rw [show (a : ℤ)+1+k-1 = (a : ℤ)+k by ring,
        show (a : ℤ)+1+k-2 = (a : ℤ)+(k-1) by ring]
  have hz :
      (z : ℝ)*((bpm_monomial 1 0 + bpm_monomial 1 1)*bpm_population a b (z-1)).coeff
        (m,(a : ℤ)+k) =
      (z : ℝ)*(bpm_mass a b (z-1) (m-1) k + bpm_mass a b (z-1) (m-1) (k-1)) := by
    simp only [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      bpm_shift_coeff, sub_zero, bpm_mass, hmi]
    rw [show (a : ℤ)+k-1 = (a : ℤ)+(k-1) by ring]
  rw [ha,hz] at he
  have hb : (bpm_population a (b-1) z).coeff ((m : ℤ)-1,(a : ℤ)+k-1) =
      bpm_mass a (b-1) z (m-1) (k-1) := by
    simp only [bpm_mass,hmi]
    rw [show (a : ℤ)+k-1 = (a : ℤ)+(k-1) by ring]
  rw [hb] at he
  rw [hfull]
  have hnR : ((a+b+z : ℕ) : ℝ) = 2*(m : ℝ)-1 := by
    have hnat : a+b+z+1 = 2*m := by omega
    have hreal : ((a+b+z : ℕ) : ℝ)+1 = 2*(m : ℝ) := by exact_mod_cast hnat
    linarith
  rw [hnR] at he
  norm_num only [Int.cast_one] at he
  nlinarith [he]

/- The bases b=1,2 above are the two parity calculations. For b≥3 each
partner-conditioned remainder retains positive discordance, so the fair
convolution lemma closes strong induction on the balanced arm size. -/
lemma bpm_positive_shape (m : ℕ) : ∀ a b z : ℕ, 0 < m → a+b+z = 2*m → 1 ≤ b →
    SDShape (bpm_mass a b z m) b := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a b z hm hn hd
    cases b with
    | zero => omega
    | succ b =>
      by_cases hb0 : b = 0
      · subst b
        exact bpm_shape_one a z m hn
      by_cases hb1 : b = 1
      · subst b
        exact bpm_shape_two a z m hn
      have hb : 2 ≤ b := by omega
      have hm2 : 2 ≤ m := by omega
      have hm' : 0 < m-1 := by omega
      have hlt : m-1 < m := by omega
      apply bpm_shape_of_step _ _ (bpm_mass_symm a (b+1) z m hn)
      intro k hk
      have hrec0 := bpm_partner_recurrence a b z m hm hn k
      have hrec1 := bpm_partner_recurrence a b z m hm hn (k+1)
      have ha :
          (a : ℝ)*(bpm_mass (a-1) b z (m-1) (k+1) + bpm_mass (a-1) b z (m-1) k) ≤
          (a : ℝ)*(bpm_mass (a-1) b z (m-1) k + bpm_mass (a-1) b z (m-1) (k-1)) := by
        by_cases ha0 : a = 0
        · simp [ha0]
        · have hf := ih (m-1) hlt (a-1) b z hm' (by omega) (by omega)
          have hs := (independent_convolution_shape _ b hf).2 k (k+1) (by omega) (by omega)
          simp only [smoothMass, show k+1-1 = k by ring] at hs
          exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg a)
      have hbmass := ih (m-1) hlt a (b-1) z hm' (by omega) (by omega)
      have hbcast : ((b-1 : ℕ) : ℤ) = (b : ℤ)-1 := by omega
      have hbs := hbmass.2 (k-1) k (by rw [hbcast]; omega) (by omega)
      have hbm := mul_le_mul_of_nonneg_left hbs (show 0 ≤ 2*(b : ℝ) by positivity)
      have hz :
          (z : ℝ)*(bpm_mass a b (z-1) (m-1) (k+1) + bpm_mass a b (z-1) (m-1) k) ≤
          (z : ℝ)*(bpm_mass a b (z-1) (m-1) k + bpm_mass a b (z-1) (m-1) (k-1)) := by
        by_cases hz0 : z = 0
        · simp [hz0]
        · have hf := ih (m-1) hlt a b (z-1) hm' (by omega) (by omega)
          have hs := (independent_convolution_shape _ b hf).2 k (k+1) (by omega) (by omega)
          simp only [smoothMass, show k+1-1 = k by ring] at hs
          exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg z)
      simp only [show k+1-1 = k by ring] at hrec1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      nlinarith

lemma bpm_slice_shape (a b z m : ℕ) (hm : 0 < m) (hn : a+b+z = 2*m) (hd : 1 ≤ b) :
    SDShape (fun k : ℤ => (bpm_population a b z).coeff (m,k)) (2*(a : ℤ)+b) := by
  have hf := bpm_positive_shape m a b z hm hn hd
  constructor
  · intro k
    have h := hf.1 (k-a)
    simp only [bpm_mass] at h
    convert h using 1 <;> congr 1 <;> omega
  · intro i j hi hij
    have h := hf.2 (i-a) (j-a) (by omega) (by omega)
    simpa only [bpm_mass, add_sub_cancel] using h

/-! Linear evaluation of finite generating functions; this also evaluates
tail indicators without infinite sums or probability infrastructure. -/

noncomputable def bpm_eval (F : bpm_Algebra) (f : ℤ × ℤ → ℝ) : ℝ :=
  F.coeff.sum fun p r => r*f p

@[simp] lemma bpm_eval_zero (f : ℤ × ℤ → ℝ) : bpm_eval 0 f = 0 := by simp [bpm_eval]

@[simp] lemma bpm_eval_single (p : ℤ × ℤ) (r : ℝ) (f : ℤ × ℤ → ℝ) :
    bpm_eval (AddMonoidAlgebra.single p r) f = r*f p := by simp [bpm_eval]

@[simp] lemma bpm_eval_monomial (i j : ℤ) (f : ℤ × ℤ → ℝ) :
    bpm_eval (bpm_monomial i j) f = f (i,j) := by simp [bpm_monomial]

@[simp] lemma bpm_eval_add (F G : bpm_Algebra) (f : ℤ × ℤ → ℝ) :
    bpm_eval (F+G) f = bpm_eval F f + bpm_eval G f := by
  simp [bpm_eval, Finsupp.sum_add_index', add_mul]

@[simp] lemma bpm_eval_smul (r : ℝ) (F : bpm_Algebra) (f : ℤ × ℤ → ℝ) :
    bpm_eval (r • F) f = r*bpm_eval F f := by
  simp [bpm_eval, Finsupp.sum_smul_index', mul_assoc, Finsupp.mul_sum]

@[simp] lemma bpm_eval_neg (F : bpm_Algebra) (f : ℤ × ℤ → ℝ) :
    bpm_eval (-F) f = -bpm_eval F f := by
  simpa only [neg_one_smul, neg_one_mul] using bpm_eval_smul (-1) F f

@[simp] lemma bpm_eval_sub (F G : bpm_Algebra) (f : ℤ × ℤ → ℝ) :
    bpm_eval (F-G) f = bpm_eval F f - bpm_eval G f := by simp [sub_eq_add_neg]

lemma bpm_eval_congr (F : bpm_Algebra) {f g : ℤ × ℤ → ℝ} (h : ∀ p, f p = g p) :
    bpm_eval F f = bpm_eval F g := by rw [show f = g from funext h]

lemma bpm_eval_add_fun (F : bpm_Algebra) (f g : ℤ × ℤ → ℝ) :
    bpm_eval F (fun p => f p+g p) = bpm_eval F f + bpm_eval F g := by
  simp [bpm_eval, mul_add, Finsupp.sum_add]

lemma bpm_eval_sub_fun (F : bpm_Algebra) (f g : ℤ × ℤ → ℝ) :
    bpm_eval F (fun p => f p-g p) = bpm_eval F f - bpm_eval F g := by
  simp [bpm_eval, mul_sub, Finsupp.sum_sub]

lemma bpm_eval_const_mul_fun (F : bpm_Algebra) (r : ℝ) (f : ℤ × ℤ → ℝ) :
    bpm_eval F (fun p => r*f p) = r*bpm_eval F f := by
  simp [bpm_eval, Finsupp.mul_sum, mul_left_comm]

lemma bpm_eval_shift (i j : ℤ) (F : bpm_Algebra) (f : ℤ × ℤ → ℝ) :
    bpm_eval (bpm_monomial i j * F) f = bpm_eval F (fun p => f (i+p.1,j+p.2)) := by
  induction F using AddMonoidAlgebra.induction_on with
  | of p =>
    rcases p with ⟨k,l⟩
    change bpm_eval (bpm_monomial i j * bpm_monomial k l) f =
      bpm_eval (bpm_monomial k l) _
    simp
  | add F G hF hG => simp only [mul_add,bpm_eval_add,hF,hG]
  | smul r F hF => simp only [mul_smul_comm,bpm_eval_smul,hF]

lemma bpm_eval_coeff (F : bpm_Algebra) (p : ℤ × ℤ) :
    bpm_eval F (fun q => if q = p then 1 else 0) = F.coeff p := by
  simp only [bpm_eval, mul_ite, mul_one, mul_zero]
  rw [Finsupp.sum_eq_single p]
  · simp
  · intro q hq hqp; simp [hqp]
  · intro hp; simp

noncomputable def bpm_second (F : bpm_Algebra) : bpm_Algebra :=
  bpm_monomial 1 0 * F + bpm_monomial 1 2 * F -
    (2 : ℝ) • (bpm_monomial 1 1 * F)

lemma bpm_upper_second (F : bpm_Algebra) (m H : ℤ) :
    bpm_eval (bpm_second F) (fun p => if p.1 = m ∧ H ≤ p.2 then 1 else 0) =
      F.coeff (m-1,H-2) - F.coeff (m-1,H-1) := by
  simp only [bpm_second, bpm_eval_sub, bpm_eval_add, bpm_eval_smul, bpm_eval_shift]
  rw [← bpm_eval_add_fun, ← bpm_eval_const_mul_fun, ← bpm_eval_sub_fun,
    ← bpm_eval_coeff F (m-1,H-2), ← bpm_eval_coeff F (m-1,H-1), ← bpm_eval_sub_fun]
  apply bpm_eval_congr
  rintro ⟨i,j⟩
  dsimp only
  simp only [Prod.mk.injEq]
  split_ifs <;> norm_num at * <;> omega

lemma bpm_lower_second (F : bpm_Algebra) (m L : ℤ) :
    bpm_eval (bpm_second F) (fun p => if p.1 = m ∧ p.2 ≤ L then 1 else 0) =
      F.coeff (m-1,L) - F.coeff (m-1,L-1) := by
  simp only [bpm_second, bpm_eval_sub, bpm_eval_add, bpm_eval_smul, bpm_eval_shift]
  rw [← bpm_eval_add_fun, ← bpm_eval_const_mul_fun, ← bpm_eval_sub_fun,
    ← bpm_eval_coeff F (m-1,L), ← bpm_eval_coeff F (m-1,L-1), ← bpm_eval_sub_fun]
  apply bpm_eval_congr
  rintro ⟨i,j⟩
  dsimp only
  simp only [Prod.mk.injEq]
  split_ifs <;> norm_num at * <;> omega

lemma bpm_abs_tail (W t x : ℤ) :
    |2*t-W| ≤ |2*x-W| ↔ max t (W-t) ≤ x ∨ x ≤ W-max t (W-t) := by
  by_cases ht : 0 ≤ 2*t-W
  · rw [max_eq_left (show W-t ≤ t by omega), abs_of_nonneg ht]
    by_cases hx : 0 ≤ 2*x-W
    · rw [abs_of_nonneg hx]; omega
    · rw [abs_of_neg (by omega : 2*x-W < 0)]; omega
  · rw [max_eq_right (show t ≤ W-t by omega), abs_of_neg (by omega : 2*t-W < 0)]
    by_cases hx : 0 ≤ 2*x-W
    · rw [abs_of_nonneg hx]; omega
    · rw [abs_of_neg (by omega : 2*x-W < 0)]; omega

lemma bpm_shape_boundary (f : ℤ → ℝ) (C H : ℤ) (hf : SDShape f C)
    (hH : C+2 < 2*H) : f (H-1) ≤ f (H-2) := by
  by_cases hr : C ≤ 2*(H-2)
  · exact hf.2 (H-2) (H-1) hr (by omega)
  · have he : C-(H-2) = H-1 := by omega
    rw [← he, hf.1]

lemma bpm_tail_second_nonneg (F : bpm_Algebra) (m W t : ℤ)
    (hf : SDShape (fun k : ℤ => F.coeff (m-1,k)) (W-2)) :
    0 ≤ bpm_eval (bpm_second F)
      (fun p => if p.1 = m ∧ |2*t-W| ≤ |2*p.2-W| then 1 else 0) := by
  by_cases ht : 2*t = W
  · have hz : 2*t-W = 0 := by omega
    simp only [hz, abs_zero, abs_nonneg, and_true]
    simp only [bpm_second,bpm_eval_sub,bpm_eval_add,bpm_eval_smul,bpm_eval_shift]
    ring_nf
    exact le_rfl
  · let H := max t (W-t)
    have hH : W < 2*H := by dsimp [H]; omega
    have he : (fun p : ℤ × ℤ =>
        if p.1 = m ∧ |2*t-W| ≤ |2*p.2-W| then (1 : ℝ) else 0) =
      (fun p : ℤ × ℤ => (if p.1 = m ∧ H ≤ p.2 then 1 else 0) +
        (if p.1 = m ∧ p.2 ≤ W-H then 1 else 0)) := by
      funext p
      simp only [bpm_abs_tail]
      change (if p.1 = m ∧ (H ≤ p.2 ∨ p.2 ≤ W-H) then (1 : ℝ) else 0) = _
      split_ifs <;> norm_num at * <;> omega
    rw [he,bpm_eval_add_fun,bpm_upper_second,bpm_lower_second]
    have hs0 := hf.1 (H-2)
    have hs1 := hf.1 (H-1)
    have hbound := bpm_shape_boundary _ (W-2) H hf (by omega)
    dsimp only at hs0 hs1 hbound
    rw [show W-2-(H-2) = W-H by ring] at hs0
    rw [show W-2-(H-1) = W-H-1 by ring] at hs1
    rw [hs0,hs1]
    linarith

lemma bpm_unit_pair_identity :
    bpm_unit 2 * bpm_unit 0 = bpm_unit 1 ^ 2 +
      bpm_monomial 1 0 + bpm_monomial 1 2 - (2 : ℝ) • bpm_monomial 1 1 := by
  have he : bpm_monomial 1 2 * bpm_monomial 1 0 = bpm_monomial 1 1 ^ 2 := by
    simp only [pow_two,bpm_monomial_mul]
    norm_num
  simp only [bpm_unit,Algebra.smul_def,map_ofNat]
  linear_combination he

/- Merging one 10/01 pair into 11/00 changes the generating function by
the second finite difference of the balanced remainder's mass. -/
lemma bpm_merge_identity (a b z : ℕ) :
    bpm_population (a+1) b (z+1) =
      bpm_population a (b+2) z + bpm_second (bpm_population a b z) := by
  have he : bpm_population (a+1) b (z+1) =
      (bpm_unit 2 * bpm_unit 0) * bpm_population a b z := by
    simp only [bpm_population,pow_succ]
    ring
  rw [he,bpm_unit_pair_identity]
  simp only [bpm_population,bpm_second,pow_add,Algebra.smul_def,map_ofNat]
  ring

lemma bpm_eval_sum {ι : Type*} (s : Finset ι) (F : ι → bpm_Algebra) (f : ℤ × ℤ → ℝ) :
    bpm_eval (∑ i ∈ s, F i) f = ∑ i ∈ s, bpm_eval (F i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

lemma bpm_prod_monomials {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℤ) :
    (∏ i ∈ s, bpm_monomial 1 (w i)) = bpm_monomial s.card (∑ i ∈ s, w i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, ih, bpm_monomial_mul,
      Finset.card_insert_of_notMem hi, Finset.sum_insert hi, Nat.cast_add,Nat.cast_one]
    congr 1
    omega

lemma bpm_generating_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℤ) :
    (∏ i, bpm_unit (w i)) =
      ∑ z : Finset ι, bpm_monomial z.card (∑ i ∈ z, w i) := by
  simp only [bpm_unit]
  rw [Finset.prod_one_add]
  simp only [bpm_prod_monomials]
  congr 1

def bpm_weight (t : Bool × Bool) : ℤ := (if t.1 then 1 else 0) + (if t.2 then 1 else 0)

lemma bpm_generating_table {n : ℕ} (w : PotentialTable n) :
    (∏ i, bpm_unit (bpm_weight (w i))) =
      bpm_population (tableCounts w).a ((tableCounts w).b+(tableCounts w).c) (tableCounts w).d := by
  have h := Finset.prod_fiberwise' (Finset.univ : Finset (Fin n)) w
    (fun t => bpm_unit (bpm_weight t))
  simpa [Finset.prod_const,Fintype.prod_prod_type,bpm_weight,tableCounts,bpm_population,
    pow_add,mul_comm,mul_left_comm,mul_assoc] using h.symm

lemma bpm_weight_sum {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) :
    (∑ i ∈ z, bpm_weight (w i)) =
      2*((neyman_treated w z).a : ℤ)+(neyman_treated w z).b+(neyman_treated w z).c := by
  have hweight (t : Bool × Bool) : bpm_weight t =
      (if t = (true,true) then (2 : ℤ) else 0) +
      (if t = (true,false) then 1 else 0) +
      (if t = (false,true) then 1 else 0) := by
    rcases t with ⟨a,b⟩
    cases a <;> cases b <;> decide
  simp_rw [hweight]
  simp [Finset.sum_add_distrib,Finset.sum_ite,neyman_treated,neyman_pack]
  ring

lemma bpm_eval_design (v : Counts) (m : ℕ) (E : ℤ → ℝ) :
    bpm_eval (bpm_population v.a (v.b+v.c) v.d)
      (fun p => if p.1 = m then E p.2 else 0) =
      ((randomStates v m).map fun q =>
        (multiplicity v q : ℝ)*E (2*(q.a : ℤ)+q.b+q.c)).sum := by
  obtain ⟨w,hw⟩ := neyman_exists_table v
  rw [← hw, ← bpm_generating_table, bpm_generating_expansion, bpm_eval_sum]
  simp only [bpm_eval_monomial]
  have hsub : (∑ z : Finset (Fin v.total),
      if (z.card : ℤ) = m then E (∑ i ∈ z, bpm_weight (w i)) else 0) =
      ∑ z : Assignment v.total m, E (∑ i ∈ z.val, bpm_weight (w i)) := by
    simp only [Nat.cast_inj]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hsub]
  simp_rw [bpm_weight_sum]
  simpa only [hw] using neyman_sum_pushforward w v hw m (fun q => E (2*(q.a : ℤ)+q.b+q.c))

lemma bpm_deviation_observed (v q : Counts) (m : ℕ) (hn : v.total = 2*m)
    (hq : q ∈ randomStates v m) :
    deviationNumerator v (observed v q) m = (m : ℤ)^2 *
      (2*(2*(q.a : ℤ)+q.b+q.c) - (2*(v.a : ℤ)+v.b+v.c)) := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  have hc' : ((v.a-q.a+v.c-q.c : ℕ) : ℤ) = (v.a : ℤ)-q.a+v.c-q.c := by
    rw [Nat.cast_sub (show q.c ≤ v.a-q.a+v.c by omega), Nat.cast_add, Nat.cast_sub ha]
  have hn' : (v.total : ℤ) = 2*(m : ℤ) := by exact_mod_cast hn
  simp only [deviationNumerator,observed,Counts.effect,Nat.cast_add]
  rw [hn',hc']
  ring

lemma bpm_deviation_data (v o : Counts) (m : ℕ) (hn : v.total = 2*m) :
    deviationNumerator v o m = (m : ℤ)^2 *
      (2*((o.a : ℤ)-o.c) - v.effect) := by
  have hn' : (v.total : ℤ) = 2*(m : ℤ) := by exact_mod_cast hn
  simp only [deviationNumerator,hn']
  ring

lemma bpm_tail_indicator (v o q : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    (deviationNumerator v o m).natAbs ≤ (deviationNumerator v (observed v q) m).natAbs ↔
      |2*((o.a : ℤ)-o.c)-v.effect| ≤
        |2*(2*(q.a : ℤ)+q.b+q.c)-(2*(v.a : ℤ)+v.b+v.c)| := by
  rw [bpm_deviation_observed v q m hn hq,bpm_deviation_data v o m hn,
    Int.natAbs_mul,Int.natAbs_mul]
  have hp : 0 < ((m : ℤ)^2).natAbs := by
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    exact Int.natAbs_pos.mpr (pow_ne_zero _ hm')
  rw [mul_le_mul_iff_right₀ hp]
  rw [← Nat.cast_le (α := ℤ),Int.natCast_natAbs,Int.natCast_natAbs]

lemma bpm_tailCount_eval (v o : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hom : o.a+o.b = m) :
    (tailCount v o : ℝ) = bpm_eval (bpm_population v.a (v.b+v.c) v.d)
      (fun p => if p.1 = m ∧
        |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*p.2-(2*(v.a : ℤ)+v.b+v.c)| then 1 else 0) := by
  have he : (fun p : ℤ × ℤ => if p.1 = m ∧
      |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*p.2-(2*(v.a : ℤ)+v.b+v.c)| then (1 : ℝ) else 0) =
      (fun p : ℤ × ℤ => if p.1 = m then
        (if |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*p.2-(2*(v.a : ℤ)+v.b+v.c)| then 1 else 0) else 0) := by
    funext p
    split_ifs <;> simp_all
  rw [he,bpm_eval_design v m
    (fun x => if |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*x-(2*(v.a : ℤ)+v.b+v.c)| then 1 else 0)]
  simp only [tailCount,hom,Nat.cast_list_sum,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  have hiff := bpm_tail_indicator v o q m hm hn hq
  simp only [ge_iff_le] at *
  simp only [hiff]
  split_ifs <;> simp

/-- The exact count-vector version of the balanced two-unit comparison. -/
theorem balanced_pvalue_monotonicity_proof (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hn : v.total = o.total)
    (hmin : 1 ≤ min v.b v.c) (hmax : 2 ≤ max v.b v.c) :
    pValue ⟨v.a+1,v.b-1,v.c-1,v.d+1⟩ o ≥ pValue v o := by
  let m := o.a+o.b
  let r := v.b+v.c-2
  let v' : Counts := ⟨v.a+1,v.b-1,v.c-1,v.d+1⟩
  have hb : 1 ≤ v.b := by omega
  have hc : 1 ≤ v.c := by omega
  have hdisc : 3 ≤ v.b+v.c := by omega
  have hm : 0 < m := ho.1
  have hsize : v.total = 2*m := by
    rw [hn]
    dsimp [m,Counts.total]
    omega
  have hvsize : v.a+v.b+v.c+v.d = 2*m := hsize
  have hres : r+2 = v.b+v.c := by dsimp [r]; omega
  have hres' : (v.b-1)+(v.c-1) = r := by dsimp [r]; omega
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hm2 : 2 ≤ m := by omega
  have hm' : 0 < m-1 := by omega
  have hremain : v.a+r+v.d = 2*(m-1) := by omega
  have hsize' : v'.total = 2*m := by
    dsimp [v',Counts.total]
    omega
  let W : ℤ := 2*(v.a : ℤ)+v.b+v.c
  let t : ℤ := (o.a : ℤ)-o.c+v.a+v.c
  have htheta : |2*((o.a : ℤ)-o.c)-v.effect| = |2*t-W| := by
    congr 1
    dsimp [t,W,Counts.effect]
    ring
  have heffect : v'.effect = v.effect := by
    dsimp [v',Counts.effect]
    rw [Nat.cast_sub hb,Nat.cast_sub hc]
    ring
  have hW' : 2*(v'.a : ℤ)+v'.b+v'.c = W := by
    dsimp [v',W]
    rw [Nat.cast_sub hb,Nat.cast_sub hc]
    push_cast
    ring
  have hpoly : bpm_population v'.a (v'.b+v'.c) v'.d =
      bpm_population v.a (r+2) v.d + bpm_second (bpm_population v.a r v.d) := by
    change bpm_population (v.a+1) ((v.b-1)+(v.c-1)) (v.d+1) = _
    rw [hres']
    exact bpm_merge_identity v.a r v.d
  have hold := bpm_tailCount_eval v o m hm hsize rfl
  have hnew := bpm_tailCount_eval v' o m hm hsize' rfl
  simp only [htheta] at hold
  simp only [heffect,hW',htheta] at hnew
  rw [← hres] at hold
  change (tailCount v o : ℝ) = bpm_eval (bpm_population v.a (r+2) v.d)
    (fun p => if p.1 = m ∧ |2*t-W| ≤ |2*p.2-W| then 1 else 0) at hold
  rw [hpoly,bpm_eval_add] at hnew
  have hmcast : ((m-1 : ℕ) : ℤ) = (m : ℤ)-1 := by omega
  have hW2 : W-2 = 2*(v.a : ℤ)+r := by dsimp [W]; omega
  have hshape := bpm_slice_shape v.a r v.d (m-1) hm' hremain hr
  have hshape' : SDShape (fun k : ℤ =>
      (bpm_population v.a r v.d).coeff ((m : ℤ)-1,k)) (W-2) := by
    simpa only [hmcast,hW2] using hshape
  have hnonneg := bpm_tail_second_nonneg (bpm_population v.a r v.d) m W t hshape'
  have hcountsR : (tailCount v o : ℝ) ≤ tailCount v' o := by
    rw [hold,hnew]
    exact le_add_of_nonneg_right hnonneg
  have hcounts : tailCount v o ≤ tailCount v' o := by exact_mod_cast hcountsR
  change pValue v o ≤ pValue v' o
  have htotal : v'.total = v.total := by omega
  simp only [pValue,htotal]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcounts) (by positivity)

end AronowAudit.P003.Wave1
