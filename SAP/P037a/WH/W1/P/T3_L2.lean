import SAP.P037a.WH.W1.Leaves
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T3_L2

open Set

private lemma iteratedDeriv_exp_neg (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Real.exp (-x)) =
      fun x => (-1 : ℝ) ^ n * Real.exp (-x) := by
  have hfun : (fun x : ℝ => Real.exp (-x)) = fun x => Real.exp ((-1 : ℝ) * x) := by
    funext x
    congr 1
    ring
  rw [hfun, iteratedDeriv_exp_const_mul]
  funext x
  simp

private lemma taylor_polynomial_eq (n : ℕ) (u : ℝ) (hu : 0 < u) :
    taylorWithinEval (fun x : ℝ => Real.exp (-x)) n (Set.Icc 0 u) 0 u =
      SAP.P037a.WH.W1.expTaylor n u := by
  have hs : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) u) := uniqueDiffOn_Icc hu
  rw [taylor_within_apply]
  unfold SAP.P037a.WH.W1.expTaylor
  apply Finset.sum_congr rfl
  intro k hk
  have hcont : ContDiff ℝ k (fun x : ℝ => Real.exp (-x)) := by fun_prop
  have hderiv : iteratedDerivWithin k (fun x : ℝ => Real.exp (-x)) (Set.Icc 0 u) 0 =
      (-1 : ℝ) ^ k := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hcont.contDiffAt)
      (show (0 : ℝ) ∈ Set.Icc 0 u from ⟨le_rfl, le_of_lt hu⟩)]
    rw [iteratedDeriv_exp_neg]
    simp
  rw [hderiv, sub_zero, smul_eq_mul]
  rw [div_eq_mul_inv]
  calc
    ((↑(k.factorial) : ℝ)⁻¹ * u ^ k) * (-1 : ℝ) ^ k =
        ((-1 : ℝ) ^ k * u ^ k) * (↑(k.factorial) : ℝ)⁻¹ := by ring
    _ = (-u) ^ k / k.factorial := by
      rw [← mul_pow, div_eq_mul_inv]
      simp only [neg_one_mul]

private lemma taylor_remainder25 (u : ℝ) (hu : 0 < u) :
    SAP.P037a.WH.W1.expTaylor 25 u ≤ Real.exp (-u) := by
  let f : ℝ → ℝ := fun x => Real.exp (-x)
  have hrem := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := u) (x₀ := 0) (n := 25) (by linarith)
    (by dsimp [f]; fun_prop)
  rcases hrem with ⟨x', hx', hTaylor⟩
  have hderiv : iteratedDeriv 26 f x' = Real.exp (-x') := by
    dsimp [f]
    rw [iteratedDeriv_exp_neg]
    norm_num
  have herror : 0 ≤ iteratedDeriv 26 f x' * (u - 0) ^ 26 / (Nat.factorial 26 : ℝ) := by
    rw [hderiv]
    positivity
  have hdiff : 0 ≤ Real.exp (-u) - SAP.P037a.WH.W1.expTaylor 25 u := by
    have hlocal : 0 ≤ f u - taylorWithinEval f 25 (uIcc 0 u) 0 u := by
      rw [hTaylor]
      exact herror
    have hpoly := taylor_polynomial_eq 25 u hu
    simpa only [f, uIcc_of_lt hu, hpoly] using hlocal
  linarith

private lemma taylor_remainder24 (u : ℝ) (hu : 0 < u) :
    Real.exp (-u) ≤ SAP.P037a.WH.W1.expTaylor 24 u := by
  let f : ℝ → ℝ := fun x => Real.exp (-x)
  have hrem := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := u) (x₀ := 0) (n := 24) (by linarith)
    (by dsimp [f]; fun_prop)
  rcases hrem with ⟨x', hx', hTaylor⟩
  have hderiv : iteratedDeriv 25 f x' = -Real.exp (-x') := by
    dsimp [f]
    rw [iteratedDeriv_exp_neg]
    norm_num
  have herror : iteratedDeriv 25 f x' * (u - 0) ^ 25 / (Nat.factorial 25 : ℝ) ≤ 0 := by
    rw [hderiv]
    have hp : 0 ≤ Real.exp (-x') * (u - 0) ^ 25 / (Nat.factorial 25 : ℝ) := by positivity
    nlinarith
  have hdiff : Real.exp (-u) - SAP.P037a.WH.W1.expTaylor 24 u ≤ 0 := by
    have hlocal : f u - taylorWithinEval f 24 (uIcc 0 u) 0 u ≤ 0 := by
      rw [hTaylor]
      exact herror
    have hpoly := taylor_polynomial_eq 24 u hu
    simpa only [f, uIcc_of_lt hu, hpoly] using hlocal
  linarith

end SAP.P037a.WH.W1.P.T3_L2

theorem SAP.P037a.WH.W1.T3_L2_proof : SAP.P037a.WH.W1.T3_L2 := by
  intro u hu
  by_cases hzero : u = 0
  · subst u
    have hexp : ∀ d : ℕ, SAP.P037a.WH.W1.expTaylor d (0 : ℝ) = 1 := by
      intro d
      unfold SAP.P037a.WH.W1.expTaylor
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        rw [neg_zero, zero_pow (Nat.ne_of_gt hkpos), zero_div]
      · simp
    constructor <;> simp [hexp]
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hzero)
    exact ⟨SAP.P037a.WH.W1.P.T3_L2.taylor_remainder25 u hu',
      SAP.P037a.WH.W1.P.T3_L2.taylor_remainder24 u hu'⟩
