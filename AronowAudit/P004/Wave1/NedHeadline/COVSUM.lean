import AronowAudit.P004.Wave1.NedHeadline.DY
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-!
Finite product algebra for covariance and variance bounds. Covariance bilinearity avoids
requiring centered `X i`. The conditional projection retains the pointwise bound `M`.
-/

private theorem covsum_condition_depends {N : ℕ} (p : Fin N → ℝ)
    (J : Finset (Fin N)) (U : Assignment N → ℝ) :
    DependsOn (conditionOn p J U) (J : Set (Fin N)) := by
  classical
  intro z z' hzz'
  have hevent (w : Assignment N) :
      (∀ j ∈ J, w j = z j) ↔ (∀ j ∈ J, w j = z' j) := by
    constructor
    · intro hw j hj
      exact (hw j hj).trans (hzz' j hj)
    · intro hw j hj
      exact (hw j hj).trans (hzz' j hj).symm
  have hnum : (fun w => if ∀ j ∈ J, w j = z j then U w else 0) =
      (fun w => if ∀ j ∈ J, w j = z' j then U w else 0) := by
    funext w
    simp only [hevent w]
  have hden : (∏ j ∈ J, coin (p j) (z j)) = ∏ j ∈ J, coin (p j) (z' j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hzz' j hj]
  unfold conditionOn
  rw [hnum, hden]

private theorem covsum_cylinder_mass {N : ℕ} (p : Fin N → ℝ)
    (J : Finset (Fin N)) (z : Assignment N) :
    expect p (fun w => if ∀ j ∈ J, w j = z j then (1 : ℝ) else 0) =
      ∏ j ∈ J, coin (p j) (z j) := by
  classical
  let S : Set (Fin N) := (J : Set (Fin N))
  let a₀ : S → Bool := fun j => z j
  have hdep : DependsOn
      (fun w : Assignment N => if ∀ j ∈ J, w j = z j then (1 : ℝ) else 0) S := by
    intro x y hxy
    have hevent : (∀ j ∈ J, x j = z j) ↔ (∀ j ∈ J, y j = z j) := by
      constructor
      · intro hx j hj
        exact (hxy j hj).symm.trans (hx j hj)
      · intro hy j hj
        exact (hxy j hj).trans (hy j hj)
    simp only [hevent]
  have htest (a : S → Bool) :
      (∀ j ∈ J, GraphCompletion.join S a (fun _ => false) j = z j) ↔ a = a₀ := by
    constructor
    · intro ha
      funext j
      calc
        a j = GraphCompletion.join S a (fun _ => false) j :=
          (GraphCompletion.join_left S a (fun _ => false) j).symm
        _ = z j := ha j j.property
        _ = a₀ j := rfl
    · rintro rfl
      intro j hj
      exact GraphCompletion.join_left S a₀ (fun _ => false) ⟨j, hj⟩
  rw [GraphCompletion.expect_left p S _ hdep]
  have hcalc : (∑ a : S → Bool, GraphCompletion.cubeWeight (fun j : S => p j) a *
      (if ∀ j ∈ J, GraphCompletion.join S a (fun _ => false) j = z j
        then (1 : ℝ) else 0)) = ∏ j ∈ J, coin (p j) (z j) := by
    simp_rw [htest]
    calc
      (∑ a : S → Bool, GraphCompletion.cubeWeight (fun j : S => p j) a *
          (if a = a₀ then (1 : ℝ) else 0)) =
          GraphCompletion.cubeWeight (fun j : S => p j) a₀ := by
        rw [Finset.sum_eq_single a₀]
        · simp only [↓reduceIte, mul_one]
        · intro a _ ha
          rw [if_neg ha, mul_zero]
        · intro ha
          exact (ha (Finset.mem_univ a₀)).elim
      _ = ∏ j ∈ J, coin (p j) (z j) := by
        change (∏ j : S, coin (p j) (z j)) = _
        exact Finset.prod_finset_coe (fun j => coin (p j) (z j)) J
  convert hcalc using 8

private theorem covsum_condition_bound {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (J : Finset (Fin N)) (U : Assignment N → ℝ)
    (M : ℝ) (hU : ∀ z, |U z| ≤ M) (z : Assignment N) :
    |conditionOn p J U z| ≤ M := by
  classical
  let m : ℝ := ∏ j ∈ J, coin (p j) (z j)
  have hm : 0 < m := by
    apply Finset.prod_pos
    intro j _
    unfold coin
    split_ifs <;> have hpj := hp j <;> linarith
  have hlo := expect_mono p hp
    (fun w => (-M) * (if ∀ j ∈ J, w j = z j then (1 : ℝ) else 0))
    (fun w => if ∀ j ∈ J, w j = z j then U w else 0) (by
      intro w
      by_cases hw : ∀ j ∈ J, w j = z j
      · simpa only [if_pos hw, mul_one] using (abs_le.mp (hU w)).1
      · simp only [if_neg hw, mul_zero, le_refl])
  have hhi := expect_mono p hp
    (fun w => if ∀ j ∈ J, w j = z j then U w else 0)
    (fun w => M * (if ∀ j ∈ J, w j = z j then (1 : ℝ) else 0)) (by
      intro w
      by_cases hw : ∀ j ∈ J, w j = z j
      · simpa only [if_pos hw, mul_one] using (abs_le.mp (hU w)).2
      · simp only [if_neg hw, mul_zero, le_refl])
  rw [expect_mul, covsum_cylinder_mass] at hlo hhi
  change |expect p (fun w => if ∀ j ∈ J, w j = z j then U w else 0) / m| ≤ M
  exact abs_le.mpr ⟨(le_div_iff₀ hm).2 hlo, (div_le_iff₀ hm).2 hhi⟩

private theorem covsum_second_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (U : Assignment N → ℝ) :
    0 ≤ expect p (fun z => (U z)^2) := by
  unfold expect
  exact Finset.sum_nonneg (fun z _ =>
    mul_nonneg (design_weight_nonneg p hp z) (sq_nonneg (U z)))

private theorem covsum_l2_bound {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (U : Assignment N → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hU : ∀ z, |U z| ≤ M) : l2Norm p U ≤ M := by
  have hsecond : expect p (fun z => (U z)^2) ≤ M^2 := by
    calc
      expect p (fun z => (U z)^2) ≤ expect p (fun _ => M^2) := by
        apply expect_mono p hp
        intro z
        exact sq_le_sq' (abs_le.mp (hU z)).1 (abs_le.mp (hU z)).2
      _ = M^2 := expect_const p _
  calc
    l2Norm p U = Real.sqrt (expect p (fun z => (U z)^2)) := rfl
    _ ≤ Real.sqrt (M^2) := Real.sqrt_le_sqrt hsecond
    _ = M := Real.sqrt_sq hM

private theorem covsum_cov_l2 {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (U V : Assignment N → ℝ) :
    |cov p U V| ≤ l2Norm p U * l2Norm p V := by
  -- Weighted Cauchy--Schwarz, using nonnegative weights directly.
  have hcs (F G : Assignment N → ℝ) :
      (expect p (fun z => F z * G z))^2 ≤
        expect p (fun z => (F z)^2) * expect p (fun z => (G z)^2) := by
    unfold expect
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro z _
      exact mul_nonneg (design_weight_nonneg p hp z) (sq_nonneg (F z))
    · intro z _
      exact mul_nonneg (design_weight_nonneg p hp z) (sq_nonneg (G z))
    · intro z _
      exact le_of_eq (by ring)
  have hvarU : expect p (fun z => (U z - expect p U)^2) = variance p U := by
    simpa only [variance, pow_two] using (cov_centered p U U).symm
  have hvarV : expect p (fun z => (V z - expect p V)^2) = variance p V := by
    simpa only [variance, pow_two] using (cov_centered p V V).symm
  have hcovsq : (cov p U V)^2 ≤ variance p U * variance p V := by
    have hh := hcs (fun z => U z - expect p U) (fun z => V z - expect p V)
    rw [← cov_centered p U V, hvarU, hvarV] at hh
    exact hh
  have hsecond : (cov p U V)^2 ≤
      expect p (fun z => (U z)^2) * expect p (fun z => (V z)^2) := by
    exact hcovsq.trans (mul_le_mul (variance_le_second p U) (variance_le_second p V)
      (variance_nonneg p hp V) (covsum_second_nonneg p hp U))
  calc
    |cov p U V| ≤ Real.sqrt
        (expect p (fun z => (U z)^2) * expect p (fun z => (V z)^2)) :=
      Real.abs_le_sqrt hsecond
    _ = l2Norm p U * l2Norm p V :=
      Real.sqrt_mul (covsum_second_nonneg p hp U) _

private theorem covsum_cov_sub_left {N : ℕ} (p : Fin N → ℝ)
    (U Q V : Assignment N → ℝ) :
    cov p (fun z => U z - Q z) V = cov p U V - cov p Q V := by
  have hprod : (fun z => (U z - Q z) * V z) =
      (fun z => U z * V z - Q z * V z) := by funext z; ring
  simp only [cov, hprod, expect_sub]
  ring

private theorem covsum_cov_sub_right {N : ℕ} (p : Fin N → ℝ)
    (U V Q : Assignment N → ℝ) :
    cov p U (fun z => V z - Q z) = cov p U V - cov p U Q := by
  have hprod : (fun z => U z * (V z - Q z)) =
      (fun z => U z * V z - U z * Q z) := by funext z; ring
  simp only [cov, hprod, expect_sub]
  ring

/-- A uniform bound on the absolute covariance row sums gives the desired sum variance. -/
theorem covsum_proof : COVSUM := by
  classical
  intro N p X D ψ Kc Cb A e M hF hM hX
  let π : Fin N → ℝ := fun _ => p
  have hp : ∀ k, 0 < π k ∧ π k < 1 := fun _ => hF.hp
  have hK0 : 0 ≤ Kc := hF.hKc
  have hA0 : 0 ≤ A := hF.hA
  have hnormX (i : Fin N) : l2Norm π (X i) ≤ M :=
    covsum_l2_bound π hp (X i) M hM (hX i)
  have hcovall (i j : Fin N) : |cov π (X i) (X j)| ≤ M^2 := by
    calc
      |cov π (X i) (X j)| ≤ l2Norm π (X i) * l2Norm π (X j) :=
        covsum_cov_l2 π hp _ _
      _ ≤ M * M := mul_le_mul (hnormX i) (hnormX j)
        (Real.sqrt_nonneg _) hM
      _ = M^2 := by ring

  have hcovfar (i j : Fin N) (hij : 3 < D i j) :
      |cov π (X i) (X j)| ≤ 2 * M * Kc * ψ (D i j / 3) := by
    let t : ℝ := D i j / 3
    let Q : Fin N → Assignment N → ℝ :=
      fun k => conditionOn π (ball D k t) (X k)
    let E : Fin N → Assignment N → ℝ := fun k z => X k z - Q k z
    have ht0 : 0 ≤ t := by dsimp only [t]; linarith
    have hψ0 : 0 ≤ ψ t := hF.hψ t ht0
    have hnormE (k : Fin N) : l2Norm π (E k) ≤ Kc * ψ t :=
      hF.hNED k t ht0
    have hnormQ (k : Fin N) : l2Norm π (Q k) ≤ M := by
      apply covsum_l2_bound π hp (Q k) M hM
      intro z
      exact covsum_condition_bound π hp (ball D k t) (X k) M (hX k) z
    have hdisjoint : Disjoint (ball D i t) (ball D j t) := by
      apply Finset.disjoint_left.mpr
      intro k hki hkj
      have hik : D i k ≤ t := (Finset.mem_filter.mp hki).2
      have hjk : D j k ≤ t := (Finset.mem_filter.mp hkj).2
      have htri : D i j ≤ D i k + D k j := hF.hD.2.2.2 i k j
      rw [hF.hD.2.2.1 k j] at htri
      dsimp only [t] at hik hjk
      linarith
    have hQi : DependsOn (Q i) (ball D i t : Set (Fin N)) :=
      covsum_condition_depends π _ _
    have hQj : DependsOn (Q j) (ball D j t : Set (Fin N)) :=
      covsum_condition_depends π _ _
    have hsubset : (ball D j t : Set (Fin N)) ⊆ (ball D i t : Set (Fin N))ᶜ := by
      intro k hkj hki
      exact Finset.disjoint_left.mp hdisjoint hki hkj
    have hindep := GraphCompletion.expect_mul_of_disjoint_depends π
      (ball D i t : Set (Fin N)) (Q i) (Q j) hQi (hQj.mono hsubset)
    have hzero : cov π (Q i) (Q j) = 0 := by
      unfold cov
      rw [hindep, sub_self]
    have hdecomp : cov π (X i) (X j) =
        cov π (E i) (X j) + cov π (Q i) (E j) := by
      have hleft : cov π (E i) (X j) = cov π (X i) (X j) - cov π (Q i) (X j) :=
        covsum_cov_sub_left π (X i) (Q i) (X j)
      have hright : cov π (Q i) (E j) = cov π (Q i) (X j) - cov π (Q i) (Q j) :=
        covsum_cov_sub_right π (Q i) (X j) (Q j)
      linarith
    have hfirst : |cov π (E i) (X j)| ≤ (Kc * ψ t) * M := by
      calc
        |cov π (E i) (X j)| ≤ l2Norm π (E i) * l2Norm π (X j) :=
          covsum_cov_l2 π hp _ _
        _ ≤ (Kc * ψ t) * M := mul_le_mul (hnormE i) (hnormX j)
          (Real.sqrt_nonneg _) (mul_nonneg hK0 hψ0)
    have hsecond : |cov π (Q i) (E j)| ≤ M * (Kc * ψ t) := by
      calc
        |cov π (Q i) (E j)| ≤ l2Norm π (Q i) * l2Norm π (E j) :=
          covsum_cov_l2 π hp _ _
        _ ≤ M * (Kc * ψ t) := mul_le_mul (hnormQ i) (hnormE j)
          (Real.sqrt_nonneg _) hM
    calc
      |cov π (X i) (X j)| = |cov π (E i) (X j) + cov π (Q i) (E j)| := by
        rw [hdecomp]
      _ ≤ |cov π (E i) (X j)| + |cov π (Q i) (E j)| := abs_add_le _ _
      _ ≤ (Kc * ψ t) * M + M * (Kc * ψ t) := add_le_add hfirst hsecond
      _ = 2 * M * Kc * ψ (D i j / 3) := by dsimp only [t]; ring

  have hfar_sum (i : Fin N) :
      (∑ j ∈ Finset.univ.filter (fun j => 3 < D i j), |cov π (X i) (X j)|) ≤
        74 * Cb * M * Kc * A / (1 - (2 : ℝ) ^ (2 - e)) := by
    have hd := dy_proof D i Cb 1 e (2 * M * Kc * A)
      (fun j => |cov π (X i) (X j)|) hF.hCb (by norm_num) hF.he
      (by positivity) (hF.hspacing i) (by
        intro j hij
        have hij' : 3 < D i j := by simpa only [mul_one] using hij
        have ht1 : 1 ≤ D i j / 3 := by linarith
        refine ⟨abs_nonneg _, ?_⟩
        calc
          |cov π (X i) (X j)| ≤ 2 * M * Kc * ψ (D i j / 3) := hcovfar i j hij'
          _ ≤ (2 * M * Kc) * (A * (D i j / 3) ^ (-e)) :=
            mul_le_mul_of_nonneg_left (hF.henv _ ht1) (by positivity)
          _ = (2 * M * Kc * A) * (D i j / (3 * 1)) ^ (-e) := by
            simp only [mul_one]
            ring)
    calc
      (∑ j ∈ Finset.univ.filter (fun j => 3 < D i j), |cov π (X i) (X j)|) ≤
          37 * Cb * (2 * M * Kc * A) / (1 - (2 : ℝ) ^ (2 - e)) := by
        simpa only [one_pow, mul_one] using hd
      _ = 74 * Cb * M * Kc * A / (1 - (2 : ℝ) ^ (2 - e)) := by ring

  have hnear_sum (i : Fin N) :
      ∑ j ∈ ball D i 3, |cov π (X i) (X j)| ≤ 10 * Cb * M^2 := by
    have hcard : ((ball D i 3).card : ℝ) ≤ 10 * Cb := by
      have hh := hF.hspacing i 3 (by norm_num)
      norm_num at hh
      nlinarith only [hh]
    calc
      ∑ j ∈ ball D i 3, |cov π (X i) (X j)| ≤ ∑ _j ∈ ball D i 3, M^2 :=
        Finset.sum_le_sum (fun j _ => hcovall i j)
      _ = ((ball D i 3).card : ℝ) * M^2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (10 * Cb) * M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)

  have hrow (i : Fin N) : ∑ j, |cov π (X i) (X j)| ≤
      10 * Cb * M^2 + 74 * Cb * M * Kc * A / (1 - (2 : ℝ) ^ (2 - e)) := by
    have hsplit : (∑ j, |cov π (X i) (X j)|) =
        (∑ j ∈ ball D i 3, |cov π (X i) (X j)|) +
        ∑ j ∈ Finset.univ.filter (fun j => 3 < D i j), |cov π (X i) (X j)| := by
      simpa only [ball, not_le] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j => D i j ≤ 3) (fun j => |cov π (X i) (X j)|)).symm
    rw [hsplit]
    exact add_le_add (hnear_sum i) (hfar_sum i)

  rw [variance_sum]
  calc
    (∑ i, ∑ j, cov (fun _ => p) (X i) (X j)) ≤
        ∑ i, ∑ j, |cov π (X i) (X j)| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => le_abs_self (cov π (X i) (X j)))
    _ ≤ ∑ _i : Fin N,
        (10 * Cb * M^2 + 74 * Cb * M * Kc * A / (1 - (2 : ℝ) ^ (2 - e))) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (N : ℝ) *
        (10 * Cb * M^2 + 74 * Cb * M * Kc * A / (1 - (2 : ℝ) ^ (2 - e))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end AronowAudit.P004.Wave1.NedHeadline
