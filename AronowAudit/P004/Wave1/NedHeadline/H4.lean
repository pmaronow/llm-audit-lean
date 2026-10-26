import AronowAudit.P004.Wave1.NedHeadline.H2
import AronowAudit.P004.Wave1.NedHeadline.LOCCLT
import AronowAudit.P004.Wave1.NedFarCovarianceBlueprint

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

private theorem variance_sub_const {N : ℕ} (p : Fin N → ℝ)
    (Y : Assignment N → ℝ) (c : ℝ) :
    variance p (fun z => Y z - c) = variance p Y := by
  simp only [variance, cov_centered, expect_sub, expect_const]
  congr 1
  funext z
  ring

theorem h4_proof : H4.{u} := by
  intro Space _ _ P p d hS hnondeg
  obtain ⟨E⟩ := exists_scoreEnvelope P p d hS
  obtain ⟨v, hv, hvN⟩ := hnondeg
  let π : ∀ N, Fin N → ℝ := fun _ _ => p
  let R : ∀ N, CircleTable N := fun N => circleAverage (P N) d
  let μ : ∀ N, Bool → ℝ := fun N => barMu (π N) (R N)
  let X : ∀ N, Fin N → Assignment N → ℝ := fun N i z =>
    μ N true - μ N false + residualContrast (π N) (R N) (fun _ a => μ N a) i z -
      nodeEffect (π N) (R N) i
  let α : ∀ N, Fin N → Bool → ℝ := fun _ _ a => bit a / p - (1 - bit a) / (1 - p)
  let β : ∀ N, Fin N → Bool → ℝ := fun N i a =>
    μ N true - μ N false - bit a * μ N true / p +
      (1 - bit a) * μ N false / (1 - p) - nodeEffect (π N) (R N) i
  let M : ℝ := 4 * E.B + 2 * E.B * E.L
  have hXaff (N : ℕ) : X N = fun i z => α N i (z i) * R N i z + β N i (z i) := by
    funext i z
    dsimp [X, α, β, residualContrast, π]
    ring
  have hmean : ∀ N i, expect (π N) (X N i) = 0 := by
    intro N i
    change expect (π N) (fun z => μ N true - μ N false +
      residualContrast (π N) (R N) (fun _ a => μ N a) i z - nodeEffect (π N) (R N) i) = 0
    rw [expect_sub, expect_add, expect_const,
      residualContrast_mean (π N) (R N) (fun _ a => μ N a) i (fun _ => hS.hp), expect_const]
    simp only [residualEffect]
    ring
  have hned : ∀ N i t, 0 ≤ t → l2Norm (π N)
      (fun z => X N i z - conditionOn (π N)
        (ball (nodeSeparation (P N)) i t) (X N i) z) ≤ (E.L * E.G) * E.ψ t := by
    intro N i t ht
    rw [hXaff]
    exact E.affine_ned hS.hp N (α N) (β N)
      (fun _ a => E.contrast_coefficient hS.hp a) i t ht
  have hbound : ∀ᶠ N in atTop, ∀ i z, |X N i z| ≤ M := by
    filter_upwards [E.hbound] with N hRN
    have hμ (a : Bool) : |μ N a| ≤ E.B :=
      NedFarCovariance.barMu_abs_le p hS.hp (R N) E.B E.hB.le hRN a
    have hres (i : Fin N) (z : Assignment N) (a : Bool) : |R N i z - μ N a| ≤ 2 * E.B :=
      (abs_sub _ _).trans (by linarith [hRN i z, hμ a])
    have hτ (i : Fin N) : |nodeEffect (π N) (R N) i| ≤ 2 * E.B := by
      unfold nodeEffect
      exact (abs_sub _ _).trans (by linarith
        [ComponentCompletion.marginal_abs_le (π N) (fun _ => hS.hp) (R N) E.B hRN i true,
         ComponentCompletion.marginal_abs_le (π N) (fun _ => hS.hp) (R N) E.B hRN i false])
    have hμdiff : |μ N true - μ N false| ≤ 2 * E.B :=
      (abs_sub _ _).trans (by linarith [hμ true, hμ false])
    have hcontrast (i : Fin N) (z : Assignment N) :
        |residualContrast (π N) (R N) (fun _ a => μ N a) i z| ≤ 2 * E.B * E.L := by
      have hq : 0 < 1 - p := sub_pos.mpr hS.hp.2
      cases hz : z i
      · simp only [residualContrast, hz, bit, Bool.false_eq_true, if_false, zero_mul,
          zero_div, sub_zero, one_mul, zero_sub, abs_neg]
        change |(R N i z - μ N false) / (1 - p)| ≤ _
        rw [abs_div, abs_of_pos hq]
        calc
          _ ≤ (2 * E.B) / (1 - p) := div_le_div_of_nonneg_right (hres i z false) hq.le
          _ = 2 * E.B * (1 / (1 - p)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left E.hL0 (mul_nonneg (by norm_num) E.hB.le)
      · simp only [residualContrast, hz, bit, if_true, one_mul, sub_self, zero_mul,
          zero_div, sub_zero]
        change |(R N i z - μ N true) / p| ≤ _
        rw [abs_div, abs_of_pos hS.hp.1]
        calc
          _ ≤ (2 * E.B) / p := div_le_div_of_nonneg_right (hres i z true) hS.hp.1.le
          _ = 2 * E.B * (1 / p) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left E.hL1 (mul_nonneg (by norm_num) E.hB.le)
    intro i z
    change |μ N true - μ N false +
      residualContrast (π N) (R N) (fun _ a => μ N a) i z - nodeEffect (π N) (R N) i| ≤ M
    calc
      _ ≤ |μ N true - μ N false +
          residualContrast (π N) (R N) (fun _ a => μ N a) i z| +
          |nodeEffect (π N) (R N) i| := abs_sub _ _
      _ ≤ |μ N true - μ N false| +
          |residualContrast (π N) (R N) (fun _ a => μ N a) i z| +
          |nodeEffect (π N) (R N) i| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ M := by dsimp [M]; linarith [hμdiff, hcontrast i z, hτ i]
  have hfits (N : ℕ) :
      (fun (_ : Fin N) a => if a then μ N true else μ N false) = fun _ a => μ N a := by
    funext i a
    cases a <;> rfl
  have hsum (N : ℕ) (hN : 0 < N) (z : Assignment N) :
      (∑ i, X N i z) = (N : ℝ) * (linearHajek (π N) (R N) z - ame (π N) (R N)) := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hid := centered_summand_identity (π N) (R N) (μ N true) (μ N false) hN
      (fun _ => hS.hp)
    have hXi (i : Fin N) : X N i z =
        (N : ℝ) * centeredSummand (π N) (R N) (μ N true) (μ N false) i z := by
      simp only [centeredSummand, hfits]
      change X N i z = (N : ℝ) * (X N i z / N)
      field_simp [hn]
    calc
      _ = ∑ i, (N : ℝ) * centeredSummand (π N) (R N) (μ N true) (μ N false) i z :=
        Finset.sum_congr rfl (fun i _ => hXi i)
      _ = (N : ℝ) * ∑ i, centeredSummand (π N) (R N) (μ N true) (μ N false) i z :=
        (Finset.mul_sum _ _ _).symm
      _ = (N : ℝ) * (augmented (π N) (R N)
          (fun _ a => if a then μ N true else μ N false) z - ame (π N) (R N)) := by
        rw [hid.2.1 z]
      _ = _ := by rw [hfits] <;> rfl
  have hvarsum (N : ℕ) (hN : 0 < N) :
      variance (π N) (fun z => ∑ i, X N i z) = (N : ℝ)^2 *
        variance (π N) (linearHajek (π N) (R N)) := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hquot : (fun z => (∑ i, X N i z) / N) =
        fun z => linearHajek (π N) (R N) z - ame (π N) (R N) := by
      funext z
      rw [hsum N hN z, mul_div_cancel_left₀ _ hn]
    have hvdiv : variance (π N) (linearHajek (π N) (R N)) =
        variance (π N) (fun z => ∑ i, X N i z) / (N : ℝ)^2 := by
      calc
        _ = variance (π N) (fun z => linearHajek (π N) (R N) z - ame (π N) (R N)) :=
          (variance_sub_const _ _ _).symm
        _ = variance (π N) (fun z => (∑ i, X N i z) / N) := congrArg (variance (π N)) hquot.symm
        _ = _ := variance_div _ _ _
    have he := (eq_div_iff (pow_ne_zero 2 hn)).mp hvdiv
    calc
      _ = variance (π N) (linearHajek (π N) (R N)) * (N : ℝ)^2 := he.symm
      _ = _ := mul_comm _ _
  have hfloor : ∀ᶠ N in atTop, v * N ≤ variance (π N) (fun z => ∑ i, X N i z) := by
    filter_upwards [hvN, eventually_gt_atTop 0] with N hvN' hN
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc
      v * N = (N : ℝ) * v := mul_comm _ _
      _ ≤ (N : ℝ) * ((N : ℝ) * variance (π N) (linearHajek (π N) (R N))) :=
        mul_le_mul_of_nonneg_left hvN' hn
      _ = variance (π N) (fun z => ∑ i, X N i z) := by rw [hvarsum N hN] <;> ring
  have hCLT := locclt_proof p hS.hp X (fun N => nodeSeparation (P N)) E.ψ
    (E.L * E.G) E.Cb E.A E.e M v E.hmetric E.hspacing E.hCb E.hψ E.hψanti E.he
    E.hA E.henv (mul_nonneg E.hL.le E.hG) hned hbound hmean hv hfloor
  have hnormalized (N : ℕ) (hN : 0 < N) (z : Assignment N) :
      (∑ i, X N i z) / Real.sqrt (variance (π N) (fun z => ∑ i, X N i z)) =
      (linearHajek (π N) (R N) z - ame (π N) (R N)) /
        Real.sqrt (variance (π N) (linearHajek (π N) (R N))) := by
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    rw [hsum N hN z, hvarsum N hN, Real.sqrt_mul (sq_nonneg (N : ℝ)), Real.sqrt_sq hn.le]
    exact mul_div_mul_left _ _ hn.ne'
  intro x
  have he : (fun N => prob (π N) (fun z =>
      (∑ i, X N i z) / Real.sqrt (variance (π N) (fun z => ∑ i, X N i z)) ≤ x)) =ᶠ[atTop]
      (fun N => prob (π N) (fun z =>
        (linearHajek (π N) (R N) z - ame (π N) (R N)) /
          Real.sqrt (variance (π N) (linearHajek (π N) (R N))) ≤ x)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    apply congrArg (prob (π N))
    funext z
    rw [hnormalized N hN z]
  exact Filter.Tendsto.congr' he (hCLT x)

end
end AronowAudit.P004.Wave1.NedHeadline
