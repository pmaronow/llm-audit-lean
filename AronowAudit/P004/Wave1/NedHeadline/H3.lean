import AronowAudit.P004.Wave1.NedHeadline.H2
import AronowAudit.P004.Wave1.NedHeadline.RATIO
import AronowAudit.P004.Wave1.NedHeadline.DEN
import AronowAudit.P004.Wave1.NedFarCovarianceBlueprint
import AronowAudit.P004.Wave1.DesignLimits.DL1
import AronowAudit.P004.Wave1.DesignLimits.DL2
import AronowAudit.P004.Wave1.DesignLimits.DL3

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

def armCoefficient (p : ℝ) (a b : Bool) : ℝ := (if b = a then 1 else 0) / coin p a

def armResidual {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool)
    (i : Fin N) (z : Assignment N) : ℝ :=
  (if z i = a then R i z - barMu (fun _ => p) R a else 0) / coin p a

theorem armResidual_affine {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) :
    armResidual p R a = fun i z => armCoefficient p a (z i) * R i z -
      armCoefficient p a (z i) * barMu (fun _ => p) R a := by
  classical
  funext i z
  by_cases hz : z i = a <;>
    simp [armResidual, armCoefficient, hz, div_eq_mul_inv] <;> ring

theorem armResidual_mean {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool)
    (hp : 0 < p ∧ p < 1) (i : Fin N) :
    expect (fun _ => p) (armResidual p R a i) =
      marginal (fun _ => p) R i a - barMu (fun _ => p) R a := by
  unfold armResidual
  rw [expect_div]
  change marginal (fun _ => p)
    (fun j z => R j z - barMu (fun _ => p) R a) i a = _
  rw [marginal_is_marginalization (fun _ => p) _ i a (fun _ => hp),
    expect_sub, expect_const,
    ← marginal_is_marginalization (fun _ => p) R i a (fun _ => hp)]

theorem armResidual_sum_mean {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1) :
    expect (fun _ => p) (fun z => ∑ i, armResidual p R a i z) = 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [expect_sum]
  simp_rw [armResidual_mean p R a hp]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, barMu]
  field_simp [hn] <;> ring

theorem ScoreEnvelope.arm_coefficient {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] {P : PopulationSequence Space} {p d : ℝ}
    (E : ScoreEnvelope P p d) (hp : 0 < p ∧ p < 1) (a b : Bool) :
    |armCoefficient p a b| ≤ E.L := by
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  cases a <;> cases b
  · simpa [armCoefficient, coin, abs_div, abs_of_pos hq] using E.hL0
  · simpa [armCoefficient, coin] using E.hL.le
  · simpa [armCoefficient, coin] using E.hL.le
  · simpa [armCoefficient, coin, abs_div, abs_of_pos hp.1] using E.hL1

theorem finite_prob_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop) : 0 ≤ prob p A := by
  classical
  have h := expect_mono p hp (fun _ => 0) (fun z => if A z then 1 else 0)
    (fun z => by split_ifs <;> norm_num)
  simpa only [expect_const, prob] using h

theorem finite_prob_cover {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B C : Assignment N → Prop)
    (hcover : ∀ z, A z → B z ∨ C z) : prob p A ≤ prob p B + prob p C := by
  classical
  unfold prob
  rw [← expect_add]
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · rcases hcover z ha with hb | hc
    · by_cases hc : C z <;> norm_num [ha, hb, hc]
    · by_cases hb : B z <;> norm_num [ha, hb, hc]
  · by_cases hb : B z <;> by_cases hc : C z <;> norm_num [ha, hb, hc]

theorem h3_proof : H3.{u} := by
  intro Space _ _ P p d hS
  classical
  obtain ⟨E⟩ := exists_scoreEnvelope P p d hS
  let π : ∀ N, Fin N → ℝ := fun _ _ => p
  let R : ∀ N, CircleTable N := fun N => circleAverage (P N) d
  let X : Bool → ∀ N, Fin N → Assignment N → ℝ := fun a N => armResidual p (R N) a
  let B : Bool → ∀ N, Assignment N → ℝ := fun a N z => (∑ i, X a N i z) / N
  let δ : Bool → ∀ N, Assignment N → ℝ := fun a N z => armCount z a / (N * coin p a) - 1
  let D : Bool → ℝ := fun a => if a then (1 - p) / p else p / (1 - p)
  let M : ℝ := 2 * E.B * E.L
  let V : ℝ := |10 * E.Cb * M^2 +
    74 * E.Cb * M * (E.L * E.G) * E.A / (1 - (2 : ℝ) ^ (2 - E.e))|
  let F : ℝ := 2 * V + D true + D false
  let Good : ∀ N, Assignment N → Prop := fun N z =>
    |δ true N z| ≤ 1 / 2 ∧ |δ false N z| ≤ 1 / 2
  let W : ∀ N, Assignment N → ℝ := fun N z =>
    2 * Real.sqrt N * (|B true N z| * |δ true N z| + |B false N z| * |δ false N z|)
  let U : ∀ N, Assignment N → ℝ := fun N z => Real.sqrt N *
    (linearHajek (π N) (R N) z - hajek (R N) z)
  have hadm : AdmissibleSeq π := fun _ _ => hS.hp
  have hM : 0 ≤ M := by exact mul_nonneg (mul_nonneg (by norm_num) E.hB.le) E.hL.le
  have hV : 0 ≤ V := abs_nonneg _
  have hD : ∀ a, 0 ≤ D a := by
    intro a
    cases a
    · exact div_nonneg hS.hp.1.le (sub_pos.mpr hS.hp.2).le
    · exact div_nonneg (sub_pos.mpr hS.hp.2).le hS.hp.1.le
  have hW : ∀ N z, 0 ≤ W N z := by intro N z; dsimp [W]; positivity
  have hden (N : ℕ) (hN : 0 < N) (a : Bool) :
      expect (π N) (fun z => (δ a N z)^2) = D a / N := by
    have h := den_proof N p hN hS.hp
    cases a
    · calc
        _ = p / (N * (1 - p)) := h.2
        _ = D false / N := by dsimp [D]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    · calc
        _ = (1 - p) / (N * p) := h.1
        _ = D true / N := by dsimp [D]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hBsecond : ∀ᶠ N in atTop, ∀ a,
      expect (π N) (fun z => (B a N z)^2) ≤ V / N := by
    filter_upwards [E.hbound, E.hspacing, eventually_gt_atTop 0] with N hRN hsp hN
    intro a
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hμ : |barMu (π N) (R N) a| ≤ E.B :=
      NedFarCovariance.barMu_abs_le p hS.hp (R N) E.B E.hB.le hRN a
    let α : Fin N → Bool → ℝ := fun _ b => armCoefficient p a b
    let β : Fin N → Bool → ℝ := fun _ b => -armCoefficient p a b * barMu (π N) (R N) a
    have hXaff : X a N = fun i z => α i (z i) * R N i z + β i (z i) := by
      rw [show X a N = armResidual p (R N) a from rfl, armResidual_affine]
      funext i z
      dsimp [α, β]
      ring
    have hLF : LocalFamily p (X a N) (nodeSeparation (P N)) E.ψ
        (E.L * E.G) E.Cb E.A E.e := by
      rw [hXaff]
      exact E.affine_family hS.hp N hsp α β (fun _ b => E.arm_coefficient hS.hp a b)
    have hXB : ∀ i z, |X a N i z| ≤ M := by
      intro i z
      have hres : |R N i z - barMu (π N) (R N) a| ≤ 2 * E.B :=
        (abs_sub _ _).trans (by linarith [hRN i z])
      have he : X a N i z = armCoefficient p a (z i) *
          (R N i z - barMu (π N) (R N) a) := by
        rw [hXaff]
        dsimp [α, β]
        ring
      rw [he, abs_mul]
      calc
        _ ≤ E.L * (2 * E.B) := mul_le_mul (E.arm_coefficient hS.hp a (z i))
          hres (abs_nonneg _) E.hL.le
        _ = M := by ring
    have hsum : variance (π N) (fun z => ∑ i, X a N i z) ≤ (N : ℝ) * V := by
      exact (covsum_proof p (X a N) (nodeSeparation (P N)) E.ψ (E.L * E.G)
        E.Cb E.A E.e M hLF hM hXB).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) hn.le)
    have hm : expect (π N) (B a N) = 0 := by
      change expect (π N) (fun z => (∑ i, armResidual p (R N) a i z) / N) = 0
      rw [expect_div, armResidual_sum_mean p (R N) a hN hS.hp, zero_div]
    calc
      _ = variance (π N) (B a N) := by
        simp only [variance, cov, hm, zero_mul, sub_zero, pow_two]
      _ = variance (π N) (fun z => ∑ i, X a N i z) / (N : ℝ)^2 := variance_div _ _ _
      _ ≤ ((N : ℝ) * V) / (N : ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = V / N := by field_simp [hn.ne'] <;> ring
  have hbadbound : ∀ᶠ N in atTop,
      prob (π N) (fun z => ¬ Good N z) ≤ (4 * (D true + D false)) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have htail (a : Bool) : prob (π N) (fun z => (1 / 2 : ℝ) < |δ a N z|) ≤
        4 * D a / N := by
      calc
        _ ≤ expect (π N) (fun z => (δ a N z)^2) / (1 / 2 : ℝ)^2 :=
          (dl1_proof (π N) (hadm N) (δ a N) (1 / 2) (by norm_num)).2
        _ = _ := by rw [hden N hN a]; norm_num <;> ring
    calc
      _ ≤ prob (π N) (fun z => (1 / 2 : ℝ) < |δ true N z|) +
          prob (π N) (fun z => (1 / 2 : ℝ) < |δ false N z|) := by
        apply finite_prob_cover (π N) (hadm N)
        intro z hz
        change ¬ (|δ true N z| ≤ 1 / 2 ∧ |δ false N z| ≤ 1 / 2) at hz
        by_cases ht : |δ true N z| ≤ 1 / 2
        · exact Or.inr (lt_of_not_ge (fun hf => hz ⟨ht, hf⟩))
        · exact Or.inl (lt_of_not_ge ht)
      _ ≤ 4 * D true / N + 4 * D false / N := add_le_add (htail true) (htail false)
      _ = _ := by ring
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hbad : Tendsto (fun N => prob (π N) (fun z => ¬ Good N z)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N => finite_prob_nonneg (π N) (hadm N) _))
      hbadbound
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun N : ℕ => (4 * (D true + D false)) * (N : ℝ)⁻¹) atTop
        (nhds ((4 * (D true + D false)) * 0)))
  have hWfirst : ∀ᶠ N in atTop, expect (π N) (fun z => |W N z|) ≤ F / Real.sqrt N := by
    filter_upwards [hBsecond, eventually_gt_atTop 0] with N hBN hN
    have hy (b c : ℝ) : 2 * (|b| * |c|) ≤ b^2 + c^2 := by
      nlinarith [sq_nonneg (|b| - |c|), sq_abs b, sq_abs c]
    have hpoint (z : Assignment N) : |W N z| ≤ Real.sqrt N *
        ((B true N z)^2 + (δ true N z)^2 + (B false N z)^2 + (δ false N z)^2) := by
      rw [abs_of_nonneg (hW N z)]
      have hsum : 2 * (|B true N z| * |δ true N z| + |B false N z| * |δ false N z|) ≤
          (B true N z)^2 + (δ true N z)^2 + (B false N z)^2 + (δ false N z)^2 := by
        linarith [hy (B true N z) (δ true N z), hy (B false N z) (δ false N z)]
      calc
        W N z = Real.sqrt N * (2 *
          (|B true N z| * |δ true N z| + |B false N z| * |δ false N z|)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    calc
      _ ≤ expect (π N) (fun z => Real.sqrt N *
          ((B true N z)^2 + (δ true N z)^2 + (B false N z)^2 + (δ false N z)^2)) :=
        expect_mono (π N) (hadm N) _ _ hpoint
      _ = Real.sqrt N * (expect (π N) (fun z => (B true N z)^2) +
          expect (π N) (fun z => (δ true N z)^2) +
          expect (π N) (fun z => (B false N z)^2) +
          expect (π N) (fun z => (δ false N z)^2)) := by
        rw [expect_mul, expect_add, expect_add, expect_add]
      _ ≤ Real.sqrt N * (V / N + D true / N + V / N + D false / N) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [hden N hN true, hden N hN false]
        linarith [hBN true, hBN false]
      _ = F * (Real.sqrt N / N) := by dsimp [F]; ring
      _ = F / Real.sqrt N := by rw [Real.sqrt_div_self'] <;> ring
  have hWlim : Tendsto (fun N => expect (π N) (fun z => |W N z|)) atTop (nhds 0) := by
    refine squeeze_zero' ?_ hWfirst ?_
    · apply Eventually.of_forall
      intro N
      have h := expect_mono (π N) (hadm N) (fun _ => 0) (fun z => |W N z|)
        (fun z => abs_nonneg _)
      simpa only [expect_const] using h
    · have hs : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul hs : Tendsto (fun N : ℕ => F * (Real.sqrt N)⁻¹)
          atTop (nhds (F * 0)))
  have hWp : InProb π W := (dl2_proof π hadm W).1 hWlim
  have hdom : ∀ᶠ N in atTop, ∀ z, Good N z → |U N z| ≤ |W N z| := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    intro z hg
    have hBt : B true N z =
        (∑ i, bit (z i) * (R N i z - barMu (π N) (R N) true)) / (N * p) := by
      have hi (i : Fin N) : X true N i z =
          bit (z i) * (R N i z - barMu (π N) (R N) true) / p := by
        cases hz : z i <;> simp [X, armResidual, coin, bit, hz, π]
      dsimp only [B]
      simp_rw [hi]
      rw [← Finset.sum_div]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have hBf : B false N z =
        (∑ i, (1 - bit (z i)) * (R N i z - barMu (π N) (R N) false)) /
          (N * (1 - p)) := by
      have hi (i : Fin N) : X false N i z =
          (1 - bit (z i)) * (R N i z - barMu (π N) (R N) false) / (1 - p) := by
        cases hz : z i <;> simp [X, armResidual, coin, bit, hz, π]
      dsimp only [B]
      simp_rw [hi]
      rw [← Finset.sum_div]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have hr := ratio_proof p (R N) z hN hS.hp
      (show |armCount z true / (N * p) - 1| ≤ 1 / 2 from hg.1)
      (show |armCount z false / (N * (1 - p)) - 1| ≤ 1 / 2 from hg.2)
    rw [← hBt, ← hBf] at hr
    change |linearHajek (π N) (R N) z - hajek (R N) z| ≤
      2 * (|B true N z| * |δ true N z| + |B false N z| * |δ false N z|) at hr
    change |Real.sqrt N * (linearHajek (π N) (R N) z - hajek (R N) z)| ≤ |W N z|
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (hW N z)]
    calc
      _ ≤ Real.sqrt N * (2 *
        (|B true N z| * |δ true N z| + |B false N z| * |δ false N z|)) :=
          mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)
      _ = W N z := by ring
  exact dl3_proof π hadm U W Good hbad hdom hWp

end
end AronowAudit.P004.Wave1.NedHeadline
