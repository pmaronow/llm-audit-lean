import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T9_L2

open scoped BigOperators Classical
noncomputable section

abbrev fair (N : ℕ) : Fin N → ℝ := fun _ => 1 / 2

def tailEvent (N : ℕ) (z : SAP.P004a.Assignment N) : Prop :=
  (N : ℝ) / 4 < (AronowAudit.P004.Wave1.t9b6_signsum z)^2

def negTailEvent (N : ℕ) (z : SAP.P004a.Assignment N) : Prop :=
  AronowAudit.P004.Wave1.t9b6_signsum z < 0 ∧ tailEvent N z

def posTailEvent (N : ℕ) (z : SAP.P004a.Assignment N) : Prop :=
  0 < AronowAudit.P004.Wave1.t9b6_signsum z ∧ tailEvent N z

def tailSq (N : ℕ) (z : SAP.P004a.Assignment N) : ℝ :=
  if tailEvent N z then (AronowAudit.P004.Wave1.t9b6_signsum z)^2 else 0

def tailFourth (N : ℕ) (z : SAP.P004a.Assignment N) : ℝ :=
  if tailEvent N z then (AronowAudit.P004.Wave1.t9b6_signsum z)^4 else 0

def tailInd (N : ℕ) (z : SAP.P004a.Assignment N) : ℝ :=
  if tailEvent N z then 1 else 0

lemma fair_weight {N : ℕ} (z : AronowAudit.P004.Assignment N) :
    AronowAudit.P004.designWeight (fair N) z = (1 / 2 : ℝ)^N := by
  norm_num [fair, AronowAudit.P004.designWeight, AronowAudit.P004.coin,
    Finset.prod_const, Fintype.card_fin]
  rw [one_div_pow]
  rw [one_div]

lemma expect_fair_uniform {N : ℕ} (f : AronowAudit.P004.Assignment N → ℝ) :
    AronowAudit.P004.expect (fair N) f = (1 / 2 : ℝ)^N * ∑ z, f z := by
  unfold AronowAudit.P004.expect
  calc
    (∑ z, AronowAudit.P004.designWeight (fair N) z * f z) =
        ∑ z, (1 / 2 : ℝ)^N * f z := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [fair_weight]
    _ = (1 / 2 : ℝ)^N * ∑ z, f z := by rw [Finset.mul_sum]

lemma tail_expect_lower {N : ℕ} (hN : 0 < N) :
    (3 * (N : ℝ) / 4) ≤
      AronowAudit.P004.expect (fair N) (tailSq N) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hpoint (z : AronowAudit.P004.Assignment N) :
      (AronowAudit.P004.Wave1.t9b6_signsum z)^2 ≤
        (N : ℝ) / 4 + tailSq N z := by
    by_cases ht : tailEvent N z
    · simp [tailSq, ht]
      positivity
    · simp [tailSq, ht]
      exact le_of_not_gt ht
  have hh := AronowAudit.P004.expect_mono (fair N)
    (by intro i; constructor <;> norm_num [fair])
    (fun z => (AronowAudit.P004.Wave1.t9b6_signsum z)^2)
    (fun z => (N : ℝ)/4 + tailSq N z) hpoint
  rw [AronowAudit.P004.expect_add, AronowAudit.P004.expect_const,
    (AronowAudit.P004.Wave1.t9b6_moments N).1] at hh
  linarith

lemma tail_expect_fourth_le {N : ℕ} :
    AronowAudit.P004.expect (fair N) (tailFourth N) ≤
      AronowAudit.P004.expect (fair N)
        (fun z => (AronowAudit.P004.Wave1.t9b6_signsum z)^4) := by
  apply AronowAudit.P004.expect_mono (fair N)
    (by intro i; constructor <;> norm_num [fair])
  intro z
  by_cases ht : tailEvent N z
  · simp [tailFourth, ht]
  · simp [tailFourth, ht]
    positivity

lemma tail_cauchy {N : ℕ} :
    (AronowAudit.P004.expect (fair N) (tailSq N))^2 ≤
      AronowAudit.P004.expect (fair N) (tailFourth N) *
        AronowAudit.P004.prob (fair N) (tailEvent N) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (tailSq N) (tailInd N)
  have hmul :
      ((1 / 2 : ℝ)^N * ∑ z, tailSq N z * tailInd N z)^2 ≤
        ((1 / 2 : ℝ)^N * ∑ z, (tailSq N z)^2) *
          ((1 / 2 : ℝ)^N * ∑ z, (tailInd N z)^2) := by
    have hscaled := mul_le_mul_of_nonneg_left hcs
      (sq_nonneg ((1 / 2 : ℝ)^N))
    calc
      _ = ((1 / 2 : ℝ)^N)^2 * (∑ z, tailSq N z * tailInd N z)^2 := by ring
      _ ≤ ((1 / 2 : ℝ)^N)^2 *
          ((∑ z, (tailSq N z)^2) * ∑ z, (tailInd N z)^2) := hscaled
      _ = _ := by ring
  have hprod :
      (fun z => tailSq N z * tailInd N z) = tailSq N := by
    funext z
    by_cases ht : tailEvent N z <;> simp [tailSq, tailInd, ht]
  have hsquare : (fun z => (tailSq N z)^2) = tailFourth N := by
    funext z
    by_cases ht : tailEvent N z
    · simp [tailSq, tailFourth, ht]
      ring
    · simp [tailSq, tailFourth, ht]
  have hind : (fun z => (tailInd N z)^2) = tailInd N := by
    funext z
    by_cases ht : tailEvent N z <;> simp [tailInd, ht]
  have hprob : AronowAudit.P004.prob (fair N) (tailEvent N) =
      AronowAudit.P004.expect (fair N) (tailInd N) := by
    rfl
  rw [hprob]
  rw [expect_fair_uniform, expect_fair_uniform, expect_fair_uniform]
  rw [hprod, hsquare, hind] at hmul
  exact hmul

lemma tail_split {N : ℕ} (hN : 0 < N) :
    AronowAudit.P004.prob (fair N) (tailEvent N) =
      2 * AronowAudit.P004.prob (fair N) (negTailEvent N) := by
  have heq : AronowAudit.P004.prob (fair N) (posTailEvent N) =
      AronowAudit.P004.prob (fair N) (negTailEvent N) := by
    rw [AronowAudit.P004.Wave1.t9b6_prob_flip]
    congr 1
    funext z
    apply propext
    simp only [posTailEvent, negTailEvent, tailEvent,
      AronowAudit.P004.Wave1.t9b6_signsum_flip]
    constructor <;> rintro ⟨hs, ht⟩ <;> constructor <;>
      nlinarith [sq_nonneg (AronowAudit.P004.Wave1.t9b6_signsum z)]
  have hsplit : AronowAudit.P004.prob (fair N) (tailEvent N) =
      AronowAudit.P004.prob (fair N) (negTailEvent N) +
        AronowAudit.P004.prob (fair N) (posTailEvent N) := by
    unfold AronowAudit.P004.prob
    rw [← AronowAudit.P004.expect_add]
    congr 1
    funext z
    by_cases ht : tailEvent N z
    · have hz : AronowAudit.P004.Wave1.t9b6_signsum z ≠ 0 := by
        intro hz
        change (N : ℝ)/4 < (AronowAudit.P004.Wave1.t9b6_signsum z)^2 at ht
        rw [hz] at ht
        have hn : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
        norm_num at ht
        linarith
      change (N : ℝ)/4 <
        (AronowAudit.P004.Wave1.t9b6_signsum z)^2 at ht
      rcases lt_or_gt_of_ne hz with hs | hs <;>
        simp [negTailEvent, posTailEvent, tailEvent, ht, hs, hs.not_gt]
    · change ¬ ((N : ℝ)/4 <
        (AronowAudit.P004.Wave1.t9b6_signsum z)^2) at ht
      simp [negTailEvent, posTailEvent, tailEvent, ht]
  rw [hsplit, heq]
  ring

lemma boundary_signsum_eq (N : ℕ) (z : SAP.P004a.Assignment N) :
    SAP.P004a.boundarySignSum z =
      AronowAudit.P004.Wave1.t9b6_signsum z := by
  unfold SAP.P004a.boundarySignSum AronowAudit.P004.Wave1.t9b6_signsum
  apply Finset.sum_congr rfl
  intro i hi
  cases z i <;> norm_num [SAP.P004a.bit, AronowAudit.P004.bit]

lemma prob_sign_event_eq {N : ℕ} (φ : ℝ → Prop) :
    SAP.P004a.prob (fair N) (fun z => φ (SAP.P004a.boundarySignSum z)) =
      AronowAudit.P004.prob (fair N)
        (fun z => φ (AronowAudit.P004.Wave1.t9b6_signsum z)) := by
  have hevent :
      (fun z : SAP.P004a.Assignment N =>
        φ (SAP.P004a.boundarySignSum z)) =
      (fun z => φ (AronowAudit.P004.Wave1.t9b6_signsum z)) := by
    funext z
    rw [boundary_signsum_eq]
  rw [hevent]
  unfold SAP.P004a.prob AronowAudit.P004.prob
  unfold SAP.P004a.expect AronowAudit.P004.expect
  apply Finset.sum_congr rfl
  intro z hz
  have hw : SAP.P004a.designWeight (fair N) z =
      AronowAudit.P004.designWeight (fair N) z := by
    simp [SAP.P004a.designWeight, AronowAudit.P004.designWeight,
      SAP.P004a.coin, AronowAudit.P004.coin]
  rw [hw]

end
end SAP.P004a.WH.W2.P.T9_L2

open SAP.P004a.WH.W2.P.T9_L2

theorem SAP.P004a.WH.W2.T9_L2_proof : SAP.P004a.WH.W2.T9_L2 := by
  intro N hN
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hfourth :
      AronowAudit.P004.expect (fair N)
        (fun z => (AronowAudit.P004.Wave1.t9b6_signsum z)^4) =
        3*(N:ℝ)^2 - 2*N := (AronowAudit.P004.Wave1.t9b6_moments N).2
  have hden : 0 < 3*(N:ℝ)^2 - 2*N := by nlinarith
  have hprob_nonneg :
      0 ≤ AronowAudit.P004.prob (fair N) (tailEvent N) := by
    unfold AronowAudit.P004.prob AronowAudit.P004.expect
    change 0 ≤ ∑ z,
      AronowAudit.P004.designWeight (fair N) z * tailInd N z
    apply Finset.sum_nonneg
    intro z hz
    apply mul_nonneg
    · exact AronowAudit.P004.design_weight_nonneg (fair N)
        (by intro i; constructor <;> norm_num [fair]) z
    · by_cases ht : tailEvent N z <;> simp [tailInd, ht]
  have hmain :
      9*(N:ℝ)^2 / 16 ≤
        (3*(N:ℝ)^2 - 2*N) *
          AronowAudit.P004.prob (fair N) (tailEvent N) := by
    have hlower := tail_expect_lower hN
    have hcs := tail_cauchy (N := N)
    have hfourth_le := tail_expect_fourth_le (N := N)
    rw [hfourth] at hfourth_le
    have hprod := mul_le_mul_of_nonneg_right hfourth_le hprob_nonneg
    have hsq : (3*(N:ℝ)/4)^2 ≤
        (AronowAudit.P004.expect (fair N) (tailSq N))^2 := by
      nlinarith [hlower, (sq_nonneg (AronowAudit.P004.expect (fair N) (tailSq N)))]
    calc
      9*(N:ℝ)^2/16 ≤ (3*(N:ℝ)/4)^2 := le_of_eq (by ring)
      _ ≤ (AronowAudit.P004.expect (fair N) (tailSq N))^2 := hsq
      _ ≤ AronowAudit.P004.expect (fair N) (tailFourth N) *
          AronowAudit.P004.prob (fair N) (tailEvent N) := hcs
      _ ≤ (3*(N:ℝ)^2 - 2*N) *
          AronowAudit.P004.prob (fair N) (tailEvent N) := hprod
  have htailLower :
      9*(N:ℝ)^2/(16*(3*(N:ℝ)^2-2*N)) ≤
        AronowAudit.P004.prob (fair N) (tailEvent N) := by
    apply (div_le_iff₀ (by positivity :
      0 < 16*(3*(N:ℝ)^2-2*N))).2
    nlinarith [hmain]
  have htailEq := prob_sign_event_eq (N := N)
    (fun x => (N:ℝ)/4 < x^2)
  have hnegEq := prob_sign_event_eq (N := N)
    (fun x => x < 0 ∧ (N:ℝ)/4 < x^2)
  have hsplit := tail_split hN
  have hfirst :
      9*(N:ℝ)^2/(16*(3*(N:ℝ)^2-2*N)) ≤
        SAP.P004a.prob (fair N)
          (fun z => (N:ℝ)/4 < (SAP.P004a.boundarySignSum z)^2) := by
    rw [htailEq]
    exact htailLower
  have hsecond :
      SAP.P004a.prob (fair N)
        (fun z => SAP.P004a.boundarySignSum z < 0 ∧
          (N:ℝ)/4 < (SAP.P004a.boundarySignSum z)^2) =
        SAP.P004a.prob (fair N)
          (fun z => (N:ℝ)/4 <
            (SAP.P004a.boundarySignSum z)^2) / 2 := by
    rw [hnegEq, htailEq]
    change AronowAudit.P004.prob (fair N) (negTailEvent N) =
      AronowAudit.P004.prob (fair N) (tailEvent N) / 2
    rw [hsplit]
    ring
  exact ⟨hfirst, hsecond⟩

