import SAP.P044.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000
namespace SAP.P044.WH.W1.P.T2_L8
open Finset
open scoped BigOperators
noncomputable section
private def i0 (n : ℕ) : Fin (w1MatchingN n) := ⟨0, by unfold w1MatchingN; omega⟩
private def c (n : ℕ) : ℚ := 2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n)
private def sign (n : ℕ) (s : Fin (w1MatchingR n)) : ℚ :=
  if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then 1 else -1
private def signed (n : ℕ) (s : Fin (w1MatchingR n)) : ℚ := c n * sign n s
private theorem fin_nonempty (n : ℕ) : Nonempty (Fin (w1MatchingR n)) := ⟨⟨0, by unfold w1MatchingR; omega⟩⟩
private theorem uniform_total {α : Type} [Fintype α] [Nonempty α] : (∑ a : α, w1Uniform a) = 1 := by
  simp [w1Uniform, Fintype.card_ne_zero]
private theorem uniform_const {α : Type} [Fintype α] [Nonempty α] (z : ℚ) : expect w1Uniform (fun _ : α => z) = z := by
  unfold expect w1Uniform
  simp [Fintype.card_ne_zero]
private theorem expect_constant_of_total {α : Type} [Fintype α] (p : α → ℚ) (htotal : (∑ a, p a) = 1) (z : ℚ) : expect p (fun _ : α => z) = z := by
  unfold expect
  calc
    (∑ a, p a * z) = (∑ a, p a) * z := by simp [Finset.sum_mul]
    _ = z := by rw [htotal]; ring
private theorem independent_expect_snd (n : ℕ) (g : Fin (w1MatchingR n) → ℚ) : expect (w1MatchingIndependentMass n) (fun x => g x.2) = expect w1Uniform g := by
  unfold expect w1MatchingIndependentMass
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [uniform_total, one_mul]
private theorem assignment_indicator_expect (n : ℕ) (hg : W1MatchingGeometry n) (hm : W1MatchingMarginals n) : expect w1Uniform (fun s : Fin (w1MatchingR n) => if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) = 1 / 2 := by
  have hexp (s : Fin (w1MatchingR n)) :
      (w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩) = true ↔
        w1MatchingF n s ⟨0, by unfold w1MatchingN; omega⟩ = Exposure.d11 := by
    rw [hg.2.2.2.1 s ⟨0, by unfold w1MatchingN; omega⟩]
    cases w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ <;> simp
  have hfun : (fun s : Fin (w1MatchingR n) =>
      if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) =
      fun s => if w1MatchingF n s ⟨0, by unfold w1MatchingN; omega⟩ = Exposure.d11 then 1 else 0 := by
    funext s
    by_cases hs : w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩
    · have he := (hexp s).mp hs
      simp [hs, he]
    · have he : w1MatchingF n s ⟨0, by unfold w1MatchingN; omega⟩ ≠ Exposure.d11 := by
        intro h
        exact hs ((hexp s).mpr h)
      simp [hs, he]
  rw [hfun]
  calc
    expect w1Uniform (fun s : Fin (w1MatchingR n) =>
        if w1MatchingF n s ⟨0, by unfold w1MatchingN; omega⟩ = Exposure.d11 then 1 else 0) =
        marginal w1Uniform (w1MatchingF n) ⟨0, by unfold w1MatchingN; omega⟩ Exposure.d11 * 1 :=
          AronowAudit.P044.expect_event w1Uniform (w1MatchingF n)
            ⟨0, by unfold w1MatchingN; omega⟩ Exposure.d11 1
    _ = 1 / 2 := by
      have hmarg := hm.1 (⟨0, by unfold w1MatchingN; omega⟩ : Fin (w1MatchingN n)) Exposure.d11
      have hi : (⟨0, by unfold w1MatchingN; omega⟩ : Fin (w1MatchingN n)).val < 2 := by simp
      rw [if_pos hi] at hmarg
      simpa [hmarg]
private theorem uniform_sign_mean (n : ℕ) (hg : W1MatchingGeometry n) (hm : W1MatchingMarginals n) : expect w1Uniform (sign n) = 0 := by
  letI : Nonempty (Fin (w1MatchingR n)) := fin_nonempty n
  have hprob : expect w1Uniform (fun s : Fin (w1MatchingR n) =>
      if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) =
      1 / 2 := assignment_indicator_expect n hg hm
  have hrep : (fun s : Fin (w1MatchingR n) => sign n s) =
      fun s => 2 * (if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) - 1 := by
    funext s
    by_cases hs : w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ <;>
      norm_num [sign, hs]
  change expect w1Uniform (fun s : Fin (w1MatchingR n) => sign n s) = 0
  rw [hrep]
  have hmul : expect w1Uniform (fun s : Fin (w1MatchingR n) =>
      2 * (if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0)) =
      2 * expect w1Uniform (fun s : Fin (w1MatchingR n) =>
        if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) :=
    AronowAudit.P044.expect_const_mul w1Uniform
      (fun s : Fin (w1MatchingR n) =>
        if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) 2
  calc
    expect w1Uniform (fun s : Fin (w1MatchingR n) =>
        2 * (if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) - 1) =
        expect w1Uniform (fun s : Fin (w1MatchingR n) =>
          2 * (if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0)) -
          expect w1Uniform (fun _ : Fin (w1MatchingR n) => (1 : ℚ)) :=
            AronowAudit.P044.expect_sub w1Uniform _ _
    _ = 2 * expect w1Uniform (fun s : Fin (w1MatchingR n) =>
          if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else 0) -
          expect w1Uniform (fun _ : Fin (w1MatchingR n) => (1 : ℚ)) := by
            exact congrArg (fun z : ℚ => z - expect w1Uniform
              (fun _ : Fin (w1MatchingR n) => (1 : ℚ))) hmul
    _ = 0 := by rw [hprob, uniform_const]; norm_num
private theorem uniform_signed_mean (n : ℕ) (hg : W1MatchingGeometry n) (hm : W1MatchingMarginals n) : expect w1Uniform (signed n) = 0 := by
  letI : Nonempty (Fin (w1MatchingR n)) := fin_nonempty n
  have hrep : (fun s : Fin (w1MatchingR n) => signed n s) =
      fun s => c n * sign n s := rfl
  change expect w1Uniform (fun s : Fin (w1MatchingR n) => signed n s) = 0
  rw [hrep]
  calc
    expect w1Uniform (fun s : Fin (w1MatchingR n) => c n * sign n s) =
        c n * expect w1Uniform (sign n) := by
          exact AronowAudit.P044.expect_const_mul w1Uniform (sign n) (c n)
    _ = 0 := by rw [uniform_sign_mean n hg hm]; ring
private theorem uniform_signed_sq (n : ℕ) : expect w1Uniform (fun s : Fin (w1MatchingR n) => signed n s ^ 2) = c n ^ 2 := by
  letI : Nonempty (Fin (w1MatchingR n)) := fin_nonempty n
  have hrep : (fun s : Fin (w1MatchingR n) => signed n s ^ 2) =
      fun _ => c n ^ 2 := by
    funext s
    cases hb : w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ <;>
      simp [signed, sign, hb] <;> ring
  rw [hrep, uniform_const]
private theorem signed_sq_const (n : ℕ) (s : Fin (w1MatchingR n)) : signed n s ^ 2 = c n ^ 2 := by
  cases hb : w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ <;>
    simp [signed, sign, hb] <;> ring
private theorem N_pos (n : ℕ) : 0 < (w1MatchingN n : ℚ) := by
  unfold w1MatchingN
  positivity
private theorem w_pos (n : ℕ) : 0 < w1MatchingWeight n := by
  unfold w1MatchingWeight
  positivity
private theorem q_pos (n : ℕ) : 0 < w1MatchingJoint n := by
  unfold w1MatchingJoint
  positivity
private theorem c_sq (n : ℕ) : c n ^ 2 = 4 / ((w1MatchingN n : ℚ) ^ 2 * w1MatchingWeight n ^ 2) := by
  unfold c
  have hN := ne_of_gt (N_pos n)
  have hw := ne_of_gt (w_pos n)
  field_simp
  <;> ring
private theorem v_const (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n))) (s : Fin (w1MatchingR n)) (hwithin : W1MatchingWithin n) (hcross : W1MatchingCross n) : w1MatchingV n e s = (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n - 2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 := by
  unfold w1MatchingV varianceEstimate
  rw [hwithin e s, hcross e s]
  have hw := ne_of_gt (w_pos n)
  have hq := ne_of_gt (q_pos n)
  have hN := ne_of_gt (N_pos n)
  field_simp
  <;> ring
private theorem shortfall_formula (n : ℕ) : (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n - 2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 - 4 / ((w1MatchingN n : ℚ) ^ 2 * w1MatchingWeight n ^ 2) = -2 * (2 * (n : ℚ) + 5) / (((n : ℚ) + 2) * ((n : ℚ) + 3) * (w1MatchingN n : ℚ) ^ 2) := by
  unfold w1MatchingWeight w1MatchingJoint w1MatchingN
  have hn : (2 * (n : ℚ) + 5) ≠ 0 := by positivity
  have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have hn3 : ((n : ℚ) + 3) ≠ 0 := by positivity
  have hnN : (2 * ((n : ℚ) + 3)) ≠ 0 := by positivity
  field_simp
  <;> ring_nf
private theorem shortfall_neg (n : ℕ) :
    -2 * (2 * (n : ℚ) + 5) /
      (((n : ℚ) + 2) * ((n : ℚ) + 3) * (w1MatchingN n : ℚ) ^ 2) < 0 := by
  apply div_neg_of_neg_of_pos
  · have hp : 0 < 2 * (n : ℚ) + 5 := by positivity
    linarith
  · have hN := N_pos n
    positivity
end
end SAP.P044.WH.W1.P.T2_L8
open SAP.P044 AronowAudit.P044 SAP.P044.WH.W1.P.T2_L8
/-- The independent-observation and first-bank-row moment calculations for the matching witness. -/
theorem SAP.P044.WH.W1.T2_L8_proof : SAP.P044.WH.W1.T2_L8 := by
  intro n hg hm hpoint hwithin hcross hlaw
  dsimp only [W1MatchingMoments]
  letI : Nonempty (Fin (w1MatchingR n)) := fin_nonempty n
  let first : Fin (w1MatchingR n) := w1MatchingFirst n
  have ht_ind_fun : (fun x : Equiv.Perm (Fin (w1MatchingR n)) × Fin (w1MatchingR n) =>
      w1MatchingT n x.1 x.2) = fun x => signed n x.2 := by
    funext x
    rw [hpoint x.1 x.2]
    change (if w1MatchingAssignments n x.2 ⟨0, by unfold w1MatchingN; omega⟩ then
        2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) else
        -(2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n))) =
      c n * (if w1MatchingAssignments n x.2 ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else -1)
    cases hb : w1MatchingAssignments n x.2 ⟨0, by unfold w1MatchingN; omega⟩ <;>
      simp [hb, c] <;> ring
  have ht_ind_sq_fun : (fun x : Equiv.Perm (Fin (w1MatchingR n)) × Fin (w1MatchingR n) =>
      w1MatchingT n x.1 x.2 ^ 2) = fun x => signed n x.2 ^ 2 := by
    funext x
    rw [hpoint x.1 x.2]
    change (if w1MatchingAssignments n x.2 ⟨0, by unfold w1MatchingN; omega⟩ then
        2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) else
        -(2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n))) ^ 2 =
      (c n * (if w1MatchingAssignments n x.2 ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else -1)) ^ 2
    cases hb : w1MatchingAssignments n x.2 ⟨0, by unfold w1MatchingN; omega⟩ <;>
      simp [hb, c] <;> ring
  have ht_ind_mean : expect (w1MatchingIndependentMass n)
      (fun x => w1MatchingT n x.1 x.2) = 0 := by
    rw [ht_ind_fun, independent_expect_snd, uniform_signed_mean n hg hm]
  have ht_ind_second : expect (w1MatchingIndependentMass n)
      (fun x => w1MatchingT n x.1 x.2 ^ 2) = c n ^ 2 := by
    calc
      expect (w1MatchingIndependentMass n) (fun x => w1MatchingT n x.1 x.2 ^ 2) =
          expect (w1MatchingIndependentMass n) (fun x => signed n x.2 ^ 2) := by
            apply congrArg (expect (w1MatchingIndependentMass n))
            funext x
            exact congrArg (fun z : ℚ => z ^ 2) (congrFun ht_ind_fun x)
      _ = expect w1Uniform (fun s : Fin (w1MatchingR n) => signed n s ^ 2) :=
          independent_expect_snd n (fun s => signed n s ^ 2)
      _ = c n ^ 2 := uniform_signed_sq n
  have ht1_fun : (fun e : Equiv.Perm (Fin (w1MatchingR n)) =>
      w1MatchingT n e (e first)) = fun e => signed n (e first) := by
    funext e
    rw [hpoint e (e first)]
    change (if w1MatchingAssignments n (e first) ⟨0, by unfold w1MatchingN; omega⟩ then
        2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) else
        -(2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n))) =
      c n * (if w1MatchingAssignments n (e first) ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else -1)
    cases hb : w1MatchingAssignments n (e first) ⟨0, by unfold w1MatchingN; omega⟩ <;>
      simp [hb, c] <;> ring
  have ht1_sq_fun : (fun e : Equiv.Perm (Fin (w1MatchingR n)) =>
      w1MatchingT n e (e first) ^ 2) = fun e => signed n (e first) ^ 2 := by
    funext e
    rw [hpoint e (e first)]
    change (if w1MatchingAssignments n (e first) ⟨0, by unfold w1MatchingN; omega⟩ then
        2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) else
        -(2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n))) ^ 2 =
      (c n * (if w1MatchingAssignments n (e first) ⟨0, by unfold w1MatchingN; omega⟩ then (1 : ℚ) else -1)) ^ 2
    cases hb : w1MatchingAssignments n (e first) ⟨0, by unfold w1MatchingN; omega⟩ <;>
      simp [hb, c] <;> ring
  have ht1_mean : expect w1Uniform
      (fun e : Equiv.Perm (Fin (w1MatchingR n)) => w1MatchingT n e (e first)) = 0 := by
    rw [ht1_fun, hlaw first (signed n), uniform_signed_mean n hg hm]
  haveI : Nonempty (Equiv.Perm (Fin (w1MatchingR n))) := ⟨Equiv.refl _⟩
  have ht1_second : expect w1Uniform
      (fun e : Equiv.Perm (Fin (w1MatchingR n)) =>
        w1MatchingT n e (e first) ^ 2) = c n ^ 2 := by
    calc
      expect w1Uniform (fun e : Equiv.Perm (Fin (w1MatchingR n)) =>
          w1MatchingT n e (e first) ^ 2) =
          expect w1Uniform (fun e : Equiv.Perm (Fin (w1MatchingR n)) =>
            signed n (e first) ^ 2) := by
            apply congrArg (expect w1Uniform)
            funext e
            exact congrArg (fun z : ℚ => z ^ 2) (congrFun ht1_fun e)
      _ = c n ^ 2 := by
          have hc : (fun e : Equiv.Perm (Fin (w1MatchingR n)) => signed n (e first) ^ 2) =
              fun _ : Equiv.Perm (Fin (w1MatchingR n)) => c n ^ 2 := by
                funext e
                exact signed_sq_const n (e first)
          rw [hc]
          exact uniform_const _
  have hv_ind_fun : (fun x : Equiv.Perm (Fin (w1MatchingR n)) × Fin (w1MatchingR n) =>
      w1MatchingV n x.1 x.2) = fun _ =>
      (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
        2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 := by
    funext x
    exact v_const n x.1 x.2 hwithin hcross
  have hv_ind : expect (w1MatchingIndependentMass n)
      (fun x => w1MatchingV n x.1 x.2) =
      (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
        2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 := by
    rw [hv_ind_fun]
    calc
      expect (w1MatchingIndependentMass n) (fun _ =>
          (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
            2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2) =
          expect w1Uniform (fun _ : Fin (w1MatchingR n) =>
            (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
              2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2) :=
            independent_expect_snd n (fun _ : Fin (w1MatchingR n) =>
              (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
                2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2)
      _ = _ := uniform_const _
  have hv1_fun : (fun e : Equiv.Perm (Fin (w1MatchingR n)) =>
      w1MatchingV n e (e first)) = fun _ =>
      (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
        2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 := by
    funext e
    exact v_const n e (e first) hwithin hcross
  have hv1 : expect w1Uniform
      (fun e : Equiv.Perm (Fin (w1MatchingR n)) => w1MatchingV n e (e first)) =
      (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
        2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 := by
    rw [hv1_fun]
    exact uniform_const _
  have hvar_ind : designVariance (w1MatchingIndependentMass n)
      (fun x => w1MatchingT n x.1 x.2) =
      4 / ((w1MatchingN n : ℚ) ^ 2 * w1MatchingWeight n ^ 2) := by
    unfold designVariance
    rw [ht_ind_second, ht_ind_mean, c_sq]
    norm_num
  have hvar1 : designVariance w1Uniform
      (fun e : Equiv.Perm (Fin (w1MatchingR n)) => w1MatchingT n e (e first)) =
      4 / ((w1MatchingN n : ℚ) ^ 2 * w1MatchingWeight n ^ 2) := by
    unfold designVariance
    rw [ht1_second, ht1_mean, c_sq]
    norm_num
  have hshort :
      (4 / w1MatchingWeight n ^ 2 + 2 / w1MatchingWeight n -
        2 / w1MatchingJoint n) / (w1MatchingN n : ℚ) ^ 2 -
        4 / ((w1MatchingN n : ℚ) ^ 2 * w1MatchingWeight n ^ 2) =
      -2 * (2 * (n : ℚ) + 5) /
        (((n : ℚ) + 2) * ((n : ℚ) + 3) * (w1MatchingN n : ℚ) ^ 2) :=
    shortfall_formula n
  have hneg := shortfall_neg n
  refine ⟨ht_ind_mean, hvar_ind, hv_ind, ht1_mean, hvar1, hv1, ?_, ?_, ?_, ?_⟩
  · rw [hv_ind, hvar_ind]
    exact hshort
  · rw [hv1, hvar1]
    exact hshort
  · rw [hv_ind, hvar_ind]
    linarith [hshort, hneg]
  · rw [hv1, hvar1]
    linarith [hshort, hneg]
