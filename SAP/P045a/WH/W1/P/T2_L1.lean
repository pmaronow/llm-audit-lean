import SAP.P045a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset
open SAP.P045a
open SAP.P045a.WH.W1

namespace SAP.P045a.WH.W1.P.T2_L1
noncomputable section

theorem expect_of_pushforward {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (q : β → ℝ) (X : β → ℝ)
    (h : ∀ z, prob p (fun a => f a = z) = q z) :
    expect p (fun a => X (f a)) = expect q X := by
  classical
  have hfiber (z : β) : (∑ a, if f a = z then p a else 0) = q z := by
    simpa [prob, expect, mul_ite, mul_one, mul_zero] using h z
  calc
    expect p (fun a => X (f a)) =
        ∑ a, ∑ z, if f a = z then p a * X z else 0 := by
      unfold expect
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro z hz hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = ∑ z, ∑ a, if f a = z then p a * X z else 0 := Finset.sum_comm
    _ = ∑ z, (∑ a, if f a = z then p a else 0) * X z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    _ = expect q X := by
      simp_rw [hfiber]
      rfl

theorem expect_finset_sum_local {Ω I : Type*} [Fintype Ω]
    (p : Ω → ℝ) (S : Finset I) (X : I → Ω → ℝ) :
    expect p (fun w => ∑ i ∈ S, X i w) = ∑ i ∈ S, expect p (X i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_regime_sum {G : ℕ} {n : Fin G → ℕ}
    (QH : Design (GroupAssignments n))
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (X : (g : Fin G) → Assignment (n g) → ℝ)
    (R : Finset (Fin G))
    (hcoord : ∀ g ∈ R, ∀ z,
      prob QH.mass (fun u => u g = z) = q g z) :
    expect QH.mass (fun u => ∑ g ∈ R, X g (u g)) =
      ∑ g ∈ R, expect (q g) (X g) := by
  rw [expect_finset_sum_local]
  apply Finset.sum_congr rfl
  intro g hg
  exact expect_of_pushforward QH.mass (fun u => u g) (q g) (X g) (hcoord g hg)

theorem joint_regime_average {G C : ℕ} {n : Fin G → ℕ}
    (hCG : C ≤ G)
    (Q : Finset (Fin G) → Design (GroupAssignments n))
    (X : (g : Fin G) → Assignment (n g) → ℝ)
    (high : Bool) (hcount : 0 < w1RegimeCount G C high) :
    expect (w1JointMass C Q) (w1RegimeMean C high X) =
      average (firstStageSets G C) (fun H =>
        (∑ g ∈ w1RegimeSet high H,
          expect (Q H).mass (fun u => X g (u g))) / w1RegimeCount G C high) := by
  classical
  let S := firstStageSets G C
  let k : ℝ := w1RegimeCount G C high
  have hk : k ≠ 0 := by
    dsimp [k]
    exact ne_of_gt (Nat.cast_pos.mpr hcount)
  have hS : (S.card : ℝ) ≠ 0 := by
    have hpos : 0 < S.card := by
      apply Finset.card_pos.mpr
      exact Finset.powersetCard_nonempty.mpr (by simpa using hCG)
    exact ne_of_gt (Nat.cast_pos.mpr hpos)
  have hinner (H : Finset (Fin G)) :
      (∑ u : GroupAssignments n,
        (if H ∈ S then (Q H).mass u / (S.card : ℝ) else 0) *
          ((∑ g ∈ w1RegimeSet high H, X g (u g)) / k)) =
        if H ∈ S then
          (∑ g ∈ w1RegimeSet high H,
            expect (Q H).mass (fun u => X g (u g))) / k / (S.card : ℝ)
        else 0 := by
    by_cases hH : H ∈ S
    · simp only [hH, if_pos]
      calc
        (∑ u : GroupAssignments n,
            (Q H).mass u / (S.card : ℝ) *
              ((∑ g ∈ w1RegimeSet high H, X g (u g)) / k)) =
            (∑ u : GroupAssignments n,
              (Q H).mass u * (∑ g ∈ w1RegimeSet high H, X g (u g))) *
                ((S.card : ℝ)⁻¹ * k⁻¹) := by
          simp only [div_eq_mul_inv]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u hu
          ring
        _ = expect (Q H).mass
              (fun u => ∑ g ∈ w1RegimeSet high H, X g (u g)) *
                ((S.card : ℝ)⁻¹ * k⁻¹) := rfl
        _ = (∑ g ∈ w1RegimeSet high H,
              expect (Q H).mass (fun u => X g (u g))) / k / (S.card : ℝ) := by
          rw [expect_finset_sum_local]
          simp only [div_eq_mul_inv]
          ring
    · simp [hH]
  calc
    expect (w1JointMass C Q) (w1RegimeMean C high X) =
        ∑ H : Finset (Fin G), ∑ u : GroupAssignments n,
          (if H ∈ S then (Q H).mass u / (S.card : ℝ) else 0) *
            ((∑ g ∈ w1RegimeSet high H, X g (u g)) / k) := by
      unfold expect w1JointMass w1RegimeMean
      simp only [Fintype.sum_prod_type]
      rfl
    _ = ∑ H : Finset (Fin G),
          if H ∈ S then
            (∑ g ∈ w1RegimeSet high H,
              expect (Q H).mass (fun u => X g (u g))) / k / (S.card : ℝ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      exact hinner H
    _ = average S (fun H =>
          (∑ g ∈ w1RegimeSet high H,
            expect (Q H).mass (fun u => X g (u g))) / w1RegimeCount G C high) := by
      have hrestrict :
          (∑ H : Finset (Fin G),
            if H ∈ S then
              (∑ g ∈ w1RegimeSet high H,
                expect (Q H).mass (fun u => X g (u g))) / k / (S.card : ℝ)
            else 0) =
          ∑ H ∈ S,
            (∑ g ∈ w1RegimeSet high H,
              expect (Q H).mass (fun u => X g (u g))) / k / (S.card : ℝ) := by
        simp
      rw [hrestrict]
      simp only [average, S, k]
      rw [← Finset.sum_div]

end
end SAP.P045a.WH.W1.P.T2_L1

open SAP.P045a.WH.W1.P.T2_L1

theorem SAP.P045a.WH.W1.T2_L1_proof : SAP.P045a.WH.W1.T2_L1 := by
  intro G C hCG n high hcount Q q hlaw X
  let E : Fin G → ℝ := fun g => expect (q g) (X g)
  have hreduce := joint_regime_average hCG Q X high hcount
  have hgroups :
      average (firstStageSets G C) (fun H =>
        (∑ g ∈ w1RegimeSet high H,
          expect (Q H).mass (fun u => X g (u g))) / w1RegimeCount G C high) =
        average (firstStageSets G C) (fun H =>
          (∑ g ∈ w1RegimeSet high H, E g) / w1RegimeCount G C high) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro H hH
    have hsum := expect_regime_sum (Q H) q X (w1RegimeSet high H)
      (fun g hg z => hlaw H hH g hg z)
    have hlocal := expect_finset_sum_local (Q H).mass (w1RegimeSet high H)
      (fun g u => X g (u g))
    have htotal := hlocal.symm.trans hsum
    simpa [E] using congrArg
      (fun v : ℝ => v / w1RegimeCount G C high) htotal
  have htarget :
      average (firstStageSets G C) (fun H =>
        (∑ g ∈ w1RegimeSet high H, E g) / w1RegimeCount G C high) = mean E := by
    cases high with
    | false =>
      have hlt : C < G := by simpa [w1RegimeCount] using hcount
      have hk : 0 < G - C := by omega
      have hcomp := AronowAudit.P045.Wave1.dvc_complement_average
        (N := G) (s := C) hCG
        (fun T : Finset (Fin G) => (∑ g ∈ T, E g) / (G - C))
      have huniform := AronowAudit.P045.uniform_first_stage_mean hk (Nat.sub_le G C) E
      have huniform' :
          AronowAudit.P045.average (AronowAudit.P045.firstStageSets G (G - C))
              (fun T => (∑ g ∈ T, E g) / (↑G - ↑C)) = AronowAudit.P045.mean E := by
        simpa only [Nat.cast_sub hCG] using huniform
      have htotal := hcomp.trans huniform'
      simpa only [average, AronowAudit.P045.average, mean,
        AronowAudit.P045.mean, firstStageSets,
        AronowAudit.P045.firstStageSets, w1RegimeSet, w1RegimeCount,
        Bool.false_eq_true, if_false, Nat.cast_sub hCG] using htotal
    | true =>
      have hC : 0 < C := by simpa [w1RegimeCount] using hcount
      exact AronowAudit.P045.uniform_first_stage_mean hC hCG E
  calc
    expect (w1JointMass C Q) (w1RegimeMean C high X) =
        average (firstStageSets G C) (fun H =>
          (∑ g ∈ w1RegimeSet high H,
            expect (Q H).mass (fun u => X g (u g))) / w1RegimeCount G C high) := hreduce
    _ = average (firstStageSets G C) (fun H =>
          (∑ g ∈ w1RegimeSet high H, E g) / w1RegimeCount G C high) := hgroups
    _ = mean E := htarget
    _ = mean (fun g => expect (q g) (X g)) := by rfl

