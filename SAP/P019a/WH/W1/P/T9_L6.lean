import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T9_L6

open SAP.P019a Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical

theorem finite_mean_difference_bound {α : Type*} [Fintype α]
    (P : FiniteLaw α) (D : α → Prop) [DecidablePred D]
    (f g : α → ℝ) (K : ℝ)
    (hf : ∀ x, |f x| ≤ K) (hg : ∀ x, |g x| ≤ K)
    (heq : ∀ x, D x → f x = g x) :
    |P.mean f - P.mean g| ≤ (2 * |K|) * P.prob (fun x => ¬ D x) := by
  let B := 2 * |K|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfg (x : α) : |f x - g x| ≤ B := by
    have hfx : |f x| ≤ |K| := le_trans (hf x) (le_abs_self K)
    have hgx : |g x| ≤ |K| := le_trans (hg x) (le_abs_self K)
    dsimp [B]
    calc
      |f x - g x| = |f x + -g x| := by rw [sub_eq_add_neg]
      _ ≤ |f x| + |-g x| := abs_add_le _ _
      _ = |f x| + |g x| := by rw [abs_neg]
      _ ≤ |K| + |K| := add_le_add hfx hgx
      _ = 2 * |K| := by ring
  have hterm (x : α) :
      -(B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0))) ≤
        P.mass x * (f x - g x) ∧
      P.mass x * (f x - g x) ≤
        B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0)) := by
    by_cases hd : D x
    · simp [hd, heq x hd]
    · have h := abs_le.mp (hfg x)
      have hl := mul_le_mul_of_nonneg_left h.1 (P.nonneg x)
      have hu := mul_le_mul_of_nonneg_left h.2 (P.nonneg x)
      constructor
      · calc
          -(B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0))) = P.mass x * -B := by
            simp [hd]; ring
          _ ≤ P.mass x * (f x - g x) := hl
      · calc
          P.mass x * (f x - g x) ≤ P.mass x * B := hu
          _ = B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0)) := by
            simp [hd]; ring
  have hlo := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => (hterm x).1)
  have hhi := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => (hterm x).2)
  have hmeanSub : P.mean (fun x => f x - g x) = P.mean f - P.mean g := by
    have h := AronowAudit.P019.mean_sub (SAP.P019a.Bridge.toLaw P) f g
    simpa only [SAP.P019a.Bridge.mean_eq] using h
  have hprob : P.prob (fun x => ¬ D x) =
      ∑ x, P.mass x * (if ¬ D x then (1 : ℝ) else 0) := rfl
  have hsum : P.mean (fun x => f x - g x) =
      ∑ x, P.mass x * (f x - g x) := rfl
  change |P.mean f - P.mean g| ≤ B * P.prob (fun x => ¬ D x)
  rw [← hmeanSub, hsum]
  apply abs_le.mpr
  constructor
  · calc
      -(B * P.prob (fun x => ¬ D x)) =
          ∑ x, -(B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0))) := by
            calc
              -(B * P.prob (fun x => ¬ D x)) =
                  -(B * ∑ x, P.mass x * (if ¬ D x then (1 : ℝ) else 0)) := by rw [hprob]
              _ = -(∑ x, B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0))) := by rw [Finset.mul_sum]
              _ = ∑ x, -(B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0))) := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ x, P.mass x * (f x - g x) := hlo
  · calc
      ∑ x, P.mass x * (f x - g x) ≤
          ∑ x, B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0)) := hhi
      _ = B * P.prob (fun x => ¬ D x) := by
          calc
            ∑ x, B * (P.mass x * (if ¬ D x then (1 : ℝ) else 0)) =
                B * ∑ x, P.mass x * (if ¬ D x then (1 : ℝ) else 0) := by rw [Finset.mul_sum]
            _ = B * P.prob (fun x => ¬ D x) := by rw [hprob]

theorem finite_probability_complement {α : Type*} [Fintype α]
    (P : FiniteLaw α) (D : α → Prop) [DecidablePred D] :
    P.prob (fun x => ¬ D x) = 1 - P.prob D := by
  have h := AronowAudit.P019.probability_complement (SAP.P019a.Bridge.toLaw P) D
  simpa only [SAP.P019a.Bridge.prob_eq] using h

end

end SAP.P019a.WH.W1.P.T9_L6

open SAP.P019a Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

theorem SAP.P019a.WH.W1.T9_L6_proof : SAP.P019a.WH.W1.T9_L6 := by
  classical
  intro E _ P D hD F _ _ _ T C Q hQ hAgree hT
  intro f hf hBound
  obtain ⟨K, hK⟩ := hBound
  have hTlim := hT f hf ⟨K, hK⟩
  have hbad : Tendsto (fun n : ℕ => (P.iid n).prob (fun s => ¬ D n s))
      atTop (nhds 0) := by
    have hEq : (fun n : ℕ => (P.iid n).prob (fun s => ¬ D n s)) =
        fun n => 1 - (P.iid n).prob (D n) := by
      funext n
      exact SAP.P019a.WH.W1.P.T9_L6.finite_probability_complement (P.iid n) (D n)
    rw [hEq]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hD
  have herror : Tendsto (fun n : ℕ =>
      (2 * |K|) * (P.iid n).prob (fun s => ¬ D n s)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 * |K|))).mul hbad
  have hdiff : Tendsto (fun n : ℕ =>
      (P.iid n).mean (fun s => f (C n s)) -
        (P.iid n).mean (fun s => f (T n s))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_) herror
    exact SAP.P019a.WH.W1.P.T9_L6.finite_mean_difference_bound (P.iid n) (D n)
      (fun s => f (C n s)) (fun s => f (T n s)) K
      (fun s => hK (C n s)) (fun s => hK (T n s)) (fun s hs => by
        rw [hAgree n s hs])
  have hfun : (fun n : ℕ => (P.iid n).mean (fun s => f (C n s))) =
      fun n => ((P.iid n).mean (fun s => f (C n s)) -
        (P.iid n).mean (fun s => f (T n s))) +
          (P.iid n).mean (fun s => f (T n s)) := by
    funext n
    ring
  rw [hfun]
  simpa using hdiff.add hTlim

