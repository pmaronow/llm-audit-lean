import SAP.P005a.WH.W2.Leaves
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L12

noncomputable section

open Finset
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

lemma subsetSum_hermitian {N k : ℕ} (X : Fin N → Matrix (Fin k) (Fin k) ℝ)
    (hX : ∀ i, (X i).IsHermitian) (S : Finset (Fin N)) :
    (SAP.P005a.WH.W2.subsetSum X S).IsHermitian := by
  classical
  unfold SAP.P005a.WH.W2.subsetSum
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (hX i).add ih

lemma scaledTraceExp_convex (k : ℕ) (θ : ℝ)
    (hC : SAP.P005a.WH.W2.traceExpConvex) :
    ConvexOn ℝ (SAP.P005a.WH.W2.hermitianSet k)
      (fun A => SAP.P005a.WH.W2.traceExp (θ • A)) := by
  let L : Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ :=
    θ • (LinearMap.id : Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ)
  have hL : ∀ A, A ∈ SAP.P005a.WH.W2.hermitianSet k → L A ∈
      SAP.P005a.WH.W2.hermitianSet k := by
    intro A hA
    change (θ • A).IsHermitian
    exact hA.smul (by unfold IsSelfAdjoint; rfl)
  have hc := (hC k).comp_linearMap L
  refine ⟨?_, ?_⟩
  · exact (hC k).1
  · intro A hA B hB a b ha hb hab
    have h := hc.2 (hL A hA) (hL B hB) ha hb hab
    simpa [Function.comp, L, LinearMap.smul_apply, smul_smul] using h

lemma log_two_bounds :
    (9 / 16 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 3 / 4 := by
  constructor
  · have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  · have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith

lemma upper_scalar_bound (s : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    (1 + μ)^s / Real.exp (Real.log 2 * (2 * (s : ℝ) * μ)) ≤
      Real.exp (-((s : ℝ) * μ) / 8) := by
  let x : ℝ := (s : ℝ) * μ
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hμ
  have hlog : Real.log (1 + μ) ≤ μ := by
    calc
      Real.log (1 + μ) ≤ (1 + μ) - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      _ = μ := by ring
  have hbase : 1 + μ ≤ Real.exp μ := Real.le_exp_of_log_le hlog
  have hpow : (1 + μ)^s ≤ Real.exp x := by
    rw [show x = (s : ℝ) * μ by rfl, Real.exp_nat_mul μ s]
    exact pow_le_pow_left₀ (by positivity) hbase s
  have hlog2 := log_two_bounds.1
  have hxlog : (9 / 8 : ℝ) * x ≤ Real.log 2 * (2 * x) := by
    have hh := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ 2 * x)
    nlinarith
  have hexp : Real.exp x ≤ Real.exp (-x / 8 + Real.log 2 * (2 * x)) := by
    apply Real.exp_le_exp.mpr
    linarith
  apply (div_le_iff₀ (Real.exp_pos _)).2
  rw [← Real.exp_add]
  have hpow' : (1 + μ)^s ≤ Real.exp ((s : ℝ) * μ) := by simpa [x] using hpow
  have hexp' : Real.exp ((s : ℝ) * μ) ≤
      Real.exp (-((s : ℝ) * μ) / 8 + Real.log 2 * (2 * (s : ℝ) * μ)) := by
    simpa [x, mul_assoc] using hexp
  exact hpow'.trans hexp'

lemma lower_scalar_bound (s : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (1 - μ / 2)^s / Real.exp (Real.log 2 * (-((s : ℝ) * μ) / 2)) ≤
      Real.exp (-((s : ℝ) * μ) / 8) := by
  let x : ℝ := (s : ℝ) * μ
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hμ0
  have hbase : 1 - μ / 2 ≤ Real.exp (-μ / 2) := by
    have h := Real.add_one_le_exp (-μ / 2)
    nlinarith
  have hpow : (1 - μ / 2)^s ≤ Real.exp (-x / 2) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - μ / 2) hbase s
    rw [← Real.exp_nat_mul (-μ / 2) s] at h
    have heq : (s : ℝ) * (-μ / 2) = -x / 2 := by dsimp [x]; ring
    rw [heq] at h
    exact h
  have hlog2 := log_two_bounds.2
  have hxlog : Real.log 2 * (x / 2) ≤ (3 / 8 : ℝ) * x := by
    have hh := mul_le_mul_of_nonneg_right hlog2 (by positivity : 0 ≤ x / 2)
    nlinarith
  have hexp : Real.exp (-x / 2) ≤ Real.exp (-x / 8 + Real.log 2 * (-x / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (div_le_iff₀ (Real.exp_pos _)).2
  rw [← Real.exp_add]
  exact hpow.trans hexp

end

end SAP.P005a.WH.W2.P.T9_L12

open Finset Filter SAP.P005a.Bridge
open SAP.P005a.WH.W2.P.T9_L12
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

theorem SAP.P005a.WH.W2.T9_L12_proof : SAP.P005a.WH.W2.T9_L12 := by
  intro hSpec hConv hSampling hMGF N k s hN hk hsn X hX μ hμ hμ1 hmean
  let upper : Finset (Fin N) → Prop := fun S =>
    ∃ v : Fin k → ℝ, SAP.P005a.WH.W2.unitVector v ∧
      2 * (s : ℝ) * μ < SAP.P005a.WH.W2.quadratic
        (SAP.P005a.WH.W2.subsetSum X S) v
  let lower : Finset (Fin N) → Prop := fun S =>
    ∃ v : Fin k → ℝ, SAP.P005a.WH.W2.unitVector v ∧
      SAP.P005a.WH.W2.quadratic (SAP.P005a.WH.W2.subsetSum X S) v <
        (s : ℝ) * μ / 2
  let bad : Finset (Fin N) → Prop := fun S =>
    ∃ v : Fin k → ℝ, SAP.P005a.WH.W2.unitVector v ∧
      (SAP.P005a.WH.W2.quadratic (SAP.P005a.WH.W2.subsetSum X S) v <
          (s : ℝ) * μ / 2 ∨
        2 * (s : ℝ) * μ <
          SAP.P005a.WH.W2.quadratic (SAP.P005a.WH.W2.subsetSum X S) v)
  let θ : ℝ := Real.log 2
  let x : ℝ := (s : ℝ) * μ
  have hθ : 0 < θ := Real.log_pos (by norm_num)
  have hXherm : ∀ i, (X i).IsHermitian := by
    intro i
    exact (hX i).1.1
  have htraceUpper :
      expectation s (fun S => SAP.P005a.WH.W2.traceExp
        (θ • SAP.P005a.WH.W2.subsetSum X S)) ≤ (k : ℝ) * (1 + μ)^s := by
    have hconv := scaledTraceExp_convex k θ hConv
    calc
      expectation s (fun S => SAP.P005a.WH.W2.traceExp
          (θ • SAP.P005a.WH.W2.subsetSum X S)) ≤
        iidAverage N s (fun w => SAP.P005a.WH.W2.traceExp
          (θ • SAP.P005a.WH.W2.drawSum X w)) := by
            exact hSampling N k s hN hsn X hXherm _ hconv
      _ ≤ (k : ℝ) * (1 + μ * (Real.exp θ - 1))^s :=
        hMGF N k s hN X hX μ hμ.le hμ1 hmean θ
      _ = (k : ℝ) * (1 + μ)^s := by
        have he : Real.exp θ = 2 := by
          rw [show θ = Real.log 2 by rfl, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [he]
        ring
  have htraceLower :
      expectation s (fun S => SAP.P005a.WH.W2.traceExp
        (θ • (-SAP.P005a.WH.W2.subsetSum X S))) ≤ (k : ℝ) * (1 - μ / 2)^s := by
    have hconv := scaledTraceExp_convex k (-θ) hConv
    have hnegExp : Real.exp (-θ) = (1 / 2 : ℝ) := by
      rw [show θ = Real.log 2 by rfl, Real.exp_neg,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    calc
      expectation s (fun S => SAP.P005a.WH.W2.traceExp
          (θ • (-SAP.P005a.WH.W2.subsetSum X S))) =
        expectation s (fun S => SAP.P005a.WH.W2.traceExp
          ((-θ) • SAP.P005a.WH.W2.subsetSum X S)) := by
            apply congrArg (fun f => expectation s f)
            funext S
            simp [smul_neg, neg_smul]
      _ ≤ iidAverage N s (fun w => SAP.P005a.WH.W2.traceExp
          ((-θ) • SAP.P005a.WH.W2.drawSum X w)) := by
            exact hSampling N k s hN hsn X hXherm _ hconv
      _ ≤ (k : ℝ) * (1 + μ * (Real.exp (-θ) - 1))^s :=
        hMGF N k s hN X hX μ hμ.le hμ1 hmean (-θ)
      _ = (k : ℝ) * (1 - μ / 2)^s := by rw [hnegExp]; ring
  have hupperNonneg : ∀ S ∈ design N s,
      0 ≤ SAP.P005a.WH.W2.traceExp
        (θ • SAP.P005a.WH.W2.subsetSum X S) := by
    intro S hS
    have hA := subsetSum_hermitian X hXherm S
    have hAθ : (θ • SAP.P005a.WH.W2.subsetSum X S).IsHermitian :=
      hA.smul (by unfold IsSelfAdjoint; rfl)
    have hp := (hSpec k _ hAθ).1
    unfold SAP.P005a.WH.W2.traceExp
    exact hp.trace_nonneg
  have hlowerNonneg : ∀ S ∈ design N s,
      0 ≤ SAP.P005a.WH.W2.traceExp
        (θ • (-SAP.P005a.WH.W2.subsetSum X S)) := by
    intro S hS
    have hA := (subsetSum_hermitian X hXherm S).neg
    have hAθ : (θ • (-SAP.P005a.WH.W2.subsetSum X S)).IsHermitian :=
      hA.smul (by unfold IsSelfAdjoint; rfl)
    have hp := (hSpec k _ hAθ).1
    unfold SAP.P005a.WH.W2.traceExp
    exact hp.trace_nonneg
  have hupperProb : probability s upper ≤
      (k : ℝ) * Real.exp (-x / 8) := by
    let B : ℝ := Real.exp (θ * (2 * x))
    have hB : 0 < B := Real.exp_pos _
    have hmark := AronowAudit.P005.Wave1.CondT8T9_markov s
      (fun S => SAP.P005a.WH.W2.traceExp
        (θ • SAP.P005a.WH.W2.subsetSum X S)) hupperNonneg B hB
    have hdom : probability s upper ≤ probability s (fun S => B <
        SAP.P005a.WH.W2.traceExp (θ • SAP.P005a.WH.W2.subsetSum X S)) := by
      apply AronowAudit.P005.Wave1.CondT8T9_probability_mono
      intro S hS hU
      rcases hU with ⟨v, hv, hvq⟩
      let q := SAP.P005a.WH.W2.quadratic
        (SAP.P005a.WH.W2.subsetSum X S) v
      let a := 2 * x
      let b := (a + q) / 2
      have hab : a < b := by dsimp [b]; linarith
      have hbq : b < q := by dsimp [b]; linarith
      have hA := subsetSum_hermitian X hXherm S
      have hspec := (hSpec k (SAP.P005a.WH.W2.subsetSum X S) hA).2 b θ hθ
        ⟨v, hv, by simpa [q, b, a, x] using hbq⟩
      have hexp : Real.exp (θ * a) < Real.exp (θ * b) :=
        Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hθ)
      dsimp [B]
      exact lt_of_lt_of_le (by simpa [a] using hexp) hspec
    have hmarkov := hdom.trans hmark
    have hE : expectation s (fun S => SAP.P005a.WH.W2.traceExp
        (θ • SAP.P005a.WH.W2.subsetSum X S)) / B ≤
        (k : ℝ) * Real.exp (-x / 8) := by
      have hscl := upper_scalar_bound s μ hμ.le
      have hdiv := div_le_div_of_nonneg_right htraceUpper (le_of_lt hB)
      have hquot : (1 + μ)^s / B ≤ Real.exp (-x / 8) := by
        simpa [B, x, θ, mul_assoc] using hscl
      calc
        _ ≤ (k : ℝ) * (1 + μ)^s / B := hdiv
        _ = (k : ℝ) * ((1 + μ)^s / B) := by ring
        _ ≤ (k : ℝ) * Real.exp (-x / 8) :=
          mul_le_mul_of_nonneg_left hquot (by positivity : 0 ≤ (k : ℝ))
    exact hmarkov.trans hE
  have hlowerProb : probability s lower ≤
      (k : ℝ) * Real.exp (-x / 8) := by
    let B : ℝ := Real.exp (θ * (-x / 2))
    have hB : 0 < B := Real.exp_pos _
    have hmark := AronowAudit.P005.Wave1.CondT8T9_markov s
      (fun S => SAP.P005a.WH.W2.traceExp
        (θ • (-SAP.P005a.WH.W2.subsetSum X S))) hlowerNonneg B hB
    have hdom : probability s lower ≤ probability s (fun S => B <
        SAP.P005a.WH.W2.traceExp (θ • (-SAP.P005a.WH.W2.subsetSum X S))) := by
      apply AronowAudit.P005.Wave1.CondT8T9_probability_mono
      intro S hS hL
      rcases hL with ⟨v, hv, hvq⟩
      let q := SAP.P005a.WH.W2.quadratic
        (-SAP.P005a.WH.W2.subsetSum X S) v
      let a := -x / 2
      let b := (a + q) / 2
      have hqneg : q = -SAP.P005a.WH.W2.quadratic
          (SAP.P005a.WH.W2.subsetSum X S) v := by
        simp [q, SAP.P005a.WH.W2.quadratic, SAP.P005a.dot,
          Matrix.neg_mulVec, Finset.sum_neg_distrib, mul_neg]
      have hq : -x / 2 < q := by
        rw [hqneg]
        have hh : -((s : ℝ) * μ) / 2 <
            -SAP.P005a.WH.W2.quadratic (SAP.P005a.WH.W2.subsetSum X S) v := by
          linarith [hvq]
        simpa [x] using hh
      have hab : a < b := by dsimp [b, a]; nlinarith
      have hbq : b < q := by dsimp [b, a]; nlinarith
      have hA := (subsetSum_hermitian X hXherm S).neg
      have hspec := (hSpec k (-SAP.P005a.WH.W2.subsetSum X S) hA).2 b θ hθ
        ⟨v, hv, by simpa [q, b, a, x] using hbq⟩
      have hexp : Real.exp (θ * a) < Real.exp (θ * b) :=
        Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hθ)
      dsimp [B]
      exact lt_of_lt_of_le (by simpa [a, x] using hexp) hspec
    have hmarkov := hdom.trans hmark
    have hE : expectation s (fun S => SAP.P005a.WH.W2.traceExp
        (θ • (-SAP.P005a.WH.W2.subsetSum X S))) / B ≤
        (k : ℝ) * Real.exp (-x / 8) := by
      have hscl := lower_scalar_bound s μ hμ.le hμ1
      have hquot : (1 - μ / 2)^s / B ≤ Real.exp (-x / 8) := by
        simpa [B, x, θ] using hscl
      have hdiv := div_le_div_of_nonneg_right htraceLower (le_of_lt hB)
      calc
        _ ≤ (k : ℝ) * (1 - μ / 2)^s / B := hdiv
        _ = (k : ℝ) * ((1 - μ / 2)^s / B) := by ring
        _ ≤ (k : ℝ) * Real.exp (-x / 8) :=
          mul_le_mul_of_nonneg_left hquot (by positivity : 0 ≤ (k : ℝ))
    exact hmarkov.trans hE
  have hbad : ∀ S ∈ design N s, bad S → upper S ∨ lower S := by
    intro S hS h
    rcases h with ⟨v, hv, hq | hq⟩
    · exact Or.inr ⟨v, hv, hq⟩
    · exact Or.inl ⟨v, hv, hq⟩
  have hmono := AronowAudit.P005.Wave1.CondT8T9_probability_mono s bad
    (fun S => upper S ∨ lower S) hbad
  have hunion := AronowAudit.P005.Wave1.CondT8T9_probability_union s upper lower
  calc
    probability s bad ≤ probability s (fun S => upper S ∨ lower S) := hmono
    _ ≤ probability s upper + probability s lower := hunion
    _ ≤ (k : ℝ) * Real.exp (-x / 8) + (k : ℝ) * Real.exp (-x / 8) :=
      add_le_add hupperProb hlowerProb
    _ = 2 * (k : ℝ) * Real.exp (-x / 8) := by ring

