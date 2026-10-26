import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Boundary Chebyshev estimates, with all interval and constant calculations
kept explicit. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n12_proof : N12 := by
  classical
  intro h10 h11 t ht
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have htne : (t : ℝ) ≠ 0 := ne_of_gt htpos
  have ht4 : (16 : ℝ) ≤ (t : ℝ) ^ 4 := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (t : ℝ) ^ 4 := by gcongr
  have hd : 3 ≤ t ^ 3 := by
    have h : (2 : ℕ) ^ 3 ≤ t ^ 3 := by gcongr
    norm_num at h
    omega
  let a : ℝ := 1 / (t : ℝ) ^ 4
  let ell : ℝ → ℝ := fun z => (2 * z - 1 - a) / (1 - a)
  let r : Polynomial ℝ := chebR t
  let B : ℝ := 3 * (t : ℝ) ^ 6 / 640
  have ha : 0 < a := by dsimp [a]; positivity
  have ha16 : a ≤ 1 / 16 := by
    dsimp [a]
    exact one_div_le_one_div_of_le (by norm_num) ht4
  have hden : 0 < 1 - a := by linarith
  have hdenne : 1 - a ≠ 0 := ne_of_gt hden
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heval (z : ℝ) :
      r.eval z = (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).eval (ell z) := by
    change (chebR t).eval z = _
    rw [chebR, eval_comp]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    congr 1
    change 2 / (1 - a) * z - (1 + a) / (1 - a) = (2 * z - 1 - a) / (1 - a)
    field_simp [hdenne]
    <;> ring
  have hdeg : r.natDegree ≤ t ^ 3 := by
    let l : Polynomial ℝ := C (2 / (1 - a)) * X - C ((1 + a) / (1 - a))
    have hl : l.natDegree ≤ 1 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (by simp)
      · simp
    calc
      r.natDegree ≤ (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).natDegree * l.natDegree :=
        natDegree_comp_le
      _ = t ^ 3 * l.natDegree := by simp
      _ ≤ t ^ 3 * 1 := Nat.mul_le_mul_left _ hl
      _ = t ^ 3 := Nat.mul_one _
  have hbounded : ∀ z ∈ Set.Icc a 1, |r.eval z| ≤ 1 := by
    intro z hz
    have hzL : -1 ≤ ell z := by
      dsimp [ell]
      apply (le_div_iff₀ hden).2
      linarith [hz.1]
    have hzU : ell z ≤ 1 := by
      dsimp [ell]
      apply (div_le_iff₀ hden).2
      linarith [hz.2]
    rw [heval]
    exact h10 (t ^ 3) (ell z) ⟨hzL, hzU⟩
  have hboundary : ∀ z ∈ Set.Icc (0 : ℝ) (a / 4), B ≤ |r.eval z| := by
    intro z hz
    let s : ℝ := -ell z - 1
    have hs_eq : s = (2 * a - 2 * z) / (1 - a) := by
      dsimp [s, ell]
      field_simp [hdenne]
      <;> ring
    have hs0 : 0 ≤ s := by
      rw [hs_eq]
      exact div_nonneg (by linarith [hz.2]) hden.le
    have hs1 : s ≤ 1 := by
      rw [hs_eq]
      apply (div_le_iff₀ hden).2
      linarith [hz.1]
    have hs_lower : (3 / 2 : ℝ) * a ≤ s := by
      rw [hs_eq]
      apply (le_div_iff₀ hden).2
      nlinarith [hz.2, sq_nonneg a]
    have hgrowth := h11 (t ^ 3) hd s hs0 hs1
    have harith : B ≤ ((t ^ 3 : ℕ) : ℝ) ^ 6 * s ^ 3 / 720 := by
      calc
        B = ((t ^ 3 : ℕ) : ℝ) ^ 6 * ((3 / 2 : ℝ) * a) ^ 3 / 720 := by
          dsimp [B, a]
          push_cast
          field_simp [htne]
          <;> ring
        _ ≤ ((t ^ 3 : ℕ) : ℝ) ^ 6 * s ^ 3 / 720 := by
          gcongr
    have hpos_eval : 0 ≤ (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).eval (1 + s) :=
      le_trans (by positivity) hgrowth
    have hsign : |((((t ^ 3 : ℕ) : ℤ)).negOnePow : ℝ)| = 1 := by
      simp [Int.cast_negOnePow_natCast, abs_pow]
    have hell : ell z = -(1 + s) := by dsimp [s]; ring
    rw [heval, hell, Chebyshev.T_eval_neg, abs_mul, hsign, one_mul,
      abs_of_nonneg hpos_eval]
    exact harith.trans hgrowth
  let J : Set ℝ := Set.Icc 0 (a / 4)
  have hJsub : J ⊆ Set.Icc (0 : ℝ) (1 / 2) := by
    intro z hz
    exact ⟨hz.1, le_trans hz.2 (by linarith)⟩
  have hcont : Continuous (fun z : ℝ => r.eval z * r.eval z) :=
    r.continuous.mul r.continuous
  have hJint : IntegrableOn (fun z : ℝ => r.eval z * r.eval z) J :=
    hcont.integrableOn_Icc
  have hIint : IntegrableOn (fun z : ℝ => r.eval z * r.eval z)
      (Set.Icc (0 : ℝ) (1 / 2)) := hcont.integrableOn_Icc
  have hsquare : ∀ z ∈ J, B ^ 2 ≤ r.eval z * r.eval z := by
    intro z hz
    have h := hboundary z hz
    have hsq : B ^ 2 ≤ |r.eval z| ^ 2 := pow_le_pow_left₀ hB h 2
    simpa [sq_abs, pow_two] using hsq
  have hconst : volume.real J * B ^ 2 ≤ ∫ z in J, r.eval z * r.eval z := by
    simpa only [smul_eq_mul] using
      (setIntegral_ge_of_const_le (μ := volume) (s := J)
        (c := B ^ 2) measurableSet_Icc (by simp [J]) hsquare hJint)
  have hmono : (∫ z in J, r.eval z * r.eval z) ≤ regionInt r r := by
    exact setIntegral_mono_set hIint
      (Filter.Eventually.of_forall (fun z => mul_self_nonneg (r.eval z)))
      (Filter.Eventually.of_forall (fun _ hz => hJsub hz))
  have hvol : volume.real J = a / 4 := by
    change volume.real (Set.Icc (0 : ℝ) (a / 4)) = a / 4
    rw [Real.volume_real_Icc_of_le (by positivity)]
    ring
  have hnumeric : volume.real J * B ^ 2 = 9 * (t : ℝ) ^ 8 / 1638400 := by
    rw [hvol]
    dsimp [a, B]
    field_simp [htne]
    <;> ring
  refine ⟨hdeg, hbounded, ?_⟩
  rw [← hnumeric]
  exact hconst.trans hmono

end

end AronowAudit.P001.Wave1.SieveRate
