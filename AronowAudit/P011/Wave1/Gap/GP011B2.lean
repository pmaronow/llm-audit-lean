import AronowAudit.P011.P011_CorrectedAsymptoticCompletion
import AronowAudit.P011.P011_SpectralCompletion
import AronowAudit.P011.P011_DataMatrixCompletion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Order.Lattice

/-!
Exact optimum for sign vectors and its probability limits.
-/

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000




/-! Exact optimum for sign vectors and its probability limits. -/

def unbounded_caps_equalGraph {n : ℕ} (y : Fin n → ℝ) : Graph n :=
  ⟨fun i j => decide (i ≠ j ∧ y i = y j), by
    constructor
    · intro i j
      by_cases hij : i = j
      · subst j; rfl
      · by_cases he : y i = y j
        · simp [hij, Ne.symm hij, he]
        · simp [hij, Ne.symm hij, he, Ne.symm he]
    · intro i
      simp⟩

lemma unbounded_caps_all_compatible {n : ℕ} (B : Graph n) :
    Compatible (emptyGraph n) (fun _ => n - 1) B := by
  constructor
  · intro i j hij
    simp [emptyGraph] at hij
  · exact simple_degree_bound B

lemma unbounded_caps_average_bound {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) : |average y| ≤ 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi (i : Fin n) : |y i| ≤ 1 := by
    rcases hy i with hi | hi <;> rw [hi] <;> norm_num
  unfold average
  rw [abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
    _ = 1 * (n : ℝ) := by simp

lemma unbounded_caps_oracle_entry {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (i j : Fin n) :
    oracleMatrix (unbounded_caps_equalGraph y) i j = (1 + y i * y j) / 2 := by
  by_cases hij : i = j
  · subst j
    rcases hy i with hi | hi <;>
      norm_num [oracleMatrix, adjacency, unbounded_caps_equalGraph,
        Matrix.add_apply, Matrix.one_apply, hi]
  · rcases hy i with hi | hi <;> rcases hy j with hj | hj <;>
      norm_num [oracleMatrix, adjacency, unbounded_caps_equalGraph,
        Matrix.add_apply, Matrix.one_apply, hij, hi, hj]

lemma unbounded_caps_pair_domination {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (B : Graph n) (i j : Fin n) :
    adjacency B i j * centered y i * centered y j ≤
      adjacency (unbounded_caps_equalGraph y) i j * centered y i * centered y j := by
  by_cases hij : i = j
  · subst j
    simp [adjacency, B.property.2, unbounded_caps_equalGraph]
  · by_cases he : y i = y j
    · have hprod : 0 ≤ centered y i * centered y j := by
        simpa only [centered, he, ← sq] using sq_nonneg (y j - average y)
      have hadj : adjacency (unbounded_caps_equalGraph y) i j = 1 := by
        simp [adjacency, unbounded_caps_equalGraph, hij, he]
      rw [hadj]
      cases hb : B.val i j <;> simp [adjacency, hb] <;> linarith
    · have hav := abs_le.mp (unbounded_caps_average_bound hn y hy)
      have hav2 : average y ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (average y), mul_nonneg (by linarith : 0 ≤ 1 - average y)
          (by linarith : 0 ≤ 1 + average y)]
      have hprod : centered y i * centered y j ≤ 0 := by
        rcases hy i with hi | hi <;> rcases hy j with hj | hj
        · exact False.elim (he (hi.trans hj.symm))
        · dsimp only [centered]
          rw [hi, hj]
          nlinarith
        · dsimp only [centered]
          rw [hi, hj]
          nlinarith
        · exact False.elim (he (hi.trans hj.symm))
      have hadj : adjacency (unbounded_caps_equalGraph y) i j = 0 := by
        simp [adjacency, unbounded_caps_equalGraph, he]
      rw [hadj]
      cases hb : B.val i j <;> simp [adjacency, hb] <;> linarith

lemma unbounded_caps_witness_max {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (B : Graph n) :
    V1 B y ≤ V1 (unbounded_caps_equalGraph y) y := by
  unfold V1
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply add_le_add le_rfl
  unfold quadratic
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact unbounded_caps_pair_domination hn y hy B i j

lemma unbounded_caps_witness_value {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    V1 (unbounded_caps_equalGraph y) y = (1 - average y ^ 2) ^ 2 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs (i : Fin n) : y i ^ 2 = 1 := by
    rcases hy i with hi | hi <;> rw [hi] <;> norm_num
  have hsum : (∑ i, y i ^ 2) = (n : ℝ) := by simp [hs]
  have hav : (∑ i, y i) = (n : ℝ) * average y := by
    unfold average
    field_simp [hn0]
    <;> ring
  have hprod : (∑ i, y i * centered y i) = (n : ℝ) * (1 - average y ^ 2) := by
    simp_rw [centered, mul_sub, ← pow_two]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hav]
    ring
  have hq : quadratic (oracleMatrix (unbounded_caps_equalGraph y)) (centered y) =
      ((∑ i, centered y i) ^ 2 + (∑ i, y i * centered y i) ^ 2) / 2 := by
    unfold quadratic
    simp_rw [unbounded_caps_oracle_entry y hy]
    have hterm (i j : Fin n) :
        (1 + y i * y j) / 2 * centered y i * centered y j =
          (centered y i * centered y j +
            (y i * centered y i) * (y j * centered y j)) / 2 := by ring
    simp_rw [hterm]
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [← variance_form_oracle, varianceForm, hq, centered_sum_zero hn y, hprod]
  field_simp [hn0]
  <;> ring

lemma unbounded_caps_sign_young {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    VYoung (fun _ => n - 1) y = 1 - average y ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hncast : 1 + ((n - 1 : ℕ) : ℝ) = (n : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hs (i : Fin n) : y i ^ 2 = 1 := by
    rcases hy i with hi | hi <;> rw [hi] <;> norm_num
  have hsum : (∑ i, y i ^ 2) = (n : ℝ) := by simp [hs]
  unfold VYoung
  simp only [truncatedDegree, min_self, hncast, ← Finset.mul_sum]
  rw [DenseCompletion.centered_sq hn, hsum]
  field_simp [hn0]
  <;> ring

lemma unbounded_caps_sign_optimum {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (A : Graph n)
    (hm : Maximizes (emptyGraph n) (fun _ => n - 1) (fun B => V1 B y) A) :
    V1 A y = (1 - average y ^ 2) ^ 2 / 2 ∧
      VYoung (fun _ => n - 1) y = 1 - average y ^ 2 := by
  have he : V1 A y = V1 (unbounded_caps_equalGraph y) y :=
    le_antisymm (unbounded_caps_witness_max hn y hy A)
      (hm.2 _ (unbounded_caps_all_compatible _))
  exact ⟨he.trans (unbounded_caps_witness_value hn y hy), unbounded_caps_sign_young hn y hy⟩

lemma unbounded_caps_polynomial_limit (f : ℝ → ℝ) (hf : Continuous f) :
    InProbability signFamily (fun _ y => f (average y)) (fun _ => f 0) := by
  let (k : ℕ) : IsProbabilityMeasure (signModel (k + 1)).law := (signModel (k + 1)).probability
  have hc := CoverageCompletion.rowCP_continuous_pair (fun k => (signModel (k + 1)).law)
    (fun _ y => average y) (fun _ _ => (0 : ℝ)) 0 0 DataMatrixCompletion.average_CP
    (CoverageCompletion.rowCP_det _ (fun _ => (0 : ℝ)) 0 tendsto_const_nhds)
    (fun p : ℝ × ℝ => f p.1) (hf.comp continuous_fst).continuousAt
  exact hc

theorem unbounded_caps_gap_proof (A : ∀ k, (Fin (k+1) → ℝ) → Graph (k+1))
    (hm : ∀ k y, Maximizes (emptyGraph (k+1)) (fun _ => k)
      (fun B => V1 B y) (A k y)) :
    (∀ k y, (∀ i, y i = 1 ∨ y i = -1) →
      V1 (A k y) y = (1-average y^2)^2/2 ∧
      VYoung (fun _ => k) y = 1-average y^2) ∧
    InProbability signFamily (fun k y => V1 (A k y) y) (fun _ => 1/2) ∧
    InProbability signFamily (fun k y => VYoung (fun _ => k) y) (fun _ => 1) := by
  have hfinite (k : ℕ) (y : Fin (k + 1) → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
      V1 (A k y) y = (1 - average y ^ 2) ^ 2 / 2 ∧
      VYoung (fun _ => k) y = 1 - average y ^ 2 := by
    simpa only [Nat.succ_sub_one, Nat.add_sub_cancel] using
      unbounded_caps_sign_optimum (Nat.succ_pos k) y hy (A k y) (hm k y)
  refine ⟨hfinite, ?_, ?_⟩
  · have hc := unbounded_caps_polynomial_limit (fun b : ℝ => (1 - b ^ 2) ^ 2 / 2)
      (by fun_prop)
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero, one_pow] at hc
    intro ε hε
    convert hc ε hε using 1
    funext k
    apply measureReal_congr
    filter_upwards [DataMatrixCompletion.ae_signs (k + 1)] with y hy
    exact congrArg (fun t => |t - 1/2| > ε) (hfinite k y hy).1
  · have hc := unbounded_caps_polynomial_limit (fun b : ℝ => 1 - b ^ 2) (by fun_prop)
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero] at hc
    intro ε hε
    convert hc ε hε using 1
    funext k
    apply measureReal_congr
    filter_upwards [DataMatrixCompletion.ae_signs (k + 1)] with y hy
    exact congrArg (fun t => |t - 1| > ε) (hfinite k y hy).2




end
end AronowAudit.P011.Wave1
