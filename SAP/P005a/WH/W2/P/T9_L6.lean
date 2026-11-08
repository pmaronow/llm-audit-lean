import SAP.P005a.WH.W2.Leaves
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

namespace SAP.P005a.WH.W2.P.T9_L6

open Finset Matrix

lemma trace_mul_transpose_cauchy (k : ℕ) (X Y : Matrix (Fin k) (Fin k) ℝ) :
    (Matrix.trace (X * Yᵀ)) ^ 2 ≤
      Matrix.trace (X * Xᵀ) * Matrix.trace (Y * Yᵀ) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product Finset.univ)
    (fun ij : Fin k × Fin k => X ij.1 ij.2)
    (fun ij : Fin k × Fin k => Y ij.1 ij.2)
  have htr : Matrix.trace (X * Yᵀ) =
      ∑ ij : Fin k × Fin k, X ij.1 ij.2 * Y ij.1 ij.2 := by
    simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      ← Finset.univ_product_univ, Finset.sum_product]
  have hxx : Matrix.trace (X * Xᵀ) =
      ∑ ij : Fin k × Fin k, (X ij.1 ij.2) ^ 2 := by
    simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      ← Finset.univ_product_univ, Finset.sum_product, pow_two]
  have hyy : Matrix.trace (Y * Yᵀ) =
      ∑ ij : Fin k × Fin k, (Y ij.1 ij.2) ^ 2 := by
    simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      ← Finset.univ_product_univ, Finset.sum_product, pow_two]
  rw [htr, hxx, hyy]
  exact hcs

lemma trace_square_le_frobenius (k : ℕ) (X : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.trace (X * X) ≤ Matrix.trace (X * Xᵀ) := by
  have hc := trace_mul_transpose_cauchy k X Xᵀ
  have heq : Matrix.trace (Xᵀ * X) = Matrix.trace (X * Xᵀ) :=
    Matrix.trace_mul_comm _ _
  have hsq : (Matrix.trace (X * X)) ^ 2 ≤
      (Matrix.trace (X * Xᵀ)) ^ 2 := by
    simpa [Matrix.transpose_transpose, pow_two, heq] using hc
  have hnon : 0 ≤ Matrix.trace (X * Xᵀ) := by
    exact (Matrix.posSemidef_self_mul_conjTranspose X).trace_nonneg
  by_cases hpos : 0 ≤ Matrix.trace (X * X)
  · exact (sq_le_sq₀ hpos hnon).mp hsq
  · exact (le_of_lt (lt_of_not_ge hpos)).trans hnon

lemma trace_mul_le_self_square {k : ℕ} (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (heq : Matrix.trace (P ^ 2) = Matrix.trace (Q ^ 2)) :
    Matrix.trace (P * Q) ≤ Matrix.trace (P ^ 2) := by
  have hPT : Pᵀ = P := by simpa using hP.isHermitian.eq
  have hQT : Qᵀ = Q := by simpa using hQ.isHermitian.eq
  have hc := trace_mul_transpose_cauchy k P Q
  have heq' : Matrix.trace (P * P) = Matrix.trace (Q * Q) := by
    simpa [pow_two] using heq
  have hsq : (Matrix.trace (P * Q)) ^ 2 ≤
      (Matrix.trace (P ^ 2)) ^ 2 := by
    calc
      (Matrix.trace (P * Q)) ^ 2 ≤
          Matrix.trace (P * Pᵀ) * Matrix.trace (Q * Qᵀ) := by
            simpa [hQT] using hc
      _ = (Matrix.trace (P ^ 2)) ^ 2 := by
            rw [hPT, hQT, pow_two, ← heq', pow_two]
  have hnon : 0 ≤ Matrix.trace (P ^ 2) := (hP.pow 2).trace_nonneg
  by_cases hpos : 0 ≤ Matrix.trace (P * Q)
  · exact (sq_le_sq₀ hpos hnon).mp hsq
  · exact (le_of_lt (lt_of_not_ge hpos)).trans hnon

lemma mul_pow_rotate {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Y * (X * Y) ^ n * X = (Y * X) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        Y * ((X * Y) ^ n * (X * Y)) * X =
            (Y * (X * Y) ^ n * X) * (Y * X) := by
              simp only [mul_assoc]
        _ = (Y * X) ^ (n + 1) * (Y * X) := by rw [ih]
        _ = (Y * X) ^ (n + 1 + 1) := by
              simp [pow_succ, Nat.add_assoc]

lemma trace_mul_pow_swap {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Matrix.trace ((X * Y) ^ n) = Matrix.trace ((Y * X) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        Matrix.trace ((X * Y) ^ n * (X * Y)) =
            Matrix.trace (Y * (X * Y) ^ n * X) := by
              rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
        _ = Matrix.trace ((Y * X) ^ (n + 1)) := by
              rw [mul_pow_rotate]
        _ = Matrix.trace ((Y * X) ^ n * (Y * X)) := by rw [pow_succ]

lemma trace_pow_reflect {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Matrix.trace ((X ^ 2 * Y ^ 2) ^ n) =
      Matrix.trace ((X * Y ^ 2 * X) ^ n) := by
  calc
    Matrix.trace ((X ^ 2 * Y ^ 2) ^ n) =
        Matrix.trace ((Y ^ 2 * X ^ 2) ^ n) := trace_mul_pow_swap (X ^ 2) (Y ^ 2) n
    _ = Matrix.trace (((Y ^ 2 * X) * X) ^ n) := by
        congr 1
        simp only [pow_two]
        rw [← Matrix.mul_assoc]
    _ = Matrix.trace ((X * (Y ^ 2 * X)) ^ n) :=
        (trace_mul_pow_swap X (Y ^ 2 * X) n).symm
    _ = Matrix.trace ((X * Y ^ 2 * X) ^ n) := by
        congr 1
        rw [← Matrix.mul_assoc]

def reflectedA {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (j i : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (A * B) ^ (2 ^ (j - i)) * (B * A) ^ (2 ^ (j - i))

def reflectedB {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (j i : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (B * A) ^ (2 ^ (j - i)) * (A * B) ^ (2 ^ (j - i))

lemma reflected_factor {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (j i : ℕ) :
    (∃ X, reflectedA A B j i = X * Xᵀ ∧ reflectedB A B j i = Xᵀ * X) := by
  let X := (A * B) ^ (2 ^ (j - i))
  have hAT : Aᵀ = A := by simpa using hA.isHermitian.eq
  have hBT : Bᵀ = B := by simpa using hB.isHermitian.eq
  have hXT : ((A * B) ^ (2 ^ (j - i)))ᵀ = (B * A) ^ (2 ^ (j - i)) := by
    simp [Matrix.transpose_pow, Matrix.transpose_mul, hAT, hBT]
  refine ⟨X, ?_, ?_⟩ <;> simp [X, reflectedA, reflectedB, hXT]

lemma reflectedA_pos {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (j i : ℕ) :
    (reflectedA A B j i).PosSemidef := by
  obtain ⟨X, hX, -⟩ := reflected_factor A B hA hB j i
  rw [hX]
  simpa using Matrix.posSemidef_self_mul_conjTranspose X

lemma reflectedB_pos {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (j i : ℕ) :
    (reflectedB A B j i).PosSemidef := by
  obtain ⟨X, -, hX⟩ := reflected_factor A B hA hB j i
  rw [hX]
  simpa using Matrix.posSemidef_conjTranspose_mul_self X

lemma reflected_trace_pow_eq {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (j i n : ℕ) :
    Matrix.trace ((reflectedA A B j i) ^ n) =
      Matrix.trace ((reflectedB A B j i) ^ n) := by
  obtain ⟨X, hX, hY⟩ := reflected_factor A B hA hB j i
  rw [hX, hY]
  exact trace_mul_pow_swap X Xᵀ n

lemma reflected_trace_edge {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (j i n : ℕ) (hi : i < j) :
    Matrix.trace ((reflectedA A B j i) ^ n) =
      Matrix.trace ((reflectedA A B j (i + 1) * reflectedB A B j (i + 1)) ^ n) := by
  let q := 2 ^ (j - (i + 1))
  have hsub : j - i = (j - (i + 1)) + 1 := by omega
  have hpow : 2 ^ (j - i) = q * 2 := by
    rw [hsub, pow_succ]
  have hA : reflectedA A B j i =
      ((A * B) ^ q) ^ 2 * ((B * A) ^ q) ^ 2 := by
    simp [reflectedA, hpow, q, pow_mul]
  have hB : reflectedA A B j (i + 1) * reflectedB A B j (i + 1) =
      (A * B) ^ q * ((B * A) ^ q) ^ 2 * (A * B) ^ q := by
    simp [reflectedA, reflectedB, q, mul_assoc, pow_two]
  rw [hA, hB]
  exact trace_pow_reflect ((A * B) ^ q) ((B * A) ^ q) n

lemma reflected_terminal {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Matrix.trace ((reflectedA A B n n) ^ (2 ^ (n - 1))) =
      Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ (n - 1))) := by
  let e := 2 ^ (n - 1)
  calc
    Matrix.trace ((reflectedA A B n n) ^ e) =
        Matrix.trace (((A * B) * (B * A)) ^ e) := by
          simp [reflectedA, e, pow_zero, pow_one]
    _ = Matrix.trace (((B * A) * (A * B)) ^ e) :=
          trace_mul_pow_swap (A * B) (B * A) e
    _ = Matrix.trace ((B * (A ^ 2 * B)) ^ e) := by
          congr 1
          simp [pow_two, mul_assoc]
    _ = Matrix.trace (((A ^ 2 * B) * B) ^ e) :=
          trace_mul_pow_swap B (A ^ 2 * B) e
    _ = Matrix.trace ((A ^ 2 * B ^ 2) ^ e) := by
          congr 1
          simp [pow_two, mul_assoc]

lemma reflected_chain_aux {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (n : ℕ)
    (hprev : ∀ r, r < n → ∀ C D : Matrix (Fin k) (Fin k) ℝ,
      C.PosSemidef → D.PosSemidef →
      Matrix.trace ((C * D) ^ (2 ^ r)) ≤ Matrix.trace (C ^ (2 ^ r) * D ^ (2 ^ r)))
    (i r : ℕ) (hi : 1 ≤ i) (hir : i + r = n) :
    Matrix.trace ((reflectedA A B n i) ^ (2 ^ (i - 1))) ≤
      Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ (n - 1))) := by
  induction r generalizing i with
  | zero =>
      have hni : i = n := by omega
      subst n
      exact (reflected_terminal A B i).le
  | succ r ih =>
      have hlt : i < n := by omega
      have hnext : (i + 1) + r = n := by omega
      let e := 2 ^ (i - 1)
      have he : 2 ^ i = e * 2 := by
        calc
          2 ^ i = 2 ^ (i - 1 + 1) := by congr 1; omega
          _ = 2 ^ (i - 1) * 2 := by rw [pow_succ]
          _ = e * 2 := rfl
      have hpa := reflectedA_pos A B hA hB n (i + 1)
      have hpb := reflectedB_pos A B hA hB n (i + 1)
      have hAeq := reflected_trace_pow_eq A B hA hB n (i + 1) (e * 2)
      have hAeq' : Matrix.trace ((reflectedA A B n (i + 1) ^ e) ^ 2) =
          Matrix.trace ((reflectedB A B n (i + 1) ^ e) ^ 2) := by
        simpa [pow_mul] using hAeq
      calc
        Matrix.trace ((reflectedA A B n i) ^ e) =
            Matrix.trace ((reflectedA A B n (i + 1) *
              reflectedB A B n (i + 1)) ^ e) := reflected_trace_edge A B n i e hlt
        _ ≤ Matrix.trace (reflectedA A B n (i + 1) ^ e *
              reflectedB A B n (i + 1) ^ e) := by
            exact hprev (i - 1) (by omega) _ _ hpa hpb
        _ ≤ Matrix.trace ((reflectedA A B n (i + 1) ^ e) ^ 2) :=
            trace_mul_le_self_square _ _ (hpa.pow e) (hpb.pow e) hAeq'
        _ = Matrix.trace (reflectedA A B n (i + 1) ^ (2 ^ i)) := by
            rw [he, ← pow_mul]
        _ ≤ Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ (n - 1))) := by
            simpa [Nat.add_sub_cancel] using ih (i + 1) (by omega) hnext

lemma golden_step {k : ℕ} (n : ℕ)
    (hprev : ∀ r, r < n → ∀ C D : Matrix (Fin k) (Fin k) ℝ,
      C.PosSemidef → D.PosSemidef →
      Matrix.trace ((C * D) ^ (2 ^ r)) ≤ Matrix.trace (C ^ (2 ^ r) * D ^ (2 ^ r)))
    (A B : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hn : 0 < n) :
    Matrix.trace ((A * B) ^ (2 ^ n)) ≤
      Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ (n - 1))) := by
  let e := 2 ^ (n - 1)
  have he : 2 ^ n = e * 2 := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = e * 2 := rfl
  have hAT : Aᵀ = A := by simpa using hA.isHermitian.eq
  have hBT : Bᵀ = B := by simpa using hB.isHermitian.eq
  have hXT : ((A * B) ^ e)ᵀ = (B * A) ^ e := by
    simp [Matrix.transpose_pow, Matrix.transpose_mul, hAT, hBT]
  have hRA : reflectedA A B n 1 = (A * B) ^ e * ((A * B) ^ e)ᵀ := by
    simp [reflectedA, e, hXT]
  have hpow : (A * B) ^ (2 ^ n) = ((A * B) ^ e) ^ 2 := by
    rw [he, ← pow_mul]
  calc
    Matrix.trace ((A * B) ^ (2 ^ n)) =
        Matrix.trace (((A * B) ^ e) * ((A * B) ^ e)) := by
          rw [hpow, pow_two]
    _ ≤ Matrix.trace ((A * B) ^ e * ((A * B) ^ e)ᵀ) :=
          trace_square_le_frobenius k ((A * B) ^ e)
    _ = Matrix.trace (reflectedA A B n 1) := by rw [hRA]
    _ ≤ Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ (n - 1))) := by
          simpa using reflected_chain_aux A B hA hB n hprev 1 (n - 1)
            (by omega) (by omega)

lemma dyadic_trace_all (k : ℕ) :
    ∀ j, ∀ A B : Matrix (Fin k) (Fin k) ℝ,
      A.PosSemidef → B.PosSemidef →
      Matrix.trace ((A * B) ^ (2 ^ j)) ≤ Matrix.trace (A ^ (2 ^ j) * B ^ (2 ^ j)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro A B hA hB
      cases j with
      | zero => simp
      | succ n =>
          have hprev : ∀ r, r < n + 1 → ∀ C D : Matrix (Fin k) (Fin k) ℝ,
              C.PosSemidef → D.PosSemidef →
              Matrix.trace ((C * D) ^ (2 ^ r)) ≤
                Matrix.trace (C ^ (2 ^ r) * D ^ (2 ^ r)) := by
            intro r hr C D hC hD
            exact ih r hr C D hC hD
          have hstep := golden_step (n + 1) hprev A B hA hB (by omega)
          have hIH := ih n (by omega) (A ^ 2) (B ^ 2) (hA.pow 2) (hB.pow 2)
          calc
            Matrix.trace ((A * B) ^ (2 ^ (n + 1))) ≤
                Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ n)) := by
                  simpa using hstep
            _ ≤ Matrix.trace ((A ^ 2) ^ (2 ^ n) * (B ^ 2) ^ (2 ^ n)) := hIH
            _ = Matrix.trace (A ^ (2 ^ (n + 1)) * B ^ (2 ^ (n + 1))) := by
                  congr 1
                  congr 1
                  · calc
                      (A ^ 2) ^ (2 ^ n) = A ^ (2 * 2 ^ n) := by rw [← pow_mul]
                      _ = A ^ (2 ^ (n + 1)) := by
                        congr 1
                        rw [Nat.mul_comm, pow_succ]
                  · calc
                      (B ^ 2) ^ (2 ^ n) = B ^ (2 * 2 ^ n) := by rw [← pow_mul]
                      _ = B ^ (2 ^ (n + 1)) := by
                        congr 1
                        rw [Nat.mul_comm, pow_succ]

end SAP.P005a.WH.W2.P.T9_L6

theorem SAP.P005a.WH.W2.T9_L6_proof : SAP.P005a.WH.W2.T9_L6 := by
  intro k A B hA hB j
  exact SAP.P005a.WH.W2.P.T9_L6.dyadic_trace_all k j A B hA hB
