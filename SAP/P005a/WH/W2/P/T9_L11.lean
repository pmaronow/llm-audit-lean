import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

namespace SAP.P005a.WH.W2.P.T9_L11

noncomputable section

open Finset Filter SAP.P005a.Bridge
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

private theorem exp_posSemidef_of_hermitian {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian) :
    (NormedSpace.exp A).PosSemidef := by
  let H := (2 : ℝ)⁻¹ • A
  have hH : H.IsHermitian := hA.smul (by unfold IsSelfAdjoint; norm_num)
  have hcomm : Commute H H := Commute.refl H
  have hmul : NormedSpace.exp A = NormedSpace.exp H * NormedSpace.exp H := by
    have he := Matrix.exp_add_of_commute H H hcomm
    have hsum : H + H = A := by
      dsimp [H]
      rw [← add_smul]
      norm_num
    rw [← hsum]
    exact he
  have hstar : (NormedSpace.exp H)ᴴ = NormedSpace.exp H := by
    rw [← Matrix.exp_conjTranspose, hH.eq]
  have hstarT : (NormedSpace.exp H)ᵀ = NormedSpace.exp H := by
    simpa using hstar
  rw [hmul]
  have hp := Matrix.posSemidef_conjTranspose_mul_self (NormedSpace.exp H)
  rw [hstar] at hp
  exact hp

private theorem trace_mul_nonneg_of_posSemidef {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  classical
  let Uu := hA.1.eigenvectorUnitary
  let U : Matrix (Fin k) (Fin k) ℝ := Uu
  let d := hA.1.eigenvalues
  have hdiag : A = U * Matrix.diagonal d * (star U : Matrix (Fin k) (Fin k) ℝ) := by
    have hspec := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    simpa [U, Uu, d] using hspec
  rw [Matrix.star_eq_conjTranspose] at hdiag
  let C := Uᴴ * B * U
  have hC : C.PosSemidef := by
    change (Uᴴ * B * U).PosSemidef
    exact hB.conjTranspose_mul_mul_same U
  have htrace : Matrix.trace (A * B) = Matrix.trace (Matrix.diagonal d * C) := by
    calc
      Matrix.trace (A * B) =
          Matrix.trace (U * Matrix.diagonal d * (Uᴴ * B)) := by
            rw [hdiag]
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Uᴴ * B) * U * Matrix.diagonal d) :=
            Matrix.trace_mul_cycle U (Matrix.diagonal d) (Uᴴ * B)
      _ = Matrix.trace (Matrix.diagonal d * C) := by
            rw [Matrix.trace_mul_comm]
  rw [htrace]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa using mul_nonneg (hA.eigenvalues_nonneg i) hC.diag_nonneg
  · simp [hij]

private theorem trace_mul_order_of_posSemidef {k : ℕ}
    (E A B : Matrix (Fin k) (Fin k) ℝ) (hE : E.PosSemidef)
    (hAB : (B - A).PosSemidef) :
    Matrix.trace (E * A) ≤ Matrix.trace (E * B) := by
  have hp := trace_mul_nonneg_of_posSemidef E (B - A) hE hAB
  have heq : E * B = E * A + E * (B - A) := by
    calc
      E * B = E * (A + (B - A)) := by congr 1 <;> abel
      _ = E * A + E * (B - A) := mul_add E A (B - A)
  calc
    Matrix.trace (E * A) ≤ Matrix.trace (E * A) + Matrix.trace (E * (B - A)) :=
      le_add_of_nonneg_right hp
    _ = Matrix.trace (E * B) := by
      have ht := congrArg Matrix.trace heq
      rw [Matrix.trace_add] at ht
      exact ht.symm

private theorem drawSum_cons {N k s : ℕ}
    (X : Fin N → Matrix (Fin k) (Fin k) ℝ) (x : Fin N) (g : Fin s → Fin N) :
    drawSum X (Fin.cons x g) = drawSum X g + X x := by
  simp [drawSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_comm]

end

end SAP.P005a.WH.W2.P.T9_L11

open SAP.P005a.WH.W2.P.T9_L11
open Finset Filter SAP.P005a.Bridge
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

theorem SAP.P005a.WH.W2.T9_L11_proof : SAP.P005a.WH.W2.T9_L11 := by
  intro hGT hChord
  intro N k s hN X hX μ hμ0 hμ1 hmean θ
  let c : ℝ := 1 + μ * (Real.exp θ - 1)
  have hc : 0 ≤ c := by
    dsimp [c]
    nlinarith [Real.exp_pos θ]
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  have havg := hChord N k hN X hX μ hμ0 hμ1 hmean θ
  have hraw : ∀ n : ℕ,
      (∑ w : Fin n → Fin N, traceExp (θ • drawSum X w)) ≤
        (N : ℝ)^n * (k : ℝ) * c^n := by
    intro n
    induction n with
    | zero =>
        simp [traceExp, drawSum, c]
    | succ n ih =>
        let e : (Fin N × (Fin n → Fin N)) ≃
            (Fin (n + 1) → Fin N) := Fin.consEquiv (fun _ : Fin (n + 1) => Fin N)
        have hsplit :
            (∑ w : Fin (n + 1) → Fin N, traceExp (θ • drawSum X w)) =
              ∑ g : Fin n → Fin N, ∑ x : Fin N,
                traceExp (θ • drawSum X (Fin.cons x g)) := by
          have hcomp :
              (∑ p : Fin N × (Fin n → Fin N),
                  traceExp (θ • drawSum X (Fin.cons p.1 p.2))) =
                ∑ w : Fin (n + 1) → Fin N, traceExp (θ • drawSum X w) :=
            by
              calc
                (∑ p : Fin N × (Fin n → Fin N),
                    traceExp (θ • drawSum X (Fin.cons p.1 p.2))) =
                  ∑ p : Fin N × (Fin n → Fin N), traceExp (θ • drawSum X (e p)) := by
                    simp [e, Fin.consEquiv]
                _ = ∑ w : Fin (n + 1) → Fin N,
                    traceExp (θ • drawSum X w) :=
                      Equiv.sum_comp e (fun w : Fin (n + 1) → Fin N =>
                        traceExp (θ • drawSum X w))
          rw [hcomp.symm]
          simp_rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
        have hsection : ∀ g : Fin n → Fin N,
            (∑ x : Fin N, traceExp (θ • drawSum X (Fin.cons x g))) ≤
              (N : ℝ) * c * traceExp (θ • drawSum X g) := by
          intro g
          let E := NormedSpace.exp (θ • drawSum X g)
          have hdraw : (drawSum X g).IsHermitian := by
            apply Matrix.IsHermitian.ext
            intro i j
            simp only [drawSum, Matrix.sum_apply, star_sum, Matrix.conjTranspose_apply]
            apply Finset.sum_congr rfl
            intro l hl
            exact (hX (g l)).1.1.apply i j
          have htheta : (θ • drawSum X g).IsHermitian :=
            hdraw.smul (by unfold IsSelfAdjoint; rfl)
          have hE : E.PosSemidef := by
            simpa [E] using exp_posSemidef_of_hermitian (θ • drawSum X g) htheta
          have hsumTrace :
              (∑ x : Fin N, Matrix.trace
                  (E * NormedSpace.exp (θ • X x))) =
                Matrix.trace (E * ∑ x : Fin N, NormedSpace.exp (θ • X x)) := by
            simp [Matrix.mul_sum, Matrix.trace_sum]
          have horder : Matrix.trace (E * ((N : ℝ)⁻¹ •
                ∑ x : Fin N, NormedSpace.exp (θ • X x))) ≤
                Matrix.trace (E * (c • (1 : Matrix (Fin k) (Fin k) ℝ))) := by
            apply trace_mul_order_of_posSemidef E _ _ hE
            simpa [matrixLE, c] using havg
          have hconvert :
              Matrix.trace (E * ((N : ℝ)⁻¹ •
                ∑ x : Fin N, NormedSpace.exp (θ • X x))) =
                (N : ℝ)⁻¹ * Matrix.trace
                  (E * ∑ x : Fin N, NormedSpace.exp (θ • X x)) := by
            simp [Matrix.mul_smul, Matrix.trace_smul]
          have hbound :
              Matrix.trace (E * ∑ x : Fin N, NormedSpace.exp (θ • X x)) ≤
                (N : ℝ) * c * Matrix.trace E := by
            have hrhs : Matrix.trace (E * (c • (1 : Matrix (Fin k) (Fin k) ℝ))) =
                c * Matrix.trace E := by simp [Matrix.mul_smul, Matrix.trace_smul]
            rw [hconvert, hrhs] at horder
            have hmul := mul_le_mul_of_nonneg_left horder hNreal.le
            have hcancel : (N : ℝ) * ((N : ℝ)⁻¹ *
                Matrix.trace (E * ∑ x : Fin N, NormedSpace.exp (θ • X x))) =
                Matrix.trace (E * ∑ x : Fin N, NormedSpace.exp (θ • X x)) := by
              field_simp [hNne]
            rw [hcancel] at hmul
            nlinarith [hmul]
          calc
            (∑ x : Fin N, traceExp (θ • drawSum X (Fin.cons x g))) ≤
                ∑ x : Fin N, Matrix.trace (E * NormedSpace.exp (θ • X x)) := by
              apply Finset.sum_le_sum
              intro x hx
              have hsum := drawSum_cons X x g
              have hA : (θ • drawSum X g).IsHermitian := htheta
              have hB : (θ • X x).IsHermitian :=
                (hX x).1.1.smul (by unfold IsSelfAdjoint; rfl)
              have hgt := hGT k (θ • drawSum X g) (θ • X x) hA hB
              simpa [traceExp, E, hsum, smul_add] using hgt
            _ = Matrix.trace (E * ∑ x : Fin N, NormedSpace.exp (θ • X x)) := hsumTrace
            _ ≤ (N : ℝ) * c * Matrix.trace E := hbound
        rw [hsplit]
        calc
          (∑ g : Fin n → Fin N, ∑ x : Fin N,
              traceExp (θ • drawSum X (Fin.cons x g))) ≤
            ∑ g : Fin n → Fin N, (N : ℝ) * c * traceExp (θ • drawSum X g) := by
              apply Finset.sum_le_sum
              intro g hg
              exact hsection g
          _ = (N : ℝ) * c *
              (∑ g : Fin n → Fin N, traceExp (θ • drawSum X g)) := by
                simp [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          _ ≤ (N : ℝ) * c * ((N : ℝ)^n * (k : ℝ) * c^n) := by
                exact mul_le_mul_of_nonneg_left ih (mul_nonneg hNreal.le hc)
          _ = (N : ℝ)^(n+1) * (k : ℝ) * c^(n+1) := by
                rw [pow_succ, pow_succ]
                ring
  change (∑ w : Fin s → Fin N, traceExp (θ • drawSum X w)) / (N : ℝ)^s ≤
    (k : ℝ) * c^s
  rw [div_le_iff₀ (pow_pos hNreal s)]
  calc
    (∑ w : Fin s → Fin N, traceExp (θ • drawSum X w)) ≤
        (N : ℝ)^s * (k : ℝ) * c^s := hraw s
    _ = ((k : ℝ) * c^s) * (N : ℝ)^s := by ring

