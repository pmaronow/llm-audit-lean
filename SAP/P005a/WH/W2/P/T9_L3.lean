import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L3

noncomputable section
open Finset
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

lemma hermitian_combo {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (a b : ℝ) :
    (a • A + b • B).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hAi : A j i = A i j := by simpa using hA.apply i j
  have hBi : B j i = B i j := by simpa using hB.apply i j
  simp [Matrix.add_apply, Matrix.smul_apply, hAi, hBi]

lemma quadratic_combo {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (v : Fin k → ℝ) (a b : ℝ) :
    SAP.P005a.WH.W2.quadratic (a • A + b • B) v =
      a * SAP.P005a.WH.W2.quadratic A v + b * SAP.P005a.WH.W2.quadratic B v := by
  unfold SAP.P005a.WH.W2.quadratic SAP.P005a.dot
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply]
  calc
    _ = ∑ i, (a * (v i * (A *ᵥ v) i) + b * (v i * (B *ᵥ v) i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * (∑ i, v i * (A *ᵥ v) i) + b * (∑ i, v i * (B *ᵥ v) i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma unitary_column_unit {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℝ) (i : Fin k) :
    SAP.P005a.WH.W2.unitVector (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self U) i) i
  have hs : (∑ j, (U : Matrix (Fin k) (Fin k) ℝ) j i *
      (U : Matrix (Fin k) (Fin k) ℝ) j i) = 1 := by
    simpa [Matrix.mul_apply] using h
  simpa [SAP.P005a.WH.W2.unitVector, SAP.P005a.dot] using hs

lemma quadratic_exp_sum {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    (∑ i, SAP.P005a.WH.W2.quadratic M
      (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) = Matrix.trace M := by
  have hUU : (U : Matrix (Fin k) (Fin k) ℝ) * star (U : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have hexpand : Matrix.trace
      (star (U : Matrix (Fin k) (Fin k) ℝ) * M * (U : Matrix (Fin k) (Fin k) ℝ)) =
      ∑ i, SAP.P005a.WH.W2.quadratic M
        (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) := by
    classical
    simp only [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i hi
    simp [SAP.P005a.WH.W2.quadratic, SAP.P005a.dot, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.mulVec,
      dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  calc
    _ = Matrix.trace (star (U : Matrix (Fin k) (Fin k) ℝ) * M *
        (U : Matrix (Fin k) (Fin k) ℝ)) := hexpand.symm
    _ = Matrix.trace ((U : Matrix (Fin k) (Fin k) ℝ) *
        star (U : Matrix (Fin k) (Fin k) ℝ) * M) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace M := by rw [hUU, Matrix.one_mul]

lemma trace_exp_eigenvalues {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) :
    Matrix.trace (NormedSpace.exp A) = ∑ i, Real.exp (hA.eigenvalues i) := by
  let U : Matrix.unitaryGroup (Fin k) ℝ := hA.eigenvectorUnitary
  let D : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal hA.eigenvalues
  have hinv : (U : Matrix (Fin k) (Fin k) ℝ)⁻¹ = star (U : Matrix (Fin k) (Fin k) ℝ) :=
    Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self U)
  have hdiag : A = (U : Matrix (Fin k) (Fin k) ℝ) * D *
      (U : Matrix (Fin k) (Fin k) ℝ)⁻¹ := by
    rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [U, D, hinv]
  calc
    Matrix.trace (NormedSpace.exp A) = Matrix.trace
        ((U : Matrix (Fin k) (Fin k) ℝ) * NormedSpace.exp D *
          (U : Matrix (Fin k) (Fin k) ℝ)⁻¹) := by
      rw [hdiag, Matrix.exp_conj _ _ (Unitary.isUnit_coe)]
    _ = Matrix.trace (NormedSpace.exp D) := by
      rw [Matrix.trace_mul_cycle]
      rw [hinv, Unitary.coe_star_mul_self, Matrix.one_mul]
    _ = ∑ i, Real.exp (hA.eigenvalues i) := by
      simp [D, Matrix.exp_diagonal, Real.exp_eq_exp_ℝ]

lemma quadratic_eigenvalue {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian)
    (i : Fin k) :
    SAP.P005a.WH.W2.quadratic A
      (fun j => (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) j i) = hA.eigenvalues i := by
  let U : Matrix.unitaryGroup (Fin k) ℝ := hA.eigenvectorUnitary
  have hv : ⇑(hA.eigenvectorBasis i) = fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i := by
    funext j
    simp [U, Matrix.IsHermitian.eigenvectorUnitary_apply]
  have heq : SAP.P005a.WH.W2.quadratic A (⇑(hA.eigenvectorBasis i)) = hA.eigenvalues i := by
    rw [hA.eigenvalues_eq i]
    simp [SAP.P005a.WH.W2.quadratic, SAP.P005a.dot, dotProduct]
  simpa [hv] using heq

lemma trace_exp_convex_of_peierls (hp : SAP.P005a.WH.W2.peierls) :
    SAP.P005a.WH.W2.traceExpConvex := by
  intro k
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb hab
    change A.IsHermitian at hA
    change B.IsHermitian at hB
    change (a • A + b • B).IsHermitian
    exact hermitian_combo A B hA hB a b
  · intro A hA B hB a b ha hb hab
    change A.IsHermitian at hA
    change B.IsHermitian at hB
    change Matrix.trace (NormedSpace.exp (a • A + b • B)) ≤
      a • Matrix.trace (NormedSpace.exp A) + b • Matrix.trace (NormedSpace.exp B)
    let C : Matrix (Fin k) (Fin k) ℝ := a • A + b • B
    have hC : C.IsHermitian := by
      exact hermitian_combo A B hA hB a b
    let U : Matrix.unitaryGroup (Fin k) ℝ := hC.eigenvectorUnitary
    have hpoint (i : Fin k) :
        Real.exp (SAP.P005a.WH.W2.quadratic C
          (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) ≤
        a * SAP.P005a.WH.W2.quadratic (NormedSpace.exp A)
            (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) +
        b * SAP.P005a.WH.W2.quadratic (NormedSpace.exp B)
            (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) := by
      have hv := unitary_column_unit U i
      have hq := quadratic_combo A B
        (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) a b
      have hscalar := convexOn_exp.2 (Set.mem_univ
          (SAP.P005a.WH.W2.quadratic A
            (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)))
        (Set.mem_univ (SAP.P005a.WH.W2.quadratic B
          (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i))) ha hb hab
      have hpa := hp k A hA (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) hv
      have hpb := hp k B hB (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) hv
      calc
        _ = Real.exp (a * SAP.P005a.WH.W2.quadratic A
              (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) +
            b * SAP.P005a.WH.W2.quadratic B
              (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) := by
                rw [show SAP.P005a.WH.W2.quadratic C
                    (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) =
                    a * SAP.P005a.WH.W2.quadratic A
                      (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) +
                    b * SAP.P005a.WH.W2.quadratic B
                      (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) by
                    simpa [C] using hq]
        _ ≤ a * Real.exp (SAP.P005a.WH.W2.quadratic A
              (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) +
            b * Real.exp (SAP.P005a.WH.W2.quadratic B
              (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) := hscalar
        _ ≤ a * SAP.P005a.WH.W2.quadratic (NormedSpace.exp A)
              (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) +
            b * SAP.P005a.WH.W2.quadratic (NormedSpace.exp B)
              (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) := by
                exact add_le_add (mul_le_mul_of_nonneg_left hpa ha)
                  (mul_le_mul_of_nonneg_left hpb hb)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    have htraceC : Matrix.trace (NormedSpace.exp C) =
        ∑ i, Real.exp (SAP.P005a.WH.W2.quadratic C
          (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) := by
      rw [trace_exp_eigenvalues C hC]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact (quadratic_eigenvalue hC i).symm
    have htraceA := quadratic_exp_sum U (NormedSpace.exp A)
    have htraceB := quadratic_exp_sum U (NormedSpace.exp B)
    calc
      Matrix.trace (NormedSpace.exp C) =
          ∑ i, Real.exp (SAP.P005a.WH.W2.quadratic C
            (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) := htraceC
      _ ≤ ∑ i, (a * SAP.P005a.WH.W2.quadratic (NormedSpace.exp A)
            (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i) +
          b * SAP.P005a.WH.W2.quadratic (NormedSpace.exp B)
            (fun j => (U : Matrix (Fin k) (Fin k) ℝ) j i)) := hsum
      _ = a * Matrix.trace (NormedSpace.exp A) + b * Matrix.trace (NormedSpace.exp B) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            htraceA, htraceB]
      _ = a • Matrix.trace (NormedSpace.exp A) + b • Matrix.trace (NormedSpace.exp B) := by
          simp [smul_eq_mul]

end
end SAP.P005a.WH.W2.P.T9_L3

theorem SAP.P005a.WH.W2.T9_L3_proof : SAP.P005a.WH.W2.T9_L3 := by
  intro hp
  exact SAP.P005a.WH.W2.P.T9_L3.trace_exp_convex_of_peierls hp
