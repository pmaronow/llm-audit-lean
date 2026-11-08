import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000

namespace SAP.P005a.WH.W2.P.T9_L10

open Finset Matrix
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

private theorem scalar_exp_chord (θ x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (θ * x) ≤ 1 + x * (Real.exp θ - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ θ)
    (sub_nonneg.mpr hx1) hx0 (by ring : (1 - x) + x = 1)
  have h' : Real.exp (θ * x) ≤ 1 - x + x * Real.exp θ := by
    simpa [smul_eq_mul, Real.exp_zero, mul_comm] using h
  nlinarith

private theorem eigenvalue_le_one {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hU : (1 - A).PosSemidef) (i : Fin k) :
    hA.1.eigenvalues i ≤ 1 := by
  let v := (hA.1.eigenvectorBasis i).ofLp
  have hvnorm : v ⬝ᵥ v = 1 := by
    have hb : ‖hA.1.eigenvectorBasis i‖ = 1 := hA.1.eigenvectorBasis.orthonormal.1 i
    calc
      v ⬝ᵥ v = ∑ j, v j ^ 2 := by simp [dotProduct, pow_two]
      _ = ‖hA.1.eigenvectorBasis i‖ ^ 2 := by
        change (∑ j, ((hA.1.eigenvectorBasis i).ofLp j) ^ 2) = _
        exact (EuclideanSpace.real_norm_sq_eq (hA.1.eigenvectorBasis i)).symm
      _ = 1 := by rw [hb]; norm_num
  have hveig : A *ᵥ v = hA.1.eigenvalues i • v := by
    simpa [v] using hA.1.mulVec_eigenvectorBasis i
  have hq := hU.dotProduct_mulVec_nonneg v
  have hmv : (1 - A) *ᵥ v = v - A *ᵥ v := by
    ext j
    simp [Matrix.mulVec, Matrix.one_apply, dotProduct, Finset.sum_sub_distrib, sub_mul]
  rw [hmv] at hq
  rw [hveig] at hq
  simp [dotProduct_sub, dotProduct_smul, hvnorm, smul_eq_mul] at hq
  linarith

private theorem one_draw_chord {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hU : (1 - A).PosSemidef) (θ : ℝ) :
    (1 + (Real.exp θ - 1) • A - NormedSpace.exp (θ • A)).PosSemidef := by
  classical
  let h := hA.1
  let U := h.eigenvectorUnitary
  let e : Matrix (Fin k) (Fin k) ℝ ≃⋆ₐ[ℝ] Matrix (Fin k) (Fin k) ℝ :=
    Unitary.conjStarAlgAut ℝ _ U
  let eig : Fin k → ℝ := h.eigenvalues
  let d : Fin k → ℝ := fun j => 1 + (Real.exp θ - 1) * eig j - Real.exp (θ * eig j)
  have hspec : A = e (diagonal eig) := by
    simpa [e, eig, Unitary.conjStarAlgAut_apply] using h.spectral_theorem
  have hscaled : θ • A = e (diagonal (fun j => θ * eig j)) := by
    rw [hspec, ← map_smul]
    congr 1
    ext i j
    simp [eig, Matrix.diagonal, smul_eq_mul]
  have heCont : Continuous (e : Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ) := by
    change Continuous (fun M => (U : Matrix (Fin k) (Fin k) ℝ) * M * star (U : Matrix (Fin k) (Fin k) ℝ))
    fun_prop
  have hexp : NormedSpace.exp (θ • A) = e (diagonal (fun j => Real.exp (θ * eig j))) := by
    calc
      NormedSpace.exp (θ • A) = NormedSpace.exp (e (diagonal (fun j => θ * eig j))) := by
        rw [hscaled]
      _ = e (NormedSpace.exp (diagonal (fun j => θ * eig j))) :=
        (NormedSpace.map_exp e heCont _).symm
      _ = e (diagonal (fun j => Real.exp (θ * eig j))) := by
        apply congrArg e
        rw [Matrix.exp_diagonal]
        congr 1
        funext j
        have hm := NormedSpace.map_exp (Pi.evalRingHom (fun _ : Fin k => ℝ) j) (continuous_apply j)
          (fun l : Fin k => θ * eig l)
        simpa only [Pi.evalRingHom_apply, Real.exp_eq_exp_ℝ] using hm
  have hd : (diagonal d).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro j
    have heig0 : 0 ≤ eig j := by
      exact hA.eigenvalues_nonneg j
    have heig1 : eig j ≤ 1 := eigenvalue_le_one A hA hU j
    have hs := scalar_exp_chord θ (eig j) heig0 heig1
    dsimp [d]
    nlinarith
  have hdiag : diagonal d = 1 + (Real.exp θ - 1) • diagonal eig -
      diagonal (fun j => Real.exp (θ * eig j)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, diagonal, one_apply, smul_eq_mul]
    · simp [d, diagonal, one_apply, hij]
  have htarget : 1 + (Real.exp θ - 1) • A - NormedSpace.exp (θ • A) = e (diagonal d) := by
    calc
      _ = 1 + (Real.exp θ - 1) • e (diagonal eig) -
            e (diagonal (fun j => Real.exp (θ * eig j))) := by rw [hexp, hspec]
      _ = e (1 + (Real.exp θ - 1) • diagonal eig -
            diagonal (fun j => Real.exp (θ * eig j))) := by
        simp only [map_sub, map_add, map_smul, map_one]
      _ = e (diagonal d) := congrArg e hdiag.symm
  have hepos : (e (diagonal d)).PosSemidef := by
    change ((U : Matrix (Fin k) (Fin k) ℝ) * diagonal d *
      star (U : Matrix (Fin k) (Fin k) ℝ)).PosSemidef
    exact hd.mul_mul_conjTranspose_same (B := (U : Matrix (Fin k) (Fin k) ℝ))
  rw [htarget]
  exact hepos

theorem proof : SAP.P005a.WH.W2.T9_L10 := by
  intro N k hN X hX μ hμ0 hμ1 hmean θ
  classical
  let c : ℝ := Real.exp θ - 1
  have hper (i : Fin N) :
      (1 + c • X i - NormedSpace.exp (θ • X i)).PosSemidef :=
    one_draw_chord (X i) (hX i).1 (hX i).2 θ
  have hsum : (∑ i : Fin N, (1 + c • X i - NormedSpace.exp (θ • X i))).PosSemidef := by
    simpa using (Matrix.posSemidef_sum Finset.univ (fun i hi => hper i))
  have havg : ((N : ℝ)⁻¹ •
      (∑ i : Fin N, (1 + c • X i - NormedSpace.exp (θ • X i)))).PosSemidef :=
    hsum.smul (inv_nonneg.mpr (by positivity))
  change (((1 + μ * (Real.exp θ - 1)) • (1 : Matrix (Fin k) (Fin k) ℝ)) -
    (N : ℝ)⁻¹ • (∑ i : Fin N, NormedSpace.exp (θ • X i))).PosSemidef
  have heq :
      (1 + μ * c) • (1 : Matrix (Fin k) (Fin k) ℝ) -
        (N : ℝ)⁻¹ • (∑ i : Fin N, NormedSpace.exp (θ • X i)) =
      (N : ℝ)⁻¹ • (∑ i : Fin N,
        (1 + c • X i - NormedSpace.exp (θ • X i))) := by
    have hsumId :
        (∑ i : Fin N, (1 + c • X i - NormedSpace.exp (θ • X i))) =
          (N : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) +
            c • (∑ i : Fin N, X i) -
              (∑ i : Fin N, NormedSpace.exp (θ • X i)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
      simp [Finset.sum_const]
      ext i j
      simp [Matrix.natCast_apply, Matrix.one_apply]
    rw [hsumId]
    have hNinv : (N : ℝ)⁻¹ * (N : ℝ) = 1 := by
      field_simp
    simp only [smul_sub, smul_add, smul_smul]
    rw [hNinv]
    have hc : ((N : ℝ)⁻¹ * c) • (∑ i : Fin N, X i) =
        c • ((N : ℝ)⁻¹ • (∑ i : Fin N, X i)) := by
      rw [smul_smul]
      congr 1
      ring
    rw [hc, hmean]
    module
  rw [heq]
  exact havg

end SAP.P005a.WH.W2.P.T9_L10

theorem SAP.P005a.WH.W2.T9_L10_proof : SAP.P005a.WH.W2.T9_L10 :=
  SAP.P005a.WH.W2.P.T9_L10.proof
