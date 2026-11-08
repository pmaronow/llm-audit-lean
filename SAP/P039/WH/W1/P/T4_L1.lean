import SAP.P039.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T4_L1

open scoped BigOperators Matrix

theorem whole_geometry {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (hZ : AronowAudit.P039.FullColumnRank Z)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k + 1 < n) :
    SAP.P039.WholeRegressionGeometry Z x := by
  let M := AronowAudit.P039.residualMaker Z
  let A := AronowAudit.P039.fullDesign Z x
  let sm := dotProduct x (M *ᵥ x)
  let e := SAP.P039.wholeRegressorContrast Z x
  let Q := AronowAudit.P039.residualMaker A
  have hA : AronowAudit.P039.FullColumnRank A :=
    AronowAudit.P039.RegressionCompletion.fullDesign_full_rank Z x hZ hx
  have hsse : AronowAudit.P039.olsSSE Z x = sm := by
    unfold AronowAudit.P039.olsSSE
    rw [← (AronowAudit.P039.ols_projection_identities Z hZ).2.2.2.2.2 x |>.1]
    change AronowAudit.P039.squaredLength (AronowAudit.P039.residualMaker Z *ᵥ x) = _
    exact AronowAudit.P039.RegressionCompletion.residual_quadratic Z hZ x
  have hsm : 0 < sm := by
    rw [← hsse]
    exact AronowAudit.P039.FiniteCompletion.residual_positive Z x hA
  have hsqrt : 0 < Real.sqrt sm := Real.sqrt_pos.2 hsm
  have hresquad :
      AronowAudit.P039.squaredLength (M *ᵥ x) = sm := by
    dsimp [sm, M]
    exact (AronowAudit.P039.RegressionCompletion.residual_quadratic Z hZ x).trans rfl
  have hnorm : dotProduct e e = 1 := by
    dsimp [e, SAP.P039.wholeRegressorContrast]
    rw [smul_dotProduct, dotProduct_smul]
    change (Real.sqrt sm)⁻¹ • ((Real.sqrt sm)⁻¹ •
      AronowAudit.P039.squaredLength (AronowAudit.P039.residualMaker Z *ᵥ x)) = 1
    change AronowAudit.P039.squaredLength (AronowAudit.P039.residualMaker Z *ᵥ x) =
      dotProduct x (AronowAudit.P039.residualMaker Z *ᵥ x) at hresquad
    rw [hresquad]
    simp only [smul_eq_mul]
    have hsquare := Real.sq_sqrt (le_of_lt hsm)
    field_simp [ne_of_gt hsqrt]
    nlinarith [hsquare]
  have hproj := AronowAudit.P039.ols_projection_identities A hA
  have hQsym : Qᵀ = Q := by
    dsimp [Q]
    exact hproj.2.2.1
  have hQidem : Q * Q = Q := by
    dsimp [Q]
    exact hproj.2.2.2.1
  have hQA : Q * A = 0 := by
    dsimp [Q, A]
    exact hproj.2.2.2.2.1
  have hvspan : M *ᵥ x = A *ᵥ Fin.snoc (-(AronowAudit.P039.ols Z x)) (1 : ℝ) := by
    dsimp [M, A]
    rw [AronowAudit.P039.FiniteCompletion.fullDesign_snoc]
    rw [(AronowAudit.P039.ols_projection_identities Z hZ).2.2.2.2.2 x |>.1]
    unfold AronowAudit.P039.olsResidual
    simp only [Matrix.mulVec_neg, one_smul, sub_eq_add_neg]
    abel
  have hQv : Q *ᵥ (M *ᵥ x) = 0 := by
    change Q *ᵥ (M *ᵥ x) = 0
    rw [hvspan, Matrix.mulVec_mulVec, hQA, Matrix.zero_mulVec]
  have hQe : Q *ᵥ e = 0 := by
    change Q *ᵥ ((Real.sqrt sm)⁻¹ • (M *ᵥ x)) = 0
    rw [Matrix.mulVec_smul, hQv, smul_zero]
  have hrank : Q.rank = n - k - 1 := by
    dsimp [Q, A]
    rw [AronowAudit.P039.CovarianceCompletion.residual_rank _ hA]
    omega
  have hcoeff :
      ∀ (γ : Fin k → ℝ) (ε : Fin n → ℝ),
        AronowAudit.P039.ols A (Z *ᵥ γ + ε) (Fin.last k) * Real.sqrt sm =
          dotProduct e ε := by
    intro γ ε
    obtain ⟨_, _, _, hlast, _, _, _⟩ :=
      AronowAudit.P039.RegressionCompletion.full_fit Z x (Z *ᵥ γ + ε) hZ hx
    have hMZ : M * Z = 0 := by
      dsimp [M]
      exact (AronowAudit.P039.ols_projection_identities Z hZ).2.2.2.2.1
    have hMkill : M *ᵥ (Z *ᵥ γ) = 0 := by
      rw [Matrix.mulVec_mulVec, hMZ, Matrix.zero_mulVec]
    have hMeq : M *ᵥ (Z *ᵥ γ + ε) = M *ᵥ ε := by
      rw [Matrix.mulVec_add, hMkill, zero_add]
    have hsym := AronowAudit.P039.RegressionCompletion.symmetric_dot M
      (AronowAudit.P039.ols_projection_identities Z hZ).2.2.1 x ε
    rw [hMeq] at hlast
    change AronowAudit.P039.ols A (Z *ᵥ γ + ε) (Fin.last k) =
      dotProduct x (M *ᵥ ε) / sm at hlast
    rw [hlast]
    change (dotProduct x (M *ᵥ ε) / sm) * Real.sqrt sm =
      dotProduct ((Real.sqrt sm)⁻¹ • (M *ᵥ x)) ε
    rw [smul_dotProduct, smul_eq_mul, hsym]
    field_simp [ne_of_gt hsqrt, ne_of_gt hsm]
    rw [Real.sq_sqrt (le_of_lt hsm)]
    <;> ring
  have hresidual :
      ∀ (γ : Fin k → ℝ) (ε : Fin n → ℝ),
        AronowAudit.P039.olsResidual A (Z *ᵥ γ + ε) = Q *ᵥ ε := by
    intro γ ε
    have hZγ : Q *ᵥ (Z *ᵥ γ) = 0 := by
      have hz : A *ᵥ Fin.snoc γ (0 : ℝ) = Z *ᵥ γ := by
        change AronowAudit.P039.fullDesign Z x *ᵥ Fin.snoc γ (0 : ℝ) = Z *ᵥ γ
        rw [AronowAudit.P039.FiniteCompletion.fullDesign_snoc]
        simp
      rw [← hz, Matrix.mulVec_mulVec, hQA, Matrix.zero_mulVec]
    have hid := hproj.2.2.2.2.2 (Z *ᵥ γ + ε)
    rw [Matrix.mulVec_add, hZγ, zero_add] at hid
    dsimp [Q, A]
    exact hid.1.symm
  have hse : ∀ y : Fin n → ℝ,
      AronowAudit.P039.olsSESquared A y (Fin.last k) =
        AronowAudit.P039.olsSSE A y / (((n : ℝ) - k - 1) * sm) := by
    intro y
    obtain ⟨_, _, _, _, _, _, hinv⟩ :=
      AronowAudit.P039.RegressionCompletion.full_fit Z x y hZ hx
    have hinv' : (Aᵀ * A)⁻¹ (Fin.last k) (Fin.last k) = 1 / sm := by
      simpa [A, M, sm] using hinv
    unfold AronowAudit.P039.olsSESquared
    rw [hinv']
    have hcast : ((n : ℝ) - (k + 1 : ℕ)) = (n : ℝ) - k - 1 := by
      norm_num [Nat.cast_add]
      ring
    have hdf : 0 < (n : ℝ) - k - 1 := by
      have hkn : (k : ℝ) + 1 < (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hcast]
    field_simp [ne_of_gt hsm, ne_of_gt hdf]
    <;> ring
  dsimp [SAP.P039.WholeRegressionGeometry, sm, e, Q, M, A]
  exact ⟨hsm, hnorm, hQsym, hQidem, hQe, hrank, hcoeff, hresidual, hse⟩

end SAP.P039.WH.W1.P.T4_L1

theorem SAP.P039.WH.W1.T4_L1_proof : SAP.P039.WH.W1.T4_L1 := by
  intro n k Z x hZ hx hn
  exact SAP.P039.WH.W1.P.T4_L1.whole_geometry Z x hZ hx hn
