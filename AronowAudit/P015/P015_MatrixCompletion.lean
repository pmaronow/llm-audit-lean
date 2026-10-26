import AronowAudit.P015.P015_MatrixDefinitions

namespace AronowAudit.P015.MatrixCompletion
open Matrix Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

lemma gram_posDef {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ)
    (hZ : (Z.transpose * Z).det ≠ 0) : (Z.transpose * Z).PosDef := by
  apply Matrix.PosDef.conjTranspose_mul_self Z
  intro x y hxy
  have h := congrArg ((Z.transpose * Z)⁻¹.mulVec ∘ Z.transpose.mulVec) hxy
  simpa only [Function.comp_apply, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hZ), Matrix.one_mulVec] using h

lemma precision_posDef {q : ℕ} (S Q : Matrix (Fin q) (Fin q) ℝ)
    (hS : S.PosSemidef) (hQ : Q.PosDef) (σ : ℝ) (hσ : 0 < σ) :
    (groupPrecision S Q σ).PosDef := by
  exact (Matrix.PosDef.posSemidef_add hS (hQ.inv.smul hσ)).inv

lemma raw_gls {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ)
    (S : Matrix (Fin q) (Fin q) ℝ) (σ : ℝ)
    (hS : S.PosSemidef) (hσ : 0 < σ) (hQ : (Z.transpose * Z).det ≠ 0) :
    let P := groupPrecision S (Z.transpose * Z) σ
    let V := Z*S*Z.transpose + σ • 1
    Z.transpose*V⁻¹*Z = P ∧ Z.transpose*V⁻¹ = P*(Z.transpose*Z)⁻¹*Z.transpose := by
  let Q := Z.transpose * Z
  let Ω := S + σ • Q⁻¹
  let V := Z*S*Z.transpose + σ • 1
  have hQp : Q.PosDef := gram_posDef Z hQ
  have hΩ : Ω.PosDef := Matrix.PosDef.posSemidef_add hS (hQp.inv.smul hσ)
  have hV : V.PosDef := by
    apply Matrix.PosDef.posSemidef_add
    · simpa using hS.mul_mul_conjTranspose_same Z
    · exact Matrix.PosDef.one.smul hσ
  have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQ)
  have hQj : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ)
  have hΩi : Ω * Ω⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hΩ.isUnit)
  have hVi : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hV.isUnit)
  have hb : V * (Z * Q⁻¹) = Z * Ω := by
    dsimp [V, Ω]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Z.transpose Z Q⁻¹]
    change Z * (S * (Q * Q⁻¹)) + σ • (Z * Q⁻¹) = Z*S + σ • (Z*Q⁻¹)
    rw [hQi, Matrix.mul_one]
  have hc : V⁻¹ * Z = Z * Q⁻¹ * Ω⁻¹ := by
    have hh : V * (Z * Q⁻¹ * Ω⁻¹) = Z := by
      rw [← Matrix.mul_assoc, hb, Matrix.mul_assoc, hΩi, Matrix.mul_one]
    have hh' := congrArg (fun A => V⁻¹ * A) hh
    simpa only [← Matrix.mul_assoc, hVi, Matrix.one_mul] using hh'.symm
  have hd : Z.transpose * V⁻¹ = Ω⁻¹ * Q⁻¹ * Z.transpose := by
    have hh := congrArg Matrix.transpose hc
    simpa only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      hV.isHermitian.isSymm.eq, hΩ.isHermitian.isSymm.eq, hQp.isHermitian.isSymm.eq,
      Matrix.mul_assoc] using hh
  change Z.transpose * V⁻¹ * Z = Ω⁻¹ ∧ Z.transpose * V⁻¹ = Ω⁻¹ * Q⁻¹ * Z.transpose
  refine ⟨?_, hd⟩
  rw [hd, Matrix.mul_assoc, Matrix.mul_assoc]
  change Ω⁻¹ * (Q⁻¹ * Q) = Ω⁻¹
  rw [hQj, Matrix.mul_one]

lemma pooling_difference {G Q : Type*} [Fintype G] [Fintype Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) (μ m : Q → ℝ)
    (hP : ∀ g, (P g).IsSymm)
    (hμ : (∑ g, P g).mulVec μ = ∑ g, (P g).mulVec (t g)) :
    poolingLoss P t m = poolingLoss P t μ +
      dotProduct (m-μ) ((∑ g, P g).mulVec (m-μ)) := by
  have hs : ∑ g, (P g).mulVec (t g-μ) = 0 := by
    simp only [Matrix.mulVec_sub, Finset.sum_sub_distrib, ← Matrix.sum_mulVec, hμ,
      sub_self]
  have hc : (∑ g, dotProduct (t g-μ) ((P g).mulVec (m-μ))) = 0 := by
    calc
      _ = dotProduct (m-μ) (∑ g, (P g).mulVec (t g-μ)) := by
        rw [dotProduct_sum]
        apply Finset.sum_congr rfl
        intro g _
        exact (hP g).dotProduct_mulVec_comm
      _ = 0 := by rw [hs, dotProduct_zero]
  have ht (g : G) : dotProduct (t g-m) ((P g).mulVec (t g-m)) =
      dotProduct (t g-μ) ((P g).mulVec (t g-μ)) -
      2*dotProduct (t g-μ) ((P g).mulVec (m-μ)) +
      dotProduct (m-μ) ((P g).mulVec (m-μ)) := by
    have he : t g-m = (t g-μ)-(m-μ) := by abel
    rw [he, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      (hP g).dotProduct_mulVec_comm (x := m-μ) (y := t g-μ)]
    ring
  unfold poolingLoss
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hc,
    mul_zero, sub_zero, ← dotProduct_sum, ← Matrix.sum_mulVec]

lemma scalar_block_weights {G Q : Type*} [Fintype G] [Fintype Q] [DecidableEq Q]
    (P : G → Matrix Q Q ℝ) (hH : IsUnit (∑ g, P g).det) (b : Q)
    (hrow : ∀ g j, j ≠ b → (P g) b j = 0 ∧ (P g) j b = 0)
    (hdiag : ∀ g, 0 < (P g) b b) [Nonempty G] :
    ∀ g j, ((∑ h, P h)⁻¹ * P g) b j =
      if j=b then P g b b/(∑ h, P h b b) else 0 := by
  let H := ∑ g, P g
  let p := ∑ g, P g b b
  have hp : 0 < p := Finset.sum_pos (fun g _ => hdiag g) Finset.univ_nonempty
  have hr (j : Q) : H b j = if j=b then p else 0 := by
    dsimp [H, p]
    by_cases hj : j=b
    · simp [hj, Matrix.sum_apply]
    · simp [hj, Matrix.sum_apply, fun g => (hrow g j hj).1]
  have hi (j : Q) : H⁻¹ b j = if j=b then 1/p else 0 := by
    have hh := congrArg (fun A : Matrix Q Q ℝ => A b j) (Matrix.mul_nonsing_inv H hH)
    simp only [Matrix.mul_apply, hr, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hh
    by_cases hj : j=b
    · subst j
      simp only [Matrix.one_apply_eq] at hh
      simp only [if_pos rfl]
      apply (eq_div_iff hp.ne').2
      simpa only [mul_comm] using hh
    · simp only [if_neg hj]
      have hz : p * H⁻¹ b j = 0 := by simpa [Matrix.one_apply, Ne.symm hj] using hh
      exact (mul_eq_zero.mp hz).resolve_left hp.ne'
  intro g j
  change (H⁻¹ * P g) b j = _
  simp only [Matrix.mul_apply, hi, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  by_cases hj : j=b
  · simp [hj, div_eq_mul_inv, mul_comm, p]
  · simp [hj, (hrow g j hj).1]


theorem corrected_matrix_pooling_completed (G q : ℕ) (hG : 1 ≤ G) (hq : 1 ≤ q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (y : ∀ g, Fin (n g) → ℝ) (S : Matrix (Fin q) (Fin q) ℝ)
    (σ₂ : Fin G → ℝ) (hS : S.PosSemidef)
    (hσ : ∀ g, 0 < σ₂ g) (hQ : ∀ g, ((Z g).transpose * Z g).det ≠ 0) :
    let P := fun g => groupPrecision S ((Z g).transpose*Z g) (σ₂ g)
    let H := ∑ g, P g
    let A := fun g => H⁻¹*P g
    let t := fun g => ols (Z g) (y g)
    let V : ∀ g, Matrix (Fin (n g)) (Fin (n g)) ℝ := fun g => Z g*S*(Z g).transpose+σ₂ g • 1
    (∀ m, poolingLoss P t (pooledGLS P t) ≤ poolingLoss P t m) ∧
    (∀ m, poolingLoss P t m = poolingLoss P t (pooledGLS P t) → m = pooledGLS P t) ∧
    pooledGLS P t = ∑ g, (A g).mulVec (t g) ∧ (∑ g, A g) = 1 ∧
    (∀ g, (Z g).transpose*(V g)⁻¹*Z g = P g ∧
      ((Z g).transpose*(V g)⁻¹).mulVec (y g) = (P g).mulVec (t g)) ∧
    pooledGLS P t = (∑ g, (Z g).transpose*(V g)⁻¹*Z g)⁻¹.mulVec
      (∑ g, ((Z g).transpose*(V g)⁻¹).mulVec (y g)) ∧
    (∀ b : Fin q, (∀ g j, j ≠ b → (P g) b j = 0 ∧ (P g) j b = 0) →
      (∀ g, 0 < (P g) b b) →
      ∀ g j, A g b j = if j=b then P g b b/(∑ h, P h b b) else 0) := by
  classical
  letI : Nonempty (Fin G) := ⟨⟨0, by omega⟩⟩
  dsimp only
  let P := fun g => groupPrecision S ((Z g).transpose * Z g) (σ₂ g)
  let H := ∑ g, P g
  let t := fun g => ols (Z g) (y g)
  let μ := pooledGLS P t
  have hP : ∀ g, (P g).PosDef := fun g =>
    precision_posDef S _ hS (gram_posDef (Z g) (hQ g)) (σ₂ g) (hσ g)
  have hH : H.PosDef := Matrix.posDef_sum Finset.univ_nonempty (fun g _ => hP g)
  have hHi : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hnormal : H.mulVec μ = ∑ g, (P g).mulVec (t g) := by
    dsimp [μ, pooledGLS]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hHi, Matrix.one_mulVec]
  have hdiff (m : Fin q → ℝ) : poolingLoss P t m = poolingLoss P t μ +
      dotProduct (m-μ) (H.mulVec (m-μ)) :=
    pooling_difference P t μ m (fun g => (hP g).isHermitian.isSymm) hnormal
  have hraw (g : Fin G) := raw_gls (Z g) S (σ₂ g) hS (hσ g) (hQ g)
  have hy (g : Fin G) :
      (((Z g).transpose * (Z g*S*(Z g).transpose + σ₂ g • 1)⁻¹).mulVec (y g)) =
        (P g).mulVec (t g) := by
    rw [(hraw g).2]
    simp only [t, ols, P, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    change poolingLoss P t μ ≤ poolingLoss P t m
    rw [hdiff m]
    exact le_add_of_nonneg_right (by
      simpa only [star_trivial] using hH.posSemidef.dotProduct_mulVec_nonneg (m-μ))
  · intro m heq
    change m=μ
    by_contra hm
    have hp := hH.dotProduct_mulVec_pos (sub_ne_zero.mpr hm)
    simp only [star_trivial] at hp
    change poolingLoss P t m = poolingLoss P t μ at heq
    linarith [hdiff m]
  · change H⁻¹.mulVec (∑ g, (P g).mulVec (t g)) =
      ∑ g, (H⁻¹ * P g).mulVec (t g)
    simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_sum]
  · change (∑ g, H⁻¹ * P g) = 1
    rw [← Finset.mul_sum, Matrix.nonsing_inv_mul H hHi]
  · intro g
    exact ⟨(hraw g).1, hy g⟩
  · have ha : (∑ g, (Z g).transpose * (Z g*S*(Z g).transpose + σ₂ g • 1)⁻¹ * Z g)=H := by
      apply Finset.sum_congr rfl
      intro g _
      exact (hraw g).1
    have hb : (∑ g, ((Z g).transpose * (Z g*S*(Z g).transpose + σ₂ g • 1)⁻¹).mulVec (y g)) =
        ∑ g, (P g).mulVec (t g) := Finset.sum_congr rfl (fun g _ => hy g)
    rw [ha, hb]
    rfl
  · intro b hrow hdiag
    exact scalar_block_weights P hHi b hrow hdiag

end
end AronowAudit.P015.MatrixCompletion
