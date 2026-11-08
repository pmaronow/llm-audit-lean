import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T8_L7

open scoped BigOperators Matrix

noncomputable section

def blockEquiv (m : ℕ) : Fin 5 × Fin m ≃ Fin (5*m) where
  toFun x := ⟨x.1.val + 5*x.2.val, by omega⟩
  invFun i := (⟨i.val % 5, Nat.mod_lt _ (by omega)⟩, ⟨i.val / 5, by omega⟩)
  left_inv x := by
    apply Prod.ext
    · apply Fin.ext
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.1.isLt]
    · apply Fin.ext
      simp [Nat.add_mul_div_left, Nat.div_eq_of_lt x.1.isLt]
  right_inv i := by
    apply Fin.ext
    exact Nat.mod_add_div i.val 5

def lift (m : ℕ) (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin (5*m)) (Fin (5*m)) ℝ :=
  Matrix.reindex (blockEquiv m) (blockEquiv m) (Matrix.blockDiagonal fun _ : Fin m => A)

lemma lift_mul (m : ℕ) (A B : Matrix (Fin 5) (Fin 5) ℝ) :
    lift m (A*B) = lift m A * lift m B := by
  simp only [lift, Matrix.reindex_apply]
  rw [Matrix.blockDiagonal_mul]
  exact (Matrix.submatrix_mul_equiv
    (Matrix.blockDiagonal fun _ : Fin m => A)
    (Matrix.blockDiagonal fun _ : Fin m => B)
    (blockEquiv m).symm (blockEquiv m).symm (blockEquiv m).symm).symm

lemma lift_add (m : ℕ) (A B : Matrix (Fin 5) (Fin 5) ℝ) :
    lift m (A+B) = lift m A + lift m B := by
  ext i j
  by_cases h : ((blockEquiv m).symm i).2 = ((blockEquiv m).symm j).2 <;>
    simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal, h]

lemma lift_smul (m : ℕ) (r : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ) :
    lift m (r • A) = r • lift m A := by
  ext i j
  simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal]

lemma lift_sub (m : ℕ) (A B : Matrix (Fin 5) (Fin 5) ℝ) :
    lift m (A-B) = lift m A - lift m B := by
  rw [sub_eq_add_neg, lift_add, sub_eq_add_neg]
  congr 1
  rw [show -B = (-1 : ℝ) • B by simp, lift_smul,
    show -lift m B = (-1 : ℝ) • lift m B by simp]

lemma lift_one (m : ℕ) : lift m (1 : Matrix (Fin 5) (Fin 5) ℝ) = 1 := by
  ext i j
  by_cases hb : ((blockEquiv m).symm i).2 = ((blockEquiv m).symm j).2
  · by_cases hl : ((blockEquiv m).symm i).1 = ((blockEquiv m).symm j).1
    · have hij : i = j := by
        apply (blockEquiv m).symm.injective
        exact Prod.ext hl hb
      simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal,
        Matrix.one_apply, hb, hl, hij]
    · have hij : i ≠ j := by
        intro h
        apply hl
        exact congrArg Prod.fst (congrArg (blockEquiv m).symm h)
      simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal,
        Matrix.one_apply, hb, hl, hij]
  · have hij : i ≠ j := by
      intro h
      apply hb
      exact congrArg Prod.snd (congrArg (blockEquiv m).symm h)
    simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal,
      Matrix.one_apply, hb, hij]

lemma lift_zero (m : ℕ) : lift m (0 : Matrix (Fin 5) (Fin 5) ℝ) = 0 := by
  ext i j
  simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal]

lemma lift_natCast (m n : ℕ) :
    lift m (n : Matrix (Fin 5) (Fin 5) ℝ) = (n : Matrix (Fin (5*m)) (Fin (5*m)) ℝ) := by
  induction n with
  | zero => simp [lift_zero]
  | succ n ih =>
    rw [Nat.cast_succ, lift_add, ih, lift_one, Nat.cast_succ]

lemma repeatedBlock_eq_lift (m : ℕ) (pd : Bool) :
    SAP.P004a.starBlockKernel m pd = lift m (if pd then SAP.P004a.starPD else SAP.P004a.starKernel) := by
  ext i j
  let ci : Fin 5 × Fin m :=
    (⟨i.val % 5, Nat.mod_lt _ (by omega)⟩, ⟨i.val / 5, by omega⟩)
  let cj : Fin 5 × Fin m :=
    (⟨j.val % 5, Nat.mod_lt _ (by omega)⟩, ⟨j.val / 5, by omega⟩)
  have hi : blockEquiv m ci = i := by
    apply Fin.ext
    exact Nat.mod_add_div i.val 5
  have hj : blockEquiv m cj = j := by
    apply Fin.ext
    exact Nat.mod_add_div j.val 5
  have hci : (blockEquiv m).symm i = ci := by
    calc
      (blockEquiv m).symm i = (blockEquiv m).symm (blockEquiv m ci) := by rw [hi]
      _ = ci := Equiv.symm_apply_apply _ _
  have hcj : (blockEquiv m).symm j = cj := by
    calc
      (blockEquiv m).symm j = (blockEquiv m).symm (blockEquiv m cj) := by rw [hj]
      _ = cj := Equiv.symm_apply_apply _ _
  simp [lift, Matrix.reindex_apply, Matrix.submatrix, Matrix.blockDiagonal,
    SAP.P004a.starBlockKernel, ci, cj, hci, hcj]

lemma starKernel_poly :
    (SAP.P004a.starKernel + 1) * (SAP.P004a.starKernel - 1) *
      (SAP.P004a.starKernel - (3 : ℝ) • 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, Fin.sum_univ_succ]
    <;> norm_num [SAP.P004a.starKernel, Matrix.of_apply, Matrix.one_apply,
      Matrix.smul_apply]

lemma starKernel_sq :
    SAP.P004a.starKernel * SAP.P004a.starKernel = Matrix.of (fun i j : Fin 5 =>
      if i = 0 then if j = 0 then 5 else 2
      else if j = 0 then 2 else if i = j then 2 else 1) := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_succ]
    <;> norm_num [SAP.P004a.starKernel, Matrix.of_apply]

lemma starKernel_positive_formula :
    (1/8 : ℝ) • (SAP.P004a.starKernel * SAP.P004a.starKernel +
      (4 : ℝ) • SAP.P004a.starKernel + (3 : ℝ) • 1) = SAP.P004a.starPD := by
  rw [starKernel_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SAP.P004a.starPD, SAP.P004a.starKernel,
      SAP.P004a.starNegativeVector, Matrix.of_apply, Matrix.one_apply,
      Matrix.smul_apply]

lemma spectralKernel_as_conjugate {N : ℕ} (vals : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℝ) (trim : Bool) :
    SAP.P004a.spectralKernel vals V trim =
      V * Matrix.diagonal (fun k => if trim then max (vals k) 0 else vals k) * Vᵀ := by
  ext i j
  change (∑ k, (if trim then max (vals k) 0 else vals k) * V i k * V j k) =
    (V * Matrix.diagonal (fun k => if trim then max (vals k) 0 else vals k) * Vᵀ) i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hinner (k : Fin N) :
      (Matrix.diagonal (fun k => if trim then max (vals k) 0 else vals k) * Vᵀ) k j =
        (if trim then max (vals k) 0 else vals k) * V j k := by
    rw [Matrix.diagonal_mul, Matrix.transpose_apply]
  simp_rw [hinner]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma positiveKernel_of_polynomial {N : ℕ} (K Q : Matrix (Fin N) (Fin N) ℝ)
    (hKsym : K.IsSymm)
    (hpoly : (K + 1) * (K - 1) * (K - (3 : ℝ) • 1) = 0)
    (hQ : (1/8 : ℝ) • (K*K + (4 : ℝ) • K + (3 : ℝ) • 1) = Q) :
    SAP.P004a.positiveKernel K = Q := by
  obtain ⟨vals, V, horth, hK, hpos⟩ := SAP.P004a.WH.W2.positiveKernel_data K hKsym
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal vals
  have hrep : K = V * D * Vᵀ := by
    calc
      K = SAP.P004a.spectralKernel vals V false := hK.symm
      _ = V * D * Vᵀ := by
        rw [spectralKernel_as_conjugate]
        congr 1
  have hKV : K * V = V * D := by
    rw [hrep]
    simp [Matrix.mul_assoc, horth]
  have hplus : (K + 1) * V = V * (D + 1) := by
    rw [Matrix.add_mul, hKV, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
  have hminus : (K - 1) * V = V * (D - 1) := by
    calc
      (K - 1) * V = K * V - 1 * V := Matrix.sub_mul _ _ _
      _ = V * D - V := by rw [hKV, Matrix.one_mul]
      _ = V * (D - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
  have hminus3 : (K - (3 : ℝ) • 1) * V = V * (D - (3 : ℝ) • 1) := by
    calc
      (K - (3 : ℝ) • 1) * V = K * V - ((3 : ℝ) • 1) * V := Matrix.sub_mul _ _ _
      _ = V * D - (3 : ℝ) • V := by rw [hKV, Matrix.smul_mul, Matrix.one_mul]
      _ = V * D - V * ((3 : ℝ) • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = V * (D - (3 : ℝ) • 1) := by rw [Matrix.mul_sub]
  have hpolyV : ((K + 1) * (K - 1) * (K - (3 : ℝ) • 1)) * V =
      V * ((D + 1) * (D - 1) * (D - (3 : ℝ) • 1)) := by
    calc
      ((K + 1) * (K - 1) * (K - (3 : ℝ) • 1)) * V =
          (K + 1) * (K - 1) * ((K - (3 : ℝ) • 1) * V) := by simp [Matrix.mul_assoc]
      _ = (K + 1) * (K - 1) * (V * (D - (3 : ℝ) • 1)) := by rw [hminus3]
      _ = (K + 1) * ((K - 1) * V) * (D - (3 : ℝ) • 1) := by simp [Matrix.mul_assoc]
      _ = (K + 1) * (V * (D - 1)) * (D - (3 : ℝ) • 1) := by rw [hminus]
      _ = ((K + 1) * V) * (D - 1) * (D - (3 : ℝ) • 1) := by simp [Matrix.mul_assoc]
      _ = (V * (D + 1)) * (D - 1) * (D - (3 : ℝ) • 1) := by rw [hplus]
      _ = V * ((D + 1) * (D - 1) * (D - (3 : ℝ) • 1)) := by simp [Matrix.mul_assoc]
  have hzeroV : (0 : Matrix (Fin N) (Fin N) ℝ) =
      V * ((D + 1) * (D - 1) * (D - (3 : ℝ) • 1)) := by
    simpa [hpoly] using hpolyV
  have hdiag0 : (D + 1) * (D - 1) * (D - (3 : ℝ) • 1) = 0 := by
    have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => Vᵀ * M) hzeroV
    calc
      (D + 1) * (D - 1) * (D - (3 : ℝ) • 1) =
          Vᵀ * (V * ((D + 1) * (D - 1) * (D - (3 : ℝ) • 1))) := by
            rw [← Matrix.mul_assoc, horth, Matrix.one_mul]
      _ = 0 := by simpa using hh.symm
  have hdiagmul (f g : Fin N → ℝ) :
      Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal (fun k => f k * g k) := by
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hfactor :
      (D + 1) * (D - 1) * (D - (3 : ℝ) • 1) =
        Matrix.diagonal (fun k => (vals k + 1) * (vals k - 1) * (vals k - 3)) := by
    have hplusD : D + 1 = Matrix.diagonal (fun k => vals k + 1) := by
      dsimp [D]
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
    have hminusD : D - 1 = Matrix.diagonal (fun k => vals k - 1) := by
      dsimp [D]
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    have hminus3D : D - (3 : ℝ) • 1 =
        Matrix.diagonal (fun k => vals k - 3) := by
      have hthree : (3 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) =
          Matrix.diagonal (fun _ : Fin N => (3 : ℝ)) := by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
        congr 1
        funext x
        norm_num
      dsimp [D]
      rw [hthree, ← Matrix.diagonal_sub]
    rw [hplusD, hminusD, hminus3D, hdiagmul, hdiagmul]
  have hrootFun : (fun k : Fin N => (vals k + 1) * (vals k - 1) * (vals k - 3)) = 0 := by
    apply (Matrix.diagonal_eq_zero).mp
    rw [← hfactor]
    exact hdiag0
  have hroot (k : Fin N) :
      (vals k + 1) * (vals k - 1) * (vals k - 3) = 0 := by
    exact congrFun hrootFun k
  have hscalar (k : Fin N) :
      max (vals k) 0 = (vals k ^ 2 + 4 * vals k + 3) / 8 := by
    have hr := hroot k
    rcases mul_eq_zero.mp hr with hleft | hright
    · rcases mul_eq_zero.mp hleft with hneg | hone
      · have ht : vals k = -1 := by linarith
        simp [ht] <;> norm_num
      · have ht : vals k = 1 := by linarith
        simp [ht] <;> norm_num
    · have ht : vals k = 3 := by linarith
      simp [ht] <;> norm_num
  have hspec : SAP.P004a.spectralKernel vals V true =
      V * Matrix.diagonal (fun k => max (vals k) 0) * Vᵀ := by
    simpa using spectralKernel_as_conjugate vals V true
  have hsq : K*K = V * Matrix.diagonal (fun k => vals k ^ 2) * Vᵀ := by
    rw [hrep]
    have hDD : D * D = Matrix.diagonal (fun k => vals k ^ 2) := by
      ext i j
      dsimp [D]
      rw [Matrix.diagonal_mul]
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
      <;> ring
    calc
      (V * D * Vᵀ) * (V * D * Vᵀ) = V * (D * ((Vᵀ * V) * (D * Vᵀ))) := by
        simp only [Matrix.mul_assoc]
      _ = V * (D * (1 * (D * Vᵀ))) := by rw [horth]
      _ = V * D * D * Vᵀ := by simp [Matrix.mul_assoc]
      _ = V * (D * D) * Vᵀ := by simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun k => vals k ^ 2) * Vᵀ := by rw [hDD]
  have hone : (1 : Matrix (Fin N) (Fin N) ℝ) = V * (1 : Matrix (Fin N) (Fin N) ℝ) * Vᵀ := by
    have hVtV : Vᵀ * V = 1 := horth
    have hVVt : V * Vᵀ = 1 := mul_eq_one_comm.mpr hVtV
    calc
      1 = V * Vᵀ := hVVt.symm
      _ = V * 1 * Vᵀ := by simp [Matrix.mul_assoc]
  have hformula : (1/8 : ℝ) • (K*K + (4 : ℝ) • K + (3 : ℝ) • 1) =
      V * Matrix.diagonal (fun k => (vals k ^ 2 + 4 * vals k + 3) / 8) * Vᵀ := by
    have hfour : (4 : ℝ) • D = Matrix.diagonal (fun k => (4 : ℝ) * vals k) := by
      dsimp [D]
      rw [← Matrix.diagonal_smul]
      congr 1 <;> funext k <;> norm_num
    have hthree : (3 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) =
        Matrix.diagonal (fun _ : Fin N => (3 : ℝ)) := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
      congr 1 <;> funext k <;> norm_num
    have hinner : Matrix.diagonal (fun k => vals k ^ 2) + (4 : ℝ) • D +
        (3 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) =
        Matrix.diagonal (fun k => vals k ^ 2 + 4 * vals k + 3) := by
      rw [hfour, hthree, ← Matrix.diagonal_add, ← Matrix.diagonal_add]
    have hsum :
        V * Matrix.diagonal (fun k => vals k ^ 2) * Vᵀ +
          (4 : ℝ) • (V * D * Vᵀ) + (3 : ℝ) • (V * (1 : Matrix (Fin N) (Fin N) ℝ) * Vᵀ) =
        V * Matrix.diagonal (fun k => vals k ^ 2 + 4 * vals k + 3) * Vᵀ := by
      have hconjSmul (c : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
          V * (c • A) * Vᵀ = c • (V * A * Vᵀ) := by
        calc
          V * (c • A) * Vᵀ = (c • (V * A)) * Vᵀ := by rw [Matrix.mul_smul]
          _ = c • ((V * A) * Vᵀ) := by rw [Matrix.smul_mul]
          _ = c • (V * A * Vᵀ) := rfl
      calc
        _ = V * (Matrix.diagonal (fun k => vals k ^ 2) + (4 : ℝ) • D +
            (3 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)) * Vᵀ := by
          symm
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
          rw [hconjSmul (4 : ℝ) D, hconjSmul (3 : ℝ) 1]
        _ = V * Matrix.diagonal (fun k => vals k ^ 2 + 4 * vals k + 3) * Vᵀ := by rw [hinner]
    rw [hsq, hrep, hone]
    calc
      (1/8 : ℝ) • (V * Matrix.diagonal (fun k => vals k ^ 2) * Vᵀ +
          (4 : ℝ) • (V * D * Vᵀ) + (3 : ℝ) • (V * (1 : Matrix (Fin N) (Fin N) ℝ) * Vᵀ)) =
          (1/8 : ℝ) • (V * Matrix.diagonal (fun k => vals k ^ 2 + 4 * vals k + 3) * Vᵀ) := by
            rw [hsum]
      _ = V * Matrix.diagonal (fun k => (vals k ^ 2 + 4 * vals k + 3) / 8) * Vᵀ := by
        let p : Fin N → ℝ := fun k => vals k ^ 2 + 4 * vals k + 3
        have hp : Matrix.diagonal ((1/8 : ℝ) • p) =
            Matrix.diagonal (fun k => p k / 8) := by
          exact congrArg Matrix.diagonal (funext fun k => by
            change (1/8 : ℝ) * p k = p k / 8
            field_simp)
        have hscale (c : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
            c • (V * A * Vᵀ) = V * (c • A) * Vᵀ := by
          calc
            c • (V * A * Vᵀ) = (c • (V * A)) * Vᵀ := (Matrix.smul_mul _ _ _).symm
            _ = (V * (c • A)) * Vᵀ := by rw [(Matrix.mul_smul _ _ _).symm]
            _ = V * (c • A) * Vᵀ := rfl
        calc
          (1/8 : ℝ) • (V * Matrix.diagonal (fun k => vals k ^ 2 + 4 * vals k + 3) * Vᵀ) =
              V * Matrix.diagonal ((1/8 : ℝ) • p) * Vᵀ := by
                rw [hscale, ← Matrix.diagonal_smul]
          _ = V * Matrix.diagonal (fun k => p k / 8) * Vᵀ := by rw [hp]
          _ = V * Matrix.diagonal (fun k => (vals k ^ 2 + 4 * vals k + 3) / 8) * Vᵀ := by
            congr 2
  have hmaxpoly : Matrix.diagonal (fun k => max (vals k) 0) =
      Matrix.diagonal (fun k => (vals k ^ 2 + 4 * vals k + 3) / 8) := by
    exact congrArg Matrix.diagonal (funext hscalar)
  have hpk : SAP.P004a.positiveKernel K = SAP.P004a.spectralKernel vals V true := hpos.symm
  rw [hpk, hspec, hmaxpoly, ← hformula, hQ]

end
end SAP.P004a.WH.W2.P.T8_L7

theorem SAP.P004a.WH.W2.T8_L7_proof : SAP.P004a.WH.W2.T8_L7 := by
  intro m
  by_cases hm : m = 0
  · subst m
    ext i j
    exact Fin.elim0 i
  have hKrep : SAP.P004a.starBlockKernel m false =
      SAP.P004a.WH.W2.P.T8_L7.lift m SAP.P004a.starKernel := by
    simpa using SAP.P004a.WH.W2.P.T8_L7.repeatedBlock_eq_lift m false
  have hQrep : SAP.P004a.starBlockKernel m true =
      SAP.P004a.WH.W2.P.T8_L7.lift m SAP.P004a.starPD := by
    simpa using SAP.P004a.WH.W2.P.T8_L7.repeatedBlock_eq_lift m true
  have hpoly :
      (SAP.P004a.starBlockKernel m false + 1) *
        (SAP.P004a.starBlockKernel m false - 1) *
        (SAP.P004a.starBlockKernel m false - (3 : ℝ) • 1) = 0 := by
    simpa [hKrep, SAP.P004a.WH.W2.P.T8_L7.lift_mul,
      SAP.P004a.WH.W2.P.T8_L7.lift_add, SAP.P004a.WH.W2.P.T8_L7.lift_sub,
      SAP.P004a.WH.W2.P.T8_L7.lift_smul,
      SAP.P004a.WH.W2.P.T8_L7.lift_one, SAP.P004a.WH.W2.P.T8_L7.lift_zero] using
      congrArg (SAP.P004a.WH.W2.P.T8_L7.lift m) SAP.P004a.WH.W2.P.T8_L7.starKernel_poly
  have hformula :
      (1/8 : ℝ) • (SAP.P004a.starBlockKernel m false * SAP.P004a.starBlockKernel m false +
        (4 : ℝ) • SAP.P004a.starBlockKernel m false + (3 : ℝ) • 1) =
      SAP.P004a.starBlockKernel m true := by
    simpa [hKrep, hQrep, SAP.P004a.WH.W2.P.T8_L7.lift_mul,
      SAP.P004a.WH.W2.P.T8_L7.lift_add, SAP.P004a.WH.W2.P.T8_L7.lift_smul,
      SAP.P004a.WH.W2.P.T8_L7.lift_one] using
      congrArg (SAP.P004a.WH.W2.P.T8_L7.lift m)
        SAP.P004a.WH.W2.P.T8_L7.starKernel_positive_formula
  have hsym : (SAP.P004a.starBlockKernel m false).IsSymm := by
    ext i j
    exact AronowAudit.P004.Wave1.t7_block_kernel_symmetric m false j i
  exact SAP.P004a.WH.W2.P.T8_L7.positiveKernel_of_polynomial _ _ hsym hpoly hformula
