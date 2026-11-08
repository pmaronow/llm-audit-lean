import SAP.P039.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

namespace SAP.P039.WH.W1.P.T4_L2

open scoped BigOperators Matrix RealInnerProductSpace
open WithLp (toLp ofLp)

private lemma dotProduct_eq_inner_toLp {n : ℕ} (x y : Fin n → ℝ) :
    dotProduct x y = inner ℝ (toLp 2 x : EuclideanSpace ℝ (Fin n)) (toLp 2 y) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct_comm]

end SAP.P039.WH.W1.P.T4_L2

open SAP.P039.WH.W1.P.T4_L2
open WithLp (toLp ofLp)
open scoped BigOperators Matrix RealInnerProductSpace

theorem SAP.P039.WH.W1.T4_L2_proof : SAP.P039.WH.W1.T4_L2 := by
  classical
  intro n ν Q e htranspose hidem hkill hunit hrank
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    LinearMap.range (Matrix.toLpLin 2 2 Q)
  have hdim : Module.finrank ℝ S = ν := by
    have hr := Q.rank_eq_finrank_range_toLin
      (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n))
    change Q.rank = Module.finrank ℝ
      (LinearMap.range (Matrix.toLin (PiLp.basisFun 2 ℝ (Fin n))
        (PiLp.basisFun 2 ℝ (Fin n)) Q)) at hr
    change Module.finrank ℝ (LinearMap.range (Matrix.toLpLin 2 2 Q)) = ν
    rw [Matrix.toLpLin_eq_toLin]
    exact hr.symm.trans hrank
  let b : OrthonormalBasis (Fin ν) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (Equiv.cast (congrArg Fin hdim))
  let qrow : Fin ν → Fin n → ℝ := fun i => ofLp ((b i : S) : EuclideanSpace ℝ (Fin n))
  let B : Matrix (Fin (ν + 1)) (Fin n) ℝ := fun i j =>
    Fin.cases (e j) (fun k => qrow k j) i
  have hsymm : Q.IsSymm := htranspose
  have hfix (v : S) : Q *ᵥ ofLp (v : EuclideanSpace ℝ (Fin n)) =
      ofLp (v : EuclideanSpace ℝ (Fin n)) := by
    obtain ⟨w, hw⟩ := v.2
    have hw' : Q *ᵥ ofLp w = ofLp (v : EuclideanSpace ℝ (Fin n)) := by
      have := congrArg ofLp hw
      simpa using this
    calc
      Q *ᵥ ofLp (v : EuclideanSpace ℝ (Fin n)) = Q *ᵥ (Q *ᵥ ofLp w) := by rw [← hw']
      _ = Q *ᵥ ofLp w := by rw [Matrix.mulVec_mulVec, hidem]
      _ = ofLp (v : EuclideanSpace ℝ (Fin n)) := hw'
  have hproj (v : S) (z : Fin n → ℝ) :
      dotProduct (ofLp (v : EuclideanSpace ℝ (Fin n))) z =
        dotProduct (ofLp (v : EuclideanSpace ℝ (Fin n))) (Q *ᵥ z) := by
    have hfixv := hfix v
    calc
      dotProduct (ofLp (v : EuclideanSpace ℝ (Fin n))) z =
          dotProduct (Q *ᵥ ofLp (v : EuclideanSpace ℝ (Fin n))) z := by rw [hfixv]
      _ = dotProduct z (Q *ᵥ ofLp (v : EuclideanSpace ℝ (Fin n))) := dotProduct_comm _ _
      _ = dotProduct (ofLp (v : EuclideanSpace ℝ (Fin n))) (Q *ᵥ z) :=
        hsymm.dotProduct_mulVec_comm
  have horth (i k : Fin ν) : dotProduct (qrow i) (qrow k) = if i = k then 1 else 0 := by
    rw [dotProduct_eq_inner_toLp]
    change inner ℝ (b i) (b k) = _
    have hb := b.orthonormal
    rw [orthonormal_iff_ite] at hb
    simpa using hb i k
  have heq0 (i : Fin ν) : dotProduct e (qrow i) = 0 := by
    have hqi := hfix (b i)
    calc
      dotProduct e (qrow i) = dotProduct e (Q *ᵥ qrow i) := by rw [hqi]
      _ = dotProduct (qrow i) (Q *ᵥ e) := hsymm.dotProduct_mulVec_comm
      _ = 0 := by rw [hkill]; simp
  have hBzero : B 0 = e := by
    funext j
    simp [B]
  have hBsucc (i : Fin ν) : B i.succ = qrow i := by
    funext j
    simp [B]
  have hrows (i k : Fin (ν + 1)) :
      dotProduct (B i) (B k) = if i = k then 1 else 0 := by
    cases i using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => simp [hBzero, hunit]
      | succ k =>
        simp only [hBzero, hBsucc]
        simp [heq0, Ne.symm (Fin.succ_ne_zero k)]
    | succ i =>
      cases k using Fin.cases with
      | zero =>
        simp only [hBzero, hBsucc]
        simp [dotProduct_comm, heq0, Fin.succ_ne_zero]
      | succ k =>
        simpa [hBsucc] using horth i k
  have hgram : B * Bᵀ = 1 := by
    ext i k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dotProduct] using
      hrows i k
  refine ⟨B, hgram, ?_, ?_⟩
  · intro j
    simp [hBzero]
  · intro z
    let qz : S := ⟨toLp 2 (Q *ᵥ z), by
      change (Matrix.toLpLin 2 2 Q) (toLp 2 z) ∈ LinearMap.range (Matrix.toLpLin 2 2 Q)
      exact LinearMap.mem_range_self _ (toLp 2 z)⟩
    have hcoord (i : Fin ν) : dotProduct (qrow i) z =
        inner ℝ (b i) qz := by
      calc
        dotProduct (qrow i) z = dotProduct (qrow i) (Q *ᵥ z) :=
          hproj (b i) z
        _ = inner ℝ (b i) qz := by
          rw [dotProduct_eq_inner_toLp]
          rfl
    have hparseval := b.sum_sq_inner_right qz
    calc
      squaredLength (Q *ᵥ z) = ‖qz‖ ^ 2 := by
        change dotProduct (Q *ᵥ z) (Q *ᵥ z) =
          ‖(toLp 2 (Q *ᵥ z) : EuclideanSpace ℝ (Fin n))‖ ^ 2
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, pow_two]
      _ = ∑ i : Fin ν, (dotProduct (qrow i) z) ^ 2 := by
        calc
          ‖qz‖ ^ 2 = ∑ i : Fin ν, (inner ℝ (b i) qz) ^ 2 :=
            hparseval.symm
          _ = ∑ i : Fin ν, (dotProduct (qrow i) z) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcoord]
      _ = ∑ i : Fin ν, ((B *ᵥ z) i.succ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Matrix.mulVec, dotProduct, hBsucc]

