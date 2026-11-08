import SAP.P001a.WH.W3.Leaves
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped BigOperators Topology Matrix

noncomputable section

namespace SAP.P001a.WH.W3.P.T5_L1

open SAP.P001a.WH.W3
open AronowAudit.P001.Wave1.SieveRate

private theorem tendsto_finset_sum_real {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : ι → ℕ → ℝ) (a : ι → ℝ)
    (hf : ∀ i, Tendsto (f i) atTop (nhds (a i))) :
    Tendsto (fun r => ∑ i, f i r) atTop (nhds (∑ i, a i)) := by
  classical
  have hsum : ∀ s : Finset ι,
      Tendsto (fun r => ∑ i ∈ s, f i r) atTop (nhds (∑ i ∈ s, a i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    | @insert i s his ih =>
        simpa [Finset.sum_insert, his] using (hf i).add ih
  simpa using hsum Finset.univ

private theorem coefficient_eval_eq_vand_mulVec {n : ℕ} (d : ℕ) (x : Fin n → ℝ)
    (b : Fin (d + 1) → ℝ) (i : Fin n) :
    (coefficientPolynomialW3 b).eval (x i) = ((vand d x).mulVec b) i := by
  simp only [coefficientPolynomialW3, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, vand, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

private theorem gram_quadratic {n m : Type*} [Fintype n] [Fintype m]
    (P : Matrix n m ℝ) (v : m → ℝ) :
    v ⬝ᵥ ((Pᵀ * P) *ᵥ v) = (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]

private theorem gram_rhs_dot {n m : Type*} [Fintype n] [Fintype m]
    (P : Matrix n m ℝ) (v : m → ℝ) (y : n → ℝ) :
    v ⬝ᵥ (Pᵀ *ᵥ y) = y ⬝ᵥ (P *ᵥ v) :=
  Matrix.dotProduct_transpose_mulVec P v y

end SAP.P001a.WH.W3.P.T5_L1

open SAP.P001a.WH.W3.P.T5_L1
open SAP.P001a.WH.W3
open AronowAudit.P001.Wave1.SieveRate

theorem SAP.P001a.WH.W3.T5_L1_proof : SAP.P001a.WH.W3.T5_L1 := by
  classical
  intro n d z
  let P : Matrix (Fin n) (Fin (d + 1)) ℝ := vand d z.1
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Pᵀ * P
  let g : Fin (d + 1) → ℝ := Pᵀ *ᵥ z.2
  let hA : A.IsHermitian := by
    dsimp [A]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_conjTranspose_mul_self P)
  let hpsd : A.PosSemidef := by
    dsimp [A]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self P)
  let B := hA.eigenvectorBasis
  let lam : Fin (d + 1) → ℝ := hA.eigenvalues
  let q : Fin (d + 1) → (Fin (d + 1) → ℝ) := fun i => (B i).ofLp
  let alpha : Fin (d + 1) → ℝ := fun i => q i ⬝ᵥ g
  let beta : Fin (d + 1) → ℝ := fun i => if lam i = 0 then 0 else alpha i / lam i
  let b : Fin (d + 1) → ℝ := ∑ i : Fin (d + 1), beta i • q i
  have hqeig (i : Fin (d + 1)) : A *ᵥ q i = lam i • q i := by
    simpa [q, lam, B] using hA.mulVec_eigenvectorBasis i
  have hlam (i : Fin (d + 1)) : 0 ≤ lam i := hpsd.eigenvalues_nonneg i
  have hquad (i : Fin (d + 1)) :
      q i ⬝ᵥ (A *ᵥ q i) = (P *ᵥ q i) ⬝ᵥ (P *ᵥ q i) := by
    simpa [A] using gram_quadratic P (q i)
  have hzeroP (i : Fin (d + 1)) (hi : lam i = 0) : P *ᵥ q i = 0 := by
    have h0 : q i ⬝ᵥ (A *ᵥ q i) = 0 := by rw [hqeig i, hi]; simp
    have h1 : (P *ᵥ q i) ⬝ᵥ (P *ᵥ q i) = 0 := by rw [← hquad i, h0]
    exact (dotProduct_self_eq_zero).mp h1
  have halpha0 (i : Fin (d + 1)) (hi : lam i = 0) : alpha i = 0 := by
    change q i ⬝ᵥ Pᵀ *ᵥ z.2 = 0
    rw [gram_rhs_dot]
    simp [hzeroP i hi]
  have hgexp : g = ∑ i : Fin (d + 1), alpha i • q i := by
    let w : EuclideanSpace ℝ (Fin (d + 1)) := WithLp.toLp 2 g
    have hs := OrthonormalBasis.sum_repr_symm B (B.repr w)
    have heq : B.repr.symm (B.repr w) = w := B.repr.symm_apply_apply w
    have hc (i : Fin (d + 1)) : (B.repr w).ofLp i = alpha i := by
      change (B.repr w).ofLp i = (B i).ofLp ⬝ᵥ (Pᵀ *ᵥ z.2)
      rw [OrthonormalBasis.repr_apply_apply]
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, q, g, w]
    have hvec := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) => v.ofLp) hs
    rw [heq] at hvec
    funext k
    have hk := congrFun hvec k
    simpa [WithLp.ofLp_toLp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, q] using hk.symm
  have hAb : A *ᵥ b = g := by
    change A *ᵥ (∑ i : Fin (d + 1), beta i • q i) = g
    rw [Matrix.mulVec_sum]
    calc
      (∑ i : Fin (d + 1), A *ᵥ (beta i • q i)) =
          ∑ i : Fin (d + 1), alpha i • q i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Matrix.mulVec_smul, hqeig i]
        by_cases hz : lam i = 0
        · simp [beta, hz, halpha0 i hz]
        · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hz)
          simp only [beta, if_neg hz]
          rw [smul_smul]
          have hd : lam i ≠ 0 := ne_of_gt hpos
          have hs : alpha i / lam i * lam i = alpha i := div_mul_cancel₀ _ hd
          simp [hs]
      _ = g := hgexp.symm
  have hbnormal : A *ᵥ b = g := hAb
  let eps : ℕ → ℝ := fun r => 1 / ((r : ℝ) + 1)
  have hepspos (r : ℕ) : 0 < eps r := by
    dsimp [eps]
    positivity
  have hepslim : Tendsto eps atTop (nhds 0) := by
    simpa [eps] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let M (r : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := A + eps r • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
  have hMpos (r : ℕ) : (M r).PosDef := by
    dsimp [M]
    exact Matrix.PosDef.posSemidef_add hpsd
      (Matrix.PosDef.smul (Matrix.PosDef.one) (hepspos r))
  have hMunit (r : ℕ) : IsUnit (M r).det := by
    apply isUnit_iff_ne_zero.mpr
    exact ne_of_gt (Matrix.PosDef.det_pos (hMpos r))
  have hwr (r : ℕ) : ridgeCoefficient n d r z =
      ∑ i : Fin (d + 1), (alpha i / (lam i + eps r)) • q i := by
    let v : Fin (d + 1) → ℝ := ∑ i : Fin (d + 1),
        (alpha i / (lam i + eps r)) • q i
    have hMv : M r *ᵥ v = g := by
      change (A + eps r • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) *ᵥ
        (∑ i : Fin (d + 1), (alpha i / (lam i + eps r)) • q i) = g
      rw [Matrix.add_mulVec, Matrix.mulVec_sum]
      calc
        (∑ i : Fin (d + 1), A *ᵥ ((alpha i / (lam i + eps r)) • q i)) +
            (eps r • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) *ᵥ
              (∑ i : Fin (d + 1), (alpha i / (lam i + eps r)) • q i) =
            ∑ i : Fin (d + 1), alpha i • q i := by
          simp_rw [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.smul_mulVec,
            Matrix.one_mulVec, hqeig, smul_smul]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          have hden : lam i + eps r ≠ 0 :=
            ne_of_gt (add_pos_of_nonneg_of_pos (hlam i) (hepspos r))
          rw [← add_smul]
          congr 1
          calc
            (alpha i / (lam i + eps r)) * lam i +
                (alpha i / (lam i + eps r)) * eps r =
                (alpha i / (lam i + eps r)) * (lam i + eps r) := by ring
            _ = alpha i := div_mul_cancel₀ _ hden
        _ = g := hgexp.symm
    have hinv : (M r)⁻¹ *ᵥ g = v := by
      calc
        (M r)⁻¹ *ᵥ g = (M r)⁻¹ *ᵥ ((M r) *ᵥ v) := by rw [hMv]
        _ = ((M r)⁻¹ * M r) *ᵥ v := by rw [← Matrix.mulVec_mulVec]
        _ = v := by rw [Matrix.nonsing_inv_mul (M r) (hMunit r), Matrix.one_mulVec]
    simpa [ridgeCoefficient, P, A, g, M, eps, v] using hinv
  have hcoef (i : Fin (d + 1)) :
      Tendsto (fun r : ℕ => alpha i / (lam i + eps r)) atTop (nhds (beta i)) := by
    by_cases hz : lam i = 0
    · have hiden : (fun r : ℕ => alpha i / (lam i + eps r)) = fun _ => (0 : ℝ) := by
        funext r
        simp [halpha0 i hz, hz]
      rw [hiden]
      simp [beta, hz]
    · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hz)
      have hden : Tendsto (fun r : ℕ => lam i + eps r) atTop (nhds (lam i + 0)) :=
        tendsto_const_nhds.add hepslim
      have hdiv := (tendsto_const_nhds (x := alpha i)).div hden (by linarith)
      have hdiv' : Tendsto (fun r : ℕ => alpha i / (lam i + eps r)) atTop
          (nhds (alpha i / lam i)) := by
        have hfun : (fun r : ℕ => alpha i / (lam i + eps r)) =
            (fun _ : ℕ => alpha i) / (fun r : ℕ => lam i + eps r) := by
          funext r
          rfl
        rw [hfun]
        simpa only [add_zero] using hdiv
      simpa [beta, hz] using hdiv'
  let bLim : Fin (d + 1) → ℝ := b
  have hlim : Tendsto (fun r : ℕ => ridgeCoefficient n d r z) atTop (nhds bLim) := by
    apply tendsto_pi_nhds.2
    intro k
    rw [show bLim k = ∑ i : Fin (d + 1), beta i * q i k by
      simp [bLim, b, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    have hs := tendsto_finset_sum_real
      (fun i r => (alpha i / (lam i + eps r)) * q i k)
      (fun i => beta i * q i k)
      (fun i => (hcoef i).mul_const (q i k))
    simpa [hwr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs
  have hbmin (c : Fin (d + 1) → ℝ) :
      (∑ i : Fin n, (z.2 i - (coefficientPolynomialW3 bLim).eval (z.1 i)) ^ 2) ≤
        ∑ i : Fin n, (z.2 i - (coefficientPolynomialW3 c).eval (z.1 i)) ^ 2 := by
    let r : Fin n → ℝ := z.2 - P *ᵥ bLim
    let u : Fin n → ℝ := P *ᵥ (c - bLim)
    have hnormal : Pᵀ *ᵥ r = 0 := by
      dsimp [r, bLim]
      rw [Matrix.mulVec_sub]
      have hcomp : Pᵀ *ᵥ (P *ᵥ b) = (Pᵀ * P) *ᵥ b :=
        Matrix.mulVec_mulVec b Pᵀ P
      rw [hcomp]
      change g - A *ᵥ b = 0
      rw [hbnormal]
      simp
    have hcross : r ⬝ᵥ u = 0 := by
      dsimp [u]
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hnormal]
      simp
    have hpoly (v : Fin (d + 1) → ℝ) (i : Fin n) :
        (coefficientPolynomialW3 v).eval (z.1 i) = (P *ᵥ v) i := by
      simpa [P] using coefficient_eval_eq_vand_mulVec d z.1 v i
    have hresb : ∀ i, z.2 i - (coefficientPolynomialW3 bLim).eval (z.1 i) = r i := by
      intro i
      rw [hpoly bLim i]
      rfl
    have hresc : ∀ i, z.2 i - (coefficientPolynomialW3 c).eval (z.1 i) = r i - u i := by
      intro i
      rw [hpoly c i]
      dsimp [r, u]
      rw [Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      ring
    have hsumB :
        (∑ i : Fin n, (z.2 i - (coefficientPolynomialW3 bLim).eval (z.1 i)) ^ 2) =
          ∑ i : Fin n, (r i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hresb i]
    have hsumC :
        (∑ i : Fin n, (z.2 i - (coefficientPolynomialW3 c).eval (z.1 i)) ^ 2) =
          ∑ i : Fin n, (r i - u i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hresc i]
    rw [hsumB, hsumC]
    have hsquare : (∑ i : Fin n, (r i - u i) ^ 2) =
        (∑ i : Fin n, (r i) ^ 2) + ∑ i : Fin n, (u i) ^ 2 := by
      calc
        _ = ∑ i : Fin n, ((r i) ^ 2 + (u i) ^ 2 - 2 * (r i * u i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i : Fin n, (r i) ^ 2) + ∑ i : Fin n, (u i) ^ 2 -
              2 * (∑ i : Fin n, r i * u i) := by
          simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ i : Fin n, (r i) ^ 2) + ∑ i : Fin n, (u i) ^ 2 := by
          rw [← dotProduct, hcross]
          ring
    rw [hsquare]
    have hnonneg : 0 ≤ ∑ i : Fin n, (u i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (u i)
    linarith
  exact ⟨bLim, hlim, hbmin⟩
