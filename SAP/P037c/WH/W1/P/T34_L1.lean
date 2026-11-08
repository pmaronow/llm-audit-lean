import SAP.P037c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.WH.W1.P.T34_L1

open scoped BigOperators
attribute [local instance] Classical.propDecidable

private def objective {n p : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (w y : Fin n → ℝ) (a : Fin p → ℝ) : ℝ :=
  ∑ i, w i * (y i - H.mulVec a i)^2

private theorem midpoint_identity {n p : ℕ}
    (H : Matrix (Fin n) (Fin p) ℝ) (w y : Fin n → ℝ)
    (a b : Fin p → ℝ) :
    objective H w y a + objective H w y b -
      2 * objective H w y (fun j => (a j + b j) / 2) =
      (∑ i, w i * (H.mulVec a i - H.mulVec b i)^2) / 2 := by
  let c : Fin p → ℝ := fun j => (a j + b j) / 2
  have hc : c = (1 / 2 : ℝ) • (a + b) := by
    funext j
    simp [c, Pi.add_apply]
    ring
  have hpred (i : Fin n) :
      H.mulVec c i = (H.mulVec a i + H.mulVec b i) / 2 := by
    have h := congrFun (congrArg (fun v : Fin p → ℝ => H.mulVec v) hc) i
    rw [Matrix.mulVec_smul, Matrix.mulVec_add] at h
    change H.mulVec c i =
      (1 / 2 : ℝ) • (H.mulVec a i + H.mulVec b i) at h
    calc
      H.mulVec c i = (1 / 2 : ℝ) • (H.mulVec a i + H.mulVec b i) := h
      _ = (H.mulVec a i + H.mulVec b i) / 2 := by
        simp only [smul_eq_mul]
        ring
  dsimp [objective]
  calc
    _ = ∑ i, (w i * (y i - H.mulVec a i)^2 +
        w i * (y i - H.mulVec b i)^2 -
        2 * (w i * (y i - H.mulVec c i)^2)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ i, (w i * (H.mulVec a i - H.mulVec b i)^2 / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpred i]
      ring
    _ = (∑ i, w i * (H.mulVec a i - H.mulVec b i)^2) / 2 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end SAP.P037c.WH.W1.P.T34_L1

theorem SAP.P037c.WH.W1.T34_L1_proof : SAP.P037c.WH.W1.T34_L1 := by
  classical
  intro n p H w y hw a b ha hb
  let c : Fin p → ℝ := fun j => (a j + b j) / 2
  have hamin :
      SAP.P037c.WH.W1.P.T34_L1.objective H w y a ≤
        SAP.P037c.WH.W1.P.T34_L1.objective H w y c := by
    simpa [SAP.P037c.WH.W1.P.T34_L1.objective, c] using ha c
  have hbmin :
      SAP.P037c.WH.W1.P.T34_L1.objective H w y b ≤
        SAP.P037c.WH.W1.P.T34_L1.objective H w y c := by
    simpa [SAP.P037c.WH.W1.P.T34_L1.objective, c] using hb c
  have hnonneg :
      0 ≤ ∑ i, w i * (H.mulVec a i - H.mulVec b i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hw i)) (sq_nonneg _)
  have hzero : ∑ i, w i * (H.mulVec a i - H.mulVec b i)^2 = 0 := by
    have hid := SAP.P037c.WH.W1.P.T34_L1.midpoint_identity H w y a b
    have hle :
        SAP.P037c.WH.W1.P.T34_L1.objective H w y a +
            SAP.P037c.WH.W1.P.T34_L1.objective H w y b -
          2 * SAP.P037c.WH.W1.P.T34_L1.objective H w y c ≤ 0 := by
      dsimp [c]
      linarith
    dsimp [c] at hle
    nlinarith [hid, hle, hnonneg]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (le_of_lt (hw i))
        (sq_nonneg (H.mulVec a i - H.mulVec b i)))).mp hzero
  funext i
  have hterm := hterms i (Finset.mem_univ i)
  have hsq : (H.mulVec a i - H.mulVec b i)^2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
