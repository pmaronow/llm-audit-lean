import AronowAudit.P015.P015_OLSCompletion
namespace AronowAudit.P015.PopulationMomentCompletion
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]

lemma linear_mul_integrable (P : Measure Ω) (V : Ω → Q → ℝ) (a : Q → ℝ)
    (Z : Ω → ℝ) (hi : ∀ j, Integrable (fun s => V s j * Z s) P) :
    Integrable (fun s => dotProduct (V s) a * Z s) P := by
  have h := integrable_finsetSum (s := Finset.univ) (fun j _ => (hi j).const_mul (a j))
  convert h using 1
  ext s
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma integral_linear_mul (P : Measure Ω) (V : Ω → Q → ℝ) (a : Q → ℝ)
    (Z : Ω → ℝ) (hi : ∀ j, Integrable (fun s => V s j * Z s) P) :
    (∫ s, dotProduct (V s) a * Z s ∂P) =
      dotProduct a (fun j => ∫ s, V s j * Z s ∂P) := by
  have he : (fun s => dotProduct (V s) a * Z s) =
      fun s => ∑ j, a j * (V s j * Z s) := by
    funext s
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul (a j))]
  simp [dotProduct, integral_const_mul]

lemma linear_product_integrable (P : Measure Ω) (V : Ω → Q → ℝ) (a : Q → ℝ)
    (Z : Ω → ℝ) (hi : ∀ j k, Integrable (fun s => V s j * V s k * Z s) P) :
    Integrable (fun s => dotProduct (V s) a * dotProduct (V s) a * Z s) P := by
  apply (linear_mul_integrable P V a (fun s => dotProduct (V s) a * Z s) ?_).congr
  · filter_upwards [] with s
    ring
  intro j
  have h := linear_mul_integrable P V a (fun s => V s j * Z s) (fun k =>
    (hi j k).congr (Eventually.of_forall (fun s => by ring)))
  exact h.congr (Eventually.of_forall (fun s => by ring))

lemma integral_linear_product (P : Measure Ω) (V : Ω → Q → ℝ) (a : Q → ℝ)
    (Z : Ω → ℝ) (hi : ∀ j k, Integrable (fun s => V s j * V s k * Z s) P) :
    (∫ s, dotProduct (V s) a * dotProduct (V s) a * Z s ∂P) =
      ∑ j, ∑ k, a j * a k * (∫ s, V s j * V s k * Z s ∂P) := by
  have hlin : ∀ j, Integrable (fun s => V s j * (dotProduct (V s) a * Z s)) P := by
    intro j
    exact (linear_mul_integrable P V a (fun s => V s j * Z s) (fun k =>
      (hi j k).congr (Eventually.of_forall (fun s => by ring)))).congr
        (Eventually.of_forall (fun s => by ring))
  calc
    _ = ∫ s, dotProduct (V s) a * (dotProduct (V s) a * Z s) ∂P := by
      congr 1; funext s; ring
    _ = ∑ j, a j * (∫ s, V s j * (dotProduct (V s) a * Z s) ∂P) :=
      integral_linear_mul P V a _ hlin
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have he : (fun s => V s j * (dotProduct (V s) a * Z s)) =
          fun s => dotProduct (V s) a * (V s j * Z s) := by funext s; ring
      rw [he, integral_linear_mul P V a _ (fun k =>
        (hi j k).congr (Eventually.of_forall (fun s => by ring)))]
      simp only [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show (fun s => V s k * (V s j * Z s)) = (fun s => V s j * V s k * Z s) by
        funext s; ring]
      ring


lemma integral_residual_sq (P : Measure Ω) (V : Ω → Q → ℝ) (a : Q → ℝ)
    (D Z : Ω → ℝ) (hd : Integrable (fun s => D s^2 * Z s) P)
    (hv : ∀ j, Integrable (fun s => V s j * D s * Z s) P)
    (hvv : ∀ j k, Integrable (fun s => V s j * V s k * Z s) P) :
    (∫ s, (D s - dotProduct (V s) a)^2 * Z s ∂P) =
      (∫ s, D s^2 * Z s ∂P) -
        2 * dotProduct a (fun j => ∫ s, V s j * D s * Z s ∂P) +
        ∑ j, ∑ k, a j * a k * (∫ s, V s j * V s k * Z s ∂P) := by
  have hvi : ∀ j, Integrable (fun s => V s j * (D s * Z s)) P := fun j =>
    (hv j).congr (Eventually.of_forall (fun s => by ring))
  have hm := linear_mul_integrable P V a (fun s => D s * Z s) hvi
  have hmm := linear_product_integrable P V a Z hvv
  have he : (fun s => (D s - dotProduct (V s) a)^2 * Z s) =
      fun s => (D s^2 * Z s - 2 * (dotProduct (V s) a * (D s * Z s))) +
        dotProduct (V s) a * dotProduct (V s) a * Z s := by
    funext s; ring
  have hsplit := integral_add (hd.sub (hm.const_mul 2)) hmm
  change (∫ s, D s^2 * Z s - 2 * (dotProduct (V s) a * (D s * Z s)) +
      dotProduct (V s) a * dotProduct (V s) a * Z s ∂P) =
    (∫ s, D s^2 * Z s - 2 * (dotProduct (V s) a * (D s * Z s)) ∂P) +
    (∫ s, dotProduct (V s) a * dotProduct (V s) a * Z s ∂P) at hsplit
  have hsub := integral_sub hd (hm.const_mul 2)
  change (∫ s, D s^2 * Z s - 2 * (dotProduct (V s) a * (D s * Z s)) ∂P) = _ at hsub
  rw [he, hsplit, hsub, integral_const_mul,
    integral_linear_mul P V a _ hvi, integral_linear_product P V a Z hvv]
  simp only [mul_assoc]


lemma ols_reindex {N R : Type*} [Fintype N] [Fintype R] [DecidableEq Q] [DecidableEq R]
    (W : Matrix N Q ℝ) (Y : N → ℝ) (e : R ≃ Q) :
    ols (W.submatrix id e) Y = (ols W Y) ∘ e := by
  have hG : (W.submatrix id e).transpose * W.submatrix id e =
      (W.transpose * W).submatrix e e := by
    ext j k
    rfl
  have hb : (W.submatrix id e).transpose.mulVec Y = W.transpose.mulVec Y ∘ e := by
    ext j
    rfl
  simp only [ols, hG, hb, Matrix.inv_submatrix_equiv]
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using
    Matrix.submatrix_mulVec_equiv ((W.transpose * W)⁻¹) (W.transpose.mulVec Y ∘ e) e e

end
end AronowAudit.P015.PopulationMomentCompletion
