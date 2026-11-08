import SAP.P001a.WH.W1.Leaves
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Polynomial InnerProductSpace
open scoped BigOperators

noncomputable section

universe u

namespace SAP.P001a.WH.W1.P.T6_L1

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Evaluation on a finite design, with the Euclidean norm on fitted values. -/
def sampleEval {n : ℕ} (x : Fin n → ℝ) :
    Polynomial ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun p := WithLp.toLp 2 (fun i => p.eval (x i))
  map_add' p q := by ext i; simp
  map_smul' a p := by ext i; simp

@[simp] lemma sampleEval_apply {n : ℕ} (x : Fin n → ℝ) (p : Polynomial ℝ)
    (i : Fin n) : sampleEval x p i = p.eval (x i) := rfl

def columns {n d : ℕ} (x : Fin n → ℝ) (k : Fin (d + 1)) :
    EuclideanSpace ℝ (Fin n) := sampleEval x (Polynomial.X ^ (k : ℕ))

def weight {n d : ℕ} (x : Fin n → ℝ) (i j : Fin (d + 1)) : ℝ :=
  ⟪gramSchmidt ℝ (columns x) i, columns x j⟫ /
    ‖gramSchmidt ℝ (columns x) i‖ ^ 2

/-- Lift Gram--Schmidt to polynomials, retaining a representative even when a
column is dependent. Division by zero contributes a zero projection. -/
def orthPoly {n d : ℕ} (x : Fin n → ℝ) (k : Fin (d + 1)) : Polynomial ℝ :=
  Polynomial.X ^ (k : ℕ) -
    ∑ i : Finset.Iio k, weight x (i : Fin (d + 1)) k • orthPoly x (i : Fin (d + 1))
termination_by k.val
decreasing_by exact (Finset.mem_Iio.mp i.property : (i : Fin (d + 1)) < k)

lemma orthPoly_def {n d : ℕ} (x : Fin n → ℝ) (k : Fin (d + 1)) :
    orthPoly x k = Polynomial.X ^ (k : ℕ) -
      ∑ i ∈ Finset.Iio k, weight x i k • orthPoly x i := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, orthPoly]

lemma sampleEval_orthPoly {n d : ℕ} (x : Fin n → ℝ) (k : Fin (d + 1)) :
    sampleEval x (orthPoly x k) = gramSchmidt ℝ (columns x) k := by
  apply wellFounded_lt.induction k
  intro k ih
  rw [orthPoly_def, map_sub, map_sum]
  simp only [map_smul]
  rw [gramSchmidt_def]
  simp only [Submodule.starProjection_singleton]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [ih i (Finset.mem_Iio.mp hi)]
  rfl

lemma orthPoly_degree {n d : ℕ} (x : Fin n → ℝ) (k : Fin (d + 1)) :
    (orthPoly x k).natDegree ≤ (k : ℕ) := by
  apply wellFounded_lt.induction k
  intro k ih
  rw [orthPoly_def]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_smul_le _ _).trans
      ((ih i (Finset.mem_Iio.mp hi)).trans (Finset.mem_Iio.mp hi).le)

lemma measurable_gs {Ω : Type u} [MeasurableSpace Ω] {n d : ℕ}
    (v : Fin (d + 1) → Ω → EuclideanSpace ℝ (Fin n))
    (hv : ∀ k, Measurable (v k)) (k : Fin (d + 1)) :
    Measurable (fun ω => gramSchmidt ℝ (fun j => v j ω) k) := by
  apply wellFounded_lt.induction k
  intro k ih
  conv =>
    arg 1
    ext ω
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
  apply (hv k).sub
  apply Finset.measurable_sum
  intro i hi
  have hm := ih i (Finset.mem_Iio.mp hi)
  exact ((hm.inner (hv k)).div (hm.norm.pow_const 2)).smul hm

lemma measurable_columns {Ω : Type u} [MeasurableSpace Ω] {n d : ℕ}
    (x : Ω → Fin n → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (k : Fin (d + 1)) : Measurable (fun ω => columns (x ω) k) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  simpa [columns, sampleEval] using (hx i).pow_const (k : ℕ)

lemma measurable_weight {Ω : Type u} [MeasurableSpace Ω] {n d : ℕ}
    (x : Ω → Fin n → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (i j : Fin (d + 1)) : Measurable (fun ω => weight (x ω) i j) := by
  have hg := measurable_gs (fun k ω => columns (x ω) k) (measurable_columns x hx) i
  exact (hg.inner (measurable_columns x hx j)).div (hg.norm.pow_const 2)

lemma measurable_orthPoly_coeff {Ω : Type u} [MeasurableSpace Ω] {n d : ℕ}
    (x : Ω → Fin n → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (k : Fin (d + 1)) (l : ℕ) :
    Measurable (fun ω => (orthPoly (x ω) k).coeff l) := by
  apply wellFounded_lt.induction k
  intro k ih
  conv =>
    arg 1
    ext ω
    rw [orthPoly_def]
    simp only [Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
      Polynomial.coeff_smul, smul_eq_mul]
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_weight x hx i k).mul (ih i (Finset.mem_Iio.mp hi))

/-- The explicit projection formula is valid for orthogonal families with zero
members as well as for linearly independent families. -/
def gsFit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (v : Fin (d + 1) → E) (y : E) : E :=
  ∑ k, (⟪gramSchmidt ℝ v k, y⟫ / ‖gramSchmidt ℝ v k‖ ^ 2) • gramSchmidt ℝ v k

lemma gsFit_residual {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (v : Fin (d + 1) → E) (y : E) (k : Fin (d + 1)) :
    ⟪gramSchmidt ℝ v k, y - gsFit v y⟫ = 0 := by
  classical
  unfold gsFit
  rw [inner_sub_right, inner_sum]
  simp only [inner_smul_right]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => by
    rw [gramSchmidt_orthogonal ℝ v hik.symm, mul_zero])]
  by_cases hk : gramSchmidt ℝ v k = 0
  · simp [hk]
  · rw [real_inner_self_eq_norm_sq, div_mul_cancel₀, sub_self]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hk)

lemma gsFit_residual_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (v : Fin (d + 1) → E) (y w : E)
    (hw : w ∈ Submodule.span ℝ (Set.range v)) :
    ⟪y - gsFit v y, w⟫ = 0 := by
  rw [← span_gramSchmidt ℝ v] at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    rw [real_inner_comm]
    exact gsFit_residual v y k
  | zero => simp
  | add a b _ _ ha hb => simp [inner_add_right, ha, hb]
  | smul a b _ hb => simp [inner_smul_right, hb]

lemma gsFit_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (v : Fin (d + 1) → E) (y : E) :
    gsFit v y ∈ Submodule.span ℝ (Set.range v) := by
  rw [← span_gramSchmidt ℝ v]
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

lemma gsFit_minimizes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (v : Fin (d + 1) → E) (y w : E)
    (hw : w ∈ Submodule.span ℝ (Set.range v)) :
    ‖y - gsFit v y‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by
  have h := gsFit_residual_span v y (w - gsFit v y)
    (Submodule.sub_mem _ hw (gsFit_mem_span v y))
  have hp := norm_sub_sq_eq_norm_sq_add_norm_sq_real h
  rw [sub_sub_sub_cancel_right] at hp
  nlinarith [sq_nonneg ‖w - gsFit v y‖]

/-- Coefficients of the least-squares polynomial, lifted from the projection. -/
def fitPoly {n : ℕ} (d : ℕ) (x y : Fin n → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (d + 1),
    (⟪gramSchmidt ℝ (columns x) k, WithLp.toLp 2 y⟫ /
      ‖gramSchmidt ℝ (columns x) k‖ ^ 2) • orthPoly x k

lemma sampleEval_fitPoly {n : ℕ} (d : ℕ) (x y : Fin n → ℝ) :
    sampleEval x (fitPoly d x y) = gsFit (columns (d := d) x) (WithLp.toLp 2 y) := by
  simp only [fitPoly, map_sum, map_smul, sampleEval_orthPoly, gsFit]

lemma fitPoly_degree {n : ℕ} (d : ℕ) (x y : Fin n → ℝ) :
    (fitPoly d x y).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((orthPoly_degree x k).trans (Nat.le_of_lt_succ k.isLt))

lemma sampleEval_mem_span {n d : ℕ} (x : Fin n → ℝ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ d) :
    sampleEval x p ∈ Submodule.span ℝ (Set.range (columns (d := d) x)) := by
  have he : p = ∑ k : Fin (d + 1), (p.coeff (k : ℕ)) • Polynomial.X ^ (k : ℕ) := by
    simpa only [Finset.sum_range, Nat.succ_eq_add_one, Polynomial.smul_eq_C_mul] using
      p.as_sum_range_C_mul_X_pow' (lt_of_le_of_lt hp (Nat.lt_succ_self _))
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro k _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

lemma sample_loss_eq {n : ℕ} (x y : Fin n → ℝ) (p : Polynomial ℝ) :
    ‖WithLp.toLp 2 y - sampleEval x p‖ ^ 2 =
      ∑ i : Fin n, (y i - p.eval (x i)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma fitPoly_minimizes {n : ℕ} (d : ℕ) (x y : Fin n → ℝ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d) :
    (∑ i : Fin n, (y i - (fitPoly d x y).eval (x i)) ^ 2) ≤
      ∑ i : Fin n, (y i - p.eval (x i)) ^ 2 := by
  rw [← sample_loss_eq, ← sample_loss_eq, sampleEval_fitPoly]
  exact gsFit_minimizes (columns x) (WithLp.toLp 2 y) (sampleEval x p)
    (sampleEval_mem_span x p hp)

lemma measurable_fitPoly_coeff {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (d : ℕ) (x y : Ω → Fin n → ℝ)
    (hx : ∀ i, Measurable (fun ω => x ω i))
    (hy : ∀ i, Measurable (fun ω => y ω i)) (l : ℕ) :
    Measurable (fun ω => (fitPoly d (x ω) (y ω)).coeff l) := by
  have hym : Measurable (fun ω => WithLp.toLp 2 (y ω)) :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (Measurable.of_eval hy)
  simp only [fitPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul]
  apply Finset.measurable_sum
  intro k _
  have hg := measurable_gs (fun k ω => columns (x ω) k) (measurable_columns x hx) k
  exact ((hg.inner hym).div (hg.norm.pow_const 2)).mul (measurable_orthPoly_coeff x hx k l)

end SAP.P001a.WH.W1.P.T6_L1

theorem SAP.P001a.WH.W1.T6_L1_proof : SAP.P001a.WH.W1.T6_L1 := by
  intro Ω _ X Y hm J
  let fit : ℕ → Ω → Polynomial ℝ := fun n ω =>
    SAP.P001a.WH.W1.P.T6_L1.fitPoly (J n)
      (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω)
  refine ⟨fit, ?_, ?_⟩
  · intro n ω
    refine ⟨SAP.P001a.WH.W1.P.T6_L1.fitPoly_degree (J n) _ _, ?_⟩
    intro p hp
    have h := SAP.P001a.WH.W1.P.T6_L1.fitPoly_minimizes (J n)
      (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) p hp
    change (∑ i : Fin n, (Y i ω - (fit n ω).eval (X i ω)) ^ 2) ≤
      ∑ i : Fin n, (Y i ω - p.eval (X i ω)) ^ 2 at h
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (Y i ω - (fit n ω).eval (X i ω)) ^ 2) n,
      Fin.sum_univ_eq_sum_range (fun i => (Y i ω - p.eval (X i ω)) ^ 2) n] at h
    exact h
  · intro n k
    exact SAP.P001a.WH.W1.P.T6_L1.measurable_fitPoly_coeff (J n)
      (fun ω (i : Fin n) => X i ω) (fun ω (i : Fin n) => Y i ω)
      (fun i => (hm i).1) (fun i => (hm i).2) k
