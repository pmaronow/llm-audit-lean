import AronowAudit.P011.P011_CorrectedAsymptoticCompletion
import AronowAudit.P011.P011_SpectralCompletion
import AronowAudit.P011.P011_DataMatrixCompletion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Order.Lattice

/-!
Draft dd-GP011B2. No Lean process was run.

Record 12: the bounded deterministic comparison and the tail-transfer reduction
are below. The sorted-cap finite witness is still needed; consequently the exact
final theorem `degree_only_conservative_proof` is not declared here.
Record 14: complete proposed proof and exact-type check.
Record 15: measurable-value and case-assembly reductions are below. The same
record-12 dependency remains; the exact final theorem is not declared here.
See the assigned run report for the precise remaining obligation.
-/

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

/-! Record 12: bounded comparison without bounding the original supplied caps. -/

def degree_only_comparisonCaps {n : ℕ} (d : Fin n → ℕ) (D : ℕ) : Fin n → ℕ :=
  fun i => min (truncatedDegree d i) D

lemma degree_only_comparisonCaps_truncated {n : ℕ} (d : Fin n → ℕ) (D : ℕ) :
    truncatedDegree (degree_only_comparisonCaps d D) = degree_only_comparisonCaps d D := by
  funext i
  exact min_eq_left ((min_le_left _ _).trans (min_le_right (d i) (n - 1)))

lemma degree_only_comparisonCaps_valid {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (D : ℕ) (hv : Compatible R d G) (hD : ∀ i, degree G i ≤ D) :
    ∀ i, degree G i ≤ degree_only_comparisonCaps d D i := by
  intro i
  exact le_min (compatible_truncated_degree R G d hv i) (hD i)

lemma degree_only_comparison_psd {n : ℕ} (G : Graph n) (c : Fin n → ℕ)
    (hc : ∀ i, degree G i ≤ c i) :
    PSD (1 + Matrix.diagonal (fun i => (c i : ℝ))) ∧
    PSD ((1 + Matrix.diagonal (fun i => (c i : ℝ))) - oracleMatrix G) := by
  have hi : PSD (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have he : (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ => 1) := by
      ext i j
      simp [Matrix.one_apply, Matrix.diagonal_apply]
    rw [he]
    exact psd_diagonal _ (fun _ => by norm_num)
  have hd : PSD (Matrix.diagonal (fun i => (c i : ℝ) - (degree G i : ℝ))) := by
    apply psd_diagonal
    intro i
    exact sub_nonneg.mpr (by exact_mod_cast hc i)
  refine ⟨psd_add _ _ hi (psd_diagonal _ (fun _ => Nat.cast_nonneg _)), ?_⟩
  have he : (1 + Matrix.diagonal (fun i => (c i : ℝ))) - oracleMatrix G =
      Matrix.diagonal (fun i => (c i : ℝ) - (degree G i : ℝ)) +
        (Matrix.diagonal (fun i => (degree G i : ℝ)) - adjacency G) := by
    ext i j
    simp only [oracleMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [he]
  exact psd_add _ _ hd (graph_laplacian_psd G)

lemma degree_only_comparison_norm {n : ℕ} (c : Fin n → ℕ) (D : ℕ)
    (hc : ∀ i, c i ≤ D) :
    operatorNorm (1 + Matrix.diagonal (fun i => (c i : ℝ))) ≤ 1 + (D : ℝ) := by
  let M : Matrix (Fin n) (Fin n) ℝ := 1 + Matrix.diagonal (fun i => (c i : ℝ))
  have he (i j : Fin n) : M i j = if i = j then 1 + (c i : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      simp [M, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]
    · simp [M, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply, hij]
  apply SchurSupport.operatorNorm_le_abs_row_sum M
  · intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp [he, hij, Ne.symm hij]
  · positivity
  · intro i
    simp_rw [he i]
    simp only [abs_ite, abs_of_nonneg (show 0 ≤ 1 + (c i : ℝ) by positivity),
      abs_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hi : (c i : ℝ) ≤ D := by exact_mod_cast hc i
    linarith

lemma degree_only_comparison_form {n : ℕ} (c : Fin n → ℕ)
    (hc : ∀ i, c i ≤ n - 1) (x : Fin n → ℝ) :
    varianceForm (1 + Matrix.diagonal (fun i => (c i : ℝ))) x = VYoung c x := by
  have hi : (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ => 1) := by
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  have ht (i : Fin n) : truncatedDegree c i = c i := min_eq_left (hc i)
  unfold varianceForm VYoung
  rw [quadratic_add, hi, quadratic_diagonal, quadratic_diagonal]
  simp only [ht, one_mul, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma degree_only_capped_young_conservative (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F) :
    Conservative F (fun k y =>
      VYoung (degree_only_comparisonCaps (F.model k).d ⌈c2⌉₊)
        (weighted (F.model k) y)) := by
  let D : ℕ := ⌈c2⌉₊
  let c := fun k => degree_only_comparisonCaps (F.model k).d D
  let M := fun k => (1 : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ) +
    Matrix.diagonal (fun i => (c k i : ℝ))
  have hdeg (k : ℕ) (i : Fin (F.size k)) : degree (F.model k).G i ≤ D := by
    have hh : (degree (F.model k).G i : ℝ) ≤ (D : ℝ) :=
      (h.2.2.2.2.2.2.2.1 k i).trans (Nat.le_ceil c2)
    exact_mod_cast hh
  have hc (k : ℕ) : ∀ i, degree (F.model k).G i ≤ c k i :=
    degree_only_comparisonCaps_valid _ _ _ D (hv k) (hdeg k)
  have hp (k : ℕ) : PSD (M k) ∧ PSD (M k - oracleMatrix (F.model k).G) :=
    degree_only_comparison_psd _ _ (hc k)
  have hnorm (k : ℕ) : operatorNorm (M k) ≤ 1 + (D : ℝ) :=
    degree_only_comparison_norm (c k) D (fun _ => min_le_right _ _)
  have hC := ((deterministic_quadratic_expansion F c1 c2 c3 c4 (1 + (D : ℝ))
    h M (fun k => (hp k).1.1) hnorm).2.2 hp).2
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      varianceForm (M k) (weighted (F.model k) y) =
        VYoung (c k) (weighted (F.model k) y) := by
    apply degree_only_comparison_form
    intro i
    exact (min_le_left _ _).trans (min_le_right _ _)
  simpa only [he, c, D] using hC

lemma degree_only_maxAbs_le {n : ℕ} (x : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ i, |x i| ≤ B) : maxAbs x ≤ B := by
  have hh : Finset.univ.sup (fun i => (⟨|x i|, abs_nonneg (x i)⟩ : ℝ≥0)) ≤
      (⟨B, hB⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    exact hx i
  exact hh

lemma degree_only_centered_bound (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (k : ℕ) :
    ∀ᵐ y ∂(F.model k).law, maxAbs (centered (weighted (F.model k) y)) ≤ 2 * c1 := by
  have hb := h.2.2.2.2.2.2.1 k
  have ha := HomoskedasticCompletion.beta_error_bound (F.positive k) (F.model k) c1 hb
  filter_upwards [hb, ha] with y hy hay
  apply degree_only_maxAbs_le _ _ (by linarith [h.2.1])
  intro i
  have he : centered (weighted (F.model k) y) i =
      (weighted (F.model k) y i - beta (F.model k)) -
        (betaHat (F.model k) y - beta (F.model k)) := by
    unfold centered betaHat
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hy i])

/-- Generic zero-error transfer; does not require the selector to be measurable. -/
lemma degree_only_tail_transfer (F : Family)
    (V W : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℕ → ℝ)
    (hV : Conservative F V) (ha : Tendsto a atTop (𝓝 0))
    (hVW : ∀ k, ∀ᵐ y ∂(F.model k).law,
      (F.size k : ℝ) * (V k y - W k y) ≤ a k) : Conservative F W := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  intro ε hε
  have he := ha.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (hV (ε / 2) (by linarith))
  filter_upwards [he] with k hk
  change (F.model k).law.real _ ≤ (F.model k).law.real _
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hVW k] with y hy
  intro hbad
  change ε < (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - W k y) at hbad
  change ε / 2 < (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y)
  nlinarith

/-- Reduction only, not the frozen node. The finite comparison premise is the
one unproved sorted-cap construction isolated by this draft. A Beam writer can
replace this premise by its independent combinatorial proof and then use this
lemma verbatim to finish record 12. -/
lemma degree_only_conservative_of_comparison (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (C : ℝ) (hC : 0 ≤ C)
    (hcompare : ∀ k y,
      (F.size k : ℝ) *
        (VYoung (degree_only_comparisonCaps (F.model k).d ⌈c2⌉₊)
          (weighted (F.model k) y) - V1 (A k y) (weighted (F.model k) y)) ≤
        C * maxAbs (centered (weighted (F.model k) y)) ^ 2 / (F.size k : ℝ)) :
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  apply degree_only_tail_transfer F _ _ (fun k => C * (2 * c1) ^ 2 / (F.size k : ℝ))
    (degree_only_capped_young_conservative F c1 c2 c3 c4 h hv)
    (hN.const_div_atTop _)
  intro k
  filter_upwards [degree_only_centered_bound F c1 c2 c3 c4 h k] with y hy
  apply (hcompare k y).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC
  exact (sq_le_sq₀ (show 0 ≤ maxAbs (centered (weighted (F.model k) y)) from
    NNReal.coe_nonneg _) (show 0 ≤ 2 * c1 by linarith [h.2.1])).mpr hy

/-- Finite maximization over Boolean adjacency functions; used only for the
comparison problem. Neither the original selector nor this choice is assumed
measurable. -/
lemma degree_only_exists_maximizer {n : ℕ} (R : Graph n) (d : Fin n → ℕ)
    (hfeasible : ∃ B, Compatible R d B) (f : Graph n → ℝ) :
    ∃ B, Maximizes R d f B := by
  classical
  let S : Finset (Graph n) := Finset.univ.filter (Compatible R d)
  obtain ⟨G, hG⟩ := hfeasible
  have hS : S.Nonempty := ⟨G, by simp [S, hG]⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image S f hS
  refine ⟨B, ?_, ?_⟩
  · simpa [S] using hB
  · intro C hC
    exact hmax C (by simp [S, hC])

lemma degree_only_empty_compatible {n : ℕ} (d : Fin n → ℕ) :
    Compatible (emptyGraph n) d (emptyGraph n) := by
  constructor
  · intro i j hij
    exact hij
  · intro i
    simp [degree, emptyGraph]

/-- Full reduction of record 12 to the independent finite theorem. The first
argument is a proof supplied by a future finite-comparison module; `type_of%`
reads only the held declaration's type, never its proof. This is deliberately
not named `degree_only_conservative_proof`, because that frozen node must not
acquire an extra hypothesis. -/
lemma degree_only_conservative_from_finite
    (hfinite : type_of% @AronowAudit.P011.degree_only_finite)
    (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F)
    (hr : ∀ k, (F.model k).R = emptyGraph (F.size k))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  let D : ℕ := ⌈c2⌉₊
  let c := fun k => degree_only_comparisonCaps (F.model k).d D
  let C : ℝ := ∑ r ∈ Finset.Icc 1 D, (3 * (r : ℝ) ^ 2 + 2 * r)
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro r _
    positivity
  apply degree_only_conservative_of_comparison F c1 c2 c3 c4 h hv A C hC
  intro k y
  let x := weighted (F.model k) y
  have hfeasible : ∃ B, Compatible (emptyGraph (F.size k)) (c k) B :=
    ⟨emptyGraph (F.size k), degree_only_empty_compatible _⟩
  obtain ⟨B, hB⟩ := degree_only_exists_maximizer (emptyGraph (F.size k)) (c k)
    hfeasible (fun B => V1 B x)
  obtain ⟨Bp, hBp⟩ := degree_only_exists_maximizer (emptyGraph (F.size k)) (c k)
    hfeasible (fun Bp => V1plus (c k) Bp x)
  have hd : ∀ i, truncatedDegree (c k) i ≤ D := by
    intro i
    rw [show truncatedDegree (c k) = c k from
      degree_only_comparisonCaps_truncated (F.model k).d D]
    exact min_le_right _ _
  have hf := @hfinite (F.size k) (F.positive k) (c k) D hd x B Bp hB hBp
  have hBoriginal : Compatible (F.model k).R (F.model k).d B := by
    constructor
    · intro i j hij
      rw [hr k] at hij
      simp [emptyGraph] at hij
    · intro i
      exact (hB.1.2 i).trans
        ((min_le_left _ _).trans (min_le_left _ _))
  have hmax : V1 B x ≤ V1 (A k y) x := (hm k y).2 B hBoriginal
  calc
    (F.size k : ℝ) * (VYoung (c k) x - V1 (A k y) x) ≤
        (F.size k : ℝ) * (VYoung (c k) x - V1 B x) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hmax _) (Nat.cast_nonneg _)
    _ ≤ C * maxAbs (centered x) ^ 2 / (F.size k : ℝ) := hf.2.1.2

/-! Record 14: exact optimum for sign vectors and its probability limits. -/

def unbounded_caps_equalGraph {n : ℕ} (y : Fin n → ℝ) : Graph n :=
  ⟨fun i j => decide (i ≠ j ∧ y i = y j), by
    constructor
    · intro i j
      by_cases hij : i = j
      · subst j; rfl
      · by_cases he : y i = y j
        · simp [hij, Ne.symm hij, he]
        · simp [hij, Ne.symm hij, he, Ne.symm he]
    · intro i
      simp⟩

lemma unbounded_caps_all_compatible {n : ℕ} (B : Graph n) :
    Compatible (emptyGraph n) (fun _ => n - 1) B := by
  constructor
  · intro i j hij
    simp [emptyGraph] at hij
  · exact simple_degree_bound B

lemma unbounded_caps_average_bound {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) : |average y| ≤ 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi (i : Fin n) : |y i| ≤ 1 := by
    rcases hy i with hi | hi <;> rw [hi] <;> norm_num
  unfold average
  rw [abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
    _ = 1 * (n : ℝ) := by simp

lemma unbounded_caps_oracle_entry {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (i j : Fin n) :
    oracleMatrix (unbounded_caps_equalGraph y) i j = (1 + y i * y j) / 2 := by
  by_cases hij : i = j
  · subst j
    rcases hy i with hi | hi <;>
      norm_num [oracleMatrix, adjacency, unbounded_caps_equalGraph,
        Matrix.add_apply, Matrix.one_apply, hi]
  · rcases hy i with hi | hi <;> rcases hy j with hj | hj <;>
      norm_num [oracleMatrix, adjacency, unbounded_caps_equalGraph,
        Matrix.add_apply, Matrix.one_apply, hij, hi, hj]

lemma unbounded_caps_pair_domination {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (B : Graph n) (i j : Fin n) :
    adjacency B i j * centered y i * centered y j ≤
      adjacency (unbounded_caps_equalGraph y) i j * centered y i * centered y j := by
  by_cases hij : i = j
  · subst j
    simp [adjacency, B.property.2, unbounded_caps_equalGraph]
  · by_cases he : y i = y j
    · have hprod : 0 ≤ centered y i * centered y j := by
        simpa only [centered, he, ← sq] using sq_nonneg (y j - average y)
      have hadj : adjacency (unbounded_caps_equalGraph y) i j = 1 := by
        simp [adjacency, unbounded_caps_equalGraph, hij, he]
      rw [hadj]
      cases hb : B.val i j <;> simp [adjacency, hb] <;> linarith
    · have hav := abs_le.mp (unbounded_caps_average_bound hn y hy)
      have hav2 : average y ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (average y), mul_nonneg (by linarith : 0 ≤ 1 - average y)
          (by linarith : 0 ≤ 1 + average y)]
      have hprod : centered y i * centered y j ≤ 0 := by
        rcases hy i with hi | hi <;> rcases hy j with hj | hj
        · exact False.elim (he (hi.trans hj.symm))
        · dsimp only [centered]
          rw [hi, hj]
          nlinarith
        · dsimp only [centered]
          rw [hi, hj]
          nlinarith
        · exact False.elim (he (hi.trans hj.symm))
      have hadj : adjacency (unbounded_caps_equalGraph y) i j = 0 := by
        simp [adjacency, unbounded_caps_equalGraph, he]
      rw [hadj]
      cases hb : B.val i j <;> simp [adjacency, hb] <;> linarith

lemma unbounded_caps_witness_max {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (B : Graph n) :
    V1 B y ≤ V1 (unbounded_caps_equalGraph y) y := by
  unfold V1
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply add_le_add le_rfl
  unfold quadratic
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact unbounded_caps_pair_domination hn y hy B i j

lemma unbounded_caps_witness_value {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    V1 (unbounded_caps_equalGraph y) y = (1 - average y ^ 2) ^ 2 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs (i : Fin n) : y i ^ 2 = 1 := by
    rcases hy i with hi | hi <;> rw [hi] <;> norm_num
  have hsum : (∑ i, y i ^ 2) = (n : ℝ) := by simp [hs]
  have hav : (∑ i, y i) = (n : ℝ) * average y := by
    unfold average
    field_simp [hn0]
    <;> ring
  have hprod : (∑ i, y i * centered y i) = (n : ℝ) * (1 - average y ^ 2) := by
    simp_rw [centered, mul_sub, ← pow_two]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hav]
    ring
  have hq : quadratic (oracleMatrix (unbounded_caps_equalGraph y)) (centered y) =
      ((∑ i, centered y i) ^ 2 + (∑ i, y i * centered y i) ^ 2) / 2 := by
    unfold quadratic
    simp_rw [unbounded_caps_oracle_entry y hy]
    have hterm (i j : Fin n) :
        (1 + y i * y j) / 2 * centered y i * centered y j =
          (centered y i * centered y j +
            (y i * centered y i) * (y j * centered y j)) / 2 := by ring
    simp_rw [hterm]
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [← variance_form_oracle, varianceForm, hq, centered_sum_zero hn y, hprod]
  field_simp [hn0]
  <;> ring

lemma unbounded_caps_sign_young {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    VYoung (fun _ => n - 1) y = 1 - average y ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hncast : 1 + ((n - 1 : ℕ) : ℝ) = (n : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hs (i : Fin n) : y i ^ 2 = 1 := by
    rcases hy i with hi | hi <;> rw [hi] <;> norm_num
  have hsum : (∑ i, y i ^ 2) = (n : ℝ) := by simp [hs]
  unfold VYoung
  simp only [truncatedDegree, min_self, hncast, ← Finset.mul_sum]
  rw [DenseCompletion.centered_sq hn, hsum]
  field_simp [hn0]
  <;> ring

lemma unbounded_caps_sign_optimum {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (A : Graph n)
    (hm : Maximizes (emptyGraph n) (fun _ => n - 1) (fun B => V1 B y) A) :
    V1 A y = (1 - average y ^ 2) ^ 2 / 2 ∧
      VYoung (fun _ => n - 1) y = 1 - average y ^ 2 := by
  have he : V1 A y = V1 (unbounded_caps_equalGraph y) y :=
    le_antisymm (unbounded_caps_witness_max hn y hy A)
      (hm.2 _ (unbounded_caps_all_compatible _))
  exact ⟨he.trans (unbounded_caps_witness_value hn y hy), unbounded_caps_sign_young hn y hy⟩

lemma unbounded_caps_polynomial_limit (f : ℝ → ℝ) (hf : Continuous f) :
    InProbability signFamily (fun _ y => f (average y)) (fun _ => f 0) := by
  let (k : ℕ) : IsProbabilityMeasure (signModel (k + 1)).law := (signModel (k + 1)).probability
  have hc := CoverageCompletion.rowCP_continuous_pair (fun k => (signModel (k + 1)).law)
    (fun _ y => average y) (fun _ _ => (0 : ℝ)) 0 0 DataMatrixCompletion.average_CP
    (CoverageCompletion.rowCP_det _ (fun _ => (0 : ℝ)) 0 tendsto_const_nhds)
    (fun p : ℝ × ℝ => f p.1) (hf.comp continuous_fst).continuousAt
  exact hc

theorem unbounded_caps_gap_proof (A : ∀ k, (Fin (k+1) → ℝ) → Graph (k+1))
    (hm : ∀ k y, Maximizes (emptyGraph (k+1)) (fun _ => k)
      (fun B => V1 B y) (A k y)) :
    (∀ k y, (∀ i, y i = 1 ∨ y i = -1) →
      V1 (A k y) y = (1-average y^2)^2/2 ∧
      VYoung (fun _ => k) y = 1-average y^2) ∧
    InProbability signFamily (fun k y => V1 (A k y) y) (fun _ => 1/2) ∧
    InProbability signFamily (fun k y => VYoung (fun _ => k) y) (fun _ => 1) := by
  have hfinite (k : ℕ) (y : Fin (k + 1) → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
      V1 (A k y) y = (1 - average y ^ 2) ^ 2 / 2 ∧
      VYoung (fun _ => k) y = 1 - average y ^ 2 := by
    simpa only [Nat.succ_sub_one, Nat.add_sub_cancel] using
      unbounded_caps_sign_optimum (Nat.succ_pos k) y hy (A k y) (hm k y)
  refine ⟨hfinite, ?_, ?_⟩
  · have hc := unbounded_caps_polynomial_limit (fun b : ℝ => (1 - b ^ 2) ^ 2 / 2)
      (by fun_prop)
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero, one_pow] at hc
    intro ε hε
    convert hc ε hε using 1
    funext k
    apply measureReal_congr
    filter_upwards [DataMatrixCompletion.ae_signs (k + 1)] with y hy
    exact congrArg (fun t => |t - 1/2| > ε) (hfinite k y hy).1
  · have hc := unbounded_caps_polynomial_limit (fun b : ℝ => 1 - b ^ 2) (by fun_prop)
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero] at hc
    intro ε hε
    convert hc ε hε using 1
    funext k
    apply measureReal_congr
    filter_upwards [DataMatrixCompletion.ae_signs (k + 1)] with y hy
    exact congrArg (fun t => |t - 1| > ε) (hfinite k y hy).2

example : type_of% @AronowAudit.P011.unbounded_caps_gap := unbounded_caps_gap_proof

/-! Record 15: finite maximum values are measurable for arbitrary selectors. -/

lemma revised_corollaries_V1_measurable {n : ℕ} (m : Model n) (B : Graph n) :
    Measurable (fun y => V1 B (weighted m y)) := by
  unfold V1 quadratic centered average weighted
  fun_prop

lemma revised_corollaries_V1plus_measurable {n : ℕ} (m : Model n) (B : Graph n) :
    Measurable (fun y => V1plus m.d B (weighted m y)) := by
  unfold V1plus V1 quadratic centered average weighted
  fun_prop

lemma revised_corollaries_VYoung_measurable {n : ℕ} (m : Model n) :
    Measurable (fun y => VYoung m.d (weighted m y)) := by
  unfold VYoung centered average weighted
  fun_prop

lemma revised_corollaries_VPositive_measurable {n : ℕ} (m : Model n) :
    Measurable (fun y => VPositive m.G (weighted m y)) := by
  unfold VPositive varianceForm quadratic centered average weighted
  fun_prop

lemma revised_corollaries_maximum_measurable {n : ℕ} (m : Model n)
    (hv : Compatible m.R m.d m.G) (f : Graph n → (Fin n → ℝ) → ℝ)
    (hf : ∀ B, Measurable (f B)) (A : (Fin n → ℝ) → Graph n)
    (hm : ∀ y, Maximizes m.R m.d (fun B => f B y) (A y)) :
    Measurable (fun y => f (A y) y) := by
  classical
  let S : Finset (Graph n) := Finset.univ.filter (Compatible m.R m.d)
  have hS : S.Nonempty := ⟨m.G, by simp [S, hv]⟩
  have hM : Measurable (S.sup' hS f) :=
    Finset.measurable_sup' hS (fun B _ => hf B)
  have he : (fun y => f (A y) y) = S.sup' hS f := by
    funext y
    apply le_antisymm
    · have ha : A y ∈ S := by simpa [S] using (hm y).1
      exact (Finset.le_sup' (f := f) ha) y
    · have hb : S.sup' hS f ≤ fun z => f (A z) z := by
        apply (Finset.sup'_le_iff hS f).mpr
        intro B hB z
        exact (hm z).2 B (by simpa [S] using hB)
      exact hb y
  rw [he]
  exact hM

lemma revised_corollaries_exists_maximizer {n : ℕ} (m : Model n)
    (hv : Compatible m.R m.d m.G) (f : Graph n → ℝ) :
    ∃ B, Maximizes m.R m.d f B := by
  classical
  let S : Finset (Graph n) := Finset.univ.filter (Compatible m.R m.d)
  have hS : S.Nonempty := ⟨m.G, by simp [S, hv]⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image S f hS
  refine ⟨B, ?_, ?_⟩
  · simpa [S] using hB
  · intro C hC
    exact hmax C (by simp [S, hC])

/-- All branches of `CorrectedClass`, including the original maximum, have
measurable scalar values independently of the missing conservative proof. -/
lemma revised_corollaries_class_measurable (F : Family)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : CorrectedClass F V) :
    ∀ k, Measurable (V k) := by
  rcases hV with ⟨hv, hcases⟩ | rfl | ⟨hv, hr, A, hm, rfl⟩ | ⟨hv, hbias, hcases⟩
  · rcases hcases with rfl | rfl | ⟨A, hm, hcases⟩
    · intro k
      exact revised_corollaries_V1plus_measurable (F.model k) (F.model k).G
    · intro k
      exact revised_corollaries_VYoung_measurable (F.model k)
    · have hA (k : ℕ) : Measurable (fun y =>
          V1plus (F.model k).d (A k y) (weighted (F.model k) y)) :=
        revised_corollaries_maximum_measurable (F.model k) (hv k)
          (fun B y => V1plus (F.model k).d B (weighted (F.model k) y))
          (revised_corollaries_V1plus_measurable (F.model k)) (A k) (hm k)
      rcases hcases with rfl | rfl
      · exact hA
      · intro k
        exact (hA k).min (revised_corollaries_VYoung_measurable (F.model k))
  · intro k
    exact revised_corollaries_VPositive_measurable (F.model k)
  · intro k
    exact revised_corollaries_maximum_measurable (F.model k) (hv k)
      (fun B y => V1 B (weighted (F.model k) y))
      (revised_corollaries_V1_measurable (F.model k)) (A k) (hm k)
  · rcases hcases with rfl | ⟨A, hm, rfl⟩
    · intro k
      exact revised_corollaries_V1_measurable (F.model k) (F.model k).G
    · intro k
      exact revised_corollaries_maximum_measurable (F.model k) (hv k)
        (fun B y => V1 B (weighted (F.model k) y))
        (revised_corollaries_V1_measurable (F.model k)) (A k) (hm k)

/-- Reduction only. Its extra premise is precisely the still unavailable
record-12 theorem specialized to `F`; it is not an added premise on the frozen
record-15 statement. Once record 12 is proved this reduction closes record 15. -/
lemma revised_corollaries_from_degree_only (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hV : CorrectedClass F V)
    (hdegree : ∀ (hv : Valid F)
      (hr : ∀ k, (F.model k).R = emptyGraph (F.size k))
      (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
      Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))) :
    Conservative F V ∧ ConservativeCoverage F V := by
  have hmeas : ∀ k, Measurable (V k) := revised_corollaries_class_measurable F V hV
  have hcon : Conservative F V := by
    rcases hV with ⟨hv, hcases⟩ | rfl | ⟨hv, hr, A, hm, rfl⟩ | ⟨hv, hbias, hcases⟩
    · have hex (k : ℕ) (y : Fin (F.size k) → ℝ) :
          ∃ B, Maximizes (F.model k).R (F.model k).d
            (fun C => V1plus (F.model k).d C (weighted (F.model k) y)) B :=
        revised_corollaries_exists_maximizer (F.model k) (hv k) _
      choose A hm using hex
      have hc := corrected_asymptotic F c1 c2 c3 c4 h hv A hm
      rcases hcases with rfl | rfl | ⟨B, hB, hcases⟩
      · exact hc.2.2.1
      · exact hc.2.2.2.2.1
      · have hb := corrected_asymptotic F c1 c2 c3 c4 h hv B hB
        rcases hcases with rfl | rfl
        · exact hb.2.2.2.1
        · exact hb.2.2.2.2.2.1
    · exact positive_part_conservative F c1 c2 c3 c4 h
    · exact hdegree hv hr A hm
    · have ho : Conservative F (fun k y =>
          V1 (F.model k).G (weighted (F.model k) y)) :=
        (oracle_mean_conditions F c1 c2 c3 c4 h).2.1.mpr hbias
      rcases hcases with rfl | ⟨A, hm, rfl⟩
      · exact ho
      · exact CorollaryCompletion.conservative_mono F _ _ ho
          (fun k y => (hm k y).2 _ (hv k))
  exact ⟨hcon, (conditional_wald_coverage F c1 c2 c3 c4 h V hmeas).2 hcon⟩

/-- Both remaining asymptotic nodes reduce to the same independent finite
comparison proof. This lemma records that dependency without asserting it. -/
lemma revised_corollaries_from_finite
    (hfinite : type_of% @AronowAudit.P011.degree_only_finite)
    (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hV : CorrectedClass F V) : Conservative F V ∧ ConservativeCoverage F V := by
  apply revised_corollaries_from_degree_only F c1 c2 c3 c4 h V hV
  intro hv hr A hm
  exact degree_only_conservative_from_finite hfinite F c1 c2 c3 c4 h hv hr A hm

end
end AronowAudit.P011.Wave1
