import AronowAudit.P011.P011_CorrectedAsymptoticCompletion
import AronowAudit.P011.P011_SpectralCompletion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Order.Lattice

/-!
Degree-only conservativeness and revised corollaries.
A maximal graph within finitely many residual bins has at most D + 1 unsaturated
vertices per bin. This yields an error C / n + D * η², sufficient for the lower-tail
limit without the exact finite sorted-clique constants.
-/

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

/-! Bounded comparison without bounding the original supplied caps. -/

def GP011B2b_degree_only_comparisonCaps {n : ℕ} (d : Fin n → ℕ) (D : ℕ) : Fin n → ℕ :=
  fun i => min (truncatedDegree d i) D

lemma GP011B2b_degree_only_comparisonCaps_valid {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (D : ℕ) (hv : Compatible R d G) (hD : ∀ i, degree G i ≤ D) :
    ∀ i, degree G i ≤ GP011B2b_degree_only_comparisonCaps d D i := by
  intro i
  exact le_min (compatible_truncated_degree R G d hv i) (hD i)

lemma GP011B2b_degree_only_comparison_psd {n : ℕ} (G : Graph n) (c : Fin n → ℕ)
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

lemma GP011B2b_degree_only_comparison_norm {n : ℕ} (c : Fin n → ℕ) (D : ℕ)
    (hc : ∀ i, c i ≤ D) :
    operatorNorm (1 + Matrix.diagonal (fun i => (c i : ℝ))) ≤ 1 + (D : ℝ) := by
  let M : Matrix (Fin n) (Fin n) ℝ := 1 + Matrix.diagonal (fun i => (c i : ℝ))
  have he (i j : Fin n) : M i j = if i = j then 1 + (c i : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      simp [M, Matrix.add_apply]
    · simp [M, Matrix.add_apply, hij]
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

lemma GP011B2b_degree_only_comparison_form {n : ℕ} (c : Fin n → ℕ)
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

lemma GP011B2b_degree_only_capped_young_conservative (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F) :
    Conservative F (fun k y =>
      VYoung (GP011B2b_degree_only_comparisonCaps (F.model k).d ⌈c2⌉₊)
        (weighted (F.model k) y)) := by
  let D : ℕ := ⌈c2⌉₊
  let c := fun k => GP011B2b_degree_only_comparisonCaps (F.model k).d D
  let M := fun k => (1 : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ) +
    Matrix.diagonal (fun i => (c k i : ℝ))
  have hdeg (k : ℕ) (i : Fin (F.size k)) : degree (F.model k).G i ≤ D := by
    have hh : (degree (F.model k).G i : ℝ) ≤ (D : ℝ) :=
      (h.2.2.2.2.2.2.2.1 k i).trans (Nat.le_ceil c2)
    exact_mod_cast hh
  have hc (k : ℕ) : ∀ i, degree (F.model k).G i ≤ c k i :=
    GP011B2b_degree_only_comparisonCaps_valid _ _ _ D (hv k) (hdeg k)
  have hp (k : ℕ) : PSD (M k) ∧ PSD (M k - oracleMatrix (F.model k).G) :=
    GP011B2b_degree_only_comparison_psd _ _ (hc k)
  have hnorm (k : ℕ) : operatorNorm (M k) ≤ 1 + (D : ℝ) :=
    GP011B2b_degree_only_comparison_norm (c k) D (fun _ => min_le_right _ _)
  have hC := ((deterministic_quadratic_expansion F c1 c2 c3 c4 (1 + (D : ℝ))
    h M (fun k => (hp k).1.1) hnorm).2.2 hp).2
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      varianceForm (M k) (weighted (F.model k) y) =
        VYoung (c k) (weighted (F.model k) y) := by
    apply GP011B2b_degree_only_comparison_form
    intro i
    exact (min_le_left _ _).trans (min_le_right _ _)
  simpa only [he, c, D] using hC

lemma GP011B2b_degree_only_centered_bound (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (k : ℕ) :
    ∀ᵐ y ∂(F.model k).law, ∀ i, |centered (weighted (F.model k) y) i| ≤ 2 * c1 := by
  have hb := h.2.2.2.2.2.2.1 k
  have ha := HomoskedasticCompletion.beta_error_bound (F.positive k) (F.model k) c1 hb
  filter_upwards [hb, ha] with y hy hay
  intro i
  have he : centered (weighted (F.model k) y) i =
      (weighted (F.model k) y i - beta (F.model k)) -
        (betaHat (F.model k) y - beta (F.model k)) := by
    unfold centered betaHat
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hy i])

/-- Add one previously absent undirected edge. -/
def GP011B2b_insert {n : ℕ} (G : Graph n) (a b : Fin n) (hab : a ≠ b) : Graph n :=
  ⟨fun i j => G.val i j || decide ((i = a ∧ j = b) ∨ (i = b ∧ j = a)), by
    constructor
    · intro i j
      dsimp only
      rw [G.property.1 i j]
      congr 1
      simp only [and_comm, or_comm]
    · intro i
      simp only [G.property.2, Bool.false_or]
      aesop⟩

lemma GP011B2b_insert_degree {n : ℕ} (G : Graph n) (a b : Fin n)
    (hab : a ≠ b) (hg : G.val a b = false) (i : Fin n) :
    degree (GP011B2b_insert G a b hab) i =
      degree G i + (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
  have hba : G.val b a = false := by rw [G.property.1, hg]
  have he (j : Fin n) :
      (if (GP011B2b_insert G a b hab).val i j then 1 else 0) =
      (if G.val i j then 1 else 0) +
        (if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0) := by
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;>
      simp_all [GP011B2b_insert] <;> omega
  unfold degree
  simp_rw [he]
  simp only [Finset.sum_add_distrib]
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    simp [hia, hib, hab, Ne.symm hab]

lemma GP011B2b_saturated_graph {n : ℕ} {α : Type} [Fintype α]
    (c : Fin n → ℕ) (q : Fin n → α) :
    ∃ G : Graph n,
      (∀ i, degree G i ≤ c i) ∧
      (∀ i j, G.val i j = true → q i = q j) ∧
      (∀ i j, degree G i < c i → degree G j < c j →
        q i = q j → i ≠ j → G.val i j = true) := by
  classical
  let S : Finset (Graph n) := Finset.univ.filter (fun G =>
    (∀ i, degree G i ≤ c i) ∧ (∀ i j, G.val i j = true → q i = q j))
  have hS : S.Nonempty := by
    refine ⟨emptyGraph n, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro i; simp [degree, emptyGraph]
    · intro i j hij; simp [emptyGraph] at hij
  obtain ⟨G, hG, hm⟩ := Finset.exists_max_image S (fun G => ∑ i, degree G i) hS
  have hp : (∀ i, degree G i ≤ c i) ∧
      (∀ i j, G.val i j = true → q i = q j) := by simpa [S] using hG
  refine ⟨G, hp.1, hp.2, ?_⟩
  intro a b ha hb hq hab
  by_contra hg
  have hg0 : G.val a b = false := Bool.eq_false_iff.mpr hg
  let H := GP011B2b_insert G a b hab
  have hd (i : Fin n) : degree H i =
      degree G i + (if i = a then 1 else 0) + (if i = b then 1 else 0) :=
    GP011B2b_insert_degree G a b hab hg0 i
  have hH : H ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro i
      rw [hd]
      by_cases hia : i = a
      · subst i; simp only [ite_true, if_neg hab]; omega
      · by_cases hib : i = b
        · subst i; simp only [ite_true, if_neg (Ne.symm hab)]; omega
        · simp only [if_neg hia, if_neg hib, add_zero]; exact hp.1 i
    · intro i j hij
      have hh : G.val i j = true ∨ (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
        simpa [H, GP011B2b_insert] using hij
      rcases hh with hh | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp.2 i j hh
      · exact hq
      · exact hq.symm
  have hmax := hm H hH
  have he : (∑ i, degree H i) = (∑ i, degree G i) + 1 + 1 := by
    simp_rw [hd]
    simp [Finset.sum_add_distrib]
  omega

lemma GP011B2b_deficit_card {n : ℕ} {α : Type} [Fintype α]
    (c : Fin n → ℕ) (q : Fin n → α) (D : ℕ) (hc : ∀ i, c i ≤ D)
    (G : Graph n) (hs : ∀ i j, degree G i < c i → degree G j < c j →
        q i = q j → i ≠ j → G.val i j = true) (a : α) :
    (Finset.univ.filter (fun i => q i = a ∧ degree G i < c i)).card ≤ D + 1 := by
  classical
  let S := Finset.univ.filter (fun i => q i = a ∧ degree G i < c i)
  by_cases hS : S.Nonempty
  · obtain ⟨i, hi⟩ := hS
    have hip : q i = a ∧ degree G i < c i := (Finset.mem_filter.mp hi).2
    have hsub : S ⊆ insert i (Finset.univ.filter (fun j => G.val i j = true)) := by
      intro j hj
      have hjp : q j = a ∧ degree G j < c j := (Finset.mem_filter.mp hj).2
      by_cases hji : j = i
      · simp [hji]
      · apply Finset.mem_insert_of_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hs i j hip.2 hjp.2 (hip.1.trans hjp.1.symm) (Ne.symm hji)
    have hdeg : (Finset.univ.filter (fun j => G.val i j = true)).card = degree G i := by
      simp [degree, Finset.card_filter]
    calc
      S.card ≤ (insert i (Finset.univ.filter (fun j => G.val i j = true))).card :=
        Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun j => G.val i j = true)).card + 1 := Finset.card_insert_le _ _
      _ ≤ D + 1 := by rw [hdeg]; have := hc i; omega
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ D + 1
    rw [this]
    simp

/-- A finite-bin comparison; its error suffices for the asymptotic theorem. -/
lemma GP011B2b_bin_comparison {n : ℕ} (hn : 0 < n) {α : Type} [Fintype α]
    (c : Fin n → ℕ) (D : ℕ) (hc : ∀ i, c i ≤ D)
    (hcn : ∀ i, c i ≤ n - 1) (x : Fin n → ℝ)
    (B η : ℝ) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hx : ∀ i, |centered x i| ≤ B) (q : Fin n → α)
    (hq : ∀ i j, q i = q j → |centered x i - centered x j| ≤ η) :
    ∃ G : Graph n, Compatible (emptyGraph n) c G ∧
      (n : ℝ) * (VYoung c x - V1 G x) ≤
        ((Fintype.card α : ℝ) * (D + 1) * D * B ^ 2) / n + D * η ^ 2 := by
  classical
  obtain ⟨G, hdeg, hedge, hsat⟩ := GP011B2b_saturated_graph c q
  refine ⟨G, ⟨?_, hdeg⟩, ?_⟩
  · intro i j hij; simp [emptyGraph] at hij
  let e := centered x
  let f := fun i => ((c i : ℝ) - degree G i) * e i ^ 2
  have hfb (i : Fin n) : f i ≤ (D : ℝ) * B ^ 2 := by
    have hci : (c i : ℝ) ≤ D := by exact_mod_cast hc i
    have hdi : (degree G i : ℝ) ≤ c i := by exact_mod_cast hdeg i
    have hei : e i ^ 2 ≤ B ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) hB).mpr (hx i)
      simpa only [sq_abs] using hh
    exact mul_le_mul (by linarith : (c i : ℝ) - degree G i ≤ D) hei
      (sq_nonneg _) (Nat.cast_nonneg _)
  have hsum : (∑ i, f i) ≤ (Fintype.card α : ℝ) * (D + 1) * D * B ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := q) (fun _ _ => Finset.mem_univ _) f]
    calc
      (∑ a, ∑ i ∈ Finset.univ with q i = a, f i) ≤
          ∑ _a : α, ((D + 1 : ℕ) : ℝ) * (D : ℝ) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        let S := Finset.univ.filter (fun i => q i = a ∧ degree G i < c i)
        have heq : (∑ i ∈ Finset.univ with q i = a, f i) = ∑ i ∈ S, f i := by
          simp only [S, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hqi : q i = a <;> by_cases hdi : degree G i < c i
          · simp [hqi, hdi]
          · have hh : degree G i = c i := by have := hdeg i; omega
            simp [hqi, f, hh]
          · simp [hqi]
          · simp [hqi]
        rw [heq]
        calc
          (∑ i ∈ S, f i) ≤ ∑ _i ∈ S, (D : ℝ) * B ^ 2 :=
            Finset.sum_le_sum (fun i _ => hfb i)
          _ = (S.card : ℝ) * ((D : ℝ) * B ^ 2) := by simp
          _ ≤ ((D + 1 : ℕ) : ℝ) * ((D : ℝ) * B ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast GP011B2b_deficit_card c q D hc G hsat a
          _ = _ := by ring
      _ = _ := by simp; ring
  have hrow (i : Fin n) :
      (∑ j, adjacency G i j * (e i - e j) ^ 2) ≤ (D : ℝ) * η ^ 2 := by
    calc
      _ ≤ ∑ j, adjacency G i j * η ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hg : G.val i j = true
        · simp only [adjacency, hg, ite_true, one_mul]
          have hh := (sq_le_sq₀ (abs_nonneg _) hη).mpr (hq i j (hedge i j hg))
          simpa only [sq_abs] using hh
        · simp [adjacency, hg]
      _ = (degree G i : ℝ) * η ^ 2 := by rw [← Finset.sum_mul, degree_row_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hdeg i).trans (hc i))
        (sq_nonneg _)
  have hloss : upperSum (fun i j => adjacency G i j * (e i - e j) ^ 2) ≤
      (n : ℝ) * D * η ^ 2 := by
    unfold upperSum
    calc
      _ ≤ ∑ i, ∑ j, adjacency G i j * (e i - e j) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro j _ _
        exact mul_nonneg (by simp [adjacency]; split <;> norm_num) (sq_nonneg _)
      _ ≤ ∑ _i : Fin n, (D : ℝ) * η ^ 2 := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp; ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (n : ℝ) * (VYoung c x - V1 G x) =
      ((∑ i, f i) + upperSum (fun i j => adjacency G i j * (e i - e j) ^ 2)) / n := by
    have ht (i : Fin n) : truncatedDegree c i = c i := min_eq_left (hcn i)
    unfold VYoung V1
    rw [degree_only_edge_identity]
    simp only [ht]
    dsimp [f, e]
    simp only [sub_mul, add_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    field_simp
    <;> ring
  rw [heq]
  calc
    _ ≤ (((Fintype.card α : ℝ) * (D + 1) * D * B ^ 2) + (n : ℝ) * D * η ^ 2) / n :=
      div_le_div_of_nonneg_right (add_le_add hsum hloss) hnR.le
    _ = _ := by field_simp


/-- The comparison constant is uniform in the sample size and the vector. -/
lemma GP011B2b_uniform_comparison (B : ℝ) (hB : 0 ≤ B) (D : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (_hn : 0 < n) (c : Fin n → ℕ),
      (∀ i, c i ≤ D) → (∀ i, c i ≤ n - 1) →
      ∀ (x : Fin n → ℝ), (∀ i, |centered x i| ≤ B) →
      ∃ G : Graph n, Compatible (emptyGraph n) c G ∧
        (n : ℝ) * (VYoung c x - V1 G x) ≤ C / n + D * η ^ 2 := by
  classical
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_Icc : IsCompact (Set.Icc (-B) B)).totallyBounded
      (η / 2) (by linarith)
  let : Fintype t := ht.fintype
  refine ⟨(Fintype.card t : ℝ) * (D + 1) * D * B ^ 2, by positivity, ?_⟩
  intro n hn c hc hcn x hx
  have hnear (i : Fin n) : ∃ a : t, dist (centered x i) a.val < η / 2 := by
    have hi : centered x i ∈ Set.Icc (-B) B := abs_le.mp (hx i)
    have hh := hcover hi
    simp only [Set.mem_iUnion, Metric.mem_ball] at hh
    obtain ⟨a, ha, hh⟩ := hh
    exact ⟨⟨a, ha⟩, hh⟩
  choose q hq using hnear
  apply GP011B2b_bin_comparison hn c D hc hcn x B η hB hη.le hx q
  intro i j hij
  have hqi := hq i
  have hqj := hq j
  rw [← hij] at hqj
  rw [← Real.dist_eq]
  calc
    dist (centered x i) (centered x j) ≤
        dist (centered x i) (q i).val + dist (q i).val (centered x j) := dist_triangle _ _ _
    _ ≤ η := by rw [dist_comm (q i).val]; linarith

theorem degree_only_conservative_proof (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F) (hr : ∀ k, (F.model k).R = emptyGraph (F.size k))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let D : ℕ := ⌈c2⌉₊
  let c := fun k => GP011B2b_degree_only_comparisonCaps (F.model k).d D
  have hcon := GP011B2b_degree_only_capped_young_conservative F c1 c2 c3 c4 h hv
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  intro ε hε
  let η := Real.sqrt (ε / (8 * ((D : ℝ) + 1)))
  have hratio : 0 < ε / (8 * ((D : ℝ) + 1)) := by positivity
  have hη : 0 < η := Real.sqrt_pos.mpr hratio
  have hηsq : η ^ 2 = ε / (8 * ((D : ℝ) + 1)) := Real.sq_sqrt hratio.le
  have hsmall : (D : ℝ) * η ^ 2 ≤ ε / 8 := by
    rw [hηsq]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have he : ε / (8 * ((D : ℝ) + 1)) * (8 * ((D : ℝ) + 1)) = ε :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [hratio.le]
  obtain ⟨C, hC, hfinite⟩ := GP011B2b_uniform_comparison (2 * c1)
    (by linarith [h.2.1]) D η hη
  have hevent : ∀ᶠ k in atTop, C / (F.size k : ℝ) < ε / 4 :=
    (hN.const_div_atTop C).eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (hcon (ε / 2) (by linarith))
  filter_upwards [hevent] with k hk
  change (F.model k).law.real _ ≤ (F.model k).law.real _
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [GP011B2b_degree_only_centered_bound F c1 c2 c3 c4 h k] with y hy
  let x := weighted (F.model k) y
  have hcx : ∀ i, |centered x i| ≤ 2 * c1 := by
    intro i
    exact hy i
  obtain ⟨G, hG, hcomp⟩ := hfinite (F.size k) (F.positive k) (c k)
    (fun _ => min_le_right _ _)
    (fun _ => (min_le_left _ _).trans (min_le_right _ _)) x hcx
  have hcompat : Compatible (F.model k).R (F.model k).d G := by
    constructor
    · intro i j hij
      rw [hr k] at hij
      simp [emptyGraph] at hij
    · intro i
      exact (hG.2 i).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmax : V1 G x ≤ V1 (A k y) x := (hm k y).2 G hcompat
  have hcmp : (F.size k : ℝ) * (VYoung (c k) x - V1 (A k y) x) ≤
      C / (F.size k : ℝ) + D * η ^ 2 := by
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hmax _) (Nat.cast_nonneg _)).trans hcomp
  intro hbad
  change ε < (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V1 (A k y) x) at hbad
  change ε / 2 < (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - VYoung (c k) x)
  nlinarith

lemma GP011B2b_revised_corollaries_V1_measurable {n : ℕ} (m : Model n) (B : Graph n) :
    Measurable (fun y => V1 B (weighted m y)) := by
  unfold V1 quadratic centered average weighted
  fun_prop

lemma GP011B2b_revised_corollaries_V1plus_measurable {n : ℕ} (m : Model n) (B : Graph n) :
    Measurable (fun y => V1plus m.d B (weighted m y)) := by
  unfold V1plus V1 quadratic centered average weighted
  fun_prop

lemma GP011B2b_revised_corollaries_VYoung_measurable {n : ℕ} (m : Model n) :
    Measurable (fun y => VYoung m.d (weighted m y)) := by
  unfold VYoung centered average weighted
  fun_prop

lemma GP011B2b_revised_corollaries_VPositive_measurable {n : ℕ} (m : Model n) :
    Measurable (fun y => VPositive m.G (weighted m y)) := by
  unfold VPositive varianceForm quadratic centered average weighted
  fun_prop

lemma GP011B2b_revised_corollaries_maximum_measurable {n : ℕ} (m : Model n)
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

lemma GP011B2b_revised_corollaries_exists_maximizer {n : ℕ} (m : Model n)
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
measurable scalar values without measurability assumptions on graph selectors. -/
lemma GP011B2b_revised_corollaries_class_measurable (F : Family)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : CorrectedClass F V) :
    ∀ k, Measurable (V k) := by
  rcases hV with ⟨hv, hcases⟩ | rfl | ⟨hv, hr, A, hm, rfl⟩ | ⟨hv, hbias, hcases⟩
  · rcases hcases with rfl | rfl | ⟨A, hm, hcases⟩
    · intro k
      exact GP011B2b_revised_corollaries_V1plus_measurable (F.model k) (F.model k).G
    · intro k
      exact GP011B2b_revised_corollaries_VYoung_measurable (F.model k)
    · have hA (k : ℕ) : Measurable (fun y =>
          V1plus (F.model k).d (A k y) (weighted (F.model k) y)) :=
        GP011B2b_revised_corollaries_maximum_measurable (F.model k) (hv k)
          (fun B y => V1plus (F.model k).d B (weighted (F.model k) y))
          (GP011B2b_revised_corollaries_V1plus_measurable (F.model k)) (A k) (hm k)
      rcases hcases with rfl | rfl
      · exact hA
      · intro k
        exact (hA k).min (GP011B2b_revised_corollaries_VYoung_measurable (F.model k))
  · intro k
    exact GP011B2b_revised_corollaries_VPositive_measurable (F.model k)
  · intro k
    exact GP011B2b_revised_corollaries_maximum_measurable (F.model k) (hv k)
      (fun B y => V1 B (weighted (F.model k) y))
      (GP011B2b_revised_corollaries_V1_measurable (F.model k)) (A k) (hm k)
  · rcases hcases with rfl | ⟨A, hm, rfl⟩
    · intro k
      exact GP011B2b_revised_corollaries_V1_measurable (F.model k) (F.model k).G
    · intro k
      exact GP011B2b_revised_corollaries_maximum_measurable (F.model k) (hv k)
        (fun B y => V1 B (weighted (F.model k) y))
        (GP011B2b_revised_corollaries_V1_measurable (F.model k)) (A k) (hm k)

theorem revised_corollaries_proof (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hV : CorrectedClass F V) :
    Conservative F V ∧ ConservativeCoverage F V := by
  have hmeas : ∀ k, Measurable (V k) := GP011B2b_revised_corollaries_class_measurable F V hV
  have hcon : Conservative F V := by
    rcases hV with ⟨hv, hcases⟩ | rfl | ⟨hv, hr, A, hm, rfl⟩ | ⟨hv, hbias, hcases⟩
    · have hex (k : ℕ) (y : Fin (F.size k) → ℝ) :
          ∃ B, Maximizes (F.model k).R (F.model k).d
            (fun C => V1plus (F.model k).d C (weighted (F.model k) y)) B :=
        GP011B2b_revised_corollaries_exists_maximizer (F.model k) (hv k) _
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
    · exact degree_only_conservative_proof F c1 c2 c3 c4 h hv hr A hm
    · have ho : Conservative F (fun k y =>
          V1 (F.model k).G (weighted (F.model k) y)) :=
        (oracle_mean_conditions F c1 c2 c3 c4 h).2.1.mpr hbias
      rcases hcases with rfl | ⟨A, hm, rfl⟩
      · exact ho
      · exact CorollaryCompletion.conservative_mono F _ _ ho
          (fun k y => (hm k y).2 _ (hv k))
  exact ⟨hcon, (conditional_wald_coverage F c1 c2 c3 c4 h V hmeas).2 hcon⟩


end
end AronowAudit.P011.Wave1
