import AronowAudit.P011.P011_Audit
import Mathlib.Data.Finset.Powerset

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

/-! Finite degree-only comparison: disjoint sorted cliques, with the two
explicit remainder bounds. All graph constructions are on the original vertices. -/

def degreeOnlyFinite_supported {n : ℕ} (H : Graph n) (s : Finset (Fin n)) : Prop :=
  ∀ i j, H.val i j = true → i ∈ s ∧ j ∈ s

def degreeOnlyFinite_penalty {n : ℕ} (H : Graph n) (e : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, adjacency H i j * (e i - e j)^2) / 2

lemma degreeOnlyFinite_edge_identity {n : ℕ} (H : Graph n) (e : Fin n → ℝ) :
    quadratic (adjacency H) e =
      (∑ i, (degree H i : ℝ) * e i^2) - degreeOnlyFinite_penalty H e := by
  have he := (graph_laplacian_identity H e).2
  have hp : degreeOnlyFinite_penalty H e =
      upperSum (fun i j => adjacency H i j * (e i - e j)^2) := by
    unfold degreeOnlyFinite_penalty
    rw [ordered_pair_sum _ (by intro i; simp)]
    have hs (i j : Fin n) : adjacency H j i = adjacency H i j := by
      unfold adjacency; rw [H.property.1 j i]
    have hh : upperSum (fun i j => adjacency H i j * (e i - e j)^2 +
        adjacency H j i * (e j - e i)^2) =
        2 * upperSum (fun i j => adjacency H i j * (e i - e j)^2) := by
      simp only [upperSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; apply Finset.sum_congr rfl
      intro j _; rw [hs]; ring
    rw [hh]; ring
  rw [← hp] at he
  have hq : quadratic (Matrix.diagonal (fun i => (degree H i : ℝ)) - adjacency H) e =
      (∑ i, (degree H i : ℝ) * e i^2) - quadratic (adjacency H) e := by
    simp [quadratic, Matrix.sub_apply, Matrix.diagonal_apply, sub_mul,
      Finset.sum_sub_distrib, pow_two, mul_assoc]
  rw [hq] at he
  linarith

lemma degreeOnlyFinite_penalty_nonneg {n : ℕ} (H : Graph n) (e : Fin n → ℝ) :
    0 ≤ degreeOnlyFinite_penalty H e := by
  unfold degreeOnlyFinite_penalty
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (by unfold adjacency; split <;> norm_num) (sq_nonneg _)

lemma degreeOnlyFinite_degree_zero {n : ℕ} {H : Graph n} {s : Finset (Fin n)}
    (hs : degreeOnlyFinite_supported H s) {i : Fin n} (hi : i ∉ s) : degree H i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hh : H.val i j = false := by
    cases h : H.val i j
    · rfl
    · exact False.elim (hi (hs i j h).1)
  simp [hh]

/-- A finite initial segment can be chosen by minimizing its sum. The exchange
argument gives exactly the separation property of a sorted initial segment. -/
lemma degreeOnlyFinite_initial {n : ℕ} (s : Finset (Fin n)) (e : Fin n → ℝ)
    (m : ℕ) (hm : m ≤ s.card) :
    ∃ t : Finset (Fin n), t ⊆ s ∧ t.card = m ∧
      ∀ i ∈ t, ∀ j ∈ s \ t, e i ≤ e j := by
  obtain ⟨t, ht, hmin⟩ := (s.powersetCard m).exists_min_image
    (fun t => ∑ i ∈ t, e i) (Finset.powersetCard_nonempty.mpr hm)
  obtain ⟨hts, htc⟩ := Finset.mem_powersetCard.mp ht
  refine ⟨t, hts, htc, ?_⟩
  intro i hi j hj
  obtain ⟨hjs, hjt⟩ := Finset.mem_sdiff.mp hj
  let u := insert j (t.erase i)
  have hji : j ∉ t.erase i := fun h => hjt (Finset.mem_of_mem_erase h)
  have hu : u ∈ s.powersetCard m := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hjs
      · exact hts (Finset.mem_of_mem_erase hk)
    · dsimp [u]
      rw [Finset.card_insert_of_notMem hji, Finset.card_erase_of_mem hi]
      have hp : 0 < t.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
  have hsum := Finset.sum_erase_add t e hi
  have hcomp := hmin u hu
  dsimp [u] at hcomp
  rw [Finset.sum_insert hji] at hcomp
  linarith

def degreeOnlyFinite_clique {n : ℕ} (s : Finset (Fin n)) : Graph n :=
  ⟨fun i j => decide (i ∈ s ∧ j ∈ s ∧ i ≠ j), by
    constructor
    · intro i j; simp only [decide_eq_decide]; tauto
    · intro i; simp⟩

lemma degreeOnlyFinite_clique_supported {n : ℕ} (s : Finset (Fin n)) :
    degreeOnlyFinite_supported (degreeOnlyFinite_clique s) s := by
  intro i j hij
  have hh : i ∈ s ∧ j ∈ s ∧ i ≠ j := of_decide_eq_true hij
  exact ⟨hh.1, hh.2.1⟩

lemma degreeOnlyFinite_clique_degree {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    degree (degreeOnlyFinite_clique s) i = if i ∈ s then s.card - 1 else 0 := by
  classical
  by_cases hi : i ∈ s
  · have he : (Finset.univ.filter (fun j : Fin n => i ∈ s ∧ j ∈ s ∧ i ≠ j)) =
        s.erase i := by ext j; simp [hi, ne_comm, and_comm]
    simp only [degree, degreeOnlyFinite_clique, decide_eq_true_eq]
    rw [← Finset.sum_filter, he]
    simp [hi, Finset.card_erase_of_mem hi]
  · simp [degree, degreeOnlyFinite_clique, hi]

def degreeOnlyFinite_join {n : ℕ} (H K : Graph n) : Graph n :=
  ⟨fun i j => H.val i j || K.val i j, by
    constructor
    · intro i j; change (H.val i j || K.val i j) = (H.val j i || K.val j i)
      rw [H.property.1 i j, K.property.1 i j]
    · intro i; simp [H.property.2 i, K.property.2 i]⟩

lemma degreeOnlyFinite_join_supported {n : ℕ} {H K : Graph n}
    {s t : Finset (Fin n)} (hH : degreeOnlyFinite_supported H s)
    (hK : degreeOnlyFinite_supported K t) :
    degreeOnlyFinite_supported (degreeOnlyFinite_join H K) (s ∪ t) := by
  intro i j hij
  have hij' : H.val i j = true ∨ K.val i j = true := by
    simpa [degreeOnlyFinite_join] using hij
  rcases hij' with hij | hij
  · exact ⟨Finset.mem_union_left _ (hH i j hij).1,
      Finset.mem_union_left _ (hH i j hij).2⟩
  · exact ⟨Finset.mem_union_right _ (hK i j hij).1,
      Finset.mem_union_right _ (hK i j hij).2⟩

lemma degreeOnlyFinite_join_adjacency {n : ℕ} {H K : Graph n}
    {s t : Finset (Fin n)} (hH : degreeOnlyFinite_supported H s)
    (hK : degreeOnlyFinite_supported K t) (hst : Disjoint s t) (i j : Fin n) :
    adjacency (degreeOnlyFinite_join H K) i j = adjacency H i j + adjacency K i j := by
  have hn : ¬ (H.val i j = true ∧ K.val i j = true) := by
    rintro ⟨h, k⟩
    exact Finset.disjoint_left.mp hst (hH i j h).1 (hK i j k).1
  cases hh : H.val i j <;> cases hk : K.val i j <;>
    simp_all [adjacency, degreeOnlyFinite_join]

lemma degreeOnlyFinite_join_degree {n : ℕ} {H K : Graph n}
    {s t : Finset (Fin n)} (hH : degreeOnlyFinite_supported H s)
    (hK : degreeOnlyFinite_supported K t) (hst : Disjoint s t) (i : Fin n) :
    degree (degreeOnlyFinite_join H K) i = degree H i + degree K i := by
  have hh : (degree (degreeOnlyFinite_join H K) i : ℝ) =
      (degree H i : ℝ) + degree K i := by
    simp_rw [degree_row_sum, degreeOnlyFinite_join_adjacency hH hK hst]
    exact Finset.sum_add_distrib
  exact_mod_cast hh

lemma degreeOnlyFinite_join_penalty {n : ℕ} {H K : Graph n}
    {s t : Finset (Fin n)} (hH : degreeOnlyFinite_supported H s)
    (hK : degreeOnlyFinite_supported K t) (hst : Disjoint s t) (e : Fin n → ℝ) :
    degreeOnlyFinite_penalty (degreeOnlyFinite_join H K) e =
      degreeOnlyFinite_penalty H e + degreeOnlyFinite_penalty K e := by
  simp [degreeOnlyFinite_penalty, degreeOnlyFinite_join_adjacency hH hK hst,
    add_mul, Finset.sum_add_distrib, add_div]

lemma degreeOnlyFinite_clique_penalty {n : ℕ} (s : Finset (Fin n)) (r : ℕ)
    (hc : s.card = r + 1) (e : Fin n → ℝ) (a b : ℝ) (hab : a ≤ b)
    (he : ∀ i ∈ s, a ≤ e i ∧ e i ≤ b) :
    degreeOnlyFinite_penalty (degreeOnlyFinite_clique s) e ≤
      ((r : ℝ) * (r + 1) / 2) * (b - a)^2 := by
  have hentry (i j : Fin n) :
      adjacency (degreeOnlyFinite_clique s) i j * (e i - e j)^2 ≤
      adjacency (degreeOnlyFinite_clique s) i j * (b - a)^2 := by
    by_cases hij : (degreeOnlyFinite_clique s).val i j = true
    · have hmem := degreeOnlyFinite_clique_supported s i j hij
      obtain ⟨hi1, hi2⟩ := he i hmem.1
      obtain ⟨hj1, hj2⟩ := he j hmem.2
      have h1 : 0 ≤ (b - a) - (e i - e j) := by linarith
      have h2 : 0 ≤ (b - a) + (e i - e j) := by linarith
      simp only [adjacency, hij, Bool.true_eq, if_true, one_mul]
      nlinarith [mul_nonneg h1 h2]
    · have hf : (degreeOnlyFinite_clique s).val i j = false := by
        cases h : (degreeOnlyFinite_clique s).val i j <;> simp_all
      simp [adjacency, hf]
  calc
    degreeOnlyFinite_penalty (degreeOnlyFinite_clique s) e ≤
        (∑ i, ∑ j, adjacency (degreeOnlyFinite_clique s) i j * (b-a)^2) / 2 := by
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hentry i j) (by norm_num)
    _ = (∑ i, (degree (degreeOnlyFinite_clique s) i : ℝ) * (b-a)^2) / 2 := by
      simp_rw [← Finset.sum_mul, ← degree_row_sum]
    _ = ((r : ℝ) * (r+1) / 2) * (b-a)^2 := by
      have hh (i : Fin n) : (degree (degreeOnlyFinite_clique s) i : ℝ) * (b-a)^2 =
          if i ∈ s then (r : ℝ) * (b-a)^2 else 0 := by
        rw [degreeOnlyFinite_clique_degree]
        by_cases hi : i ∈ s <;> simp [hi, hc]
      simp_rw [hh]
      rw [← Finset.sum_filter]
      have hfilter : (Finset.univ.filter (fun i : Fin n => i ∈ s)) = s := by ext i; simp
      simp only [hfilter, Finset.sum_const, nsmul_eq_mul, hc,
        Nat.cast_add, Nat.cast_one]
      ring

/-- At one cap level, full initial blocks have zero degree deficiency.
The interval budget telescopes because the next block starts above this one. -/
lemma degreeOnlyFinite_one_level {n : ℕ} (r : ℕ) (e : Fin n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (s : Finset (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (he : ∀ i ∈ s, a ≤ e i ∧ e i ≤ b) (heB : ∀ i ∈ s, |e i| ≤ B) :
    ∃ H : Graph n, degreeOnlyFinite_supported H s ∧ (∀ i, degree H i ≤ r) ∧
      (∑ i ∈ s, ((r : ℝ) - degree H i) * e i^2) ≤ (r : ℝ)^2 * B^2 ∧
      degreeOnlyFinite_penalty H e ≤ ((r : ℝ) * (r+1) / 2) * (b-a)^2 := by
  induction s using Finset.strongInductionOn generalizing a b with
  | _ s ih =>
    by_cases hs : s.card ≤ r
    · refine ⟨emptyGraph n, ?_, ?_, ?_, ?_⟩
      · intro i j hij; simp [emptyGraph] at hij
      · intro i; simp [degree, emptyGraph]
      · simp only [degree, emptyGraph, Bool.false_eq_true, if_false, Finset.sum_const_zero,
          Nat.cast_zero, sub_zero]
        calc
          (∑ i ∈ s, (r : ℝ) * e i^2) ≤ ∑ _i ∈ s, (r : ℝ) * B^2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hx := abs_le.mp (heB i hi)
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
            nlinarith [sq_nonneg (B - e i), sq_nonneg (B + e i)]
          _ ≤ (r : ℝ)^2 * B^2 := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            have hh : (s.card : ℝ) ≤ r := by exact_mod_cast hs
            nlinarith [mul_le_mul_of_nonneg_right hh
              (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg B))]
      · simp only [degreeOnlyFinite_penalty, adjacency, emptyGraph, Bool.false_eq_true,
          if_false, zero_mul, Finset.sum_const_zero, zero_div]
        positivity
    · have hcard : r+1 ≤ s.card := by omega
      obtain ⟨t, hts, htc, hsep⟩ := degreeOnlyFinite_initial s e (r+1) hcard
      have htne : t.Nonempty := Finset.card_pos.mp (by omega)
      have himage : (t.image e).Nonempty := htne.image e
      let v : ℝ := (t.image e).max' himage
      have hvmem : v ∈ t.image e := Finset.max'_mem _ _
      obtain ⟨iv, hiv, hveq⟩ := Finset.mem_image.mp hvmem
      have hav : a ≤ v := by rw [← hveq]; exact (he iv (hts hiv)).1
      have hvb : v ≤ b := by rw [← hveq]; exact (he iv (hts hiv)).2
      have htv (i : Fin n) (hi : i ∈ t) : e i ≤ v :=
        Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have huv (j : Fin n) (hj : j ∈ s \ t) : v ≤ e j := by
        rw [← hveq]
        exact hsep iv hiv j hj
      have hsmall : s \ t ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        have hv : iv ∈ s \ t := heq.symm ▸ hts hiv
        exact (Finset.mem_sdiff.mp hv).2 hiv
      obtain ⟨K, hK, hdK, hdefK, hpenK⟩ := ih (s \ t) hsmall v b hvb
        (fun j hj => ⟨huv j hj, (he j (Finset.mem_sdiff.mp hj).1).2⟩)
        (fun j hj => heB j (Finset.mem_sdiff.mp hj).1)
      let C := degreeOnlyFinite_clique t
      have hC : degreeOnlyFinite_supported C t := degreeOnlyFinite_clique_supported t
      have hdis : Disjoint t (s \ t) := by
        apply Finset.disjoint_left.mpr
        intro i hi hj; exact (Finset.mem_sdiff.mp hj).2 hi
      have hunion : t ∪ (s \ t) = s := Finset.union_sdiff_of_subset hts
      have hdegC (i : Fin n) : degree C i = if i ∈ t then r else 0 := by
        simp [C, degreeOnlyFinite_clique_degree, htc]
      let H := degreeOnlyFinite_join C K
      have hdegH (i : Fin n) : degree H i = degree C i + degree K i :=
        degreeOnlyFinite_join_degree hC hK hdis i
      refine ⟨H, ?_, ?_, ?_, ?_⟩
      · rw [← hunion]
        exact degreeOnlyFinite_join_supported hC hK
      · intro i
        rw [hdegH, hdegC]
        by_cases hi : i ∈ t
        · have hiu : i ∉ s \ t := by simp [hi]
          rw [if_pos hi, degreeOnlyFinite_degree_zero hK hiu, add_zero]
        · simpa [hi] using hdK i
      · have hsums : (∑ i ∈ s, ((r : ℝ) - degree H i) * e i^2) =
            ∑ i ∈ s \ t, ((r : ℝ) - degree K i) * e i^2 := by
          conv_lhs => rw [← hunion, Finset.sum_union hdis]
          have hz : (∑ i ∈ t, ((r : ℝ) - degree H i) * e i^2) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hki := degreeOnlyFinite_degree_zero hK (i := i) (by simp [hi])
            simp [hdegH, hdegC, hi, hki]
          rw [hz, zero_add]
          apply Finset.sum_congr rfl
          intro i hi
          have hit := (Finset.mem_sdiff.mp hi).2
          simp [hdegH, hdegC, hit]
        rw [hsums]
        exact hdefK
      · have hpenC : degreeOnlyFinite_penalty C e ≤
            ((r : ℝ) * (r+1) / 2) * (v-a)^2 :=
          degreeOnlyFinite_clique_penalty t r htc e a v hav
            (fun i hi => ⟨(he i (hts hi)).1, htv i hi⟩)
        change degreeOnlyFinite_penalty (degreeOnlyFinite_join C K) e ≤ _
        rw [degreeOnlyFinite_join_penalty hC hK hdis]
        have hcoef : 0 ≤ (r : ℝ) * (r+1) / 2 := by positivity
        have hrange : (v-a)^2 + (b-v)^2 ≤ (b-a)^2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hav) (sub_nonneg.mpr hvb)]
        nlinarith [mul_le_mul_of_nonneg_left hrange hcoef]

def degreeOnlyFinite_loss {n : ℕ} (s : Finset (Fin n)) (c : Fin n → ℕ)
    (w : ℕ → ℝ) (H : Graph n) (e : Fin n → ℝ) : ℝ :=
  (∑ i ∈ s, w (c i) * ((c i : ℝ) - degree H i) * e i^2) +
    degreeOnlyFinite_penalty H e

lemma degreeOnlyFinite_join_loss {n : ℕ} {H K : Graph n}
    {s t : Finset (Fin n)} (hH : degreeOnlyFinite_supported H s)
    (hK : degreeOnlyFinite_supported K t) (hst : Disjoint s t)
    (c : Fin n → ℕ) (w : ℕ → ℝ) (e : Fin n → ℝ) :
    degreeOnlyFinite_loss (s ∪ t) c w (degreeOnlyFinite_join H K) e =
      degreeOnlyFinite_loss s c w H e + degreeOnlyFinite_loss t c w K e := by
  have hdeg := degreeOnlyFinite_join_degree hH hK hst
  have hs (i : Fin n) (hi : i ∈ s) : degree (degreeOnlyFinite_join H K) i = degree H i := by
    have hit : i ∉ t := fun hit => Finset.disjoint_left.mp hst hi hit
    rw [hdeg, degreeOnlyFinite_degree_zero hK hit, add_zero]
  have ht (i : Fin n) (hi : i ∈ t) : degree (degreeOnlyFinite_join H K) i = degree K i := by
    have his : i ∉ s := fun his => Finset.disjoint_left.mp hst his hi
    rw [hdeg, degreeOnlyFinite_degree_zero hH his, zero_add]
  unfold degreeOnlyFinite_loss
  rw [Finset.sum_union hst, degreeOnlyFinite_join_penalty hH hK hst]
  have hs' : (∑ i ∈ s, w (c i) * ((c i : ℝ) - degree (degreeOnlyFinite_join H K) i) * e i^2) =
      ∑ i ∈ s, w (c i) * ((c i : ℝ) - degree H i) * e i^2 := by
    apply Finset.sum_congr rfl; intro i hi; rw [hs i hi]
  have ht' : (∑ i ∈ t, w (c i) * ((c i : ℝ) - degree (degreeOnlyFinite_join H K) i) * e i^2) =
      ∑ i ∈ t, w (c i) * ((c i : ℝ) - degree K i) * e i^2 := by
    apply Finset.sum_congr rfl; intro i hi; rw [ht i hi]
  rw [hs', ht']; ring

/-- Assemble the cap levels. The arbitrary nonnegative level weight lets the
same construction give the ordinary and corrected deficiency coefficients. -/
lemma degreeOnlyFinite_capped_cliques {n : ℕ} (c : Fin n → ℕ) (w : ℕ → ℝ)
    (hw : ∀ r, 1 ≤ r → 0 ≤ w r) (e : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (D : ℕ) (s : Finset (Fin n)) (hc : ∀ i ∈ s, c i ≤ D)
    (he : ∀ i ∈ s, |e i| ≤ B) :
    ∃ H : Graph n, degreeOnlyFinite_supported H s ∧ (∀ i ∈ s, degree H i ≤ c i) ∧
      degreeOnlyFinite_loss s c w H e ≤
        B^2 * ∑ r ∈ Finset.Icc 1 D, (w r * (r : ℝ)^2 + 2*r*(r+1)) := by
  induction D generalizing s with
  | zero =>
    refine ⟨emptyGraph n, ?_, ?_, ?_⟩
    · intro i j hij; simp [emptyGraph] at hij
    · intro i hi; simp [degree, emptyGraph]
    · have hzero (i : Fin n) (hi : i ∈ s) : c i = 0 := by have := hc i hi; omega
      have hsum : (∑ i ∈ s, w (c i) * ((c i : ℝ) - degree (emptyGraph n) i) * e i^2) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi; simp [hzero i hi, degree, emptyGraph]
      unfold degreeOnlyFinite_loss
      rw [hsum]
      simp [degreeOnlyFinite_penalty, adjacency, emptyGraph]
  | succ D ih =>
    let s₀ := s.filter (fun i => c i ≤ D)
    let s₁ := s.filter (fun i => c i = D+1)
    have hs₀ : s₀ ⊆ s := Finset.filter_subset _ _
    have hs₁ : s₁ ⊆ s := Finset.filter_subset _ _
    have hd₀ (i : Fin n) (hi : i ∈ s₀) : c i ≤ D := (Finset.mem_filter.mp hi).2
    have hd₁ (i : Fin n) (hi : i ∈ s₁) : c i = D+1 := (Finset.mem_filter.mp hi).2
    have hdis : Disjoint s₀ s₁ := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have := hd₀ i hi; have := hd₁ i hj; omega
    have hunion : s₀ ∪ s₁ = s := by
      ext i
      simp only [Finset.mem_union, s₀, s₁, Finset.mem_filter]
      constructor
      · tauto
      · intro hi
        have hci := hc i hi
        by_cases hle : c i ≤ D
        · exact Or.inl ⟨hi, hle⟩
        · exact Or.inr ⟨hi, by omega⟩
    obtain ⟨H, hH, hdH, hlH⟩ := ih s₀ hd₀ (fun i hi => he i (hs₀ hi))
    obtain ⟨K, hK, hdK, hdefK, hpenK⟩ :=
      degreeOnlyFinite_one_level (D+1) e B hB s₁ (-B) B (by linarith)
        (fun i hi => abs_le.mp (he i (hs₁ hi))) (fun i hi => he i (hs₁ hi))
    have hlK : degreeOnlyFinite_loss s₁ c w K e ≤
        B^2 * (w (D+1) * ((D+1 : ℕ) : ℝ)^2 +
          2 * ((D+1 : ℕ) : ℝ) * (((D+1 : ℕ) : ℝ)+1)) := by
      have heq : degreeOnlyFinite_loss s₁ c w K e =
          w (D+1) * (∑ i ∈ s₁, (((D+1 : ℕ) : ℝ) - degree K i) * e i^2) +
            degreeOnlyFinite_penalty K e := by
        unfold degreeOnlyFinite_loss
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi; rw [hd₁ i hi]; ring
      rw [heq]
      have hh := mul_le_mul_of_nonneg_left hdefK (hw (D+1) (by omega))
      calc
        _ ≤ w (D+1) * (((D+1 : ℕ) : ℝ)^2 * B^2) +
            ((((D+1 : ℕ) : ℝ) * (((D+1 : ℕ) : ℝ)+1) / 2) * (B - -B)^2) :=
          add_le_add hh hpenK
        _ = _ := by ring
    refine ⟨degreeOnlyFinite_join H K, ?_, ?_, ?_⟩
    · rw [← hunion]
      exact degreeOnlyFinite_join_supported hH hK
    · intro i hi
      rw [degreeOnlyFinite_join_degree hH hK hdis]
      by_cases hi₀ : i ∈ s₀
      · have hi₁ : i ∉ s₁ := fun h => Finset.disjoint_left.mp hdis hi₀ h
        rw [degreeOnlyFinite_degree_zero hK hi₁, add_zero]
        exact hdH i hi₀
      · have hi₁ : i ∈ s₁ := by
          have hh : i ∈ s₀ ∪ s₁ := hunion.symm ▸ hi
          exact (Finset.mem_union.mp hh).resolve_left hi₀
        rw [degreeOnlyFinite_degree_zero hH hi₀, zero_add, hd₁ i hi₁]
        exact hdK i
    · have hl := degreeOnlyFinite_join_loss hH hK hdis c w e
      rw [hunion] at hl
      rw [hl]
      calc
        _ ≤ B^2 * (∑ r ∈ Finset.Icc 1 D, (w r * (r : ℝ)^2 + 2*r*(r+1))) +
            B^2 * (w (D+1) * ((D+1 : ℕ) : ℝ)^2 +
              2 * ((D+1 : ℕ) : ℝ) * (((D+1 : ℕ) : ℝ)+1)) := add_le_add hlH hlK
        _ = _ := by
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ D+1)]
          ring

def degreeOnlyFinite_weight (r : ℕ) : ℝ :=
  if r = 0 then 1 else 2 - 1 / (r : ℝ)

lemma degreeOnlyFinite_weight_nonneg (r : ℕ) : 0 ≤ degreeOnlyFinite_weight r := by
  by_cases hz : r = 0
  · simp [degreeOnlyFinite_weight, hz]
  · have hp : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hz
    have h1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hdiv : 1 / (r : ℝ) ≤ 1 := (div_le_one hp).mpr h1
    simp only [degreeOnlyFinite_weight, if_neg hz]
    linarith

lemma degreeOnlyFinite_weight_correction {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    degreeOnlyFinite_weight (truncatedDegree d i) = 1 + degreeCorrection d i := by
  unfold degreeOnlyFinite_weight degreeCorrection
  split <;> ring

lemma degreeOnlyFinite_weight_max (r : ℕ) :
    max 1 (2*(r : ℝ)) = 1 + degreeOnlyFinite_weight r * r := by
  by_cases hz : r = 0
  · simp [degreeOnlyFinite_weight, hz]
  · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hne : (r : ℝ) ≠ 0 := by exact_mod_cast hz
    rw [max_eq_right (by linarith : (1 : ℝ) ≤ 2*r)]
    simp only [degreeOnlyFinite_weight, if_neg hz]
    field_simp
    <;> ring

lemma degreeOnlyFinite_weight_cost (r : ℕ) (hr : 1 ≤ r) :
    degreeOnlyFinite_weight r * (r : ℝ)^2 + 2*r*(r+1) = 4*(r : ℝ)^2+r := by
  have hz : r ≠ 0 := by omega
  have hne : (r : ℝ) ≠ 0 := by exact_mod_cast hz
  rw [degreeOnlyFinite_weight, if_neg hz]
  field_simp
  <;> ring

lemma degreeOnlyFinite_maxAbs_nonneg {n : ℕ} (e : Fin n → ℝ) : 0 ≤ maxAbs e := by
  exact NNReal.coe_nonneg _

lemma degreeOnlyFinite_abs_le_maxAbs {n : ℕ} (e : Fin n → ℝ) (i : Fin n) :
    |e i| ≤ maxAbs e := by
  exact Finset.le_sup (f := fun j => (⟨|e j|, abs_nonneg (e j)⟩ : ℝ≥0))
    (Finset.mem_univ i)

lemma degreeOnlyFinite_compatible {n : ℕ} (d : Fin n → ℕ) (H : Graph n)
    (hd : ∀ i, degree H i ≤ truncatedDegree d i) : Compatible (emptyGraph n) d H := by
  constructor
  · intro i j hij; simp [emptyGraph] at hij
  · intro i; exact (hd i).trans (min_le_left _ _)

lemma degreeOnlyFinite_loss_nonneg {n : ℕ} (c : Fin n → ℕ) (w : ℕ → ℝ)
    (hw : ∀ r, 0 ≤ w r) (H : Graph n) (hd : ∀ i, degree H i ≤ c i) (e : Fin n → ℝ) :
    0 ≤ degreeOnlyFinite_loss Finset.univ c w H e := by
  apply add_nonneg _ (degreeOnlyFinite_penalty_nonneg H e)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (sq_nonneg _)
  apply mul_nonneg (hw _)
  exact sub_nonneg.mpr (Nat.cast_le.mpr (hd i))

lemma degreeOnlyFinite_ordinary_loss {n : ℕ} (d : Fin n → ℕ) (H : Graph n)
    (e : Fin n → ℝ) :
    degreeOnlyFinite_loss Finset.univ (truncatedDegree d) (fun _ => 1) H e =
      (∑ i, (truncatedDegree d i : ℝ) * e i^2) - quadratic (adjacency H) e := by
  rw [degreeOnlyFinite_edge_identity H e]
  unfold degreeOnlyFinite_loss
  simp only [one_mul, sub_mul, Finset.sum_sub_distrib]
  ring

lemma degreeOnlyFinite_ordinary_scale {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (H : Graph n) (x : Fin n → ℝ) :
    (n : ℝ) * (VYoung d x - V1 H x) =
      degreeOnlyFinite_loss Finset.univ (truncatedDegree d) (fun _ => 1) H (centered x) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [degreeOnlyFinite_ordinary_loss]
  unfold VYoung V1
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  field_simp
  <;> ring

lemma degreeOnlyFinite_corrected_loss {n : ℕ} (d : Fin n → ℕ) (H : Graph n)
    (e : Fin n → ℝ) :
    degreeOnlyFinite_loss Finset.univ (truncatedDegree d) degreeOnlyFinite_weight H e =
      (∑ i, max 1 (2*(truncatedDegree d i : ℝ)) * e i^2) -
        ((∑ i, e i^2) + quadratic (adjacency H) e +
          ∑ i, degreeCorrection d i * degree H i * e i^2) := by
  have hp : degreeOnlyFinite_penalty H e =
      (∑ i, (degree H i : ℝ) * e i^2) - quadratic (adjacency H) e := by
    have hh := degreeOnlyFinite_edge_identity H e
    linarith
  have he (i : Fin n) :
      degreeOnlyFinite_weight (truncatedDegree d i) *
          ((truncatedDegree d i : ℝ) - degree H i) * e i^2 + (degree H i : ℝ) * e i^2 =
        max 1 (2*(truncatedDegree d i : ℝ)) * e i^2 - e i^2 -
          degreeCorrection d i * degree H i * e i^2 := by
    rw [degreeOnlyFinite_weight_max, degreeOnlyFinite_weight_correction]
    ring
  unfold degreeOnlyFinite_loss
  rw [hp]
  calc
    _ = (∑ i, (degreeOnlyFinite_weight (truncatedDegree d i) *
          ((truncatedDegree d i : ℝ) - degree H i) * e i^2 + (degree H i : ℝ) * e i^2)) -
        quadratic (adjacency H) e := by rw [Finset.sum_add_distrib]; ring
    _ = _ := by simp_rw [he, Finset.sum_sub_distrib]; ring

lemma degreeOnlyFinite_corrected_scale {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (H : Graph n) (x : Fin n → ℝ) :
    (∑ i, max 1 (2*(truncatedDegree d i : ℝ)) * centered x i^2)/n - (n : ℝ)*V1plus d H x =
      degreeOnlyFinite_loss Finset.univ (truncatedDegree d) degreeOnlyFinite_weight H (centered x) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [degreeOnlyFinite_corrected_loss]
  unfold V1plus V1
  field_simp
  <;> ring

lemma degreeOnlyFinite_ordinary_witness {n : ℕ} (d : Fin n → ℕ) (D : ℕ)
    (hd : ∀ i, truncatedDegree d i ≤ D) (e : Fin n → ℝ) :
    ∃ H : Graph n, Compatible (emptyGraph n) d H ∧
      degreeOnlyFinite_loss Finset.univ (truncatedDegree d) (fun _ => 1) H e ≤
        maxAbs e^2 * (∑ r ∈ Finset.Icc 1 D, (3*(r : ℝ)^2+2*r)) := by
  obtain ⟨H, hH, hdH, hlH⟩ := degreeOnlyFinite_capped_cliques (truncatedDegree d)
    (fun _ => 1) (by intros; norm_num) e (maxAbs e) (degreeOnlyFinite_maxAbs_nonneg e)
    D Finset.univ (fun i _ => hd i) (fun i _ => degreeOnlyFinite_abs_le_maxAbs e i)
  refine ⟨H, degreeOnlyFinite_compatible d H (fun i => hdH i (Finset.mem_univ i)), ?_⟩
  convert hlH using 2
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma degreeOnlyFinite_corrected_witness {n : ℕ} (d : Fin n → ℕ) (D : ℕ)
    (hd : ∀ i, truncatedDegree d i ≤ D) (e : Fin n → ℝ) :
    ∃ H : Graph n, Compatible (emptyGraph n) d H ∧
      degreeOnlyFinite_loss Finset.univ (truncatedDegree d) degreeOnlyFinite_weight H e ≤
        maxAbs e^2 * (∑ r ∈ Finset.Icc 1 D, (4*(r : ℝ)^2+r)) := by
  obtain ⟨H, hH, hdH, hlH⟩ := degreeOnlyFinite_capped_cliques (truncatedDegree d)
    degreeOnlyFinite_weight (fun r _ => degreeOnlyFinite_weight_nonneg r)
    e (maxAbs e) (degreeOnlyFinite_maxAbs_nonneg e) D Finset.univ
    (fun i _ => hd i) (fun i _ => degreeOnlyFinite_abs_le_maxAbs e i)
  refine ⟨H, degreeOnlyFinite_compatible d H (fun i => hdH i (Finset.mem_univ i)), ?_⟩
  convert hlH using 2
  apply Finset.sum_congr rfl
  intro r hr
  exact (degreeOnlyFinite_weight_cost r (Finset.mem_Icc.mp hr).1).symm

/-- The exact finite degree-only comparison, including both loss constants. -/
theorem degree_only_finite_proof {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (D : ℕ)
    (hd : ∀ i, truncatedDegree d i ≤ D) (x : Fin n → ℝ) (A Ap : Graph n)
    (hm : Maximizes (emptyGraph n) d (fun B => V1 B x) A)
    (hp : Maximizes (emptyGraph n) d (fun B => V1plus d B x) Ap) :
    (∀ (B : Graph n) (z : Fin n → ℝ), quadratic (adjacency B) z =
      (∑ i, (degree B i : ℝ)*z i^2) - upperSum (fun i j => adjacency B i j*(z i-z j)^2)) ∧
    (0 ≤ (n : ℝ)*(VYoung d x-V1 A x) ∧
      (n : ℝ)*(VYoung d x-V1 A x) ≤
        (∑ r ∈ Finset.Icc 1 D, (3*(r : ℝ)^2+2*r))*maxAbs (centered x)^2/n) ∧
    (0 ≤ (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ∧
      (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ≤
        maxAbs (centered x)^2/n*(∑ r ∈ Finset.Icc 1 D, (4*(r : ℝ)^2+r))) := by
  have hnle : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro B z
    have hh := (graph_laplacian_identity B z).2
    have heq : quadratic (Matrix.diagonal (fun i => (degree B i : ℝ)) - adjacency B) z =
        (∑ i, (degree B i : ℝ)*z i^2) - quadratic (adjacency B) z := by
      simp [quadratic, Matrix.sub_apply, Matrix.diagonal_apply, sub_mul,
        Finset.sum_sub_distrib, pow_two, mul_assoc]
    rw [heq] at hh
    linarith
  · exact mul_nonneg hnle (sub_nonneg.mpr (young_bound_finite _ A d hm.1 x))
  · obtain ⟨H, hH, hlH⟩ := degreeOnlyFinite_ordinary_witness d D hd (centered x)
    calc
      (n : ℝ)*(VYoung d x-V1 A x) ≤ (n : ℝ)*(VYoung d x-V1 H x) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left (hm.2 H hH) _) hnle
      _ = degreeOnlyFinite_loss Finset.univ (truncatedDegree d) (fun _ => 1) H (centered x) / n :=
        degreeOnlyFinite_ordinary_scale hn d H x
      _ ≤ (maxAbs (centered x)^2 *
          (∑ r ∈ Finset.Icc 1 D, (3*(r : ℝ)^2+2*r))) / n :=
        div_le_div_of_nonneg_right hlH hnle
      _ = _ := by ring
  · rw [degreeOnlyFinite_corrected_scale hn d Ap x]
    apply div_nonneg _ hnle
    exact degreeOnlyFinite_loss_nonneg (truncatedDegree d) degreeOnlyFinite_weight
      degreeOnlyFinite_weight_nonneg Ap
      (compatible_truncated_degree (emptyGraph n) Ap d hp.1) (centered x)
  · obtain ⟨H, hH, hlH⟩ := degreeOnlyFinite_corrected_witness d D hd (centered x)
    calc
      (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ≤
          (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d H x :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left (hp.2 H hH) hnle) _
      _ = degreeOnlyFinite_loss Finset.univ (truncatedDegree d) degreeOnlyFinite_weight H (centered x) / n :=
        degreeOnlyFinite_corrected_scale hn d H x
      _ ≤ (maxAbs (centered x)^2 *
          (∑ r ∈ Finset.Icc 1 D, (4*(r : ℝ)^2+r))) / n :=
        div_le_div_of_nonneg_right hlH hnle
      _ = _ := by ring

end
end AronowAudit.P011.Wave1
