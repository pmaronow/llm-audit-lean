import AronowAudit.P011.P011_Audit
import Mathlib.Data.Fintype.Prod

namespace AronowAudit.P011.CliqueCompletion
open scoped BigOperators Matrix
noncomputable section

theorem oracle_apply {n : ℕ} (A : Graph n) (i j : Fin n) :
    oracleMatrix A i j = if i = j ∨ A.val i j = true then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [oracleMatrix, adjacency, Matrix.one_apply, A.property.2]
  · cases ha : A.val i j <;> simp [oracleMatrix, adjacency, Matrix.one_apply, hij, ha]

theorem psd_mathlib {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : PSD M) :
    M.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simpa using hM.1 j i
  · intro x
    simpa [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using hM.2 x

theorem adjacent_columns {n : ℕ} (A : Graph n) (hp : PSD (oracleMatrix A))
    (i j : Fin n) (hij : A.val i j = true) (k : Fin n) :
    oracleMatrix A k i = oracleMatrix A k j := by
  let v : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
  have hji : A.val j i = true := (A.property.1 j i).trans hij
  have hq : star v ⬝ᵥ ((oracleMatrix A) *ᵥ v) = 0 := by
    simp [v, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
      Matrix.mulVec_single_one, single_dotProduct, oracle_apply, hij, hji]
  have hz := (psd_mathlib _ hp).dotProduct_mulVec_zero_iff.mp hq
  have hk := congrFun hz k
  have hk' : oracleMatrix A k i - oracleMatrix A k j = 0 := by
    simpa [v, Matrix.mulVec_sub, Matrix.mulVec_single_one] using hk
  exact sub_eq_zero.mp hk'

theorem clique_of_psd {n : ℕ} (A : Graph n) (hp : PSD (oracleMatrix A)) :
    CliqueUnion A := by
  intro i j k hij hjk
  rcases hij with h | hij
  · subst j; exact hjk
  rcases hjk with h | hjk
  · subst k; exact Or.inr hij
  have he := adjacent_columns A hp j k hjk i
  have h1 : oracleMatrix A i j = 1 := by simp [oracle_apply, hij]
  have h2 : oracleMatrix A i k = 1 := he.symm.trans h1
  by_contra h
  simpa [oracle_apply, h] using h2

theorem labels_exist {n : ℕ} (A : Graph n) (hA : CliqueUnion A) :
    ∃ C : Fin n → ℕ, ∀ i j, A.val i j = true ↔ i ≠ j ∧ C i = C j := by
  let s : Setoid (Fin n) := {
    r := fun i j => i = j ∨ A.val i j = true
    iseqv := ⟨fun _ => Or.inl rfl,
      by intro i j h; rcases h with h | h
         · exact Or.inl h.symm
         · exact Or.inr ((A.property.1 j i).trans h),
      by intro i j k hij hjk; exact hA i j k hij hjk⟩ }
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  let e := Fintype.equivFin (Quotient s)
  let C : Fin n → ℕ := fun i => (e (Quotient.mk s i)).val
  have hc (i j : Fin n) : C i = C j ↔ i = j ∨ A.val i j = true := by
    constructor
    · intro h
      have hq : Quotient.mk s i = Quotient.mk s j := by
        apply e.injective
        apply Fin.ext
        exact h
      exact Quotient.exact hq
    · intro h
      have hq : Quotient.mk s i = Quotient.mk s j := Quotient.sound h
      exact congrArg (fun q => (e q).val) hq
  refine ⟨C, ?_⟩
  intro i j
  constructor
  · intro hij
    refine ⟨?_, (hc i j).mpr (Or.inr hij)⟩
    intro he
    subst j
    simp [A.property.2] at hij
  · rintro ⟨hne, h⟩
    exact ((hc i j).mp h).resolve_left hne

theorem quadratic_labels {n : ℕ} (A : Graph n) (C : Fin n → ℕ)
    (hC : ∀ i j, A.val i j = true ↔ i ≠ j ∧ C i = C j) (x : Fin n → ℝ) :
    quadratic (oracleMatrix A) x =
      ∑ c ∈ Finset.univ.image C, (∑ i with C i = c, x i)^2 := by
  have hm (i j : Fin n) : oracleMatrix A i j = if C i = C j then 1 else 0 := by
    rw [oracle_apply]
    by_cases hij : i = j
    · subst j; simp
    · have he : (A.val i j = true) ↔ C i = C j := by simpa [hij] using hC i j
      simp only [hij, false_or, he]
  let f : Fin n → ℝ := fun i => x i * ∑ j with C j = C i, x j
  have hf : quadratic (oracleMatrix A) x = ∑ i, f i := by
    unfold quadratic
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    rw [Finset.mul_sum]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rw [hm]
    by_cases he : C i = C j
    · rw [if_pos he, if_pos he.symm]
      ring
    · rw [if_neg he, if_neg (Ne.symm he)]
      ring
  rw [hf]
  have hmap : ∀ i ∈ (Finset.univ : Finset (Fin n)), C i ∈ Finset.univ.image C := by
    intro i _
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image C) (g := C) hmap f]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ i ∈ Finset.univ with C i = c, f i) =
        ∑ i ∈ Finset.univ with C i = c, x i * (∑ j with C j = c, x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      rw [(Finset.mem_filter.mp hi).2]
    _ = (∑ i with C i = c, x i) * (∑ j with C j = c, x j) := by rw [Finset.sum_mul]
    _ = _ := by ring

theorem psd_of_clique {n : ℕ} (A : Graph n) (hA : CliqueUnion A) :
    PSD (oracleMatrix A) := by
  obtain ⟨C, hC⟩ := labels_exist A hA
  constructor
  · intro i j
    simp only [oracleMatrix, Matrix.add_apply, adjacency, Matrix.one_apply]
    rw [A.property.1 i j]
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij]
  · intro x
    rw [quadratic_labels A C hC]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem clique_characterization_completed {n : ℕ} (A : Graph n) :
    (PSD (oracleMatrix A) ↔ CliqueUnion A) ∧
    (∀ C : Fin n → ℕ,
      (∀ i j, A.val i j = true ↔ i ≠ j ∧ C i = C j) →
      ∀ x : Fin n → ℝ, V1 A x =
        (∑ c ∈ Finset.univ.image C, (∑ i with C i = c, centered x i)^2) / (n : ℝ)^2) := by
  refine ⟨⟨clique_of_psd A, psd_of_clique A⟩, ?_⟩
  intro C hC x
  rw [← variance_form_oracle]
  unfold varianceForm
  rw [quadratic_labels A C hC]

end
end AronowAudit.P011.CliqueCompletion

namespace AronowAudit.P011
theorem clique_characterization {n : ℕ} (A : Graph n) :
    (PSD (oracleMatrix A) ↔ CliqueUnion A) ∧
    (∀ C : Fin n → ℕ,
      (∀ i j, A.val i j = true ↔ i ≠ j ∧ C i = C j) →
      ∀ x : Fin n → ℝ, V1 A x =
        (∑ c ∈ Finset.univ.image C, (∑ i with C i = c, centered x i)^2) / (n : ℝ)^2) := by
  exact CliqueCompletion.clique_characterization_completed A
end AronowAudit.P011

namespace AronowAudit.P011.LpCompletion
open scoped BigOperators
noncomputable section

theorem edge_sum {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ e : Edge n, f e.val.1 e.val.2) = upperSum f := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by intro p; simp) (fun p => f p.1 p.2)]
  simp [Finset.sum_filter, Fintype.sum_prod_type, upperSum]

theorem fromUpper_entry {n : ℕ} (a : Edge n → Bool) (e : Edge n) :
    (fromUpper a).val e.val.1 e.val.2 = a e := by
  simp [fromUpper, e.property]

theorem adjacency_entry {n : ℕ} (a : Edge n → Bool) (e : Edge n) :
    adjacency (fromUpper a) e.val.1 e.val.2 = if a e then 1 else 0 := by
  simp [adjacency, fromUpper_entry]

theorem degree_incidence {n : ℕ} (A : Graph n) (i : Fin n) :
    (degree A i : ℝ) =
      ∑ e : Edge n, if e.val.1 = i ∨ e.val.2 = i then adjacency A e.val.1 e.val.2 else 0 := by
  have h := degree_weight_sum A (fun j => if j = i then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← edge_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : e.val.1 = i
  · have hj : e.val.2 ≠ i := by have he := e.property; intro hh; rw [hi, hh] at he; exact (lt_irrefl _) he
    simp [hi, hj]
  · by_cases hj : e.val.2 = i <;> simp [hi, hj]

def relaxedEmbedding {n : ℕ} (a : Edge n → Bool) : Edge n → ℝ :=
  fun e => if a e then 1 else 0

theorem embedding_feasible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (a : Edge n → Bool)
    (ha : Compatible R d (fromUpper a)) : RelaxedFeasible R d (relaxedEmbedding a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; cases he : a e <;> simp [relaxedEmbedding, he]
  · intro e he
    have hh := ha.1 e.val.1 e.val.2 he
    rw [fromUpper_entry] at hh
    simp [relaxedEmbedding, hh]
  · intro i
    have h := Nat.cast_le (α := ℝ).mpr (ha.2 i)
    rw [degree_incidence] at h
    simpa only [adjacency_entry, relaxedEmbedding] using h

theorem embedding_objective {n : ℕ} (a : Edge n → Bool) (w : Edge n → ℝ) :
    relaxedObjective (relaxedEmbedding a) w = upperObjective a w := by
  unfold relaxedObjective upperObjective
  apply Finset.sum_congr rfl
  intro e _
  cases he : a e <;> simp [relaxedEmbedding, he]

theorem adjacency_quadratic {n : ℕ} (a : Edge n → Bool) (x : Fin n → ℝ) :
    quadratic (adjacency (fromUpper a)) x =
      2 * upperObjective a (fun e => x e.val.1 * x e.val.2) := by
  rw [quadratic, ordered_pair_sum _ (by intro i; simp [adjacency, (fromUpper a).property.2])]
  rw [← edge_sum]
  unfold upperObjective
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hs : adjacency (fromUpper a) e.val.2 e.val.1 = adjacency (fromUpper a) e.val.1 e.val.2 := by
    unfold adjacency
    rw [(fromUpper a).property.1]
  rw [hs, adjacency_entry]
  cases he : a e <;> simp [he] <;> ring

theorem adjacency_sum {n : ℕ} (a : Edge n → Bool) :
    (∑ i, ∑ j, adjacency (fromUpper a) i j) = 2 * upperObjective a (fun _ => 1) := by
  simpa [quadratic] using adjacency_quadratic a (fun _ => 1)

theorem estimator_reconstruction {n : ℕ} (hn : 0 < n) (a : Edge n → Bool) (x : Fin n → ℝ) :
    (n : ℝ)^2 * V1 (fromUpper a) x =
      (n : ℝ) * sampleVariance x + 2 * upperObjective a (fun e => centered x e.val.1 * centered x e.val.2) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold V1 sampleVariance
  rw [adjacency_quadratic]
  field_simp

theorem relaxation_upper_bound_completed {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ)
    (w : Edge n → ℝ) (U : ℝ)
    (hU : ∀ a, RelaxedFeasible R d a → relaxedObjective a w ≤ U) :
    (∀ a : Edge n → Bool, Compatible R d (fromUpper a) → upperObjective a w ≤ U) ∧
    (∀ x a, Compatible R d (fromUpper a) →
      (∀ e, w e = centered x e.val.1*centered x e.val.2) →
      V1 (fromUpper a) x ≤ ((n : ℝ)*sampleVariance x+2*U)/(n : ℝ)^2) ∧
    ((∀ e, w e = 1) → ∀ x a, Compatible R d (fromUpper a) →
      V2 (fromUpper a) x ≤ sampleVariance x/n*(1+2*U/n)) := by
  have hbound (a : Edge n → Bool) (ha : Compatible R d (fromUpper a)) : upperObjective a w ≤ U := by
    simpa [embedding_objective] using hU (relaxedEmbedding a) (embedding_feasible R d a ha)
  refine ⟨hbound, ?_, ?_⟩
  · intro x a ha hw
    have h := hbound a ha
    have he : w = fun e => centered x e.val.1 * centered x e.val.2 := funext hw
    rw [he] at h
    have hre := estimator_reconstruction hn a x
    apply (le_div_iff₀ (show 0 < (n : ℝ)^2 by positivity)).mpr
    rw [mul_comm, hre]
    linarith
  · intro hw x a ha
    have h := hbound a ha
    have he : w = fun _ => 1 := funext hw
    rw [he] at h
    unfold V2
    rw [adjacency_sum]
    have hs : 0 ≤ sampleVariance x / (n : ℝ) :=
      div_nonneg (sample_variance_nonnegative x) (Nat.cast_nonneg n)
    apply mul_le_mul_of_nonneg_left _ hs
    gcongr

end
end AronowAudit.P011.LpCompletion

namespace AronowAudit.P011

theorem relaxation_upper_bound {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ)
    (w : Edge n → ℝ) (U : ℝ)
    (hU : ∀ a, RelaxedFeasible R d a → relaxedObjective a w ≤ U) :
    (∀ a : Edge n → Bool, Compatible R d (fromUpper a) → upperObjective a w ≤ U) ∧
    (∀ x a, Compatible R d (fromUpper a) →
      (∀ e, w e = centered x e.val.1*centered x e.val.2) →
      V1 (fromUpper a) x ≤ ((n : ℝ)*sampleVariance x+2*U)/(n : ℝ)^2) ∧
    ((∀ e, w e = 1) → ∀ x a, Compatible R d (fromUpper a) →
      V2 (fromUpper a) x ≤ sampleVariance x/n*(1+2*U/n)) := by
  exact LpCompletion.relaxation_upper_bound_completed hn R d w U hU

end AronowAudit.P011

namespace AronowAudit.P011.UpperCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
attribute [local instance] Classical.propDecidable

theorem to_from {n : ℕ} (a : Edge n → Bool) : toUpper (fromUpper a)=a := by
  funext e
  exact LpCompletion.fromUpper_entry a e

theorem from_to {n : ℕ} (A : Graph n) : fromUpper (toUpper A)=A := by
  apply Subtype.ext
  funext i j
  by_cases hij : i < j
  · simp [fromUpper, toUpper, hij]
  · by_cases hji : j < i
    · simp [fromUpper, toUpper, hij, hji, A.property.1]
    · have h : i=j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [fromUpper, A.property.2]

theorem bijective {n : ℕ} : Function.Bijective (@fromUpper n) :=
  ⟨Function.LeftInverse.injective to_from, Function.RightInverse.surjective from_to⟩

theorem degree_upper {n : ℕ} (a : Edge n → Bool) (i : Fin n) :
    degree (fromUpper a) i = upperDegree a i := by
  have h := LpCompletion.degree_incidence (fromUpper a) i
  have he : (upperDegree a i : ℝ) =
      ∑ e : Edge n, if e.val.1=i ∨ e.val.2=i then adjacency (fromUpper a) e.val.1 e.val.2 else 0 := by
    unfold upperDegree
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    cases ha : a e <;> by_cases hi : e.val.1=i ∨ e.val.2=i <;>
      simp [ha, hi, LpCompletion.adjacency_entry]
  exact_mod_cast h.trans he.symm

theorem compatible_upper {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (a : Edge n → Bool) :
    Compatible R d (fromUpper a) ↔
      (∀ e, toUpper R e=true → a e=true) ∧ ∀ i, upperDegree a i ≤ d i := by
  constructor
  · intro h
    constructor
    · intro e he
      simpa only [LpCompletion.fromUpper_entry] using h.1 e.val.1 e.val.2 he
    · intro i
      simpa only [degree_upper] using h.2 i
  · rintro ⟨hedge,hdegree⟩
    constructor
    · intro i j hij
      by_cases hlt : i < j
      · have h := hedge ⟨(i,j),hlt⟩ hij
        simpa [fromUpper, hlt] using h
      · by_cases hgt : j < i
        · have hr : R.val j i=true := (R.property.1 j i).trans hij
          have h := hedge ⟨(j,i),hgt⟩ hr
          simpa [fromUpper, hlt, hgt] using h
        · have h : i=j := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          subst j
          simp [R.property.2] at hij
    · intro i
      simpa only [degree_upper] using hdegree i

theorem maximizing_upper {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ)
    (a : Edge n → Bool) (x : Fin n → ℝ) :
    Maximizes R d (fun B => V1 B x) (fromUpper a) ↔
      Compatible R d (fromUpper a) ∧
        ∀ b, Compatible R d (fromUpper b) →
          upperObjective b (fun e => centered x e.val.1*centered x e.val.2) ≤
          upperObjective a (fun e => centered x e.val.1*centered x e.val.2) := by
  have hn2 : 0 < (n:ℝ)^2 := by positivity
  have ha := LpCompletion.estimator_reconstruction hn a x
  constructor
  · rintro ⟨hcomp,hmax⟩
    refine ⟨hcomp, ?_⟩
    intro b hb
    have h := mul_le_mul_of_nonneg_left (hmax (fromUpper b) hb) hn2.le
    have hb := LpCompletion.estimator_reconstruction hn b x
    nlinarith
  · rintro ⟨hcomp,hmax⟩
    refine ⟨hcomp, ?_⟩
    intro B hB
    have h := hmax (toUpper B) (by simpa only [from_to] using hB)
    have hb := LpCompletion.estimator_reconstruction hn (toUpper B) x
    rw [from_to] at hb
    nlinarith

theorem edge_card (n : ℕ) : Fintype.card (Edge n)=n*(n-1)/2 := by
  simpa only [Fintype.card_subtype, Fintype.card_fin, Nat.choose_two_right] using
    (Fintype.card_product_filter_lt (α := Fin n))

theorem upper_program_completed {n : ℕ} (hn : 0 < n) :
    Function.Bijective (@fromUpper n) ∧
    (∀ a : Edge n → Bool, ∀ x : Fin n → ℝ,
      quadratic (adjacency (fromUpper a)) (centered x) =
        2*upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
    (∀ a : Edge n → Bool, ∀ i, degree (fromUpper a) i = upperDegree a i) ∧
    (∀ R : Graph n, ∀ d a, Compatible R d (fromUpper a) ↔
      (∀ e, toUpper R e = true → a e = true) ∧ ∀ i, upperDegree a i ≤ d i) ∧
    (∀ R : Graph n, ∀ d a x,
      Maximizes R d (fun B => V1 B x) (fromUpper a) ↔
      Compatible R d (fromUpper a) ∧
        ∀ b, Compatible R d (fromUpper b) →
          upperObjective b (fun e => centered x e.val.1*centered x e.val.2) ≤
          upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
    (∀ (a : Edge n → Bool) (x : Fin n → ℝ), (n : ℝ)^2*V1 (fromUpper a) x = (n : ℝ)*sampleVariance x+
      2*upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
    (∀ a : Edge n → Bool, ∑ i, ∑ j, adjacency (fromUpper a) i j = 2*upperObjective a (fun _ => 1)) ∧
    Fintype.card (Edge n) = n*(n-1)/2 := by
  exact ⟨bijective, fun a x => LpCompletion.adjacency_quadratic a (centered x),
    degree_upper, compatible_upper, maximizing_upper hn,
    LpCompletion.estimator_reconstruction hn, LpCompletion.adjacency_sum, edge_card n⟩

end
end AronowAudit.P011.UpperCompletion

namespace AronowAudit.P011
theorem upper_program_equivalence {n : ℕ} (hn : 0 < n) :
    Function.Bijective (@fromUpper n) ∧
    (∀ a : Edge n → Bool, ∀ x : Fin n → ℝ,
      quadratic (adjacency (fromUpper a)) (centered x) =
        2*upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
    (∀ a : Edge n → Bool, ∀ i, degree (fromUpper a) i = upperDegree a i) ∧
    (∀ R : Graph n, ∀ d a, Compatible R d (fromUpper a) ↔
      (∀ e, toUpper R e = true → a e = true) ∧ ∀ i, upperDegree a i ≤ d i) ∧
    (∀ R : Graph n, ∀ d a x,
      Maximizes R d (fun B => V1 B x) (fromUpper a) ↔
      Compatible R d (fromUpper a) ∧
        ∀ b, Compatible R d (fromUpper b) →
          upperObjective b (fun e => centered x e.val.1*centered x e.val.2) ≤
          upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
    (∀ (a : Edge n → Bool) (x : Fin n → ℝ), (n : ℝ)^2*V1 (fromUpper a) x = (n : ℝ)*sampleVariance x+
      2*upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
    (∀ a : Edge n → Bool, ∑ i, ∑ j, adjacency (fromUpper a) i j = 2*upperObjective a (fun _ => 1)) ∧
    Fintype.card (Edge n) = n*(n-1)/2 := by
  exact UpperCompletion.upper_program_completed hn
end AronowAudit.P011

namespace AronowAudit.P011.GapCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
attribute [-simp] Finset.sum_boole
attribute [local instance] Classical.propDecidable

theorem incidence_total {n : ℕ} (a : Edge n → ℝ) :
    (∑ i, ∑ e : Edge n, if e.val.1=i ∨ e.val.2=i then a e else 0) = 2*∑ e, a e := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  calc
    _ = (∑ i, if e.val.1=i then a e else 0)+(∑ i, if e.val.2=i then a e else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h1 : e.val.1=i <;> by_cases h2 : e.val.2=i <;> simp_all
    _ = _ := by simp; ring

theorem unit_capacity_bound {n : ℕ} (R : Graph n) (a w : Edge n → ℝ)
    (ha : RelaxedFeasible R (fun _ => 1) a) (hw : ∀ e, w e ≤ 1) :
    relaxedObjective a w ≤ (n:ℝ)/2 := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => ha.2.2 i)
  rw [incidence_total] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Nat.cast_one] at hsum
  have ho : relaxedObjective a w ≤ ∑ e, a e := by
    apply Finset.sum_le_sum
    intro e _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw e) (ha.1 e).1
  linarith

theorem upper_objective_formula {n : ℕ} (a : Edge n → Bool) (x : Fin n → ℝ) :
    upperObjective a (fun e => x e.val.1*x e.val.2) =
      upperSum (fun i j => adjacency (fromUpper a) i j*x i*x j) := by
  rw [← LpCompletion.edge_sum]
  unfold upperObjective
  apply Finset.sum_congr rfl
  intro e _
  rw [LpCompletion.adjacency_entry]
  cases a e <;> simp

theorem triangle_capacity {n : ℕ} (A : Graph n) (h : ∀ i, degree A i ≤ 1)
    (i j k : Fin n) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    (if A.val i j then 1 else 0)+(if A.val i k then 1 else 0)+
      (if A.val j k then 1 else 0) ≤ (1:ℕ) := by
  have bound (u v w : Fin n) (huv : u≠v) (huw : u≠w) (hvw : v≠w) :
      (if A.val u v then 1 else 0)+(if A.val u w then 1 else 0) ≤ (1:ℕ) := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({v,w}:Finset (Fin n)) ⊆ Finset.univ from Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _) (f := fun x => if A.val u x then (1:ℕ) else 0)
    have hrow := h u
    have hpair : (∑ x ∈ ({v,w}:Finset (Fin n)), if A.val u x then (1:ℕ) else 0) =
        (if A.val u v then 1 else 0)+(if A.val u w then 1 else 0) := by rw [Finset.sum_pair hvw]
    rw [hpair] at hle
    exact le_trans hle hrow
  have h1 := bound i j k hij hik hjk
  have h2 := bound j i k hij.symm hjk hik
  have h3 := bound k i j hik.symm hjk.symm hij
  rw [A.property.1 j i] at h2
  rw [A.property.1 k i, A.property.1 k j] at h3
  omega

theorem six_integer_bound (a : Edge 6 → Bool)
    (ha : Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a)) :
    upperObjective a (fun e =>
      (![1,1,1,-1,-1,-1] : Fin 6 → ℝ) e.val.1 *
      (![1,1,1,-1,-1,-1] : Fin 6 → ℝ) e.val.2) ≤ 2 := by
  have h1 := triangle_capacity (fromUpper a) ha.2 0 1 2 (by decide) (by decide) (by decide)
  have h2 := triangle_capacity (fromUpper a) ha.2 3 4 5 (by decide) (by decide) (by decide)
  have hr1 : (if a ⟨(0,1),by decide⟩ then (1:ℝ) else 0)+
      (if a ⟨(0,2),by decide⟩ then 1 else 0)+(if a ⟨(1,2),by decide⟩ then 1 else 0) ≤ 1 := by
    exact_mod_cast h1
  have hr2 : (if a ⟨(3,4),by decide⟩ then (1:ℝ) else 0)+
      (if a ⟨(3,5),by decide⟩ then 1 else 0)+(if a ⟨(4,5),by decide⟩ then 1 else 0) ≤ 1 := by
    exact_mod_cast h2
  have hneg (e : Edge 6) : (if a e then (-1:ℝ) else 0) = -(if a e then (1:ℝ) else 0) := by
    cases a e <;> norm_num
  rw [upper_objective_formula]
  norm_num [upperSum, Finset.sum_filter, Fin.sum_univ_succ, adjacency, fromUpper]
  simp only [hneg, neg_neg]
  have hnon : ∀ e : Edge 6, (0:ℝ) ≤ if a e then 1 else 0 := by
    intro e; cases a e <;> norm_num
  linarith [hnon ⟨(0,3),by decide⟩, hnon ⟨(0,4),by decide⟩,
    hnon ⟨(0,5),by decide⟩, hnon ⟨(1,3),by decide⟩, hnon ⟨(1,4),by decide⟩,
    hnon ⟨(1,5),by decide⟩, hnon ⟨(2,3),by decide⟩, hnon ⟨(2,4),by decide⟩,
    hnon ⟨(2,5),by decide⟩]


theorem edge_sum_any {n : ℕ} (f : Edge n → ℝ) :
    (∑ e, f e) = upperSum (fun i j => if h : i < j then f ⟨(i,j),h⟩ else 0) := by
  rw [← LpCompletion.edge_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp [e.property]

def x6 : Fin 6 → ℝ := ![1,1,1,-1,-1,-1]
def a6 : Edge 6 → Bool := fun e => decide (e.val=(0,1) ∨ e.val=(3,4))

theorem six_relaxed : RelaxedFeasible (emptyGraph 6) (fun _ => 1)
    (fun e => if x6 e.val.1=x6 e.val.2 then 1/2 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    dsimp only
    split_ifs <;> norm_num
  · intro e h
    simp [toUpper, emptyGraph] at h
  · intro i
    rw [edge_sum_any]
    norm_num only [Nat.cast_one]
    fin_cases i <;> norm_num [upperSum, Finset.sum_filter, Fin.sum_univ_succ, x6]


theorem six_witness : Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a6) ∧
    upperObjective a6 (fun e => x6 e.val.1*x6 e.val.2) = 2 ∧
    V1 (fromUpper a6) x6 = 5/18 := by
  constructor
  · constructor
    · intro i j h; simp [emptyGraph] at h
    · intro i
      fin_cases i <;> norm_num [degree, fromUpper, a6, Fin.sum_univ_succ]
  · constructor
    · rw [upper_objective_formula]
      norm_num [upperSum, Finset.sum_filter, Fin.sum_univ_succ, adjacency, fromUpper, a6, x6]
    · norm_num [V1, centered, average, quadratic, adjacency, fromUpper, a6, x6,
        Fin.sum_univ_succ]

theorem three_integer_bound (A : Graph 3)
    (hA : Compatible (emptyGraph 3) (fun _ => 1) A) :
    (∑ i, ∑ j, adjacency A i j) ≤ 2 := by
  have h := triangle_capacity A hA.2 0 1 2 (by decide) (by decide) (by decide)
  have hr : (if A.val 0 1 then (1:ℝ) else 0)+(if A.val 0 2 then 1 else 0)+
      (if A.val 1 2 then 1 else 0) ≤ 1 := by exact_mod_cast h
  norm_num [Fin.sum_univ_succ, adjacency, A.property.2] 
  simp only [A.property.1 1 0, A.property.1 2 0, A.property.1 2 1]
  linarith

theorem three_relaxed : RelaxedFeasible (emptyGraph 3) (fun _ => 1) (fun _ => 1/2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; norm_num
  · intro e h; simp [toUpper, emptyGraph] at h
  · intro i
    rw [edge_sum_any]
    norm_num only [Nat.cast_one]
    fin_cases i <;> norm_num [upperSum, Finset.sum_filter, Fin.sum_univ_succ]

theorem three_witness : Compatible (emptyGraph 3) (fun _ => 1) edge12 ∧
    (∑ i, ∑ j, adjacency edge12 i j) = 2 := by
  constructor
  · constructor
    · intro i j h; simp [emptyGraph] at h
    · intro i; fin_cases i <;> norm_num [degree, edge12, Fin.sum_univ_succ]
  · norm_num [adjacency, edge12, Fin.sum_univ_succ]

theorem relaxation_gaps_completed :
    (let x : Fin 6 → ℝ := ![1,1,1,-1,-1,-1]
     let w : Edge 6 → ℝ := fun e => x e.val.1*x e.val.2
     let f : Edge 6 → ℝ := fun e => if x e.val.1=x e.val.2 then 1/2 else 0
     RelaxedFeasible (emptyGraph 6) (fun _ => 1) f ∧ relaxedObjective f w = 3 ∧
     (∀ a, RelaxedFeasible (emptyGraph 6) (fun _ => 1) a → relaxedObjective a w ≤ 3) ∧
     (∃ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) ∧
       upperObjective a w = 2 ∧ V1 (fromUpper a) x = 5/18) ∧
     (∀ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) → upperObjective a w ≤ 2) ∧
     ((6+2*3 : ℝ)/6^2=1/3)) ∧
    (RelaxedFeasible (emptyGraph 3) (fun _ => 1) (fun _ => 1/2) ∧
      relaxedObjective (fun _ => 1/2) (fun _ : Edge 3 => 1) = 3/2 ∧
      (∀ a, RelaxedFeasible (emptyGraph 3) (fun _ => 1) a → relaxedObjective a (fun _ => 1) ≤ 3/2) ∧
      (∃ A : Graph 3, Compatible (emptyGraph 3) (fun _ => 1) A ∧
        (∑ i, ∑ j, adjacency A i j) = 2) ∧
      (∀ A : Graph 3, Compatible (emptyGraph 3) (fun _ => 1) A →
        (∑ i, ∑ j, adjacency A i j) ≤ 2)) := by
  constructor
  · dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num⟩
    · convert six_relaxed using 1; ext e; simp [x6]
    · unfold relaxedObjective
      rw [edge_sum_any]
      norm_num [upperSum, Finset.sum_filter, Fin.sum_univ_succ]
    · intro a ha
      have h := unit_capacity_bound (emptyGraph 6) a
        (fun e => x6 e.val.1*x6 e.val.2) ha (by
          rintro ⟨⟨i,j⟩,hij⟩
          fin_cases i <;> fin_cases j <;> norm_num [x6])
      norm_num at h
      exact h
    · exact ⟨a6, six_witness⟩
    · exact six_integer_bound
  · refine ⟨three_relaxed, ?_, ?_, ⟨edge12, three_witness⟩, three_integer_bound⟩
    · unfold relaxedObjective
      rw [edge_sum_any]
      norm_num [upperSum, Finset.sum_filter, Fin.sum_univ_succ]
    · intro a ha
      simpa using unit_capacity_bound (emptyGraph 3) a (fun _ => 1) ha (fun _ => le_rfl)

end
end AronowAudit.P011.GapCompletion

namespace AronowAudit.P011
theorem relaxation_gaps :
    (let x : Fin 6 → ℝ := ![1,1,1,-1,-1,-1]
     let w : Edge 6 → ℝ := fun e => x e.val.1*x e.val.2
     let f : Edge 6 → ℝ := fun e => if x e.val.1=x e.val.2 then 1/2 else 0
     RelaxedFeasible (emptyGraph 6) (fun _ => 1) f ∧ relaxedObjective f w = 3 ∧
     (∀ a, RelaxedFeasible (emptyGraph 6) (fun _ => 1) a → relaxedObjective a w ≤ 3) ∧
     (∃ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) ∧
       upperObjective a w = 2 ∧ V1 (fromUpper a) x = 5/18) ∧
     (∀ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) → upperObjective a w ≤ 2) ∧
     ((6+2*3 : ℝ)/6^2=1/3)) ∧
    (RelaxedFeasible (emptyGraph 3) (fun _ => 1) (fun _ => 1/2) ∧
      relaxedObjective (fun _ => 1/2) (fun _ : Edge 3 => 1) = 3/2 ∧
      (∀ a, RelaxedFeasible (emptyGraph 3) (fun _ => 1) a → relaxedObjective a (fun _ => 1) ≤ 3/2) ∧
      (∃ A : Graph 3, Compatible (emptyGraph 3) (fun _ => 1) A ∧
        (∑ i, ∑ j, adjacency A i j) = 2) ∧
      (∀ A : Graph 3, Compatible (emptyGraph 3) (fun _ => 1) A →
        (∑ i, ∑ j, adjacency A i j) ≤ 2)) := by
  exact GapCompletion.relaxation_gaps_completed
end AronowAudit.P011

