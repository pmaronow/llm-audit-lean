import SAP.P001f.Defs.WholeW1
import SAP.P001f.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.WH.W1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Regroup actual observations by their covariate cells, including the
control-count identity and both estimator formulas. Expand the finite sums,
use `Finset.sum_comm` and `Finset.sum_eq_single` to select X i, then
`Finset.sum_div`, `Finset.sum_sub_distrib` and ring algebra. No probability
argument or denominator cancellation is needed. Expected size: 70–130 lines. -/
def T97_L1 : Prop :=
  ∀ {n : ℕ} {E : Type v} [Fintype E] [DecidableEq E]
    (X : Fin n → E) (D Y : Fin n → ℝ) (q : E → ℝ),
    (∀ x, wholeControlCount X D x = ∑ i, if X i = x then 1 - D i else 0) ∧
    wholeUnitIPW X D Y q =
      cellIPW n q (wholeTreatedSum X D Y) (wholeControlSum X D Y) ∧
    wholeCausalPlugin X D Y =
      cellPoststratification n (wholeTreatedCount X D) (wholeControlCount X D)
        (wholeTreatedSum X D Y) (wholeControlSum X D Y)

/-- Every pair of cell arm outcome sums is realizable by individual outcomes
in a binary sample with positive arm counts. Assign Y i = st(X i)/nt(X i)
in the treated arm and sc(X i)/nc(X i) in the control arm; factor each finite
cell sum and cancel its positive count. Binarity is essential. The type E is
the observed finite cell set. Expected size: 80–140 lines. -/
def T97_L2 : Prop :=
  ∀ {n : ℕ} {E : Type v} [Fintype E] [DecidableEq E]
    (X : Fin n → E) (D : Fin n → ℝ),
    (∀ i, D i = 0 ∨ D i = 1) →
    (∀ x, 0 < wholeTreatedCount X D x) →
    (∀ x, 0 < wholeControlCount X D x) →
    ∀ st sc : E → ℝ, ∃ Y : Fin n → ℝ,
      wholeTreatedSum X D Y = st ∧ wholeControlSum X D Y = sc

theorem T97_assembly (h1 : T97_L1.{v}) (h2 : T97_L2.{v}) :
    T97WholeStatement.{v} := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro n E _ _ hn X D q _ hD ht hc hq
    have hsize : ∀ x, wholeTreatedCount X D x + wholeControlCount X D x =
        wholeCellSize X x := by
      intro x
      unfold wholeControlCount
      ring
    have hs := Bridge.transportT97 n hn (wholeTreatedCount X D)
      (wholeControlCount X D) q ht hc hq
    simp only [hsize] at hs
    have hsuff : (∀ x, q x = wholeTreatedCount X D x / wholeCellSize X x) →
        ∀ Y, wholeUnitIPW X D Y q = wholeCausalPlugin X D Y := by
      intro hq' Y
      obtain ⟨_, hi, hp⟩ := h1 X D Y q
      rw [hi, hp]
      exact hs.mpr hq' _ _
    refine ⟨?_, hsuff, ?_⟩
    · intro Y
      obtain ⟨_, hi, hp⟩ := h1 X D Y q
      refine ⟨hi, ?_⟩
      simpa only [cellPoststratification, hsize] using hp
    · constructor
      · intro hall
        apply hs.mp
        intro st sc
        obtain ⟨Y, hst, hsc⟩ := h2 X D hD ht hc st sc
        obtain ⟨_, hi, hp⟩ := h1 X D Y q
        simpa only [hi, hp, hst, hsc] using hall Y
      · exact hsuff
  · simp only [wholeCausalPlugin, poststratifiedAverage, wholeCausalExampleX,
      exampleIndicator, exampleOutcome, Fin.sum_univ_succ]
    norm_num
  · simp only [wholeCausalPlugin, poststratifiedAverage, wholeCausalExampleX,
      exampleIndicator, exampleOutcome, Fin.sum_univ_succ]
    norm_num

theorem T101_assembly : T101WholeStatement.{u} := by
  classical
  constructor
  · intro Ω U A B hA hB
    have hcomp : (A ∪ B = U ∧ A ∩ B = ∅) ↔ A = U \ B := by
      constructor
      · rintro ⟨hcover, hdisj⟩
        ext x
        have he := Set.ext_iff.mp hcover x
        have hd := Set.ext_iff.mp hdisj x
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_empty_iff_false] at he hd
        simp only [Set.mem_sdiff]
        tauto
      · intro h
        subst A
        constructor <;> ext x
        · have hb : x ∈ B → x ∈ U := fun hx => hB hx
          simp only [Set.mem_union, Set.mem_sdiff]
          tauto
        · simp
    have herr : (A \ B = A ∪ (U \ B)) ↔ A = U \ B := by
      constructor
      · intro he
        ext x
        have hh := Set.ext_iff.mp he x
        have ha : x ∈ A → x ∈ U := fun hx => hA hx
        simp only [Set.mem_sdiff, Set.mem_union] at hh ⊢
        tauto
      · intro h
        subst A
        ext x
        simp only [Set.mem_sdiff, Set.mem_union]
        tauto
    refine ⟨rfl, ?_, herr.trans hcomp.symm, herr, hcomp⟩
    ext x
    have ha : x ∈ A → x ∈ U := fun hx => hA hx
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  · norm_num [Set.ext_iff]
    constructor <;> intro x <;> omega

theorem T108_assembly : T108WholeStatement.{u} := by
  classical
  intro Ω _ μ _ n hn X j hX hiid hid hj
  have hint : ∀ i, Integrable (X i) μ := fun i => (hid i).symm.integrable_snd hj
  have hEi : ∀ i, (∫ ω, X i ω ∂μ) = ∫ ω, X j ω ∂μ :=
    fun i => (hid i).integral_eq
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have havg : wholeFiniteAverage X = (fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω) := by
    funext ω
    simp only [wholeFiniteAverage, div_eq_mul_inv, mul_comm]
  have hsumi : Integrable (fun ω => ∑ i, X i ω) μ :=
    integrable_finsetSum _ (fun i _ => hint i)
  have hmean : (∫ ω, wholeFiniteAverage X ω ∂μ) = ∫ ω, X j ω ∂μ := by
    rw [havg, integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
    simp only [hEi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨hsumi.div_const _, hmean, ?_⟩
  intro hj2
  have h2 : ∀ i, MemLp (X i) 2 μ := fun i => (hid i).symm.memLp_snd hj2
  have hVi : ∀ i, variance (X i) μ = variance (X j) μ :=
    fun i => (hid i).variance_eq
  have havg2 : MemLp (wholeFiniteAverage X) 2 μ := by
    rw [havg]
    have hs : MemLp (∑ i, X i) 2 μ := memLp_finsetSum' _ (fun i _ => h2 i)
    simpa using hs.const_mul (n : ℝ)⁻¹
  have hvar : variance (wholeFiniteAverage X) μ = variance (X j) μ / n := by
    rw [havg, variance_const_mul]
    have hs : (fun ω => ∑ i, X i ω) = ∑ i, X i := by funext ω; simp
    rw [hs, IndepFun.variance_sum (fun i _ => h2 i)
      (fun i _ k _ hik => hiid.indepFun hik)]
    simp only [hVi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨havg2, hvar, ?_⟩
  intro _ ε hε
  have h := AronowAudit.P001.chebyshev_probability μ (wholeFiniteAverage X) havg2 ε hε
  change (μ {ω | ε ≤ |wholeFiniteAverage X ω - ∫ z, wholeFiniteAverage X z ∂μ|}).toReal ≤
    variance (wholeFiniteAverage X) μ / ε ^ 2 at h
  rw [hmean, hvar] at h
  simpa only [div_div, mul_comm] using h

end
end SAP.P001f.WH.W1
