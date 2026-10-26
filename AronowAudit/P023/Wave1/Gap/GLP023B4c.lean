import AronowAudit.P023.Wave1.Gap.GLP023B4
import AronowAudit.P023.Wave1.Gap.GP023B1b
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Regular
import AronowAudit.P023.P023_Review
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Tactic.FunProp

/-!
Sampling bounds for regression matrices and a corrected Proposition 2,
using polynomial projection, Legendre formulas, and Jackson approximation.
-/

namespace AronowAudit.P023.Wave1

noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter

local instance GLP023B4c_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! Almost everywhere measurability of a conditional mean descends through
the first-coordinate marginal. -/

lemma GLP023B4c_marginal_measurable (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (m : ℝ → ℝ) (hm : AEStronglyMeasurable (fun z : ℝ × ℝ => m z.1) ν) :
    AEStronglyMeasurable m (marginLaw ν) := by
  let F := hm.mk (fun z : ℝ × ℝ => m z.1)
  obtain ⟨B, hBsub, hBm, hBnull⟩ := exists_measurable_superset_of_null
    (show ν {z : ℝ × ℝ | m z.1 ≠ F z} = 0 from hm.ae_eq_mk)
  have hK (n : ℕ) : ∃ K : Set (ℝ × ℝ), K ⊆ Bᶜ ∧ IsCompact K ∧
      ν (Bᶜ \ K) < ((n : ℝ≥0∞) + 1)⁻¹ :=
    hBm.compl.exists_isCompact_sdiff_lt (measure_ne_top _ _)
      (ENNReal.inv_ne_zero.mpr (by finiteness))
  choose K hKB hKc hKmass using hK
  let T : Set (ℝ × ℝ) := ⋃ n, K n
  have hTm : MeasurableSet T := MeasurableSet.iUnion (fun n => (hKc n).measurableSet)
  have hTnull : ν Tᶜ = 0 := by
    have hb (n : ℕ) : ν Tᶜ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
      calc
        _ ≤ ν (B ∪ (Bᶜ \ K n)) := measure_mono (by
          intro z hz
          by_cases hzB : z ∈ B
          · exact Or.inl hzB
          · exact Or.inr ⟨hzB, fun hzK => hz (mem_iUnion.mpr ⟨n, hzK⟩)⟩)
        _ ≤ ν B + ν (Bᶜ \ K n) := measure_union_le _ _
        _ ≤ _ := by rw [hBnull, zero_add]; exact (hKmass n).le
    apply le_antisymm _ bot_le
    apply ge_of_tendsto (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
    exact Eventually.of_forall (fun n => by
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using hb n)
  let S : Set ℝ := ⋃ n, Prod.fst '' K n
  have hSm : MeasurableSet S := MeasurableSet.iUnion (fun n =>
    ((hKc n).image continuous_fst).measurableSet)
  letI : StandardBorelSpace T := hTm.standardBorel
  let f : T → S := fun z => ⟨z.val.1, by
    obtain ⟨n, hn⟩ := mem_iUnion.mp z.property
    exact mem_iUnion.mpr ⟨n, z.val, hn, rfl⟩⟩
  have hfm : Measurable f := (measurable_fst.comp measurable_subtype_coe).subtype_mk
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨n, z, hz, hzx⟩ := mem_iUnion.mp hx
    exact ⟨⟨z, mem_iUnion.mpr ⟨n, hz⟩⟩, Subtype.ext hzx⟩
  have hcomp : Measurable ((fun x : S => m x.val) ∘ f) := by
    have he : ((fun x : S => m x.val) ∘ f) = F ∘ (Subtype.val : T → ℝ × ℝ) := by
      funext z
      obtain ⟨n, hn⟩ := mem_iUnion.mp z.property
      exact not_not.mp (fun hne => hKB n hn (hBsub hne))
    rw [he]
    exact hm.measurable_mk.comp measurable_subtype_coe
  have hms : Measurable (fun x : S => m x.val) :=
    (hfm.measurable_comp_iff_of_surjective hfs).mp hcomp
  obtain ⟨g, hgm, hge⟩ := (MeasurableEmbedding.subtype_coe hSm).exists_measurable_extend hms
    (fun _ => inferInstance)
  apply hgm.aestronglyMeasurable.congr
  have hs : ∀ᵐ x ∂marginLaw ν, x ∈ S := by
    rw [ae_iff]
    change (Measure.map Prod.fst ν) Sᶜ = 0
    rw [Measure.map_apply measurable_fst hSm.compl]
    apply measure_mono_null _ hTnull
    intro z hz hzT
    obtain ⟨n, hn⟩ := mem_iUnion.mp hzT
    exact hz (mem_iUnion.mpr ⟨n, z, hn, rfl⟩)
  filter_upwards [hs] with x hx
  exact congrFun hge ⟨x, hx⟩

lemma GLP023B4c_marginal_integrable (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (m : ℝ → ℝ) (hm : Integrable (fun z : ℝ × ℝ => m z.1) ν) :
    Integrable m (marginLaw ν) := by
  exact (integrable_map_measure
    (GLP023B4c_marginal_measurable ν m hm.aestronglyMeasurable)
    measurable_fst.aemeasurable).mpr hm

lemma GLP023B4c_vector_nonneg (J : ℕ) (v : Fin (J+2) → ℝ) :
    0 ≤ vectorSquared J v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma GLP023B4c_vector_eq_zero (J : ℕ) (v : Fin (J+2) → ℝ) :
    vectorSquared J v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext j
    have hj := Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ j)
    change v j ^ 2 ≤ vectorSquared J v at hj
    rw [h] at hj
    exact sq_eq_zero_iff.mp (le_antisymm hj (sq_nonneg _))
  · rintro rfl
    simp [vectorSquared]

lemma GLP023B4c_vector_smul (J : ℕ) (r : ℝ) (v : Fin (J+2) → ℝ) :
    vectorSquared J (fun j => r * v j) = r^2 * vectorSquared J v := by
  simp only [vectorSquared, mul_pow, Finset.mul_sum]

lemma GLP023B4c_cauchy (J : ℕ) (a b : Fin (J+2) → ℝ) :
    |∑ j, a j * b j| ≤ Real.sqrt (vectorSquared J a) * Real.sqrt (vectorSquared J b) := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (GLP023B4c_vector_nonneg J a),
    Real.sq_sqrt (GLP023B4c_vector_nonneg J b)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma GLP023B4c_norm_eq (J : ℕ) (v : Fin (J+2) → ℝ) :
    Real.sqrt (vectorSquared J v) = ‖WithLp.toLp 2 v‖ := by
  simp [EuclideanSpace.norm_eq, vectorSquared]

lemma GLP023B4c_norm_sub (J : ℕ) (a b : Fin (J+2) → ℝ) :
    Real.sqrt (vectorSquared J (fun j => a j - b j)) ≤
      Real.sqrt (vectorSquared J a) + Real.sqrt (vectorSquared J b) := by
  simp_rw [GLP023B4c_norm_eq]
  exact norm_sub_le (WithLp.toLp 2 a) (WithLp.toLp 2 b)

lemma GLP023B4c_sphere_compact (J : ℕ) :
    IsCompact {a : EuclideanSpace ℝ (Fin (J+2)) | ∑ j, a j^2 = 1} := by
  have he := EuclideanSpace.sphere_zero_eq (n := Fin (J+2)) (1 : ℝ) zero_le_one
  simp only [one_pow] at he
  rw [← he]
  exact isCompact_sphere _ _

lemma GLP023B4c_sphere_nonempty (J : ℕ) :
    {a : EuclideanSpace ℝ (Fin (J+2)) | ∑ j, a j^2 = 1}.Nonempty := by
  refine ⟨WithLp.toLp 2 (Pi.single (0 : Fin (J+2)) (1 : ℝ)), ?_⟩
  simp [Pi.single_apply]

def GLP023B4c_apply (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ)
    (v : Fin (J+2) → ℝ) : Fin (J+2) → ℝ := fun j => ∑ l, A j l * v l

def GLP023B4c_quad (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ)
    (v : Fin (J+2) → ℝ) : ℝ := ∑ j, v j * GLP023B4c_apply J A v j

lemma GLP023B4c_apply_smul (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ)
    (v : Fin (J+2) → ℝ) (r : ℝ) :
    GLP023B4c_apply J A (fun j => r * v j) = fun j => r * GLP023B4c_apply J A v j := by
  funext j
  simp only [GLP023B4c_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma GLP023B4c_quad_smul (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ)
    (v : Fin (J+2) → ℝ) (r : ℝ) :
    GLP023B4c_quad J A (fun j => r * v j) = r^2 * GLP023B4c_quad J A v := by
  simp only [GLP023B4c_quad, GLP023B4c_apply_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma GLP023B4c_operator (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ) :
    0 ≤ matrixOperatorNorm J A ∧ ∀ v : Fin (J+2) → ℝ,
      Real.sqrt (vectorSquared J (GLP023B4c_apply J A v)) ≤
        matrixOperatorNorm J A * Real.sqrt (vectorSquared J v) := by
  let S := {a : EuclideanSpace ℝ (Fin (J+2)) | ∑ j, a j^2 = 1}
  let f : EuclideanSpace ℝ (Fin (J+2)) → ℝ := fun a =>
    Real.sqrt (vectorSquared J (GLP023B4c_apply J A (fun j => a j)))
  have hf : Continuous f := by
    apply Continuous.sqrt
    apply continuous_finset_sum
    intro j _
    apply Continuous.pow
    apply continuous_finset_sum
    intro l _
    exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin (J+2) => ℝ) l)
  have he : {r | ∃ v : Fin (J+2) → ℝ, vectorSquared J v = 1 ∧
      r = Real.sqrt (∑ j, (∑ l, A j l * v l)^2)} = f '' S := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨WithLp.toLp 2 v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun j => v j, hv, rfl⟩
  obtain ⟨a, ha, hmax, hbound⟩ := (GLP023B4c_sphere_compact J).exists_sSup_image_eq_and_ge
    (GLP023B4c_sphere_nonempty J) hf.continuousOn
  have hop : matrixOperatorNorm J A = f a := by
    unfold matrixOperatorNorm
    rw [he]
    exact hmax
  have hop0 : 0 ≤ matrixOperatorNorm J A := by rw [hop]; exact Real.sqrt_nonneg _
  refine ⟨hop0, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    simp [GLP023B4c_apply, vectorSquared]
  have hvpos : 0 < vectorSquared J v := lt_of_le_of_ne (GLP023B4c_vector_nonneg J v)
    (Ne.symm (mt (GLP023B4c_vector_eq_zero J v).mp hv))
  let t := Real.sqrt (vectorSquared J v)
  have ht : 0 < t := Real.sqrt_pos.mpr hvpos
  have hu : vectorSquared J (fun j => t⁻¹ * v j) = 1 := by
    rw [GLP023B4c_vector_smul]
    dsimp [t]
    rw [inv_pow, Real.sq_sqrt hvpos.le, inv_mul_cancel₀ hvpos.ne']
  have hb := hbound (WithLp.toLp 2 (fun j => t⁻¹ * v j)) hu
  change Real.sqrt (vectorSquared J (GLP023B4c_apply J A (fun j => t⁻¹ * v j))) ≤ f a at hb
  rw [GLP023B4c_apply_smul, GLP023B4c_vector_smul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_inv, abs_of_pos ht, ← hop] at hb
  have hmul := mul_le_mul_of_nonneg_right hb ht.le
  simpa only [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one, mul_comm t⁻¹] using hmul

lemma GLP023B4c_gram_integrable (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (j l : Fin (J+2)) :
    Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      polynomialDesign J (fun x : ℝ => x) party x l) μ := by
  apply GP023B1b_supported_integrable μ hp hs
    ((GP023B1b_column_measurable J j).mul (GP023B1b_column_measurable J l)) 1
  intro x hx
  change |polynomialDesign J (fun x : ℝ => x) party x j *
    polynomialDesign J (fun x : ℝ => x) party x l| ≤ 1
  rw [abs_mul]
  simpa using mul_le_mul (GP023B1b_column_bound J j x hx)
    (GP023B1b_column_bound J l x hx) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

lemma GLP023B4c_gram_square (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (a : Fin (J+2) → ℝ) :
    expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) a x ^ 2) =
      GLP023B4c_quad J (populationGram μ J) a := by
  let z := polynomialDesign J (fun x : ℝ => x) party
  have he (x : ℝ) : predict z a x ^ 2 =
      ∑ j, ∑ l, (z x j * z x l) * (a j * a l) := by
    simp only [predict, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  unfold expectation
  change (∫ x, predict z a x ^ 2 ∂μ) = _
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun l _ => (GLP023B4c_gram_integrable μ hp hs J j l).mul_const _))]
  unfold GLP023B4c_quad GLP023B4c_apply
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ =>
    (GLP023B4c_gram_integrable μ hp hs J j l).mul_const _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_mul_const]
  change populationGram μ J j l * (a j * a l) = _
  ring

lemma GLP023B4c_rayleigh (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    0 < smallestMomentEigenvalue μ J ∧ ∀ v : Fin (J+2) → ℝ,
      smallestMomentEigenvalue μ J * vectorSquared J v ≤
        GLP023B4c_quad J (populationGram μ J) v := by
  let S := {a : EuclideanSpace ℝ (Fin (J+2)) | ∑ j, a j^2 = 1}
  let f : EuclideanSpace ℝ (Fin (J+2)) → ℝ := fun a =>
    GLP023B4c_quad J (populationGram μ J) (fun j => a j)
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro j _
    apply (PiLp.continuous_apply 2 (fun _ : Fin (J+2) => ℝ) j).mul
    apply continuous_finset_sum
    intro l _
    exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin (J+2) => ℝ) l)
  have he : {r | ∃ a : Fin (J+2) → ℝ, (∑ j, a j^2) = 1 ∧
      r = expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) a x^2)} =
      f '' S := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨WithLp.toLp 2 a, ha, (GLP023B4c_gram_square μ hp hs J a).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun j => a j, ha, (GLP023B4c_gram_square μ hp hs J _).symm⟩
  obtain ⟨a, ha, hmin, hbound⟩ := (GLP023B4c_sphere_compact J).exists_sInf_image_eq_and_le
    (GLP023B4c_sphere_nonempty J) hf.continuousOn
  have hell : smallestMomentEigenvalue μ J = f a := by
    unfold smallestMomentEigenvalue
    rw [he]
    exact hmin
  have hellpos : 0 < smallestMomentEigenvalue μ J := by
    rw [hell]
    rw [show f a = expectation μ (fun x =>
      predict (polynomialDesign J (fun x : ℝ => x) party) (fun j => a j) x ^ 2) from
      (GLP023B4c_gram_square μ hp hs J _).symm]
    apply hpd
    intro hz
    have hzero := (GLP023B4c_vector_eq_zero J (fun j => a j)).mpr hz
    change vectorSquared J (fun j => a j) = 1 at ha
    linarith
  refine ⟨hellpos, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    simp [vectorSquared, GLP023B4c_quad, GLP023B4c_apply]
  have hvpos : 0 < vectorSquared J v := lt_of_le_of_ne (GLP023B4c_vector_nonneg J v)
    (Ne.symm (mt (GLP023B4c_vector_eq_zero J v).mp hv))
  let t := Real.sqrt (vectorSquared J v)
  have ht : 0 < t := Real.sqrt_pos.mpr hvpos
  have ht2 : t^2 = vectorSquared J v := Real.sq_sqrt hvpos.le
  have hu : vectorSquared J (fun j => t⁻¹ * v j) = 1 := by
    rw [GLP023B4c_vector_smul, inv_pow, ht2, inv_mul_cancel₀ hvpos.ne']
  have hb := hbound (WithLp.toLp 2 (fun j => t⁻¹ * v j)) hu
  change f a ≤ GLP023B4c_quad J (populationGram μ J) (fun j => t⁻¹ * v j) at hb
  rw [← hell, GLP023B4c_quad_smul, inv_pow, ht2] at hb
  have hmul := mul_le_mul_of_nonneg_right hb hvpos.le
  calc
    _ ≤ (vectorSquared J v)⁻¹ * GLP023B4c_quad J (populationGram μ J) v *
        vectorSquared J v := hmul
    _ = _ := by field_simp

lemma GLP023B4c_marginal_probability (ν : Measure (ℝ × ℝ))
    (hp : ProbabilityLaw ν) : ProbabilityLaw (marginLaw ν) := by
  simpa [ProbabilityLaw, marginLaw, Measure.map_apply measurable_fst] using hp

lemma GLP023B4c_column_bound_ae (μ : Measure ℝ) (hs : MarginSupport μ)
    (J : ℕ) (j : Fin (J+2)) :
    ∀ᵐ x ∂μ, ‖polynomialDesign J (fun x : ℝ => x) party x j‖ ≤ 1 := by
  have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := hs
  filter_upwards [hx] with x hx
  exact GP023B1b_column_bound J j x hx

lemma GLP023B4c_column_predict (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (a : Fin (J+2) → ℝ) (j : Fin (J+2)) :
    Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      predict (polynomialDesign J (fun x : ℝ => x) party) a x) μ ∧
    expectation μ (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      predict (polynomialDesign J (fun x : ℝ => x) party) a x) =
      GLP023B4c_apply J (populationGram μ J) a j := by
  let z := polynomialDesign J (fun x : ℝ => x) party
  have he (x : ℝ) : z x j * predict z a x = ∑ l, (z x j * z x l) * a l := by
    simp [predict, Finset.mul_sum, mul_assoc]
  have hi (l : Fin (J+2)) : Integrable (fun x => (z x j * z x l) * a l) μ :=
    (GLP023B4c_gram_integrable μ hp hs J j l).mul_const _
  change Integrable (fun x => z x j * predict z a x) μ ∧
    expectation μ (fun x => z x j * predict z a x) = _
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun l _ => hi l), ?_⟩
  unfold expectation
  rw [integral_finsetSum _ (fun l _ => hi l)]
  simp only [GLP023B4c_apply, populationGram, expectation, integral_mul_const, z]

lemma GLP023B4c_conditional_cross (ν : Measure (ℝ × ℝ)) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (m : ℝ → ℝ) (hm : ConditionalMean ν m)
    (J : ℕ) (j : Fin (J+2)) :
    expectation (marginLaw ν) (fun x => polynomialDesign J (fun x : ℝ => x) party x j * m x) =
      populationCross ν J j := by
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  have hmi := GLP023B4c_marginal_integrable ν m hm.2.1
  let z := fun x => polynomialDesign J (fun x : ℝ => x) party x j
  let t := (Icc (-1 : ℝ) 1).indicator z
  have htm : Measurable t := (GP023B1b_column_measurable J j).indicator measurableSet_Icc
  have htb : ∀ x, |t x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simpa [t, hx, z] using GP023B1b_column_bound J j x hx
    · simp [t, hx]
  have htest := hm.2.2 t htm ⟨1, htb⟩
  have hiz : Integrable (fun x => z x * m x) (marginLaw ν) :=
    hmi.bdd_mul (GP023B1b_column_measurable J j).aestronglyMeasurable
      (GLP023B4c_column_bound_ae _ hs J j)
  have hx : ∀ᵐ x ∂marginLaw ν, x ∈ Icc (-1 : ℝ) 1 := hs
  have hxν := ae_of_ae_map measurable_fst.aemeasurable hx
  calc
    _ = ∫ w : ℝ × ℝ, z w.1 * m w.1 ∂ν :=
      integral_map measurable_fst.aemeasurable hiz.aestronglyMeasurable
    _ = ∫ w : ℝ × ℝ, t w.1 * m w.1 ∂ν := by
      apply integral_congr_ae
      filter_upwards [hxν] with w hw
      simp [t, hw]
    _ = ∫ w : ℝ × ℝ, t w.1 * w.2 ∂ν := htest.symm
    _ = populationCross ν J j := by
      apply integral_congr_ae
      filter_upwards [hxν] with w hw
      simp [populationCross, t, hw, z]

lemma GLP023B4c_population_normal (ν : Measure (ℝ × ℝ)) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (m : ℝ → ℝ) (hm : ConditionalMean ν m)
    (J : ℕ) (hpd : MomentPositiveDefinite (marginLaw ν) J) :
    GLP023B4c_apply J (populationGram (marginLaw ν) J)
      (Classical.epsilon (PopNormal (marginLaw ν) J m)) = populationCross ν J := by
  let μ := marginLaw ν
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  have hpμ := GLP023B4c_marginal_probability ν hp
  have hmi := GLP023B4c_marginal_integrable ν m hm.2.1
  let A : (Fin (J+2) → ℝ) →ₗ[ℝ] (Fin (J+2) → ℝ) :=
    { toFun := GLP023B4c_apply J (populationGram μ J)
      map_add' := by
        intro a b
        funext j
        simp [GLP023B4c_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        exact GLP023B4c_apply_smul J _ a r }
  have hker (a : Fin (J+2) → ℝ) (ha : A a = 0) : a = 0 := by
    by_contra hne
    have hpos := hpd a hne
    rw [GLP023B4c_gram_square μ hpμ hs J a] at hpos
    have hz : GLP023B4c_quad J (populationGram μ J) a = 0 := by
      change (∑ j, a j * A a j) = 0
      rw [ha]
      simp
    linarith
  have hinj : Function.Injective A := by
    intro a b hab
    exact sub_eq_zero.mp (hker (a-b) (by rw [map_sub, hab, sub_self]))
  have hnormal (a : Fin (J+2) → ℝ) : PopNormal μ J m a ↔ A a = populationCross ν J := by
    have he (j : Fin (J+2)) : expectation μ (fun x =>
        polynomialDesign J (fun x : ℝ => x) party x j *
          (m x - predict (polynomialDesign J (fun x : ℝ => x) party) a x)) =
        populationCross ν J j - A a j := by
      simp_rw [mul_sub]
      rw [expectation, integral_sub
        (hmi.bdd_mul (GP023B1b_column_measurable J j).aestronglyMeasurable
          (GLP023B4c_column_bound_ae μ hs J j))
        (GLP023B4c_column_predict μ hpμ hs J a j).1]
      rw [← expectation, GLP023B4c_conditional_cross ν hp hs m hm J j,
        ← expectation, (GLP023B4c_column_predict μ hpμ hs J a j).2]
      rfl
    constructor
    · intro hn
      funext j
      exact (sub_eq_zero.mp ((he j).symm.trans (hn j))).symm
    · intro ha j
      rw [he, show A a j = populationCross ν J j from congrFun ha j, sub_self]
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj (populationCross ν J)
  have hn : PopNormal μ J m (Classical.epsilon (PopNormal μ J m)) :=
    Classical.epsilon_spec ⟨a, (hnormal a).mpr ha⟩
  exact (hnormal _).mp hn

lemma GLP023B4c_coefficient_bound (ν : Measure (ℝ × ℝ)) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (m : ℝ → ℝ) (hm : ConditionalMean ν m) (J : ℕ)
    (hpd : MomentPositiveDefinite (marginLaw ν) J) :
    smallestMomentEigenvalue (marginLaw ν) J *
      vectorSquared J (Classical.epsilon (PopNormal (marginLaw ν) J m)) ≤ ∫ z, z.2^2 ∂ν := by
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  let μ := marginLaw ν
  have hpμ := GLP023B4c_marginal_probability ν hp
  letI : IsProbabilityMeasure μ := ⟨hpμ⟩
  let a := Classical.epsilon (PopNormal μ J m)
  let f := predict (polynomialDesign J (fun x : ℝ => x) party) a
  have hfm := GP023B1b_predict_measurable J a
  have hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ∑ j, |a j| := by
    have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := hs
    filter_upwards [hx] with x hx
    exact GP023B1b_predict_bound J a x hx
  have hf : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable _ hfb
  have hfν : MemLp (fun z : ℝ × ℝ => f z.1) 2 ν := hf.comp_of_map measurable_fst.aemeasurable
  have hcol (j : Fin (J+2)) : Integrable (fun z : ℝ × ℝ =>
      polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2) ν :=
    hm.1.bdd_mul ((GP023B1b_column_measurable J j).comp measurable_fst).aestronglyMeasurable
      (ae_of_ae_map measurable_fst.aemeasurable (GLP023B4c_column_bound_ae μ hs J j))
  have hfy : Integrable (fun z : ℝ × ℝ => f z.1 * z.2) ν :=
    hm.1.bdd_mul (hfm.comp measurable_fst).aestronglyMeasurable
      (ae_of_ae_map measurable_fst.aemeasurable hfb)
  have hfyint : (∫ z : ℝ × ℝ, f z.1 * z.2 ∂ν) =
      GLP023B4c_quad J (populationGram μ J) a := by
    have he (z : ℝ × ℝ) : f z.1 * z.2 = ∑ j,
        (polynomialDesign J (fun x : ℝ => x) party z.1 j * z.2) * a j := by
      simp only [f, predict, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun j _ => (hcol j).mul_const _)]
    simp_rw [integral_mul_const]
    have hn := GLP023B4c_population_normal ν hp hs m hm J hpd
    change GLP023B4c_apply J (populationGram μ J) a = populationCross ν J at hn
    unfold GLP023B4c_quad
    rw [hn]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hf2int : (∫ z : ℝ × ℝ, (f z.1)^2 ∂ν) =
      GLP023B4c_quad J (populationGram μ J) a := by
    rw [← integral_map measurable_fst.aemeasurable hf.integrable_sq.aestronglyMeasurable]
    exact GLP023B4c_gram_square μ hpμ hs J a
  have hnonneg : 0 ≤ ∫ z : ℝ × ℝ, (z.2 - f z.1)^2 ∂ν :=
    integral_nonneg (fun z => sq_nonneg _)
  have hexp : (∫ z : ℝ × ℝ, (z.2 - f z.1)^2 ∂ν) =
      (∫ z, z.2^2 ∂ν) - 2 * GLP023B4c_quad J (populationGram μ J) a +
        GLP023B4c_quad J (populationGram μ J) a := by
    simp_rw [show ∀ z : ℝ × ℝ, (z.2 - f z.1)^2 =
      z.2^2 - 2 * (f z.1 * z.2) + (f z.1)^2 by intro z; ring]
    have hiSub : Integrable (fun z : ℝ × ℝ => z.2^2 - 2 * (f z.1 * z.2)) ν :=
      hsq.sub (hfy.const_mul 2)
    rw [integral_add hiSub hfν.integrable_sq,
      integral_sub hsq (hfy.const_mul 2), integral_const_mul, hfyint, hf2int]
  have hb := (GLP023B4c_rayleigh μ hpμ hs J hpd).2 a
  linarith

lemma GLP023B4c_iid_scalar {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hp : ProbabilityLaw ν)
    (f : ℝ × ℝ → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ν) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun ω => ((∑ i : Fin N, f (sample i ω)) / (N:ℝ) - ∫ z, f z ∂ν)^2) P ∧
    (∫ ω, ((∑ i : Fin N, f (sample i ω)) / (N:ℝ) - ∫ z, f z ∂ν)^2 ∂P) ≤
      (∫ z, (f z)^2 ∂ν) / (N:ℝ) := by
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  let W (i : ℕ) : Ω → ℝ := f ∘ sample i
  have hW (i : ℕ) : MemLp (W i) 2 P := hf.comp_measurePreserving
    ⟨hiid.2.1 i, hiid.2.2.1 i⟩
  have hmean (i : ℕ) : (∫ ω, W i ω ∂P) = ∫ z, f z ∂ν := by
    rw [← hiid.2.2.1 i, integral_map (hiid.2.1 i).aemeasurable hfm.aestronglyMeasurable]
    rfl
  have hvar (i : ℕ) : ProbabilityTheory.variance (W i) P = ProbabilityTheory.variance f ν := by
    exact (show MeasurePreserving (sample i) P ν from
      ⟨hiid.2.1 i, hiid.2.2.1 i⟩).variance_fun_comp hfm.aemeasurable
  have hind (i j : Fin N) (hij : i ≠ j) : ProbabilityTheory.IndepFun (W i) (W j) P :=
    (hiid.2.2.2.indepFun (fun he => hij (Fin.ext he))).comp hfm hfm
  let S : Ω → ℝ := fun ω => ∑ i : Fin N, W i ω
  have hS : MemLp S 2 P := memLp_finsetSum _ (fun i _ => hW i)
  have hSvar : ProbabilityTheory.variance S P = (N:ℝ) * ProbabilityTheory.variance f ν := by
    have hv := ProbabilityTheory.IndepFun.variance_sum (s := (Finset.univ : Finset (Fin N)))
      (X := fun i : Fin N => W i) (fun i _ => hW i) (by
        intro i _ j _ hij
        exact hind i j hij)
    have he : (∑ i : Fin N, W i) = S := by funext ω; simp [S]
    rw [he] at hv
    simpa only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hv
  let A : Ω → ℝ := fun ω => S ω * (N:ℝ)⁻¹
  have hA : MemLp A 2 P := hS.mul_const _
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hAmean : (∫ ω, A ω ∂P) = ∫ z, f z ∂ν := by
    rw [show A = fun ω => S ω * (N:ℝ)⁻¹ from rfl, integral_mul_const]
    change (∫ ω, ∑ i : Fin N, W i ω ∂P) * _ = _
    rw [integral_finsetSum (Finset.univ : Finset (Fin N))
      (fun i _ => (hW i).integrable (by norm_num))]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hNpos.ne']
  have he : (fun ω => ((∑ i : Fin N, f (sample i ω)) / (N:ℝ) - ∫ z, f z ∂ν)^2) =
      fun ω => (A ω - ∫ ω, A ω ∂P)^2 := by
    rw [hAmean]
    rfl
  rw [he]
  refine ⟨(hA.sub (memLp_const _)).integrable_sq, ?_⟩
  rw [← ProbabilityTheory.variance_eq_integral hA.aemeasurable,
    show A = fun ω => S ω * (N:ℝ)⁻¹ from rfl,
    ProbabilityTheory.variance_mul_const, hSvar]
  calc
    _ = ProbabilityTheory.variance f ν / (N:ℝ) := by field_simp [hNpos.ne']
    _ ≤ _ := div_le_div_of_nonneg_right
      (ProbabilityTheory.variance_le_expectation_sq hf.aestronglyMeasurable) hNpos.le

lemma GLP023B4c_sampling_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (J N : ℕ) (hN : 1 ≤ N) :
    (∫ ω, frobeniusSquared J (fun j l =>
      sampleGram sample N J ω j l - populationGram (marginLaw ν) J j l) ∂P) ≤
      ((J:ℝ)+2)^2/(N:ℝ) ∧
    (∫ ω, vectorSquared J (fun j =>
      sampleCross sample N J ω j - populationCross ν J j) ∂P) ≤
      ((J:ℝ)+2)*(∫ z, z.2^2 ∂ν)/(N:ℝ) := by
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  let μ := marginLaw ν
  have hpμ := GLP023B4c_marginal_probability ν hp
  let z := polynomialDesign J (fun x : ℝ => x) party
  have hcol (j : Fin (J+2)) : ∀ᵐ w : ℝ × ℝ ∂ν, ‖z w.1 j‖ ≤ 1 :=
    ae_of_ae_map measurable_fst.aemeasurable (GLP023B4c_column_bound_ae μ hs J j)
  have hgram (j l : Fin (J+2)) :
      Integrable (fun ω => (sampleGram sample N J ω j l-populationGram μ J j l)^2) P ∧
      (∫ ω, (sampleGram sample N J ω j l-populationGram μ J j l)^2 ∂P) ≤ 1/(N:ℝ) := by
    let f : ℝ × ℝ → ℝ := fun w => z w.1 j * z w.1 l
    have hfm : Measurable f := ((GP023B1b_column_measurable J j).comp measurable_fst).mul
      ((GP023B1b_column_measurable J l).comp measurable_fst)
    have hfb : ∀ᵐ w ∂ν, ‖f w‖ ≤ 1 := by
      filter_upwards [hcol j, hcol l] with w hj hl
      simpa only [f, norm_mul, mul_one] using mul_le_mul hj hl (norm_nonneg _) zero_le_one
    have hf : MemLp f 2 ν := MemLp.of_bound hfm.aestronglyMeasurable 1 hfb
    have hf2 : (∫ w, (f w)^2 ∂ν) ≤ 1 := by
      calc
        _ ≤ ∫ _w : ℝ × ℝ, (1:ℝ) ∂ν := integral_mono_ae hf.integrable_sq (integrable_const _) (by
          filter_upwards [hfb] with w hw
          have ha : |f w| ≤ 1 := hw
          nlinarith [sq_abs (f w), abs_nonneg (f w)])
        _ = 1 := by simp
    have hfmean : (∫ w, f w ∂ν) = populationGram μ J j l :=
      (integral_map measurable_fst.aemeasurable
        (GLP023B4c_gram_integrable μ hpμ hs J j l).aestronglyMeasurable).symm
    have hb := GLP023B4c_iid_scalar P ν sample hiid hp f hfm hf N hN
    rw [hfmean] at hb
    change Integrable (fun ω => (sampleGram sample N J ω j l-populationGram μ J j l)^2) P ∧
      (∫ ω, (sampleGram sample N J ω j l-populationGram μ J j l)^2 ∂P) ≤ _ at hb
    exact ⟨hb.1, hb.2.trans (div_le_div_of_nonneg_right hf2 (Nat.cast_nonneg N))⟩
  have hY : MemLp (fun w : ℝ × ℝ => w.2) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_snd.aestronglyMeasurable).mpr hsq
  have hcross (j : Fin (J+2)) :
      Integrable (fun ω => (sampleCross sample N J ω j-populationCross ν J j)^2) P ∧
      (∫ ω, (sampleCross sample N J ω j-populationCross ν J j)^2 ∂P) ≤
        (∫ w, w.2^2 ∂ν)/(N:ℝ) := by
    let f : ℝ × ℝ → ℝ := fun w => z w.1 j * w.2
    have hfm : Measurable f := ((GP023B1b_column_measurable J j).comp measurable_fst).mul
      measurable_snd
    have hfb : ∀ᵐ w ∂ν, ‖f w‖ ≤ 1 * ‖w.2‖ := by
      filter_upwards [hcol j] with w hw
      simpa only [f, norm_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg w.2)
    have hf : MemLp f 2 ν := hY.of_le_mul hfm.aestronglyMeasurable hfb
    have hf2 : (∫ w, (f w)^2 ∂ν) ≤ ∫ w, w.2^2 ∂ν := by
      apply integral_mono_ae hf.integrable_sq hsq
      filter_upwards [hfb] with w hw
      simp only [one_mul, Real.norm_eq_abs] at hw
      nlinarith [sq_abs (f w), sq_abs w.2, abs_nonneg (f w), abs_nonneg w.2]
    have hb := GLP023B4c_iid_scalar P ν sample hiid hp f hfm hf N hN
    change Integrable (fun ω => (sampleCross sample N J ω j-populationCross ν J j)^2) P ∧
      (∫ ω, (sampleCross sample N J ω j-populationCross ν J j)^2 ∂P) ≤ _ at hb
    exact ⟨hb.1, hb.2.trans (div_le_div_of_nonneg_right hf2 (Nat.cast_nonneg N))⟩
  constructor
  · unfold frobeniusSquared
    rw [integral_finsetSum (Finset.univ : Finset (Fin (J+2)))
      (fun j _ => integrable_finsetSum _ (fun l _ => (hgram j l).1))]
    calc
      _ = ∑ j : Fin (J+2), ∑ l : Fin (J+2),
          ∫ ω, (sampleGram sample N J ω j l-populationGram μ J j l)^2 ∂P := by
        apply Finset.sum_congr rfl
        intro j _
        exact integral_finsetSum _ (fun l _ => (hgram j l).1)
      _ ≤ ∑ _j : Fin (J+2), ∑ _l : Fin (J+2), 1/(N:ℝ) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => (hgram j l).2))
      _ = _ := by simp [Nat.cast_add, Nat.cast_ofNat]; ring
  · unfold vectorSquared
    rw [integral_finsetSum (Finset.univ : Finset (Fin (J+2))) (fun j _ => (hcross j).1)]
    calc
      _ ≤ ∑ _j : Fin (J+2), (∫ w, w.2^2 ∂ν)/(N:ℝ) :=
        Finset.sum_le_sum (fun j _ => (hcross j).2)
      _ = _ := by simp [Nat.cast_add, Nat.cast_ofNat]; ring

lemma GLP023B4c_sample_quad {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (N J : ℕ) (ω : Ω) (v : Fin (J+2) → ℝ) :
    GLP023B4c_quad J (sampleGram sample N J ω) v =
      (∑ i : Fin N, predict (polynomialDesign J (fun i : Fin N => (sample i ω).1)
        (fun i => party (sample i ω).1)) v i ^ 2)/(N:ℝ) := by
  let X := polynomialDesign J (fun i : Fin N => (sample i ω).1)
    (fun i => party (sample i ω).1)
  -- The column identity is a finite-sum calculation, applied before summing against v.
  
  have he (j : Fin (J+2)) : GLP023B4c_apply J (sampleGram sample N J ω) v j =
      dot (fun i => X i j) (predict X v)/(N:ℝ) := by
    unfold GLP023B4c_apply sampleGram dot predict X
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [polynomialDesign]
    ring
  unfold GLP023B4c_quad
  simp_rw [he, ← mul_div_assoc, ← Finset.sum_div]
  rw [← dot_predict_left X v (predict X v)]
  simp only [dot, pow_two, X]

lemma GLP023B4c_perturbation {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (N J : ℕ) (hN : 1 ≤ N) (ω : Ω)
    (G : Fin (J+2) → Fin (J+2) → ℝ) (t c : Fin (J+2) → ℝ) (ell M : ℝ)
    (hell : 0 < ell)
    (hcoerc : ∀ v, ell * vectorSquared J v ≤ GLP023B4c_quad J G v)
    (hnormal : GLP023B4c_apply J G c = t) (hc : ell * vectorSquared J c ≤ M)
    (hgood : matrixOperatorNorm J (fun j l => sampleGram sample N J ω j l - G j l) ≤ ell/2) :
    Real.sqrt (vectorSquared J (fun j =>
      olsCoefficients (polynomialDesign J (fun i : Fin N => (sample i ω).1)
        (fun i => party (sample i ω).1)) (fun i => (sample i ω).2) j-c j)) ≤
      (2/ell)*(Real.sqrt (vectorSquared J (fun j => sampleCross sample N J ω j-t j))+
        matrixOperatorNorm J (fun j l => sampleGram sample N J ω j l-G j l)*Real.sqrt (M/ell)) := by
  let H := sampleGram sample N J ω
  let A := fun j l => H j l - G j l
  let X := polynomialDesign J (fun i : Fin N => (sample i ω).1)
    (fun i => party (sample i ω).1)
  let chat := olsCoefficients X (fun i => (sample i ω).2)
  let dt := fun j => sampleCross sample N J ω j - t j
  have hop := GLP023B4c_operator J A
  have hqa (v : Fin (J+2) → ℝ) :
      |GLP023B4c_quad J A v| ≤ matrixOperatorNorm J A * vectorSquared J v := by
    calc
      _ ≤ Real.sqrt (vectorSquared J v) * Real.sqrt (vectorSquared J (GLP023B4c_apply J A v)) :=
        GLP023B4c_cauchy J v (GLP023B4c_apply J A v)
      _ ≤ Real.sqrt (vectorSquared J v) *
          (matrixOperatorNorm J A * Real.sqrt (vectorSquared J v)) :=
        mul_le_mul_of_nonneg_left (hop.2 v) (Real.sqrt_nonneg _)
      _ = matrixOperatorNorm J A * (Real.sqrt (vectorSquared J v))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (GLP023B4c_vector_nonneg J v)]
  have hq (v : Fin (J+2) → ℝ) :
      GLP023B4c_quad J H v = GLP023B4c_quad J G v + GLP023B4c_quad J A v := by
    simp only [GLP023B4c_quad, GLP023B4c_apply, A, sub_mul,
      Finset.sum_sub_distrib, mul_sub]
    ring
  have hcoercH (v : Fin (J+2) → ℝ) :
      ell/2 * vectorSquared J v ≤ GLP023B4c_quad J H v := by
    have ha := neg_le_abs (GLP023B4c_quad J A v)
    have hb := hqa v
    have hg := mul_le_mul_of_nonneg_right hgood (GLP023B4c_vector_nonneg J v)
    have hp := hcoerc v
    rw [hq]
    change matrixOperatorNorm J A * vectorSquared J v ≤ _ at hg
    linarith
  have hX : FullRank X := by
    intro v hv
    have hzero : GLP023B4c_quad J H v = 0 := by
      rw [GLP023B4c_sample_quad]
      have hsum : (∑ i : Fin N, predict X v i ^ 2) = 0 := by simp [hv]
      change (∑ i : Fin N, predict X v i ^ 2)/(N:ℝ) = 0
      rw [hsum, zero_div]
    have hb := hcoercH v
    rw [hzero] at hb
    apply (GLP023B4c_vector_eq_zero J v).mp
    have hv0 := GLP023B4c_vector_nonneg J v
    nlinarith
  have hchat : GLP023B4c_apply J H chat = sampleCross sample N J ω :=
    (GP023B1b_sample_normal sample N J (by omega) ω chat).mp
      (chosen_ols_spec X hX _)
  let e := fun j => chat j - c j
  have heq : GLP023B4c_apply J H e = fun j => dt j - GLP023B4c_apply J A c j := by
    funext j
    have hn := congrFun hnormal j
    have hs := congrFun hchat j
    change (∑ l, G j l * c l) = t j at hn
    change (∑ l, H j l * chat l) = sampleCross sample N J ω j at hs
    simp only [GLP023B4c_apply, e, A, dt, mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hn, hs]
    ring
  have hB : GLP023B4c_quad J H e ≤ Real.sqrt (vectorSquared J e) *
      (Real.sqrt (vectorSquared J dt) + matrixOperatorNorm J A * Real.sqrt (vectorSquared J c)) := by
    calc
      _ ≤ |GLP023B4c_quad J H e| := le_abs_self _
      _ ≤ Real.sqrt (vectorSquared J e) * Real.sqrt (vectorSquared J (GLP023B4c_apply J H e)) :=
        GLP023B4c_cauchy J e (GLP023B4c_apply J H e)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [heq]
        exact (GLP023B4c_norm_sub J dt (GLP023B4c_apply J A c)).trans
          (add_le_add le_rfl (hop.2 c))
  have hcnorm : Real.sqrt (vectorSquared J c) ≤ Real.sqrt (M/ell) := by
    apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hell).mpr
    nlinarith
  change Real.sqrt (vectorSquared J e) ≤ (2/ell)*
    (Real.sqrt (vectorSquared J dt) + matrixOperatorNorm J A * Real.sqrt (M/ell))
  by_cases he0 : vectorSquared J e = 0
  · rw [he0, Real.sqrt_zero]
    exact mul_nonneg (div_nonneg (by norm_num) hell.le)
      (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hop.1 (Real.sqrt_nonneg _)))
  have hV : 0 < vectorSquared J e := lt_of_le_of_ne (GLP023B4c_vector_nonneg J e) (Ne.symm he0)
  have hroot : 0 < Real.sqrt (vectorSquared J e) := Real.sqrt_pos.mpr hV
  have hlow := (hcoercH e).trans hB
  rw [← Real.sq_sqrt hV.le] at hlow
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hlow
  have hcancel : ell/2 * Real.sqrt (vectorSquared J e) ≤
      Real.sqrt (vectorSquared J dt) + matrixOperatorNorm J A * Real.sqrt (vectorSquared J c) := by
    apply (mul_le_mul_iff_left₀ hroot).mp
    nlinarith [hlow]
  calc
    _ ≤ (Real.sqrt (vectorSquared J dt) + matrixOperatorNorm J A *
        Real.sqrt (vectorSquared J c))/(ell/2) :=
      (le_div_iff₀ (half_pos hell)).mpr (by nlinarith [hcancel])
    _ = (2/ell)*(Real.sqrt (vectorSquared J dt) + matrixOperatorNorm J A *
        Real.sqrt (vectorSquared J c)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcnorm hop.1))
      (div_nonneg (by norm_num) hell.le)


lemma GLP023B4c_matrix_contract {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hprob : ProbabilityLaw ν)
    (hsupport : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (m : ℝ → ℝ) (hmean : ConditionalMean ν m) (J : ℕ) (hJ : 1 ≤ J)
    (hpd : MomentPositiveDefinite (marginLaw ν) J) (N : ℕ) (hN : 1 ≤ N) :
    let μ := marginLaw ν
    let M := ∫ z, z.2^2 ∂ν
    let ell := smallestMomentEigenvalue μ J
    let c := Classical.epsilon (PopNormal μ J m)
    let ΔG := fun ω j l => sampleGram sample N J ω j l-populationGram μ J j l
    let Δt := fun ω j => sampleCross sample N J ω j-populationCross ν J j
    0 < ell ∧
    (∫ ω, frobeniusSquared J (ΔG ω) ∂P) ≤ ((J:ℝ)+2)^2/(N:ℝ) ∧
    (∫ ω, vectorSquared J (Δt ω) ∂P) ≤ ((J:ℝ)+2)*M/(N:ℝ) ∧
    ell*vectorSquared J c ≤ M ∧
    (∀ ω, matrixOperatorNorm J (ΔG ω) ≤ ell/2 →
      Real.sqrt (vectorSquared J (fun j =>
        olsCoefficients (polynomialDesign J (fun i : Fin N => (sample i ω).1)
          (fun i => party (sample i ω).1)) (fun i => (sample i ω).2) j-c j)) ≤
      (2/ell)*(Real.sqrt (vectorSquared J (Δt ω))+
        matrixOperatorNorm J (ΔG ω)*Real.sqrt (M/ell))) := by
  dsimp only
  have hpμ := GLP023B4c_marginal_probability ν hprob
  have hell := GLP023B4c_rayleigh (marginLaw ν) hpμ hsupport J hpd
  have hs := GLP023B4c_sampling_bounds P ν sample hiid hprob hsupport hsq J N hN
  have hc := GLP023B4c_coefficient_bound ν hprob hsupport hsq m hmean J hpd
  refine ⟨hell.1, hs.1, hs.2, hc, ?_⟩
  intro ω hgood
  exact GLP023B4c_perturbation sample N J hN ω _ _ _ _ _ hell.1 hell.2
    (GLP023B4c_population_normal ν hprob hsupport m hmean J hpd) hc hgood


section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local instance GLP023B4c_T8_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxRecDepth 2048
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
/-! Population normal equations and Legendre formulas. -/
def GLP023B4c_T8_cpb_Bounded (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ B, ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ B

lemma GLP023B4c_T8_cpb_const (c : ℝ) : GLP023B4c_T8_cpb_Bounded (fun _ => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

lemma GLP023B4c_T8_cpb_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    GLP023B4c_T8_cpb_Bounded f := by
  refine ⟨hf.measurable, ?_⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.abs.continuousOn
  exact ⟨B, fun x hx => hB (mem_image_of_mem _ hx)⟩

lemma GLP023B4c_T8_cpb_add {f g : ℝ → ℝ}
    (hf : GLP023B4c_T8_cpb_Bounded f) (hg : GLP023B4c_T8_cpb_Bounded g) :
    GLP023B4c_T8_cpb_Bounded (fun x => f x + g x) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hf.1.add hg.1, B + C, fun x hx =>
    (abs_add_le _ _).trans (add_le_add (hB x hx) (hC x hx))⟩

lemma GLP023B4c_T8_cpb_sub {f g : ℝ → ℝ}
    (hf : GLP023B4c_T8_cpb_Bounded f) (hg : GLP023B4c_T8_cpb_Bounded g) :
    GLP023B4c_T8_cpb_Bounded (fun x => f x - g x) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hf.1.sub hg.1, B + C, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hB x hx) (hC x hx))⟩

lemma GLP023B4c_T8_cpb_mul {f g : ℝ → ℝ}
    (hf : GLP023B4c_T8_cpb_Bounded f) (hg : GLP023B4c_T8_cpb_Bounded g) :
    GLP023B4c_T8_cpb_Bounded (fun x => f x * g x) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0 (by norm_num))
  refine ⟨hf.1.mul hg.1, B * C, ?_⟩
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hB x hx) (hC x hx) (abs_nonneg _) hB0

lemma GLP023B4c_T8_cpb_square {f : ℝ → ℝ} (hf : GLP023B4c_T8_cpb_Bounded f) :
    GLP023B4c_T8_cpb_Bounded (fun x => f x ^ 2) := by
  simpa only [pow_two] using GLP023B4c_T8_cpb_mul hf hf

lemma GLP023B4c_T8_cpb_party : GLP023B4c_T8_cpb_Bounded party := by
  refine ⟨Measurable.ite measurableSet_Ici measurable_const measurable_const, 1, ?_⟩
  intro x _
  unfold party
  split_ifs <;> norm_num

lemma GLP023B4c_T8_cpb_poly (p : Polynomial ℝ) :
    GLP023B4c_T8_cpb_Bounded (fun x => p.eval x) :=
  GLP023B4c_T8_cpb_continuous p.continuous

lemma GLP023B4c_T8_cpb_integrable {μ : Measure ℝ} (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) {f : ℝ → ℝ} (hf : GLP023B4c_T8_cpb_Bounded f) :
    Integrable f μ := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  obtain ⟨B, hB⟩ := hf.2
  have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hs
  apply (integrable_const B).mono' hf.1.aestronglyMeasurable
  filter_upwards [hx] with x hxs
  simpa only [Real.norm_eq_abs] using hB x hxs

lemma GLP023B4c_T8_cpb_sum {K : Type*} [Fintype K] (f : K → ℝ → ℝ)
    (hf : ∀ k, GLP023B4c_T8_cpb_Bounded (f k)) :
    GLP023B4c_T8_cpb_Bounded (fun x => ∑ k, f k x) := by
  classical
  choose B hB using fun k => (hf k).2
  refine ⟨Finset.measurable_sum _ (fun k _ => (hf k).1), ∑ k, B k, ?_⟩
  intro x hx
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun k _ => hB k x hx))

lemma GLP023B4c_T8_cpb_predict {K : Type*} [Fintype K]
    (X : ℝ → K → ℝ) (hX : ∀ j, GLP023B4c_T8_cpb_Bounded (fun x => X x j))
    (c : K → ℝ) : GLP023B4c_T8_cpb_Bounded (predict X c) := by
  exact GLP023B4c_T8_cpb_sum _ (fun j => GLP023B4c_T8_cpb_mul (hX j) (GLP023B4c_T8_cpb_const _))

lemma GLP023B4c_T8_cpb_design (J : ℕ) (j : Fin (J + 2)) :
    GLP023B4c_T8_cpb_Bounded (fun x => polynomialDesign J (fun x : ℝ => x) party x j) := by
  unfold polynomialDesign
  split_ifs
  · exact GLP023B4c_T8_cpb_const _
  · exact GLP023B4c_T8_cpb_party
  · exact GLP023B4c_T8_cpb_continuous (continuous_id.pow _)

/-- Finite-dimensional Gram inversion, stated directly in terms of integrals. -/
lemma GLP023B4c_T8_cpb_normal_exists {K : Type*} [Fintype K]
    (μ : Measure ℝ) (hp : ProbabilityLaw μ) (hs : MarginSupport μ)
    (X : ℝ → K → ℝ) (hX : ∀ j, GLP023B4c_T8_cpb_Bounded (fun x => X x j))
    (hpos : ∀ c : K → ℝ, c ≠ 0 → 0 < expectation μ (fun x => predict X c x ^ 2))
    (m : ℝ → ℝ) (hm : GLP023B4c_T8_cpb_Bounded m) :
    ∃ c : K → ℝ, ∀ j, expectation μ (fun x => X x j * (m x - predict X c x)) = 0 := by
  classical
  have hi (c : K → ℝ) (j : K) : Integrable (fun x => X x j * predict X c x) μ :=
    GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul (hX j)
      (GLP023B4c_T8_cpb_predict X hX c))
  let A : (K → ℝ) →ₗ[ℝ] (K → ℝ) :=
    { toFun := fun c j => expectation μ (fun x => X x j * predict X c x)
      map_add' := by
        intro a b
        funext j
        have he : (fun x => X x j * predict X (a + b) x) =
            (fun x => X x j * predict X a x + X x j * predict X b x) := by
          funext x
          simp [predict, mul_add, Finset.sum_add_distrib]
        exact (congrArg (expectation μ) he).trans (integral_add (hi a j) (hi b j))
      map_smul' := by
        intro r a
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change expectation μ _ = r * expectation μ _
        have he : (fun x => X x j * predict X (r • a) x) =
            (fun x => r * (X x j * predict X a x)) := by
          funext x
          simp [predict, Finset.mul_sum, mul_assoc, mul_left_comm]
        rw [he]
        exact integral_const_mul _ _ }
  have hker : ∀ c, A c = 0 → c = 0 := by
    intro c hc
    by_contra hne
    have hz : expectation μ (fun x => predict X c x ^ 2) = 0 := by
      have he : (fun x => predict X c x ^ 2) =
          (fun x => ∑ j, c j * (X x j * predict X c x)) := by
        funext x
        rw [pow_two, show predict X c x * predict X c x =
          (∑ j, X x j * c j) * predict X c x from rfl, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      unfold expectation
      rw [he, integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul]
        change c j * A c j = 0
        rw [hc]
        simp
      · intro j _
        exact (hi c j).const_mul (c j)
    exact (ne_of_gt (hpos c hne)) hz
  have hinj : Function.Injective A := by
    intro a b hab
    exact sub_eq_zero.mp (hker (a - b) (by rw [map_sub, hab, sub_self]))
  obtain ⟨c, hc⟩ := LinearMap.surjective_of_injective hinj
    (fun j => expectation μ (fun x => X x j * m x))
  refine ⟨c, fun j => ?_⟩
  have he := congrFun hc j
  change expectation μ (fun x => X x j * predict X c x) = _ at he
  unfold expectation at he ⊢
  simp_rw [mul_sub]
  rw [integral_sub (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul (hX j) hm))
    (hi c j), he, sub_self]

def GLP023B4c_T8_cpb_polyOf (J : ℕ) (a : Fin (J + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

lemma GLP023B4c_T8_cpb_polyOf_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (x : ℝ) :
    (GLP023B4c_T8_cpb_polyOf J a).eval x = ∑ i, a i * x ^ (i : ℕ) := by
  simp [GLP023B4c_T8_cpb_polyOf, Polynomial.eval_finset_sum]

lemma GLP023B4c_T8_cpb_polyOf_degree (J : ℕ) (a : Fin (J + 1) → ℝ) :
    (GLP023B4c_T8_cpb_polyOf J a).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma GLP023B4c_T8_cpb_expansion (p : Polynomial ℝ) (J : ℕ) (hp : p.natDegree ≤ J)
    (x : ℝ) : p.eval x = ∑ i : Fin (J + 1), p.coeff i * x ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < J + 1 by omega)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- Insert the treatment coefficient after the intercept. -/
def GLP023B4c_T8_cpb_embed (J : ℕ) (a : Fin (J + 1) → ℝ) (b : ℝ) : Fin (J + 2) → ℝ :=
  Fin.cases (a 0) (Fin.cases b (fun j => a j.succ))

lemma GLP023B4c_T8_cpb_embed_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (b x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (GLP023B4c_T8_cpb_embed J a b) x =
      (∑ i, a i * x ^ (i : ℕ)) + b * party x := by
  simp [predict, polynomialDesign, GLP023B4c_T8_cpb_embed, Fin.sum_univ_succ,
    Nat.add_sub_cancel, mul_comm]
  ring

lemma GLP023B4c_T8_cpb_embed_ne (J : ℕ) (a : Fin (J + 1) → ℝ) (ha : a ≠ 0) :
    GLP023B4c_T8_cpb_embed J a 0 ≠ 0 := by
  intro he
  apply ha
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrFun he 0
  · exact congrFun he j.succ.succ

lemma GLP023B4c_T8_cpb_projection_spec (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    IsProjection μ J (projection μ J) := by
  apply Classical.epsilon_spec
  have hpos (a : Fin (J + 1) → ℝ) (ha : a ≠ 0) :
      0 < expectation μ (fun x => predict (fun x (i : Fin (J + 1)) => x ^ (i : ℕ)) a x ^ 2) := by
    have h := hpd (GLP023B4c_T8_cpb_embed J a 0) (GLP023B4c_T8_cpb_embed_ne J a ha)
    simp_rw [GLP023B4c_T8_cpb_embed_eval] at h
    simpa only [zero_mul, add_zero, predict, mul_comm] using h
  obtain ⟨a, ha⟩ := GLP023B4c_T8_cpb_normal_exists μ hp hs
    (fun x (i : Fin (J + 1)) => x ^ (i : ℕ))
    (fun _ => GLP023B4c_T8_cpb_continuous (continuous_id.pow _)) hpos party GLP023B4c_T8_cpb_party
  refine ⟨GLP023B4c_T8_cpb_polyOf J a, GLP023B4c_T8_cpb_polyOf_degree J a, ?_⟩
  intro j hj
  have he := ha (⟨j, by omega⟩ : Fin (J + 1))
  simpa only [GLP023B4c_T8_cpb_polyOf_eval, predict, mul_comm] using he

lemma GLP023B4c_T8_cpb_integral_predict {K : Type*} [Fintype K]
    (μ : Measure ℝ) (hp : ProbabilityLaw μ) (hs : MarginSupport μ)
    (X : ℝ → K → ℝ) (hX : ∀ j, GLP023B4c_T8_cpb_Bounded (fun x => X x j))
    (f : ℝ → ℝ) (hf : GLP023B4c_T8_cpb_Bounded f) (c : K → ℝ) :
    expectation μ (fun x => f x * predict X c x) =
      ∑ j, c j * expectation μ (fun x => f x * X x j) := by
  classical
  have he : (fun x => f x * predict X c x) =
      (fun x => ∑ j, c j * (f x * X x j)) := by
    funext x
    simp only [predict, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold expectation
  rw [he, integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j _
    exact (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hf (hX j))).const_mul _

lemma GLP023B4c_T8_cpb_test_poly (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (q : Polynomial ℝ) (hq : IsProjection μ J q)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
    expectation μ (fun x => (party x - q.eval x) * p.eval x) = 0 := by
  have hr := GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q)
  have he : (fun x => (party x - q.eval x) * p.eval x) =
      (fun x => (party x - q.eval x) *
        predict (fun x (i : Fin (J + 1)) => x ^ (i : ℕ)) (fun i => p.coeff i) x) := by
    funext x
    rw [GLP023B4c_T8_cpb_expansion p J hdeg]
    simp only [predict, mul_comm]
  rw [he, GLP023B4c_T8_cpb_integral_predict μ hp hs
    (fun x (i : Fin (J + 1)) => x ^ (i : ℕ))
    (fun i => GLP023B4c_T8_cpb_continuous (continuous_id.pow (i : ℕ))) _ hr]
  apply Finset.sum_eq_zero
  intro j _
  rw [hq.2 j (by omega), mul_zero]

lemma GLP023B4c_T8_cpb_residual_predict (J : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ J) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party)
      (GLP023B4c_T8_cpb_embed J (fun i => -q.coeff i) 1) x = party x - q.eval x := by
  rw [GLP023B4c_T8_cpb_embed_eval, GLP023B4c_T8_cpb_expansion q J hq]
  simp only [neg_mul, Finset.sum_neg_distrib, one_mul]
  ring

lemma GLP023B4c_T8_cpb_residual_moments (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    IsProjection μ J (projection μ J) ∧
    0 < residualVariance μ J ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => popResidual μ J x * p.eval x) = 0) ∧
    expectation μ (popResidual μ J) = 0 ∧
    expectation μ (fun x => popResidual μ J x * party x) = residualVariance μ J := by
  have hq := GLP023B4c_T8_cpb_projection_spec μ hp hs J hpd
  have hr : GLP023B4c_T8_cpb_Bounded (popResidual μ J) :=
    GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly (projection μ J))
  have horth (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
      expectation μ (fun x => popResidual μ J x * p.eval x) = 0 :=
    GLP023B4c_T8_cpb_test_poly μ hp hs J _ hq p hdeg
  have hv : 0 < residualVariance μ J := by
    let c := GLP023B4c_T8_cpb_embed J (fun i => -(projection μ J).coeff i) 1
    have hc : c ≠ 0 := by
      intro he
      have h1 := congrFun he (⟨1, by omega⟩ : Fin (J + 2))
      change (1 : ℝ) = 0 at h1
      norm_num at h1
    have h := hpd c hc
    simpa only [c, GLP023B4c_T8_cpb_residual_predict J _ hq.1,
      residualVariance, popResidual] using h
  have hz : expectation μ (popResidual μ J) = 0 := by
    simpa only [Polynomial.eval_one, mul_one] using
      horth 1 (by simp)
  have hD : expectation μ (fun x => popResidual μ J x * party x) = residualVariance μ J := by
    have he : (fun x => popResidual μ J x * party x) =
        (fun x => popResidual μ J x ^ 2 + popResidual μ J x * (projection μ J).eval x) := by
      funext x
      unfold popResidual
      ring
    unfold expectation
    rw [he, integral_add (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_square hr))
      (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr (GLP023B4c_T8_cpb_poly _)))]
    change residualVariance μ J + expectation μ _ = _
    rw [horth _ hq.1, add_zero]
  exact ⟨hq, hv, horth, hz, hD⟩

lemma GLP023B4c_T8_cpb_fwl (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J)
    (m : ℝ → ℝ) (hm : GLP023B4c_T8_cpb_Bounded m) :
    populationCoefficient μ J m = biasFunctional μ J m := by
  let X := polynomialDesign J (fun x : ℝ => x) party
  let c := Classical.epsilon (PopNormal μ J m)
  have hX := GLP023B4c_T8_cpb_design J
  have hc : PopNormal μ J m c :=
    Classical.epsilon_spec (GLP023B4c_T8_cpb_normal_exists μ hp hs X hX hpd m hm)
  obtain ⟨hq, hv, horth, hz, hD⟩ := GLP023B4c_T8_cpb_residual_moments μ hp hs J hpd
  have hr : GLP023B4c_T8_cpb_Bounded (popResidual μ J) :=
    GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly _)
  have he : GLP023B4c_T8_cpb_Bounded (fun x => m x - predict X c x) :=
    GLP023B4c_T8_cpb_sub hm (GLP023B4c_T8_cpb_predict X hX c)
  have hnormal : expectation μ (fun x => popResidual μ J x * (m x - predict X c x)) = 0 := by
    have htest := GLP023B4c_T8_cpb_integral_predict μ hp hs X hX _ he
      (GLP023B4c_T8_cpb_embed J (fun i => -(projection μ J).coeff i) 1)
    have heq : (fun x => (m x - predict X c x) *
        predict X (GLP023B4c_T8_cpb_embed J (fun i => -(projection μ J).coeff i) 1) x) =
        (fun x => popResidual μ J x * (m x - predict X c x)) := by
      funext x
      rw [GLP023B4c_T8_cpb_residual_predict J _ hq.1]
      exact mul_comm _ _
    rw [heq] at htest
    rw [htest]
    apply Finset.sum_eq_zero
    intro j _
    have hj := hc j
    have hj' : expectation μ (fun x => (m x - predict X c x) * X x j) = 0 := by
      simpa only [mul_comm] using hj
    rw [hj', mul_zero]
  have hcol (j : Fin (J + 2)) :
      expectation μ (fun x => popResidual μ J x * X x j) =
        if j = (⟨1, by omega⟩ : Fin (J + 2)) then residualVariance μ J else 0 := by
    by_cases hj0 : j.val = 0
    · simp only [X, polynomialDesign, hj0, if_pos, mul_one]
      rw [hz, if_neg (by intro hj; have := congrArg Fin.val hj; simp_all)]
    · by_cases hj1 : j.val = 1
      · have hj : j = (⟨1, by omega⟩ : Fin (J + 2)) := Fin.ext hj1
        simpa [X, polynomialDesign, hj] using hD
      · have hj : j ≠ (⟨1, by omega⟩ : Fin (J + 2)) := by
          intro heq
          exact hj1 (congrArg Fin.val heq)
        simp only [X, polynomialDesign, hj0, hj1, if_false, if_neg hj]
        exact hq.2 (j.val - 1) (by omega)
  have hpred : expectation μ (fun x => popResidual μ J x * predict X c x) =
      c ⟨1, by omega⟩ * residualVariance μ J := by
    rw [GLP023B4c_T8_cpb_integral_predict μ hp hs X hX _ hr c]
    simp_rw [hcol]
    rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (J + 2))]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg hj, mul_zero]
    · intro hj
      exact False.elim (hj (Finset.mem_univ _))
  have heq : expectation μ (fun x => popResidual μ J x * m x) =
      c ⟨1, by omega⟩ * residualVariance μ J := by
    unfold expectation at hnormal
    simp_rw [mul_sub] at hnormal
    rw [integral_sub (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr hm))
      (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr
        (GLP023B4c_T8_cpb_predict X hX c)))] at hnormal
    change expectation μ _ - expectation μ _ = 0 at hnormal
    rw [hpred] at hnormal
    exact sub_eq_zero.mp hnormal
  change c ⟨1, by omega⟩ = expectation μ _ / residualVariance μ J
  rw [heq, mul_div_cancel_right₀ _ (ne_of_gt hv)]

lemma GLP023B4c_T8_cpb_supError {h : ℝ → ℝ} (hb : GLP023B4c_T8_cpb_Bounded h)
    (p : Polynomial ℝ) :
    (∀ x ∈ Icc (-1 : ℝ) 1, |h x - p.eval x| ≤ supError h p) ∧ 0 ≤ supError h p := by
  obtain ⟨B, hB⟩ := (GLP023B4c_T8_cpb_sub hb (GLP023B4c_T8_cpb_poly p)).2
  have hbd : BddAbove ((fun x => |h x - p.eval x|) '' Icc (-1 : ℝ) 1) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  have hle (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : |h x - p.eval x| ≤ supError h p :=
    le_csSup hbd (mem_image_of_mem _ hx)
  exact ⟨hle, (abs_nonneg _).trans (hle 0 (by norm_num))⟩

theorem GLP023B4c_T8_bias_contract (ν : Measure (ℝ × ℝ))
    (hprob : ProbabilityLaw ν) (hsupport : MarginSupport (marginLaw ν))
    (hsq : Integrable (fun z => z.2^2) ν) (α β : ℝ) (h : ℝ → ℝ)
    (hm : Measurable h) (hb : ∃ B, ∀ x ∈ Set.Icc (-1) 1, |h x| ≤ B)
    (hmean : ConditionalMean ν (fun x => α + β * party x + h x))
    (J : ℕ) (hJ : 1 ≤ J) (hpd : MomentPositiveDefinite (marginLaw ν) J) :
    let μ := marginLaw ν
    let v := residualVariance μ J
    let b := populationCoefficient μ J (fun x => α + β * party x + h x)
    IsProjection μ J (projection μ J) ∧ 0 < v ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => popResidual μ J x * p.eval x) = 0) ∧
    expectation μ (popResidual μ J) = 0 ∧
    expectation μ (fun x => popResidual μ J x * party x) = v ∧
    b = biasFunctional μ J (fun x => α + β * party x + h x) ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      b - β = biasFunctional μ J h ∧
      b - β = biasFunctional μ J (fun x => h x - p.eval x) ∧
      |b - β| ≤ amplification μ J * supError h p ∧
      |b - β| ≤ rmsError μ h p / Real.sqrt v) ∧
    2 ≤ amplification μ J ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      (∀ᵐ x ∂μ, h x = p.eval x) → b = β) ∧
    (∀ t > 0, (|b - β| ≤ t ↔ |expectation μ (fun x => popResidual μ J x * h x)| ≤ t * v) ∧
      (amplification μ J * sInf {e | ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ e = supError h p} ≤ t → |b - β| ≤ t) ∧
      (sInf {e | ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ e = rmsError μ h p} ≤ t * Real.sqrt v → |b - β| ≤ t)) := by
  let μ := marginLaw ν
  let v := residualVariance μ J
  let b := populationCoefficient μ J (fun x => α + β * party x + h x)
  change IsProjection μ J (projection μ J) ∧ _
  have hp : ProbabilityLaw μ := by
    unfold ProbabilityLaw μ marginLaw
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    exact hprob
  have hs : MarginSupport μ := hsupport
  have hh : GLP023B4c_T8_cpb_Bounded h := ⟨hm, hb⟩
  have hr : GLP023B4c_T8_cpb_Bounded (popResidual μ J) :=
    GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly _)
  have hfull : GLP023B4c_T8_cpb_Bounded (fun x => α + β * party x + h x) :=
    GLP023B4c_T8_cpb_add (GLP023B4c_T8_cpb_add (GLP023B4c_T8_cpb_const α)
      (GLP023B4c_T8_cpb_mul (GLP023B4c_T8_cpb_const β) GLP023B4c_T8_cpb_party)) hh
  obtain ⟨hq, hv, horth, hz, hD⟩ := GLP023B4c_T8_cpb_residual_moments μ hp hs J hpd
  have hfwl : b = biasFunctional μ J (fun x => α + β * party x + h x) :=
    GLP023B4c_T8_cpb_fwl μ hp hs J hpd _ hfull
  have hri := GLP023B4c_T8_cpb_integrable hp hs hr
  have hrDi := GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr GLP023B4c_T8_cpb_party)
  have hrhi := GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr hh)
  have hrr := GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_square hr)
  have hbias (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
      b - β = biasFunctional μ J (fun x => h x - p.eval x) := by
    rw [hfwl]
    exact residual_bias_integral_identity μ (popResidual μ J) h (fun x => p.eval x)
      α β v (ne_of_gt hv) hri hrDi hrhi
      (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr (GLP023B4c_T8_cpb_poly p)))
      hz hD (horth p hdeg)
  have hbias0 : b - β = biasFunctional μ J h := by
    simpa only [Polynomial.eval_zero, sub_zero] using hbias 0 (by simp)
  have hbounds (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
      |b - β| ≤ amplification μ J * supError h p ∧
      |b - β| ≤ rmsError μ h p / Real.sqrt v := by
    have ha := GLP023B4c_T8_cpb_sub hh (GLP023B4c_T8_cpb_poly p)
    have hprod := GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_mul hr ha)
    rw [hbias p hdeg]
    constructor
    · apply residual_uniform_error_bound μ (popResidual μ J) _ (supError h p) v hv hri.abs hprod
      have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by rw [ae_iff]; exact hs
      filter_upwards [hx] with x hxs
      exact (GLP023B4c_T8_cpb_supError hh p).1 x hxs
    · exact residual_rms_error_bound μ (popResidual μ J) _ hrr
        (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_square ha)) hprod hv
  have hk : 2 ≤ amplification μ J :=
    residual_amplification_lower_bound μ (popResidual μ J) v hv hri hrDi hz hD
  refine ⟨hq, hv, horth, hz, hD, hfwl, ?_, hk, ?_, ?_⟩
  · intro p hdeg
    exact ⟨hbias0, hbias p hdeg, hbounds p hdeg⟩
  · intro p hdeg heq
    have hint : expectation μ (fun x => popResidual μ J x * h x) = 0 := by
      calc
        _ = expectation μ (fun x => popResidual μ J x * p.eval x) :=
          integral_congr_ae (heq.mono (fun x hx => by rw [hx]))
        _ = 0 := horth p hdeg
    apply sub_eq_zero.mp
    rw [hbias0]
    exact (congrArg (fun a => a / v) hint).trans (zero_div v)
  · intro t ht
    have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
    have hkpos : 0 < amplification μ J := lt_of_lt_of_le (by norm_num) hk
    refine ⟨?_, ?_, ?_⟩
    · rw [hbias0]
      change |expectation μ (fun x => popResidual μ J x * h x) / v| ≤ t ↔ _
      rw [abs_div, abs_of_pos hv, div_le_iff₀ hv]
    · intro htinf
      have hlow : |b - β| / amplification μ J ≤
          sInf {e | ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ e = supError h p} := by
        have hne : Set.Nonempty {e | ∃ p : Polynomial ℝ,
            p.natDegree ≤ J ∧ e = supError h p} := ⟨supError h 0, 0, by simp, rfl⟩
        apply le_csInf hne
        rintro e ⟨p, hdeg, rfl⟩
        apply (div_le_iff₀ hkpos).mpr
        simpa only [mul_comm] using (hbounds p hdeg).1
      have hle := (div_le_iff₀ hkpos).mp hlow
      calc
        _ ≤ amplification μ J * sInf {e | ∃ p : Polynomial ℝ,
            p.natDegree ≤ J ∧ e = supError h p} := by simpa only [mul_comm] using hle
        _ ≤ t := htinf
    · intro htinf
      have hlow : |b - β| * Real.sqrt v ≤
          sInf {e | ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ e = rmsError μ h p} := by
        have hne : Set.Nonempty {e | ∃ p : Polynomial ℝ,
            p.natDegree ≤ J ∧ e = rmsError μ h p} := ⟨rmsError μ h 0, 0, by simp, rfl⟩
        apply le_csInf hne
        rintro e ⟨p, hdeg, rfl⟩
        exact (le_div_iff₀ hsv).mp (hbounds p hdeg).2
      exact (mul_le_mul_iff_left₀ hsv).mp (by simpa only [mul_comm] using hlow.trans htinf)


/-! Analytic Legendre formulas. -/
/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license.
Authors: Wouter Deconinck

Source: EpsilonEridani, commit bfe8fdb3279de1c45eb1f5b9713f44f0c016f84c,
`Mathematics.Calculus.Polynomial` and `SpecialFunctions.Legendre.Basic`.
Adapted to a local namespace.
See NOTICE at the repository root.
-/
open Polynomial
section GLP023B4c_T8_urcPort
open intervalIntegral

theorem GLP023B4c_T8_urc_integral_derivative_mul_derivative_mul_comm (w p q : ℝ[X]) {a b : ℝ} (ha : w.eval a = 0)
    (hb : w.eval b = 0) :
    ∫ x in a..b, (derivative (w * derivative p) * q).eval x =
      ∫ x in a..b, (p * derivative (w * derivative q)).eval x := by
  have key : derivative (w * derivative p) * q - p * derivative (w * derivative q) =
      derivative (w * (derivative p * q - p * derivative q)) := by
    simp only [derivative_mul, derivative_sub]
    ring
  rw [← sub_eq_zero, ← integral_sub ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)]
  simp_rw [← eval_sub, key]
  rw [integral_deriv_eq_sub' _ (_root_.funext fun x => Polynomial.deriv _)
    (fun x _ => Polynomial.differentiableAt _) (Polynomial.continuous _).continuousOn]
  -- the leading coefficient `w` vanishes at both endpoints, so the boundary term drops
  simp only [eval_mul, ha, hb, zero_mul, sub_self]


noncomputable def GLP023B4c_T8_urc_legendre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => C ((n + 2 : ℝ)⁻¹) *
      ((2 * n + 3 : ℝ[X]) * X * GLP023B4c_T8_urc_legendre (n + 1) - (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre n)


@[simp] theorem GLP023B4c_T8_urc_legendre_zero : GLP023B4c_T8_urc_legendre 0 = 1 := by rw [GLP023B4c_T8_urc_legendre]


@[simp] theorem GLP023B4c_T8_urc_legendre_one : GLP023B4c_T8_urc_legendre 1 = X := by rw [GLP023B4c_T8_urc_legendre]


theorem GLP023B4c_T8_urc_legendre_add_two (n : ℕ) : GLP023B4c_T8_urc_legendre (n + 2) = C ((n + 2 : ℝ)⁻¹) *
    ((2 * n + 3 : ℝ[X]) * X * GLP023B4c_T8_urc_legendre (n + 1) - (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre n) := by
  rw [GLP023B4c_T8_urc_legendre]


theorem GLP023B4c_T8_urc_add_two_mul_legendre_add_two (n : ℕ) : (n + 2 : ℝ[X]) * GLP023B4c_T8_urc_legendre (n + 2) =
    (2 * n + 3 : ℝ[X]) * X * GLP023B4c_T8_urc_legendre (n + 1) - (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre n := by
  have hcoeff : (n + 2 : ℝ[X]) = C (n + 2 : ℝ) := by
    rw [map_add, C_eq_natCast, C_ofNat]
  rw [GLP023B4c_T8_urc_legendre_add_two, hcoeff, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (by positivity), C_1,
    one_mul]


theorem GLP023B4c_T8_urc_add_two_mul_legendre_add_two_eval (n : ℕ) (x : ℝ) : (n + 2) * (GLP023B4c_T8_urc_legendre (n + 2)).eval x =
    (2 * n + 3) * x * (GLP023B4c_T8_urc_legendre (n + 1)).eval x - (n + 1) * (GLP023B4c_T8_urc_legendre n).eval x := by
  simpa using congrArg (eval x) (GLP023B4c_T8_urc_add_two_mul_legendre_add_two n)


@[simp] theorem GLP023B4c_T8_urc_legendre_eval_one (n : ℕ) : (GLP023B4c_T8_urc_legendre n).eval 1 = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have h := GLP023B4c_T8_urc_add_two_mul_legendre_add_two_eval n 1
    rw [h₀, h₁] at h
    exact mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) (by linear_combination h)


theorem GLP023B4c_T8_urc_legendre_comp_neg_X (n : ℕ) : (GLP023B4c_T8_urc_legendre n).comp (-X) = (-1) ^ n * GLP023B4c_T8_urc_legendre n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have hne : (n + 2 : ℝ[X]) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    refine mul_left_cancel₀ hne ?_
    have h := congrArg (·.comp (-X)) (GLP023B4c_T8_urc_add_two_mul_legendre_add_two n)
    simp only [mul_comp, sub_comp, add_comp, natCast_comp, ofNat_comp, one_comp, X_comp, h₀, h₁,
      Nat.cast_ofNat] at h
    linear_combination h - (-1) ^ n * GLP023B4c_T8_urc_add_two_mul_legendre_add_two n


@[simp] theorem GLP023B4c_T8_urc_legendre_eval_neg (n : ℕ) (x : ℝ) :
    (GLP023B4c_T8_urc_legendre n).eval (-x) = (-1) ^ n * (GLP023B4c_T8_urc_legendre n).eval x := by
  simpa using congrArg (eval x) (GLP023B4c_T8_urc_legendre_comp_neg_X n)


theorem GLP023B4c_T8_urc_add_two_mul_coeff_legendre_add_two (n k : ℕ) :
    (n + 2) * (GLP023B4c_T8_urc_legendre (n + 2)).coeff (k + 1) =
      (2 * n + 3) * (GLP023B4c_T8_urc_legendre (n + 1)).coeff k - (n + 1) * (GLP023B4c_T8_urc_legendre n).coeff (k + 1) := by
  have h := congrArg (coeff · (k + 1)) (GLP023B4c_T8_urc_add_two_mul_legendre_add_two n)
  simpa [add_mul, sub_mul, mul_assoc, coeff_X_mul] using h


private theorem GLP023B4c_T8_urc_coeff_legendre_of_lt {n k : ℕ} (h : n < k) : (GLP023B4c_T8_urc_legendre n).coeff k = 0 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [coeff_one, h.ne']
  | one => simp [coeff_X, h.ne]
  | more n h₀ h₁ =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h' := GLP023B4c_T8_urc_add_two_mul_coeff_legendre_add_two n k
    rw [h₀ (by omega), h₁ (by omega)] at h'
    exact (mul_eq_zero.mp (h'.trans (by ring))).resolve_left (by positivity)


@[simp] theorem GLP023B4c_T8_urc_coeff_legendre_self (n : ℕ) : (GLP023B4c_T8_urc_legendre n).coeff n = n.centralBinom / 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Nat.centralBinom]
  | more n _ h₁ =>
    have h := GLP023B4c_T8_urc_add_two_mul_coeff_legendre_add_two n (n + 1)
    rw [h₁, GLP023B4c_T8_urc_coeff_legendre_of_lt (n := n) (k := n + 1 + 1) (by omega)] at h
    have hc : ((n + 2 : ℕ) : ℝ) * (n + 2).centralBinom = 2 * (2 * (n + 1 : ℕ) + 1) *
        (n + 1).centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ (n + 1)
    push_cast at hc
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    rw [h, mul_zero, sub_zero, pow_succ 2 (n + 1)]
    field_simp
    linear_combination -hc

private theorem GLP023B4c_T8_urc_coeff_legendre_self_ne_zero (n : ℕ) : (GLP023B4c_T8_urc_legendre n).coeff n ≠ 0 := by
  rw [GLP023B4c_T8_urc_coeff_legendre_self]
  exact div_ne_zero (by exact_mod_cast n.centralBinom_ne_zero) (by positivity)


@[simp] theorem GLP023B4c_T8_urc_legendre_ne_zero (n : ℕ) : GLP023B4c_T8_urc_legendre n ≠ 0 := fun h =>
  GLP023B4c_T8_urc_coeff_legendre_self_ne_zero n (by rw [h, coeff_zero])


@[simp] theorem GLP023B4c_T8_urc_natDegree_legendre (n : ℕ) : (GLP023B4c_T8_urc_legendre n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _ h => GLP023B4c_T8_urc_coeff_legendre_of_lt (by exact_mod_cast h))
    (GLP023B4c_T8_urc_coeff_legendre_self_ne_zero n)


@[simp] theorem GLP023B4c_T8_urc_degree_legendre (n : ℕ) : (GLP023B4c_T8_urc_legendre n).degree = n :=
  (degree_eq_iff_natDegree_eq (GLP023B4c_T8_urc_legendre_ne_zero n)).mpr (GLP023B4c_T8_urc_natDegree_legendre n)


@[simp] theorem GLP023B4c_T8_urc_leadingCoeff_legendre (n : ℕ) :
    (GLP023B4c_T8_urc_legendre n).leadingCoeff = n.centralBinom / 2 ^ n := by
  rw [leadingCoeff, GLP023B4c_T8_urc_natDegree_legendre, GLP023B4c_T8_urc_coeff_legendre_self]


private theorem GLP023B4c_T8_urc_derivative_legendre_add_two_of {n : ℕ}
    (h : X * derivative (GLP023B4c_T8_urc_legendre (n + 1)) =
      derivative (GLP023B4c_T8_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre (n + 1)) :
    derivative (GLP023B4c_T8_urc_legendre (n + 2)) =
      X * derivative (GLP023B4c_T8_urc_legendre (n + 1)) + (n + 2 : ℝ[X]) * GLP023B4c_T8_urc_legendre (n + 1) := by
  have hd := congrArg derivative (GLP023B4c_T8_urc_add_two_mul_legendre_add_two n)
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast, derivative_ofNat,
    derivative_X, derivative_one, mul_zero, add_zero, zero_add, zero_mul, mul_one] at hd
  have hne : (n + 2 : ℝ[X]) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  refine mul_left_cancel₀ hne ?_
  linear_combination hd + (n + 1) * h

private theorem GLP023B4c_T8_urc_derivative_legendre_ladder (n : ℕ) :
    X * derivative (GLP023B4c_T8_urc_legendre (n + 1)) =
        derivative (GLP023B4c_T8_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre (n + 1) ∧
      (1 - X ^ 2) * derivative (GLP023B4c_T8_urc_legendre (n + 1)) =
        (n + 1 : ℝ[X]) * (GLP023B4c_T8_urc_legendre n - X * GLP023B4c_T8_urc_legendre (n + 1)) := by
  induction n with
  | zero => constructor <;> simp [sq]
  | succ n ih =>
    have hb := GLP023B4c_T8_urc_derivative_legendre_add_two_of ih.1
    have hr := GLP023B4c_T8_urc_add_two_mul_legendre_add_two n
    push_cast
    constructor
    · linear_combination X * hb - ih.2 - hr
    · linear_combination (1 - X ^ 2) * hb + X * ih.2 + X * hr


theorem GLP023B4c_T8_urc_derivative_legendre_succ (n : ℕ) :
    derivative (GLP023B4c_T8_urc_legendre (n + 1)) = X * derivative (GLP023B4c_T8_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := GLP023B4c_T8_urc_derivative_legendre_add_two_of (GLP023B4c_T8_urc_derivative_legendre_ladder n).1
    push_cast at h ⊢
    linear_combination h


theorem GLP023B4c_T8_urc_X_mul_derivative_legendre_succ (n : ℕ) :
    X * derivative (GLP023B4c_T8_urc_legendre (n + 1)) =
      derivative (GLP023B4c_T8_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B4c_T8_urc_legendre (n + 1) :=
  (GLP023B4c_T8_urc_derivative_legendre_ladder n).1


theorem GLP023B4c_T8_urc_one_sub_X_sq_mul_derivative_legendre_succ (n : ℕ) :
    (1 - X ^ 2) * derivative (GLP023B4c_T8_urc_legendre (n + 1)) =
      (n + 1 : ℝ[X]) * (GLP023B4c_T8_urc_legendre n - X * GLP023B4c_T8_urc_legendre (n + 1)) :=
  (GLP023B4c_T8_urc_derivative_legendre_ladder n).2


theorem GLP023B4c_T8_urc_derivative_one_sub_X_sq_mul_derivative_legendre (n : ℕ) :
    derivative ((1 - X ^ 2) * derivative (GLP023B4c_T8_urc_legendre n)) =
      -((n : ℝ[X]) * ((n : ℝ[X]) + 1)) * GLP023B4c_T8_urc_legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [GLP023B4c_T8_urc_one_sub_X_sq_mul_derivative_legendre_succ]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast, derivative_one,
      derivative_X, zero_mul, zero_add, one_mul]
    push_cast
    linear_combination -(n + 1 : ℝ[X]) * GLP023B4c_T8_urc_X_mul_derivative_legendre_succ n

section Orthogonality

open MeasureTheory intervalIntegral


theorem GLP023B4c_T8_urc_integral_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (GLP023B4c_T8_urc_legendre m).eval x * (GLP023B4c_T8_urc_legendre n).eval x = 0 := by
  have hs := GLP023B4c_T8_urc_integral_derivative_mul_derivative_mul_comm (1 - X ^ 2) (GLP023B4c_T8_urc_legendre m) (GLP023B4c_T8_urc_legendre n)
    (a := -1) (b := 1) (by norm_num) (by norm_num)
  have e : ∀ (k : ℕ) (p q : ℝ[X]) (x : ℝ), eval x (-((k : ℝ[X]) * (k + 1)) * p * q) =
      -((k : ℝ) * (k + 1)) * (eval x p * eval x q) := fun k p q x => by
    simp only [eval_mul, eval_neg, eval_natCast, eval_add, eval_one]
    ring
  rw [GLP023B4c_T8_urc_derivative_one_sub_X_sq_mul_derivative_legendre,
    GLP023B4c_T8_urc_derivative_one_sub_X_sq_mul_derivative_legendre, mul_comm (GLP023B4c_T8_urc_legendre m)] at hs
  simp_rw [e, mul_comm (eval _ (GLP023B4c_T8_urc_legendre n)), intervalIntegral.integral_const_mul] at hs
  have hmn : (m : ℝ) * (m + 1) ≠ n * (n + 1) := by
    intro he
    have : m * (m + 1) = n * (n + 1) := by exact_mod_cast he
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt
    · exact (Nat.mul_lt_mul'' hlt (Nat.succ_lt_succ hlt)).ne this
    · exact (Nat.mul_lt_mul'' hlt (Nat.succ_lt_succ hlt)).ne' this
  exact (mul_eq_zero.mp (by linear_combination hs : ((n : ℝ) * (n + 1) - m * (m + 1)) *
    ∫ x in (-1 : ℝ)..1, (GLP023B4c_T8_urc_legendre m).eval x * (GLP023B4c_T8_urc_legendre n).eval x = 0)).resolve_left
    (sub_ne_zero.mpr hmn.symm)


private theorem GLP023B4c_T8_urc_add_two_mul_integral_legendre_add_two_mul (n : ℕ) (q : ℝ[X]) :
    (n + 2) * ∫ x in (-1 : ℝ)..1, (GLP023B4c_T8_urc_legendre (n + 2)).eval x * q.eval x =
      (2 * n + 3) * (∫ x in (-1 : ℝ)..1, x * (GLP023B4c_T8_urc_legendre (n + 1)).eval x * q.eval x) -
        (n + 1) * ∫ x in (-1 : ℝ)..1, (GLP023B4c_T8_urc_legendre n).eval x * q.eval x := by
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  exact integral_congr fun x _ => by
    linear_combination q.eval x * GLP023B4c_T8_urc_add_two_mul_legendre_add_two_eval n x


theorem GLP023B4c_T8_urc_integral_legendre_mul_self (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (GLP023B4c_T8_urc_legendre n).eval x * (GLP023B4c_T8_urc_legendre n).eval x = 2 / (2 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
    simp only [GLP023B4c_T8_urc_legendre_one, eval_X, ← sq]
    rw [integral_pow]
    norm_num
  | more n _ h₁ =>
    -- pair the recurrence for `Pₙ₊₂` with `Pₙ₊₂`, and the one for `Pₙ₊₃` with `Pₙ₊₁`;
    -- both produce the mixed integral `K = ∫ x Pₙ₊₁ Pₙ₊₂`
    have hA := GLP023B4c_T8_urc_add_two_mul_integral_legendre_add_two_mul n (GLP023B4c_T8_urc_legendre (n + 2))
    have hB := GLP023B4c_T8_urc_add_two_mul_integral_legendre_add_two_mul (n + 1) (GLP023B4c_T8_urc_legendre (n + 1))
    rw [GLP023B4c_T8_urc_integral_legendre_mul_legendre_of_ne (by omega : n ≠ n + 2), mul_zero, sub_zero] at hA
    rw [GLP023B4c_T8_urc_integral_legendre_mul_legendre_of_ne (by omega : n + 1 + 2 ≠ n + 1), h₁, mul_zero] at hB
    have hK : ∫ x in (-1 : ℝ)..1, x * (GLP023B4c_T8_urc_legendre (n + 1 + 1)).eval x * (GLP023B4c_T8_urc_legendre (n + 1)).eval x =
        ∫ x in (-1 : ℝ)..1, x * (GLP023B4c_T8_urc_legendre (n + 1)).eval x * (GLP023B4c_T8_urc_legendre (n + 2)).eval x :=
      integral_congr fun x _ => by ring
    rw [hK] at hB
    set K := ∫ x in (-1 : ℝ)..1, x * (GLP023B4c_T8_urc_legendre (n + 1)).eval x * (GLP023B4c_T8_urc_legendre (n + 2)).eval x
    have h3 : (2 * n + 3 : ℝ) * (2 / (2 * n + 3)) = 2 := by field_simp
    push_cast at hB ⊢
    rw [eq_div_iff (by positivity)]
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    linear_combination (2 * n + 5) * hA - (2 * n + 3) * hB + (n + 2) * h3


theorem GLP023B4c_T8_urc_integral_legendre_mul_legendre (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (GLP023B4c_T8_urc_legendre m).eval x * (GLP023B4c_T8_urc_legendre n).eval x =
      if m = n then (2 / (2 * n + 1) : ℝ) else 0 := by
  split_ifs with h
  · subst h
    exact GLP023B4c_T8_urc_integral_legendre_mul_self m
  · exact GLP023B4c_T8_urc_integral_legendre_mul_legendre_of_ne h


end Orthogonality

end GLP023B4c_T8_urcPort

lemma GLP023B4c_T8_urc_even_at_zero (m : ℕ) :
    (GLP023B4c_T8_urc_legendre (2 * m)).eval 0 = (-1 : ℝ) ^ m * centralBinomial m := by
  induction m with
  | zero => norm_num [centralBinomial]
  | succ m ih =>
    have hr := GLP023B4c_T8_urc_add_two_mul_legendre_add_two_eval (2 * m) 0
    have hc := central_binomial_recurrence m
    rw [ih] at hr
    have hidx : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hidx, pow_succ]
    push_cast at hr
    apply mul_left_cancel₀ (by positivity : (2 * (m : ℝ) + 2) ≠ 0)
    linear_combination hr + (-1 : ℝ) ^ m * hc

lemma GLP023B4c_T8_urc_half_odd (m : ℕ) :
    (∫ x in (0 : ℝ)..1, (GLP023B4c_T8_urc_legendre (2 * m + 1)).eval x) =
      (-1 : ℝ) ^ m * centralBinomial m / (2 * (m : ℝ) + 2) := by
  let P := GLP023B4c_T8_urc_legendre (2 * m + 1)
  let A := (1 - X ^ 2) * derivative P
  have hd : (derivative P).eval 0 =
      (2 * (m : ℝ) + 1) * ((-1 : ℝ) ^ m * centralBinomial m) := by
    have h := congrArg (Polynomial.eval (0 : ℝ)) (GLP023B4c_T8_urc_derivative_legendre_succ (2 * m))
    simpa [P, GLP023B4c_T8_urc_even_at_zero] using h
  have hi : (∫ x in (0 : ℝ)..1, (derivative A).eval x) = A.eval 1 - A.eval 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub' _ (_root_.funext fun x => Polynomial.deriv _)
      (fun x _ => Polynomial.differentiableAt _) (Polynomial.continuous _).continuousOn]
  have he : (∫ x in (0 : ℝ)..1, (derivative A).eval x) =
      -((2 * (m : ℝ) + 1) * (2 * m + 2)) *
        ∫ x in (0 : ℝ)..1, P.eval x := by
    dsimp only [A, P]
    rw [GLP023B4c_T8_urc_derivative_one_sub_X_sq_mul_derivative_legendre]
    simp only [eval_mul, eval_neg, eval_add, eval_natCast, eval_one, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, eval_ofNat, intervalIntegral.integral_const_mul]
    ring
  rw [he] at hi
  have ha : A.eval 1 - A.eval 0 =
      -(2 * (m : ℝ) + 1) * ((-1 : ℝ) ^ m * centralBinomial m) := by
    simp [A, hd]
    ring
  rw [ha] at hi
  apply (eq_div_iff (by positivity : (2 * (m : ℝ) + 2) ≠ 0)).mpr
  apply mul_left_cancel₀ (by positivity : (2 * (m : ℝ) + 1) ≠ 0)
  linear_combination -hi

lemma GLP023B4c_T8_urc_expectation (f : ℝ → ℝ) :
    expectation uniformMargins f = (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, f x := by
  unfold expectation uniformMargins
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

lemma GLP023B4c_T8_urc_inner (m n : ℕ) :
    expectation uniformMargins (fun x => (GLP023B4c_T8_urc_legendre m).eval x *
      (GLP023B4c_T8_urc_legendre n).eval x) =
      if m = n then (1 / (2 * (n : ℝ) + 1) : ℝ) else 0 := by
  rw [GLP023B4c_T8_urc_expectation, GLP023B4c_T8_urc_integral_legendre_mul_legendre]
  split_ifs <;> ring

lemma GLP023B4c_T8_urc_party_integral (p : Polynomial ℝ) :
    expectation uniformMargins (fun x => party x * p.eval x) =
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, p.eval x := by
  have he : (fun x => party x * p.eval x) = (Ici (0 : ℝ)).indicator (fun x => p.eval x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [party, hx, Set.indicator]
  have hi : Ici (0 : ℝ) ∩ Icc (-1 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h0, _, h1⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by linarith, h1⟩
  unfold expectation uniformMargins
  rw [integral_smul_measure, he, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hi, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

lemma GLP023B4c_T8_urc_party_even (m : ℕ) :
    expectation uniformMargins (fun x => party x *
      (GLP023B4c_T8_urc_legendre (2 * m + 2)).eval x) = 0 := by
  let p := GLP023B4c_T8_urc_legendre (2 * m + 2)
  have hwhole : (∫ x in (-1 : ℝ)..1, p.eval x) = 0 := by
    simpa only [GLP023B4c_T8_urc_legendre_zero, eval_one, mul_one] using
      GLP023B4c_T8_urc_integral_legendre_mul_legendre_of_ne
        (m := 2 * m + 2) (n := 0) (by omega)
  have heven (x : ℝ) : p.eval (-x) = p.eval x := by
    simp [p, GLP023B4c_T8_urc_legendre_eval_neg, pow_add, pow_mul]
  have hneg : (∫ x in (-1 : ℝ)..0, p.eval x) = ∫ x in (0 : ℝ)..1, p.eval x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, p.eval (-x) := by
        simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
          (fun x => p.eval x) (a := 0) (b := 1)).symm
      _ = _ := by simp_rw [heven]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (p.continuous.intervalIntegrable (μ := volume) (a := -1) (b := 0))
    (p.continuous.intervalIntegrable (μ := volume) (a := 0) (b := 1))
  rw [hwhole, hneg] at hi
  rw [GLP023B4c_T8_urc_party_integral]
  change (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1, p.eval x) = 0
  linarith

lemma GLP023B4c_T8_urc_party_odd (m : ℕ) :
    expectation uniformMargins (fun x => party x *
      (GLP023B4c_T8_urc_legendre (2 * m + 1)).eval x) =
      (-1 : ℝ) ^ m * centralBinomial m / (4 * (m : ℝ) + 4) := by
  rw [GLP023B4c_T8_urc_party_integral, GLP023B4c_T8_urc_half_odd]
  field_simp
  <;> ring

def GLP023B4c_T8_urc_moment (k : ℕ) : ℝ :=
  expectation uniformMargins (fun x => party x * (GLP023B4c_T8_urc_legendre k).eval x)

def GLP023B4c_T8_urc_q (J : ℕ) : Polynomial ℝ :=
  ∑ k : Fin (J + 1), ((2 * (k : ℕ) + 1 : ℝ) * GLP023B4c_T8_urc_moment k) •
    GLP023B4c_T8_urc_legendre k

lemma GLP023B4c_T8_urc_q_degree (J : ℕ) : (GLP023B4c_T8_urc_q J).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  rw [Polynomial.smul_eq_C_mul]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    rw [GLP023B4c_T8_urc_natDegree_legendre]
    omega)

def GLP023B4c_T8_urc_pair (f : ℝ → ℝ) (hf : GLP023B4c_T8_cpb_Bounded f) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := expectation uniformMargins (fun x => f x * p.eval x)
  map_add' p q := by
    simp only [eval_add, mul_add]
    exact integral_add
      (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B4c_T8_cpb_mul hf (GLP023B4c_T8_cpb_poly p)))
      (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B4c_T8_cpb_mul hf (GLP023B4c_T8_cpb_poly q)))
  map_smul' r p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    change expectation uniformMargins (fun x => f x * (r * p.eval x)) = _
    simp_rw [show ∀ x, f x * (r * p.eval x) = r * (f x * p.eval x) by intro x; ring]
    exact integral_const_mul _ _

lemma GLP023B4c_T8_urc_q_inner (J : ℕ) (k : Fin (J + 1)) :
    expectation uniformMargins (fun x => (GLP023B4c_T8_urc_q J).eval x *
      (GLP023B4c_T8_urc_legendre k).eval x) = GLP023B4c_T8_urc_moment k := by
  let F := GLP023B4c_T8_urc_pair (fun x => (GLP023B4c_T8_urc_legendre k).eval x)
    (GLP023B4c_T8_cpb_poly _)
  have he : expectation uniformMargins (fun x => (GLP023B4c_T8_urc_q J).eval x *
      (GLP023B4c_T8_urc_legendre k).eval x) = F (GLP023B4c_T8_urc_q J) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [he]
  unfold GLP023B4c_T8_urc_q
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hF (i : Fin (J + 1)) : F (GLP023B4c_T8_urc_legendre i) =
      if i = k then 1 / (2 * (k : ℕ) + 1 : ℝ) else 0 := by
    change expectation uniformMargins _ = _
    rw [GLP023B4c_T8_urc_inner]
    by_cases hi : i = k
    · subst i
      simp
    · have hki : (k : ℕ) ≠ i := by intro h; exact hi (Fin.ext h.symm)
      simp only [if_neg hi, if_neg hki]
  simp_rw [hF]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
    field_simp
  · intro i _ hi
    rw [if_neg hi, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

lemma GLP023B4c_T8_urc_q_spec (J : ℕ) : IsProjection uniformMargins J (GLP023B4c_T8_urc_q J) := by
  let r := fun x => party x - (GLP023B4c_T8_urc_q J).eval x
  have hr : GLP023B4c_T8_cpb_Bounded r :=
    GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly _)
  let F := GLP023B4c_T8_urc_pair r hr
  let S : Polynomial.Sequence ℝ := ⟨GLP023B4c_T8_urc_legendre, GLP023B4c_T8_urc_degree_legendre⟩
  have hspan : Submodule.span ℝ (S '' Set.Iic J) ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro p ⟨k, hk, rfl⟩
    change k ≤ J at hk
    change expectation uniformMargins (fun x => r x * (GLP023B4c_T8_urc_legendre k).eval x) = 0
    dsimp only [r]
    simp_rw [sub_mul]
    unfold expectation
    rw [integral_sub
      (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B4c_T8_cpb_mul GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly _)))
      (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B4c_T8_cpb_mul (GLP023B4c_T8_cpb_poly _) (GLP023B4c_T8_cpb_poly _)))]
    change GLP023B4c_T8_urc_moment k - expectation uniformMargins _ = 0
    rw [GLP023B4c_T8_urc_q_inner J (⟨k, by omega⟩ : Fin (J + 1)), sub_self]
  refine ⟨GLP023B4c_T8_urc_q_degree J, ?_⟩
  intro j hj
  have hp : (Polynomial.X ^ j : Polynomial ℝ) ∈ Submodule.span ℝ (S '' Set.Iic J) := by
    rw [S.span_degreeLE (fun i _ => isUnit_iff_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr (S.ne_zero i)))]
    apply Polynomial.mem_degreeLE.mpr
    simpa only [Polynomial.degree_X_pow, Nat.cast_le] using hj
  have hh := hspan hp
  change expectation uniformMargins (fun x => r x * (X ^ j).eval x) = 0 at hh
  simpa only [eval_pow, eval_X] using hh

lemma GLP023B4c_T8_urc_square_zero (p : Polynomial ℝ)
    (hz : expectation uniformMargins (fun x => p.eval x ^ 2) = 0) : p = 0 := by
  have hint := GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
    (GLP023B4c_T8_cpb_square (GLP023B4c_T8_cpb_poly p))
  have hae : ∀ᵐ x ∂uniformMargins, p.eval x = 0 := by
    have hs := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) hint).mp hz
    exact hs.mono (fun x hx => (sq_eq_zero_iff).mp hx)
  have hae' : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1), p.eval x = 0 :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)).mp hae
  have heq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (-1 : ℝ) ≠ 1) hae'
    p.continuous.continuousOn continuous_const.continuousOn
  apply p.eq_zero_of_infinite_isRoot
  exact (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
    (fun x hx => heq ⟨hx.1.le, hx.2.le⟩)

lemma GLP023B4c_T8_urc_projection_eq (J : ℕ) : projection uniformMargins J = GLP023B4c_T8_urc_q J := by
  have hq := GLP023B4c_T8_urc_q_spec J
  have hp : IsProjection uniformMargins J (projection uniformMargins J) :=
    Classical.epsilon_spec ⟨_, hq⟩
  let p := projection uniformMargins J
  let q := GLP023B4c_T8_urc_q J
  have hd : (p - q).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le p q).trans (max_le hp.1 hq.1)
  have h1 := GLP023B4c_T8_cpb_test_poly uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J p hp (p - q) hd
  have h2 := GLP023B4c_T8_cpb_test_poly uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J q hq (p - q) hd
  apply sub_eq_zero.mp
  apply GLP023B4c_T8_urc_square_zero
  have he : (fun x => (p - q).eval x ^ 2) =
      (fun x => (party x - q.eval x) * (p - q).eval x -
        (party x - p.eval x) * (p - q).eval x) := by
    funext x
    simp only [eval_sub]
    ring
  unfold expectation at *
  rw [he, integral_sub
    (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B4c_T8_cpb_mul (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q))
        (GLP023B4c_T8_cpb_poly _)))
    (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B4c_T8_cpb_mul (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly p))
        (GLP023B4c_T8_cpb_poly _))), h2, h1, sub_self]

def GLP023B4c_T8_urc_score (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * GLP023B4c_T8_urc_moment k ^ 2

lemma GLP023B4c_T8_urc_moment_zero : GLP023B4c_T8_urc_moment 0 = 1 / 2 := by
  unfold GLP023B4c_T8_urc_moment
  rw [GLP023B4c_T8_urc_party_integral]
  norm_num

lemma GLP023B4c_T8_urc_score_even (m : ℕ) : GLP023B4c_T8_urc_score (2 * m + 2) = 0 := by
  unfold GLP023B4c_T8_urc_score GLP023B4c_T8_urc_moment
  rw [GLP023B4c_T8_urc_party_even]
  ring

lemma GLP023B4c_T8_urc_score_odd (m : ℕ) :
    GLP023B4c_T8_urc_score (2 * m + 1) = (centralBinomial m ^ 2 - centralBinomial (m + 1) ^ 2) / 4 := by
  have hrec : centralBinomial (m + 1) =
      centralBinomial m * (2 * (m : ℝ) + 1) / (2 * m + 2) :=
    (eq_div_iff (by positivity)).mpr (central_binomial_recurrence m)
  have hsign : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
    norm_num
  unfold GLP023B4c_T8_urc_score GLP023B4c_T8_urc_moment
  rw [GLP023B4c_T8_urc_party_odd, hrec]
  push_cast
  rw [div_pow, mul_pow, hsign, one_mul]
  field_simp
  <;> ring

lemma GLP023B4c_T8_urc_partial_odd (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), GLP023B4c_T8_urc_score k) =
      1 / 2 - centralBinomial n ^ 2 / 4 := by
  induction n with
  | zero => norm_num [GLP023B4c_T8_urc_score, GLP023B4c_T8_urc_moment_zero, centralBinomial]
  | succ n ih =>
    have hi : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [hi, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      GLP023B4c_T8_urc_score_odd, GLP023B4c_T8_urc_score_even]
    ring

lemma GLP023B4c_T8_urc_partial_even (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 2), GLP023B4c_T8_urc_score k) =
      1 / 2 - centralBinomial (n + 1) ^ 2 / 4 := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Finset.sum_range_succ,
    GLP023B4c_T8_urc_partial_odd, GLP023B4c_T8_urc_score_odd]
  ring

lemma GLP023B4c_T8_urc_variance_sum (J : ℕ) : residualVariance uniformMargins J =
    1 / 2 - ∑ k ∈ Finset.range (J + 1), GLP023B4c_T8_urc_score k := by
  let q := GLP023B4c_T8_urc_q J
  have hq := GLP023B4c_T8_urc_q_spec J
  have horth := GLP023B4c_T8_cpb_test_poly uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J q hq q hq.1
  have hDq : expectation uniformMargins (fun x => party x * q.eval x) =
      ∑ k ∈ Finset.range (J + 1), GLP023B4c_T8_urc_score k := by
    change GLP023B4c_T8_urc_pair party GLP023B4c_T8_cpb_party (GLP023B4c_T8_urc_q J) = _
    unfold GLP023B4c_T8_urc_q
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    change ((2 * (k : ℕ) + 1 : ℝ) * GLP023B4c_T8_urc_moment k) * GLP023B4c_T8_urc_moment k = _
    unfold GLP023B4c_T8_urc_score
    ring
  have hD : expectation uniformMargins party = 1 / 2 := by
    simpa only [GLP023B4c_T8_urc_moment, GLP023B4c_T8_urc_legendre_zero, eval_one, mul_one]
      using GLP023B4c_T8_urc_moment_zero
  have he : (fun x => (party x - q.eval x) ^ 2) =
      (fun x => party x - party x * q.eval x - (party x - q.eval x) * q.eval x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [party, hx] <;> ring
  unfold residualVariance popResidual
  rw [GLP023B4c_T8_urc_projection_eq]
  change expectation uniformMargins (fun x => (party x - q.eval x) ^ 2) = _
  unfold expectation
  rw [he, integral_sub
    (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party
        (GLP023B4c_T8_cpb_mul GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q))))
    (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B4c_T8_cpb_mul (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q))
        (GLP023B4c_T8_cpb_poly q))),
    integral_sub
      (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2 GLP023B4c_T8_cpb_party)
      (GLP023B4c_T8_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B4c_T8_cpb_mul GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q)))]
  change expectation uniformMargins party - expectation uniformMargins _ - expectation uniformMargins _ = _
  rw [hD, hDq, horth, sub_zero]

lemma GLP023B4c_T8_urc_variance (J : ℕ) : residualVariance uniformMargins J =
    centralBinomial ((J + 1) / 2) ^ 2 / 4 := by
  rw [GLP023B4c_T8_urc_variance_sum]
  by_cases hmod : J % 2 = 0
  · have hlen : J + 1 = 2 * (J / 2) + 1 := by omega
    have hidx : (J + 1) / 2 = J / 2 := by omega
    rw [hidx, hlen, GLP023B4c_T8_urc_partial_odd]
    ring
  · have hlen : J + 1 = 2 * (J / 2) + 2 := by omega
    have hidx : (J + 1) / 2 = J / 2 + 1 := by omega
    rw [hidx, hlen, GLP023B4c_T8_urc_partial_even]
    ring


/-! Local density and projection comparison. -/
/-- A polynomial version of a design column with the party value fixed. -/
def GLP023B4c_T8_column_polynomial (J : ℕ) (j : Fin (J+2)) (d : ℝ) : Polynomial ℝ :=
  if j.val=0 then 1 else if j.val=1 then C d else X^(j.val-1)

/-- The fitted polynomial on either side of zero. -/
def GLP023B4c_T8_fit_polynomial (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ) : Polynomial ℝ :=
  ∑ j, C (a j)*GLP023B4c_T8_column_polynomial J j d

theorem GLP023B4c_T8_column_piecewise (J : ℕ) (j : Fin (J+2)) (x : ℝ) :
    polynomialDesign J (fun x : ℝ => x) party x j =
      if 0 ≤ x then (GLP023B4c_T8_column_polynomial J j 1).eval x
        else (GLP023B4c_T8_column_polynomial J j 0).eval x := by
  by_cases hj0 : j.val=0 <;> by_cases hj1 : j.val=1 <;> by_cases hx : 0 ≤ x <;>
    simp [polynomialDesign, GLP023B4c_T8_column_polynomial, party, hx, hj0, hj1]

theorem GLP023B4c_T8_fit_piecewise (J : ℕ) (a : Fin (J+2) → ℝ) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) a x =
      if 0 ≤ x then (GLP023B4c_T8_fit_polynomial J a 1).eval x
        else (GLP023B4c_T8_fit_polynomial J a 0).eval x := by
  simp_rw [predict, GLP023B4c_T8_column_piecewise]
  by_cases hx : 0 ≤ x <;>
    simp [hx, GLP023B4c_T8_fit_polynomial, Polynomial.eval_finsetSum, mul_comm]

/-- The constant coefficient of either fitted polynomial. -/
theorem GLP023B4c_T8_fit_coeff_zero (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ) :
    (GLP023B4c_T8_fit_polynomial J a d).coeff 0 = a ⟨0,by omega⟩ + a ⟨1,by omega⟩*d := by
  simp [GLP023B4c_T8_fit_polynomial, Polynomial.finsetSum_coeff, Fin.sum_univ_succ,
    GLP023B4c_T8_column_polynomial, Polynomial.coeff_C_mul_X_pow]

theorem GLP023B4c_T8_fit_coeff_pos (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkJ : k ≤ J) :
    (GLP023B4c_T8_fit_polynomial J a d).coeff k = a ⟨k+1,by omega⟩ := by
  have hk0 : k ≠ 0 := by omega
  unfold GLP023B4c_T8_fit_polynomial
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨k+1,by omega⟩ : Fin (J+2))]
  · simp [GLP023B4c_T8_column_polynomial, hk0, Polynomial.coeff_C_mul_X_pow]
  · intro j _ hj
    have hv : j.val ≠ k+1 := fun h => hj (Fin.ext h)
    by_cases h0 : j.val=0
    · simp [GLP023B4c_T8_column_polynomial, h0, Polynomial.coeff_C, hk0]
    · by_cases h1 : j.val=1
      · simp [GLP023B4c_T8_column_polynomial,h0,h1, Polynomial.coeff_C, hk0]
      · simp [GLP023B4c_T8_column_polynomial,h0,h1, Polynomial.coeff_C_mul_X_pow,
          show k ≠ j.val-1 by omega]
  · simp

/-- Local Lebesgue domination gives full rank of (1,D,x,...,x^J). -/
theorem GLP023B4c_T8_full_rank_of_domination (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hdom : ENNReal.ofReal c • (volume : Measure ℝ).restrict (Icc (-δ) δ) ≤ μ)
    (J : ℕ) : MomentPositiveDefinite μ J := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  intro a ha
  let X := polynomialDesign J (fun x : ℝ => x) party
  have hn : 0 ≤ expectation μ (fun x => predict X a x^2) := integral_nonneg (fun x => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  have hz' : expectation μ (fun x => predict X a x^2)=0 := hz.symm
  have hae : ∀ᵐ x ∂μ, predict X a x=0 := by
    have hsq := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (predict X a x))
      (GLP023B4c_T8_cpb_integrable hp hs (GLP023B4c_T8_cpb_square
        (GLP023B4c_T8_cpb_predict _ (GLP023B4c_T8_cpb_design J) a)))).mp hz'
    filter_upwards [hsq] with x hx
    exact sq_eq_zero_iff.mp hx
  have halocal : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-δ) δ), predict X a x=0 :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp
      (ae_mono hdom hae)
  have hneg : GLP023B4c_T8_fit_polynomial J a 0=0 := by
    have hsub : Icc (-δ) (-δ/2) ⊆ Icc (-δ) δ := by
      intro x hx
      exact ⟨hx.1,by linarith [hx.2]⟩
    have hn' := ae_restrict_of_ae_restrict_of_subset hsub halocal
    have hpoly : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-δ) (-δ/2)),
        (GLP023B4c_T8_fit_polynomial J a 0).eval x=0 := by
      filter_upwards [hn',ae_restrict_mem measurableSet_Icc] with x hx hmem
      rw [GLP023B4c_T8_fit_piecewise] at hx
      simpa only [if_neg (show ¬0 ≤ x by linarith [hmem.2])] using hx
    have heq := Measure.eqOn_Icc_of_ae_eq volume (show -δ ≠ -δ/2 by linarith)
      hpoly (GLP023B4c_T8_fit_polynomial J a 0).continuous.continuousOn continuous_const.continuousOn
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite (show -δ < -δ/2 by linarith)).mono
      (fun x hx => heq ⟨hx.1.le,hx.2.le⟩)
  have hpos : GLP023B4c_T8_fit_polynomial J a 1=0 := by
    have hsub : Icc (δ/2) δ ⊆ Icc (-δ) δ := by
      intro x hx
      exact ⟨by linarith [hx.1],hx.2⟩
    have hn' := ae_restrict_of_ae_restrict_of_subset hsub halocal
    have hpoly : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (δ/2) δ),
        (GLP023B4c_T8_fit_polynomial J a 1).eval x=0 := by
      filter_upwards [hn',ae_restrict_mem measurableSet_Icc] with x hx hmem
      rw [GLP023B4c_T8_fit_piecewise] at hx
      simpa only [if_pos (show 0 ≤ x by linarith [hmem.1])] using hx
    have heq := Measure.eqOn_Icc_of_ae_eq volume (show δ/2 ≠ δ by linarith)
      hpoly (GLP023B4c_T8_fit_polynomial J a 1).continuous.continuousOn continuous_const.continuousOn
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite (show δ/2 < δ by linarith)).mono
      (fun x hx => heq ⟨hx.1.le,hx.2.le⟩)
  apply ha
  have h0 : a ⟨0,by omega⟩=0 := by
    have h := congrArg (fun p : Polynomial ℝ => p.coeff 0) hneg
    simpa [GLP023B4c_T8_fit_coeff_zero] using h
  have h1 : a ⟨1,by omega⟩=0 := by
    have h := congrArg (fun p : Polynomial ℝ => p.coeff 0) hpos
    rw [GLP023B4c_T8_fit_coeff_zero,Polynomial.coeff_zero] at h
    norm_num only [mul_one] at h
    linarith [h0]
  funext j
  change a j=0
  by_cases hj0 : j.val=0
  · have hj : j=(⟨0,by omega⟩ : Fin (J+2)) := Fin.ext hj0
    simpa only [hj] using h0
  · by_cases hj1 : j.val=1
    · have hj : j=(⟨1,by omega⟩ : Fin (J+2)) := Fin.ext hj1
      simpa only [hj] using h1
    · have h := congrArg (fun p : Polynomial ℝ => p.coeff (j.val-1)) hneg
      rw [GLP023B4c_T8_fit_coeff_pos J a 0 (j.val-1) (by omega) (by omega), Polynomial.coeff_zero] at h
      have hj : (⟨j.val-1+1,by omega⟩ : Fin (J+2))=j := Fin.ext (by simp only; omega)
      rw [hj] at h
      exact h

/-- Borel-set domination gives domination as measures. -/
theorem GLP023B4c_T8_density_measure_domination (μ : Measure ℝ) (c δ : ℝ)
    (hdom : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-δ) δ →
      ENNReal.ofReal c * volume A ≤ μ A) :
    ENNReal.ofReal c • (volume : Measure ℝ).restrict (Icc (-δ) δ) ≤ μ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, Measure.restrict_apply hA]
  exact (hdom (A ∩ Icc (-δ) δ) (hA.inter measurableSet_Icc) inter_subset_right).trans
    (measure_mono inter_subset_left)

/-- Integral domination with integrability checked against the larger measure. -/
theorem GLP023B4c_T8_density_integral_domination (μ : Measure ℝ) (c δ : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-δ) δ →
      ENNReal.ofReal c * volume A ≤ μ A)
    (f : ℝ → ℝ) (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) :
    c * (∫ x in Icc (-δ) δ, f x) ≤ ∫ x, f x ∂μ := by
  have hi := integral_mono_measure (GLP023B4c_T8_density_measure_domination μ c δ hdom)
    (Filter.Eventually.of_forall hn) hf
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] using hi


lemma GLP023B4c_T8_projection_minimum (μ : Measure ℝ) (hprob : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (q p : Polynomial ℝ)
    (hq : IsProjection μ J q) (hp : p.natDegree ≤ J) :
    expectation μ (fun x => (party x-q.eval x)^2) ≤
      expectation μ (fun x => (party x-p.eval x)^2) := by
  have hd : (q-p).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le q p).trans (max_le hq.1 hp)
  have ho := GLP023B4c_T8_cpb_test_poly μ hprob hs J q hq (q-p) hd
  have hquad : Integrable (fun x => (q.eval x-p.eval x)^2) μ :=
    GLP023B4c_T8_cpb_integrable hprob hs (GLP023B4c_T8_cpb_square
      (GLP023B4c_T8_cpb_sub (GLP023B4c_T8_cpb_poly q) (GLP023B4c_T8_cpb_poly p)))
  have hres := GLP023B4c_T8_cpb_integrable hprob hs (GLP023B4c_T8_cpb_square
    (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q)))
  have he : (fun x => (party x-p.eval x)^2) =
      (fun x => (party x-q.eval x)^2+(q.eval x-p.eval x)^2+
        2*((party x-q.eval x)*(q-p).eval x)) := by
    funext x
    simp only [Polynomial.eval_sub]
    ring
  have hn : 0 ≤ expectation μ (fun x => (q.eval x-p.eval x)^2) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hmul := GLP023B4c_T8_cpb_integrable hprob hs (GLP023B4c_T8_cpb_mul
    (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly q))
    (GLP023B4c_T8_cpb_poly (q-p)))
  unfold expectation at *
  have hsum : Integrable (fun x => (party x-q.eval x)^2+(q.eval x-p.eval x)^2) μ := hres.add hquad
  rw [he, integral_add hsum (hmul.const_mul 2), integral_add hres hquad,
    integral_const_mul, ho]
  linarith

lemma GLP023B4c_T8_density_uniform_minimum (J : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ J) :
    residualVariance uniformMargins J ≤
      expectation uniformMargins (fun x => (party x-p.eval x)^2) := by
  have hq : IsProjection uniformMargins J (projection uniformMargins J) := by
    rw [GLP023B4c_T8_urc_projection_eq]
    exact GLP023B4c_T8_urc_q_spec J
  exact GLP023B4c_T8_projection_minimum uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J (projection uniformMargins J) p hq hp

/-- Affine rescaling of a competitor, including the factor `2 * δ`. -/
theorem GLP023B4c_T8_density_scaled_projection_minimum (J : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ J) :
    2 * δ * residualVariance uniformMargins J ≤
      ∫ x in Icc (-δ) δ, (party x - p.eval x) ^ 2 := by
  let s := p.comp (Polynomial.C δ * Polynomial.X)
  have hs : s.natDegree ≤ J := by
    apply Polynomial.natDegree_comp_le.trans
    have hd : (Polynomial.C δ * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
    exact (Nat.mul_le_mul_left p.natDegree hd).trans (by simpa using hp)
  have hparty (t : ℝ) : party (δ * t) = party t := by
    simp only [party, mul_nonneg_iff_of_pos_left hδ]
  have he : (∫ x in Icc (-δ) δ, (party x - p.eval x) ^ 2) =
      2 * δ * expectation uniformMargins (fun t => (party t - s.eval t) ^ 2) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -δ ≤ δ by linarith), GLP023B4c_T8_urc_expectation]
    have hchange := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => (party x - p.eval x) ^ 2) (a := (-1 : ℝ)) (b := 1) δ
    simp only [smul_eq_mul, mul_neg, mul_one, mul_one, neg_mul, one_mul] at hchange
    rw [← hchange]
    have heval (t : ℝ) : s.eval t = p.eval (δ * t) := by
      simp [s, Polynomial.eval_comp]
    simp_rw [hparty, ← heval]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (GLP023B4c_T8_density_uniform_minimum J s hs) (by positivity)

/-- Pure scalar portion of the variance chain. No Legendre input is needed. -/
theorem GLP023B4c_T8_density_denominator_chain (J : ℕ) (hJ : 1 ≤ J) (c δ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) :
    let n := (J + 1) / 2
    c * δ * centralBinomial n ^ 2 / 2 ≥ c * δ / (8 * (n : ℝ)) ∧
      c * δ / (8 * (n : ℝ)) ≥ c * δ / (4 * ((J : ℝ) + 1)) := by
  dsimp only
  let n := (J + 1) / 2
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have htwice : 2 * n ≤ J + 1 := by dsimp [n]; omega
  have hreal : 2 * (n : ℝ) ≤ (J : ℝ) + 1 := by exact_mod_cast htwice
  constructor
  · have hb := mul_le_mul_of_nonneg_left (central_binomial_lower_bound n hn)
      (show 0 ≤ c * δ / 2 by positivity)
    calc
      c * δ / (8 * (n : ℝ)) = (c * δ / 2) * (1 / (4 * (n : ℝ))) := by
        field_simp
        <;> ring
      _ ≤ (c * δ / 2) * centralBinomial n ^ 2 := hb
      _ = c * δ * centralBinomial n ^ 2 / 2 := by ring
  · apply (div_le_div_iff₀ (show 0 < 4 * ((J : ℝ) + 1) by positivity)
      (show 0 < 8 * (n : ℝ) by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (show 8 * (n : ℝ) ≤ 4 * ((J : ℝ) + 1) by linarith)
      (show 0 ≤ c * δ by positivity)


lemma GLP023B4c_T8_variance_lower (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (J : ℕ) (hJ : 1 ≤ J) :
    MomentPositiveDefinite (marginLaw ν) J ∧
      c*δ/(4*((J:ℝ)+1)) ≤ residualVariance (marginLaw ν) J := by
  rcases hr with ⟨hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, h0, hlip, hm, hvar⟩
  have hpμ : ProbabilityLaw (marginLaw ν) := by
    simpa [ProbabilityLaw, marginLaw, Measure.map_apply measurable_fst] using hp
  have hpd := GLP023B4c_T8_full_rank_of_domination (marginLaw ν) hpμ hs c δ hc hδ
    (GLP023B4c_T8_density_measure_domination _ c δ hdom) J
  refine ⟨hpd, ?_⟩
  have hproj := GLP023B4c_T8_cpb_projection_spec (marginLaw ν) hpμ hs J hpd
  have hd := GLP023B4c_T8_density_integral_domination (marginLaw ν) c δ hc.le hdom
    (fun x => (party x - (projection (marginLaw ν) J).eval x)^2)
    (GLP023B4c_T8_cpb_integrable hpμ hs (GLP023B4c_T8_cpb_square
      (GLP023B4c_T8_cpb_sub GLP023B4c_T8_cpb_party (GLP023B4c_T8_cpb_poly _))))
    (fun x => sq_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left
    (GLP023B4c_T8_density_scaled_projection_minimum J δ hδ _ hproj.1) hc.le
  have hden := GLP023B4c_T8_density_denominator_chain J hJ c δ hc hδ
  have he : c * (2*δ*residualVariance uniformMargins J) =
      c*δ*centralBinomial ((J+1)/2)^2/2 := by
    rw [GLP023B4c_T8_urc_variance]
    ring
  change _ ≤ expectation (marginLaw ν) _
  calc
    _ ≤ c*δ/(8*(((J+1)/2:ℕ):ℝ)) := hden.2
    _ ≤ c*δ*centralBinomial ((J+1)/2)^2/2 := hden.1
    _ = c * (2*δ*residualVariance uniformMargins J) := he.symm
    _ ≤ _ := hscale.trans hd

lemma GLP023B4c_T8_zero_approx (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (h0 : h 0 = 0)
    (hlip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |h x-h y| ≤ L*|x-y|)
    (J : ℕ) (hJ : 1 ≤ J) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ p.eval 0 = 0 ∧
      supError h p ≤ 4*jacksonK*L/((J:ℝ)+1) := by
  let s := J/2+1
  have hs : 1 ≤ s := by omega
  obtain ⟨q, hq, hconv, herr⟩ := (jackson_kernel_approximation_proof s hs h L hL hlip).2.2
  let p := q - Polynomial.C (q.eval 0)
  have hK : 0 < jacksonK := by unfold jacksonK; positivity
  have hsr : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hden : (J:ℝ)+1 ≤ 2*(s:ℝ) := by exact_mod_cast (show J+1 ≤ 2*s by omega)
  have hq0 := herr 0 (by norm_num)
  rw [h0, zero_sub, abs_neg] at hq0
  have hp (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      |h x-p.eval x| ≤ 2*(jacksonK*L/(s:ℝ)) := by
    have he : h x-p.eval x = (h x-q.eval x)+q.eval 0 := by simp [p]; ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [herr x hx])
  refine ⟨p, ?_, ?_, ?_⟩
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hq.trans (by dsimp [s]; omega)) (by simp))
  · simp [p]
  · apply csSup_le (by exact ⟨_, mem_image_of_mem _ (show (0:ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)⟩)
    rintro _ ⟨x, hx, rfl⟩
    apply (hp x hx).trans
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hsr (by positivity : 0 < (J:ℝ)+1)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden (mul_nonneg hK.le hL)]

lemma GLP023B4c_T8_coefficient_congr (μ : Measure ℝ) (J : ℕ) (m m' : ℝ → ℝ)
    (hm : m =ᵐ[μ] m') : populationCoefficient μ J m = populationCoefficient μ J m' := by
  have he : PopNormal μ J m = PopNormal μ J m' := by
    funext a
    apply propext
    apply forall_congr'
    intro j
    have hi : expectation μ (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
        (m x - predict (polynomialDesign J (fun x : ℝ => x) party) a x)) =
        expectation μ (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
        (m' x - predict (polynomialDesign J (fun x : ℝ => x) party) a x)) := by
      apply integral_congr_ae
      filter_upwards [hm] with x hx
      rw [hx]
    rw [hi]
  unfold populationCoefficient
  rw [he]

lemma GLP023B4c_T8_clamp (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (h0 : h 0 = 0)
    (hlip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |h x-h y| ≤ L*|x-y|) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x ∈ Icc (-1 : ℝ) 1, g x = h x) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, |g x| ≤ L) := by
  let clip : ℝ → ℝ := fun x => max (-1) (min 1 x)
  have hclip : ∀ x, clip x ∈ Icc (-1 : ℝ) 1 := by
    intro x
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hh : ContinuousOn h (Icc (-1 : ℝ) 1) := by
    apply LipschitzOnWith.continuousOn (K := ⟨L, hL⟩)
    apply LipschitzOnWith.of_dist_le_mul
    exact hlip
  refine ⟨h ∘ clip, hh.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    hclip, ?_, ?_⟩
  · intro x hx
    simp [clip, max_eq_right hx.1, min_eq_right hx.2]
  · intro x hx
    have hcx : clip x = x := by simp [clip, max_eq_right hx.1, min_eq_right hx.2]
    change |h (clip x)| ≤ L
    rw [hcx]
    have hb := hlip x hx 0 (by norm_num)
    rw [h0, sub_zero, sub_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left (abs_le.mpr hx) hL).trans_eq (mul_one _))


lemma GLP023B4c_T8_population_rate (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (J : ℕ) (hJ : 1 ≤ J) :
    |populationCoefficient (marginLaw ν) J (fun x => α+β*party x+h x) - β| ≤
      8*jacksonK*L / Real.sqrt (c*δ*((J:ℝ)+1)) := by
  have hr' := hr
  rcases hr' with ⟨hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, h0, hlip, hm, hvar⟩
  let μ := marginLaw ν
  have hpμ : ProbabilityLaw μ := by
    simpa [ProbabilityLaw, μ, marginLaw, Measure.map_apply measurable_fst] using hp
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  letI : IsProbabilityMeasure μ := ⟨hpμ⟩
  obtain ⟨g, hgc, hge, hgb⟩ := GLP023B4c_T8_clamp h L hL h0 hlip
  have hg0 : g 0 = 0 := (hge 0 (by norm_num)).trans h0
  have hglip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |g x-g y| ≤ L*|x-y| := by
    intro x hx y hy
    rw [hge x hx, hge y hy]
    exact hlip x hx y hy
  have hmeanEq : (fun x => α+β*party x+h x) =ᵐ[μ] (fun x => α+β*party x+g x) := by
    have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := hs
    filter_upwards [hx] with x hx
    rw [hge x hx]
  have hmeanEqν := ae_of_ae_map measurable_fst.aemeasurable hmeanEq
  have hmg : ConditionalMean ν (fun x => α+β*party x+g x) := by
    refine ⟨hm.1, hm.2.1.congr hmeanEqν, ?_⟩
    intro t ht hb
    apply (hm.2.2 t ht hb).trans
    apply integral_congr_ae
    filter_upwards [hmeanEqν] with z hz
    rw [hz]
  have hv := GLP023B4c_T8_variance_lower ν α β h c δ L σ2 hr J hJ
  obtain ⟨p, hpdeg, hp0, hperr⟩ := GLP023B4c_T8_zero_approx g L hL hg0 hglip J hJ
  have hb := GLP023B4c_T8_bias_contract ν hp hs hsq α β g hgc.measurable ⟨L, hgb⟩ hmg J hJ hv.1
  have hrms := (hb.2.2.2.2.2.2.1 p hpdeg).2.2.2
  have hK : 0 < jacksonK := by unfold jacksonK; positivity
  let x : ℝ := (J:ℝ)+1
  let E : ℝ := 4*jacksonK*L/x
  have hx : 0 < x := by dsimp [x]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ha (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : |g x-p.eval x| ≤ E :=
    ((GLP023B4c_T8_cpb_supError (GLP023B4c_T8_cpb_continuous hgc) p).1 x hx).trans hperr
  have hsqint := GLP023B4c_T8_cpb_integrable hpμ hs (GLP023B4c_T8_cpb_square
    (GLP023B4c_T8_cpb_sub (GLP023B4c_T8_cpb_continuous hgc) (GLP023B4c_T8_cpb_poly p)))
  have hquad : expectation μ (fun x => (g x-p.eval x)^2) ≤ E^2 := by
    calc
      _ ≤ ∫ _x, E^2 ∂μ := integral_mono_ae hsqint (integrable_const _) (by
        have hxs : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := hs
        filter_upwards [hxs] with x hx
        have hab := ha x hx
        nlinarith [sq_abs (g x-p.eval x), abs_nonneg (g x-p.eval x)])
      _ = E^2 := by simp
  have hRMS : rmsError μ g p ≤ E :=
    (Real.sqrt_le_sqrt hquad).trans_eq (Real.sqrt_sq hE)
  have hposv : 0 < residualVariance μ J := hb.2.1
  have hsv : 0 < Real.sqrt (residualVariance μ J) := Real.sqrt_pos.mpr hposv
  have hroot : 0 < Real.sqrt (c*δ*x) := Real.sqrt_pos.mpr (by positivity)
  have hprod : c*δ*x ≤ 4*x^2*residualVariance μ J := by
    have hb := (div_le_iff₀ (by positivity : 0 < 4*x)).mp hv.2
    have hh := mul_le_mul_of_nonneg_left hb hx.le
    nlinarith [hh]
  have hsqrt : Real.sqrt (c*δ*x) ≤ 2*x*Real.sqrt (residualVariance μ J) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    nlinarith [Real.sq_sqrt (show 0 ≤ c*δ*x by positivity), Real.sq_sqrt hposv.le]
  rw [GLP023B4c_T8_coefficient_congr μ J _ _ hmeanEq]
  apply hrms.trans
  apply (div_le_div_of_nonneg_right hRMS hsv.le).trans
  apply (div_le_div_iff₀ hsv hroot).mpr
  calc
    E * Real.sqrt (c*δ*x) = (4*jacksonK*L*Real.sqrt (c*δ*x))/x := by dsimp [E]; ring
    _ ≤ 8*jacksonK*L*Real.sqrt (residualVariance μ J) := by
      apply (div_le_iff₀ hx).mpr
      have hm := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 4*jacksonK*L by positivity)
      nlinarith [hm]

lemma GLP023B4c_T8_sampling_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (J N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun ω => frobeniusSquared J (fun j l =>
      sampleGram sample N J ω j l - populationGram (marginLaw ν) J j l)) P ∧
    Integrable (fun ω => vectorSquared J (fun j =>
      sampleCross sample N J ω j - populationCross ν J j)) P := by
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  let μ := marginLaw ν
  have hpμ := GLP023B4c_marginal_probability ν hp
  let z := polynomialDesign J (fun x : ℝ => x) party
  have hcol (j : Fin (J+2)) : ∀ᵐ w : ℝ × ℝ ∂ν, ‖z w.1 j‖ ≤ 1 :=
    ae_of_ae_map measurable_fst.aemeasurable (GLP023B4c_column_bound_ae μ hs J j)
  have hgram (j l : Fin (J+2)) :
      Integrable (fun ω => (sampleGram sample N J ω j l-populationGram μ J j l)^2) P ∧
      (∫ ω, (sampleGram sample N J ω j l-populationGram μ J j l)^2 ∂P) ≤ 1/(N:ℝ) := by
    let f : ℝ × ℝ → ℝ := fun w => z w.1 j * z w.1 l
    have hfm : Measurable f := ((GP023B1b_column_measurable J j).comp measurable_fst).mul
      ((GP023B1b_column_measurable J l).comp measurable_fst)
    have hfb : ∀ᵐ w ∂ν, ‖f w‖ ≤ 1 := by
      filter_upwards [hcol j, hcol l] with w hj hl
      simpa only [f, norm_mul, mul_one] using mul_le_mul hj hl (norm_nonneg _) zero_le_one
    have hf : MemLp f 2 ν := MemLp.of_bound hfm.aestronglyMeasurable 1 hfb
    have hf2 : (∫ w, (f w)^2 ∂ν) ≤ 1 := by
      calc
        _ ≤ ∫ _w : ℝ × ℝ, (1:ℝ) ∂ν := integral_mono_ae hf.integrable_sq (integrable_const _) (by
          filter_upwards [hfb] with w hw
          have ha : |f w| ≤ 1 := hw
          nlinarith [sq_abs (f w), abs_nonneg (f w)])
        _ = 1 := by simp
    have hfmean : (∫ w, f w ∂ν) = populationGram μ J j l :=
      (integral_map measurable_fst.aemeasurable
        (GLP023B4c_gram_integrable μ hpμ hs J j l).aestronglyMeasurable).symm
    have hb := GLP023B4c_iid_scalar P ν sample hiid hp f hfm hf N hN
    rw [hfmean] at hb
    change Integrable (fun ω => (sampleGram sample N J ω j l-populationGram μ J j l)^2) P ∧
      (∫ ω, (sampleGram sample N J ω j l-populationGram μ J j l)^2 ∂P) ≤ _ at hb
    exact ⟨hb.1, hb.2.trans (div_le_div_of_nonneg_right hf2 (Nat.cast_nonneg N))⟩
  have hY : MemLp (fun w : ℝ × ℝ => w.2) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_snd.aestronglyMeasurable).mpr hsq
  have hcross (j : Fin (J+2)) :
      Integrable (fun ω => (sampleCross sample N J ω j-populationCross ν J j)^2) P ∧
      (∫ ω, (sampleCross sample N J ω j-populationCross ν J j)^2 ∂P) ≤
        (∫ w, w.2^2 ∂ν)/(N:ℝ) := by
    let f : ℝ × ℝ → ℝ := fun w => z w.1 j * w.2
    have hfm : Measurable f := ((GP023B1b_column_measurable J j).comp measurable_fst).mul
      measurable_snd
    have hfb : ∀ᵐ w ∂ν, ‖f w‖ ≤ 1 * ‖w.2‖ := by
      filter_upwards [hcol j] with w hw
      simpa only [f, norm_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg w.2)
    have hf : MemLp f 2 ν := hY.of_le_mul hfm.aestronglyMeasurable hfb
    have hf2 : (∫ w, (f w)^2 ∂ν) ≤ ∫ w, w.2^2 ∂ν := by
      apply integral_mono_ae hf.integrable_sq hsq
      filter_upwards [hfb] with w hw
      simp only [one_mul, Real.norm_eq_abs] at hw
      nlinarith [sq_abs (f w), sq_abs w.2, abs_nonneg (f w), abs_nonneg w.2]
    have hb := GLP023B4c_iid_scalar P ν sample hiid hp f hfm hf N hN
    change Integrable (fun ω => (sampleCross sample N J ω j-populationCross ν J j)^2) P ∧
      (∫ ω, (sampleCross sample N J ω j-populationCross ν J j)^2 ∂P) ≤ _ at hb
    exact ⟨hb.1, hb.2.trans (div_le_div_of_nonneg_right hf2 (Nat.cast_nonneg N))⟩
  exact ⟨integrable_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun l _ => (hgram j l).1)), integrable_finsetSum _ (fun j _ => (hcross j).1)⟩

lemma GLP023B4c_T8_markov {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hf : Integrable f P)
    (hn : ∀ ω, 0 ≤ f ω) (t : ℝ) (ht : 0 < t) :
    P {ω | t < f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂P)/t) := by
  have hb := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hn) hf t
  have hreal : (P {ω | t ≤ f ω}).toReal ≤ (∫ ω, f ω ∂P)/t := by
    apply (le_div_iff₀ ht).mpr
    change t * (P {ω | t ≤ f ω}).toReal ≤ _ at hb
    nlinarith
  calc
    _ ≤ P {ω | t ≤ f ω} := measure_mono (by intro ω h; exact show t ≤ f ω from h.le)
    _ = ENNReal.ofReal (P {ω | t ≤ f ω}).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

lemma GLP023B4c_T8_operator_frob (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ) :
    matrixOperatorNorm J A ≤ Real.sqrt (frobeniusSquared J A) := by
  unfold matrixOperatorNorm
  apply csSup_le
  · obtain ⟨a, ha⟩ := GLP023B4c_sphere_nonempty J
    exact ⟨_, (fun j => a j), ha, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ j : Fin (J+2), (∑ l : Fin (J+2), A j l^2) * (∑ l : Fin (J+2), v l^2) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
      _ = _ := by simp only [show (∑ l, v l^2) = 1 from hv, mul_one, frobeniusSquared]

lemma GLP023B4c_T8_ell_le_one (μ : Measure ℝ) (hp : ProbabilityLaw μ) (J : ℕ) :
    smallestMomentEigenvalue μ J ≤ 1 := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact integral_nonneg (fun x => sq_nonneg _)
  · refine ⟨Pi.single (0 : Fin (J+2)) (1:ℝ), ?_, ?_⟩
    · simp [Pi.single_apply]
    · have hpred (x : ℝ) : predict (polynomialDesign J (fun x : ℝ => x) party)
          (Pi.single (0 : Fin (J+2)) (1:ℝ)) x = 1 := by
        simp only [predict, Pi.single_apply]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        simp [polynomialDesign]
      simp_rw [hpred]
      simp [expectation]


lemma GLP023B4c_T8_tracking_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (m : ℝ → ℝ) (hm : ConditionalMean ν m) (J : ℕ) (hJ : 1 ≤ J)
    (hpd : MomentPositiveDefinite (marginLaw ν) J) (N : ℕ) (hN : 1 ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    let M := ∫ z, z.2^2 ∂ν
    let ell := smallestMomentEigenvalue (marginLaw ν) J
    P {ω | ε < |samplePolynomial sample N J ω-populationCoefficient (marginLaw ν) J m|} ≤
      ENNReal.ofReal ((4+16*M/ε^2+16*(M+1)/ε^2)*((J:ℝ)+2)^2/((N:ℝ)*ell^3)) := by
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  let μ := marginLaw ν
  let M := ∫ z, z.2^2 ∂ν
  let ell := smallestMomentEigenvalue μ J
  let a := Classical.epsilon (PopNormal μ J m)
  let F := fun ω => frobeniusSquared J (fun j l => sampleGram sample N J ω j l-populationGram μ J j l)
  let T := fun ω => vectorSquared J (fun j => sampleCross sample N J ω j-populationCross ν J j)
  let O := fun ω => matrixOperatorNorm J (fun j l => sampleGram sample N J ω j l-populationGram μ J j l)
  have hb := GLP023B4c_matrix_contract P ν sample hiid hp hs hsq m hm J hJ hpd N hN
  have he : 0 < ell := hb.1
  have hM : 0 ≤ M := integral_nonneg (fun z => sq_nonneg _)
  have hel1 : ell ≤ 1 := GLP023B4c_T8_ell_le_one μ (GLP023B4c_marginal_probability ν hp) J
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  let K : ℝ := (J:ℝ)+2
  have hK : 1 ≤ K := by dsimp [K]; have hJ0 := Nat.cast_nonneg (α := ℝ) J; linarith
  have hF : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
  have hT : ∀ ω, 0 ≤ T ω := fun ω => GLP023B4c_vector_nonneg J _
  have hfi := GLP023B4c_T8_sampling_integrable P ν sample hiid hp hs hsq J N hN
  let b1 := ell^2/4
  let b2 := ε^2*ell^2/16
  let b3 := ε^2*ell^3/(16*(M+1))
  have hb1 : 0 < b1 := by dsimp [b1]; positivity
  have hb2 : 0 < b2 := by dsimp [b2]; positivity
  have hb3 : 0 < b3 := by dsimp [b3]; positivity
  have hsub : {ω | ε < |samplePolynomial sample N J ω-populationCoefficient μ J m|} ⊆
      {ω | b1 < F ω} ∪ {ω | b2 < T ω} ∪ {ω | b3 < F ω} := by
    intro ω hω
    by_contra hn
    have h1 : F ω ≤ b1 := le_of_not_gt (fun h => hn (Or.inl (Or.inl h)))
    have h2 : T ω ≤ b2 := le_of_not_gt (fun h => hn (Or.inl (Or.inr h)))
    have h3 : F ω ≤ b3 := le_of_not_gt (fun h => hn (Or.inr h))
    have hop : O ω ≤ Real.sqrt (F ω) := GLP023B4c_T8_operator_frob J _
    have hgood : O ω ≤ ell/2 := hop.trans (by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ ell/2)).mp
      rw [Real.sq_sqrt (hF ω)]
      dsimp [b1] at h1
      nlinarith)
    have ht : Real.sqrt (T ω) ≤ ε*ell/4 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ ε*ell/4)).mp
      rw [Real.sq_sqrt (hT ω)]
      dsimp [b2] at h2
      nlinarith
    have hg : O ω * Real.sqrt (M/ell) ≤ ε*ell/4 := by
      apply (mul_le_mul_of_nonneg_right hop (Real.sqrt_nonneg _)).trans
      apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (by positivity : 0 ≤ ε*ell/4)).mp
      rw [mul_pow, Real.sq_sqrt (hF ω), Real.sq_sqrt (div_nonneg hM he.le)]
      calc
        F ω * (M/ell) ≤ b3 * (M/ell) := mul_le_mul_of_nonneg_right h3 (div_nonneg hM he.le)
        _ = (ε*ell/4)^2 * (M/(M+1)) := by dsimp [b3]; field_simp; ring
        _ ≤ (ε*ell/4)^2 := by
          apply mul_le_of_le_one_right (sq_nonneg _)
          exact (div_le_one (by positivity : 0 < M+1)).mpr (by linarith)
    have hbound := hb.2.2.2.2 ω hgood
    have hnerr : Real.sqrt (vectorSquared J (fun j =>
        olsCoefficients (polynomialDesign J (fun i : Fin N => (sample i ω).1)
          (fun i => party (sample i ω).1)) (fun i => (sample i ω).2) j-a j)) ≤ ε := by
      apply hbound.trans
      change (2/ell)*(Real.sqrt (T ω)+O ω*Real.sqrt (M/ell)) ≤ ε
      calc
        _ ≤ (2/ell)*(ε*ell/4+ε*ell/4) :=
          mul_le_mul_of_nonneg_left (add_le_add ht hg) (by positivity)
        _ = ε := by field_simp <;> norm_num
    have hcoord : |samplePolynomial sample N J ω-populationCoefficient μ J m| ≤
        Real.sqrt (vectorSquared J (fun j =>
        olsCoefficients (polynomialDesign J (fun i : Fin N => (sample i ω).1)
          (fun i => party (sample i ω).1)) (fun i => (sample i ω).2) j-a j)) := by
      let e : Fin (J+2) → ℝ := fun j =>
        olsCoefficients (polynomialDesign J (fun i : Fin N => (sample i ω).1)
          (fun i => party (sample i ω).1)) (fun i => (sample i ω).2) j-a j
      change |e ⟨1, by omega⟩| ≤ Real.sqrt (vectorSquared J e)
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      exact Finset.single_le_sum (fun j _ => sq_nonneg (e j))
        (Finset.mem_univ (⟨1, by omega⟩ : Fin (J+2)))
    exact (not_lt_of_ge (hcoord.trans hnerr)) hω
  have hp1 := (GLP023B4c_T8_markov P F hfi.1 hF b1 hb1).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hb.2.1 hb1.le))
  have hp2 := (GLP023B4c_T8_markov P T hfi.2 hT b2 hb2).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hb.2.2.1 hb2.le))
  have hp3 := (GLP023B4c_T8_markov P F hfi.1 hF b3 hb3).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hb.2.1 hb3.le))
  have hR : 0 ≤ K^2/((N:ℝ)*ell^3) := by positivity
  have hreal1 : (K^2/(N:ℝ))/b1 ≤ 4*(K^2/((N:ℝ)*ell^3)) := by
    calc
      _ = 4*ell*(K^2/((N:ℝ)*ell^3)) := by dsimp [b1]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 4*ell ≤ 4) hR
  have hreal2 : (K*M/(N:ℝ))/b2 ≤ (16*M/ε^2)*(K^2/((N:ℝ)*ell^3)) := by
    calc
      _ = (16*M/ε^2)*(ell/K)*(K^2/((N:ℝ)*ell^3)) := by
        dsimp [b2]; field_simp <;> ring
      _ ≤ _ := by
        rw [mul_assoc, mul_comm (ell/K), ← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg (by positivity) hR)
          ((div_le_one (lt_of_lt_of_le zero_lt_one hK)).mpr (hel1.trans hK))
  have hreal3 : (K^2/(N:ℝ))/b3 = (16*(M+1)/ε^2)*(K^2/((N:ℝ)*ell^3)) := by
    dsimp [b3]; field_simp
  change _ ≤ ENNReal.ofReal _
  calc
    _ ≤ P ({ω | b1 < F ω} ∪ {ω | b2 < T ω} ∪ {ω | b3 < F ω}) := measure_mono hsub
    _ ≤ (P {ω | b1 < F ω} + P {ω | b2 < T ω}) + P {ω | b3 < F ω} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal ((K^2/(N:ℝ))/b1)+ENNReal.ofReal ((K*M/(N:ℝ))/b2))+
        ENNReal.ofReal ((K^2/(N:ℝ))/b3) := add_le_add (add_le_add hp1 hp2) hp3
    _ ≤ (ENNReal.ofReal (4*(K^2/((N:ℝ)*ell^3)))+
        ENNReal.ofReal ((16*M/ε^2)*(K^2/((N:ℝ)*ell^3))))+
        ENNReal.ofReal ((16*(M+1)/ε^2)*(K^2/((N:ℝ)*ell^3))) := by
      exact add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hreal1)
        (ENNReal.ofReal_le_ofReal hreal2)) (le_of_eq (congrArg ENNReal.ofReal hreal3))
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; dsimp [K]; ring


lemma GLP023B4c_T8_slow_degree (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ j → 0 < ell j) :
    ∃ degrees : ℕ → ℕ, (∀ N, 1 ≤ degrees N) ∧ Tendsto degrees atTop atTop ∧
      Tendsto (fun N => ((degrees N:ℝ)+2)^2/((N:ℝ)*(ell (degrees N))^3)) atTop (nhds 0) := by
  let f : ℕ → ℝ := fun j => ((j:ℝ)+2)^2/(ell j)^3
  let degrees : ℕ → ℕ := fun N => max 1 (Nat.findGreatest (fun j => f j ≤ Real.sqrt (N:ℝ)) N)
  have hd1 : ∀ N, 1 ≤ degrees N := fun N => le_max_left _ _
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hdtop : Tendsto degrees atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop j, hsqrt.eventually (eventually_ge_atTop (f j))] with N hN hf
    exact (Nat.le_findGreatest hN hf).trans (le_max_right _ _)
  have hfevent : ∀ᶠ N in atTop, f (degrees N) ≤ Real.sqrt (N:ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hsqrt.eventually (eventually_ge_atTop (f 1))] with N hN hf
    have hg := Nat.le_findGreatest (P := fun j => f j ≤ Real.sqrt (N:ℝ)) hN hf
    have hprop := Nat.findGreatest_spec (P := fun j => f j ≤ Real.sqrt (N:ℝ)) hN hf
    simpa only [degrees, max_eq_right hg] using hprop
  have hR : Tendsto (fun N : ℕ => 1/Real.sqrt (N:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  refine ⟨degrees, hd1, hdtop, ?_⟩
  apply squeeze_zero' _ _ hR
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg N) (pow_nonneg (hell _ (hd1 N)).le _))
  · filter_upwards [hfevent, eventually_ge_atTop 1] with N hf hN
    have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    calc
      _ = f (degrees N)/(N:ℝ) := by dsimp [f]; field_simp <;> ring
      _ ≤ Real.sqrt (N:ℝ)/(N:ℝ) := div_le_div_of_nonneg_right hf hNr.le
      _ = _ := by
        have hsq := Real.sq_sqrt hNr.le
        have hs : Real.sqrt (N:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
        apply (div_eq_div_iff hNr.ne' hs).mpr
        nlinarith


lemma GLP023B4c_T8_population_limit (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2) :
    Tendsto (fun J => populationCoefficient (marginLaw ν) J (fun x => α+β*party x+h x))
      atTop (nhds β) := by
  have hc : 0 < c := hr.2.2.2.2.1
  have hδ : 0 < δ := hr.2.2.2.2.2.1
  have htop : Tendsto (fun J : ℕ => c*δ*((J:ℝ)+1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (mul_pos hc hδ)
  have ht : Tendsto (fun J : ℕ => 8*jacksonK*L/Real.sqrt (c*δ*((J:ℝ)+1))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp htop)
  have hd : Tendsto (fun J => populationCoefficient (marginLaw ν) J
      (fun x => α+β*party x+h x) - β) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_ge_atTop 1] with J hJ
    exact GLP023B4c_T8_population_rate ν α β h c δ L σ2 hr J hJ
  simpa only [sub_add_cancel, zero_add] using hd.add_const β

lemma GLP023B4c_T8_tracking_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (m : ℝ → ℝ) (hm : ConditionalMean ν m)
    (hpd : ∀ J, 1 ≤ J → MomentPositiveDefinite (marginLaw ν) J)
    (degrees : ℕ → ℕ) (hdeg : ∀ᶠ N in atTop, 1 ≤ degrees N)
    (hrate : Tendsto (fun N => ((degrees N:ℝ)+2)^2/
      ((N:ℝ)*(smallestMomentEigenvalue (marginLaw ν) (degrees N))^3)) atTop (nhds 0)) :
    ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω-
      populationCoefficient (marginLaw ν) (degrees N) m) 0 := by
  intro ε hε
  let M := ∫ z, z.2^2 ∂ν
  have ht := ENNReal.tendsto_ofReal (hrate.const_mul (4+16*M/ε^2+16*(M+1)/ε^2))
  simp only [mul_zero, ENNReal.ofReal_zero] at ht
  apply tendsto_const_nhds.squeeze' ht (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hdeg, eventually_ge_atTop 1] with N hJ hN
  simpa only [sub_zero, mul_div_assoc] using
    GLP023B4c_T8_tracking_probability P ν sample hiid hp hs hsq m hm (degrees N) hJ
      (hpd _ hJ) N hN ε hε

lemma GLP023B4c_T8_fixed_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hp : ProbabilityLaw ν)
    (hs : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (m : ℝ → ℝ) (hm : ConditionalMean ν m)
    (hpd : ∀ J, 1 ≤ J → MomentPositiveDefinite (marginLaw ν) J)
    (J : ℕ) (hJ : 1 ≤ J) :
    ConvergesInProbability P (fun N => samplePolynomial sample N J) (populationCoefficient (marginLaw ν) J m) := by
  let ell := smallestMomentEigenvalue (marginLaw ν) J
  have hrate : Tendsto (fun N : ℕ => ((J:ℝ)+2)^2/((N:ℝ)*ell^3)) atTop (nhds 0) := by
    have he : (fun N : ℕ => ((J:ℝ)+2)^2/((N:ℝ)*ell^3)) =
        fun N : ℕ => (((J:ℝ)+2)^2/ell^3) * (N:ℝ)⁻¹ := by funext N; ring
    rw [he]
    have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hi : Tendsto
        (fun N : ℕ => (((J:ℝ)+2)^2/ell^3)*(N:ℝ)⁻¹) atTop
          (nhds ((((J:ℝ)+2)^2/ell^3)*0)))
  have ht := GLP023B4c_T8_tracking_limit P ν sample hiid hp hs hsq m hm hpd
    (fun _ => J) (Eventually.of_forall (fun _ => hJ)) hrate
  simpa only [ConvergesInProbability, sub_zero] using ht

lemma GLP023B4c_T8_tracking_target {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℕ → Ω → ℝ) (b : ℕ → ℝ) (β : ℝ)
    (ha : ConvergesInProbability P (fun N ω => A N ω-b N) 0)
    (hb : Tendsto b atTop (nhds β)) : ConvergesInProbability P A β := by
  intro ε hε
  apply tendsto_const_nhds.squeeze' (ha (ε/2) (by positivity))
    (Eventually.of_forall (fun _ => bot_le))
  have hsmall : ∀ᶠ N in atTop, |b N-β| < ε/2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hb.eventually (Metric.ball_mem_nhds β (by positivity : 0 < ε/2))
  filter_upwards [hsmall] with N hN
  apply measure_mono
  intro ω hω
  change ε/2 < |A N ω-b N-0|
  rw [sub_zero]
  have hab := abs_add_le (A N ω-b N) (b N-β)
  have he : A N ω-b N+(b N-β) = A N ω-β := by ring
  rw [he] at hab
  change ε < |A N ω-β| at hω
  linarith


lemma GLP023B4c_T8_regularize (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2) :
    ∃ g : ℝ → ℝ, Continuous g ∧ RepairedRegularity ν α β g c δ L σ2 := by
  rcases hr with ⟨hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, h0, hlip, hm, hvar⟩
  obtain ⟨g, hgc, hge, hgb⟩ := GLP023B4c_T8_clamp h L hL h0 hlip
  have hmeanEq : (fun z : ℝ × ℝ => α+β*party z.1+h z.1) =ᵐ[ν]
      (fun z : ℝ × ℝ => α+β*party z.1+g z.1) := by
    have hx : ∀ᵐ x ∂marginLaw ν, x ∈ Icc (-1 : ℝ) 1 := hs
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hx] with z hz
    rw [hge z.1 hz]
  refine ⟨g, hgc, hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, ?_, ?_, ?_, ?_⟩
  · exact (hge 0 (by norm_num)).trans h0
  · intro x hx y hy
    rw [hge x hx, hge y hy]
    exact hlip x hx y hy
  · refine ⟨hm.1, hm.2.1.congr hmeanEq, ?_⟩
    intro t ht hb
    apply (hm.2.2 t ht hb).trans
    apply integral_congr_ae
    filter_upwards [hmeanEq] with z hz
    rw [hz]
  · intro A hA hAsub
    have he : (∫ z in {z : ℝ × ℝ | z.1 ∈ A},
        (z.2-(α+β*party z.1+g z.1))^2 ∂ν) =
        ∫ z in {z : ℝ × ℝ | z.1 ∈ A}, (z.2-(α+β*party z.1+h z.1))^2 ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hmeanEq] with z hz
      rw [hz]
    rw [he]
    exact hvar A hA hAsub

lemma GLP023B4c_T8_window_moments (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (hm : Measurable h) (A : Set ℝ) (hA : MeasurableSet A) (hAs : A ⊆ Icc (-δ) δ) :
    let u := fun z : ℝ × ℝ => z.2-(α+β*party z.1+h z.1)
    Measurable u ∧ MemLp ((Prod.fst ⁻¹' A).indicator u) 2 ν ∧
      (∫ z, (Prod.fst ⁻¹' A).indicator u z ∂ν) = 0 ∧
      (∫ z, ((Prod.fst ⁻¹' A).indicator u z)^2 ∂ν) ≤ σ2*(marginLaw ν A).toReal := by
  rcases hr with ⟨hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, h0, hlip, hmean, hvar⟩
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  let μ := marginLaw ν
  let m := fun x => α+β*party x+h x
  let u := fun z : ℝ × ℝ => z.2-m z.1
  have hmb : GLP023B4c_T8_cpb_Bounded m := by
    apply GLP023B4c_T8_cpb_add
    · apply GLP023B4c_T8_cpb_add (GLP023B4c_T8_cpb_const α)
      exact GLP023B4c_T8_cpb_mul (GLP023B4c_T8_cpb_const β) GLP023B4c_T8_cpb_party
    · refine ⟨hm, L, ?_⟩
      intro x hx
      have hb := hlip x hx 0 (by norm_num)
      rw [h0, sub_zero, sub_zero] at hb
      exact hb.trans ((mul_le_mul_of_nonneg_left (abs_le.mpr hx) hL).trans_eq (mul_one _))
  have hum : Measurable u := measurable_snd.sub (hmb.1.comp measurable_fst)
  obtain ⟨B, hB⟩ := hmb.2
  have hmemm : MemLp (fun z : ℝ × ℝ => m z.1) 2 ν := by
    apply MemLp.of_bound (hmb.1.comp measurable_fst).aestronglyMeasurable B
    have hxs : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := hs
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hxs] with z hz
    exact hB z.1 hz
  have hY : MemLp (fun z : ℝ × ℝ => z.2) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_snd.aestronglyMeasurable).mpr hsq
  have hmem : MemLp ((Prod.fst ⁻¹' A).indicator u) 2 ν :=
    (hY.sub hmemm).indicator (hA.preimage measurable_fst)
  refine ⟨hum, hmem, ?_, ?_⟩
  · have ht := hmean.2.2 (A.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hA)
      ⟨1, by intro x; by_cases hx : x ∈ A <;> simp [hx]⟩
    have he : (Prod.fst ⁻¹' A).indicator u =
        (Prod.fst ⁻¹' A).indicator (fun z : ℝ × ℝ => z.2) -
          (Prod.fst ⁻¹' A).indicator (fun z : ℝ × ℝ => m z.1) := by
      funext z
      by_cases hz : z.1 ∈ A <;> simp [u, hz]
    rw [he]
    change (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : ℝ × ℝ => z.2) z -
      (Prod.fst ⁻¹' A).indicator (fun z : ℝ × ℝ => m z.1) z ∂ν) = 0
    rw [integral_sub (hmean.1.indicator (hA.preimage measurable_fst))
      ((show Integrable (fun z : ℝ × ℝ => m z.1) ν from hmean.2.1).indicator
        (hA.preimage measurable_fst))]
    apply sub_eq_zero.mpr
    convert ht using 1 <;> apply integral_congr_ae <;>
      exact Eventually.of_forall (fun z => by by_cases hz : z.1 ∈ A <;> simp [hz, m])
  · have he : (fun z => ((Prod.fst ⁻¹' A).indicator u z)^2) =
        (Prod.fst ⁻¹' A).indicator (fun z => (u z)^2) := by
      funext z
      by_cases hz : z.1 ∈ A <;> simp [hz]
    rw [he, integral_indicator (hA.preimage measurable_fst)]
    exact hvar A hA hAs

lemma GLP023B4c_T8_side_bound {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ)
    (g m : ℝ → ℝ) (L b : ℝ) (A : Set ℝ) (k : ℝ) (N : ℕ) (ω : Ω)
    (hA : ∀ x ∈ A, |g x| ≤ L*k)
    (hmodel : ∀ x ∈ A, m x = b+g x)
    (hc : 0 < sampleWindowCount sample A N ω) :
    |GP023B1b_sample_noiseSum sample A Prod.snd N ω /
        sampleWindowCount sample A N ω - b| ≤ L*k +
      |GP023B1b_sample_noiseSum sample A
        (fun z => z.2-m z.1) N ω /
        sampleWindowCount sample A N ω| := by
  classical
  let H := GP023B1b_sample_noiseSum sample A
    (fun z => g z.1) N ω
  let U := GP023B1b_sample_noiseSum sample A
    (fun z => z.2-m z.1) N ω
  let C := sampleWindowCount sample A N ω
  have hnum : GP023B1b_sample_noiseSum sample A Prod.snd N ω = (b)*C+H+U := by
    simp only [C, H, U, GP023B1b_sample_noiseSum, sampleWindowCount]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (sample i ω).1 ∈ A
    · simp only [if_pos hi, hmodel _ hi]
      ring
    · simp [hi]
  have hH : |H| ≤ L*k*C := by
    calc
      _ ≤ ∑ i : Fin N, |if (sample i ω).1 ∈ A then g (sample i ω).1 else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, if (sample i ω).1 ∈ A then L*k else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : (sample i ω).1 ∈ A
        · simp only [if_pos hi]
          exact hA _ hi
        · simp [hi]
      _ = _ := by
        unfold C sampleWindowCount
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  have he : GP023B1b_sample_noiseSum sample A Prod.snd N ω / C - b = H/C+U/C := by
    rw [hnum]
    have hC : C ≠ 0 := hc.ne'
    field_simp [hC]
    <;> ring
  change |GP023B1b_sample_noiseSum sample A Prod.snd N ω / C - b| ≤ L*k+|U/C|
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  rw [abs_div, abs_of_pos hc]
  exact (div_le_iff₀ hc).mpr hH


lemma GLP023B4c_T8_rd_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (α β : ℝ) (h : ℝ → ℝ) (c δ L σ2 : ℝ)
    (hr : RepairedRegularity ν α β h c δ L σ2) (hm : Measurable h)
    (hiid : IIDSample P ν sample) (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N)
    (hk0 : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop) :
    ConvergesInProbability P (sampleRD sample k) β := by
  have hr' := hr
  rcases hr' with ⟨hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, h0, hlip, hmean, hvar⟩
  letI : IsProbabilityMeasure ν := ⟨hp⟩
  let μ := marginLaw ν
  letI : IsProbabilityMeasure μ := by dsimp [μ, marginLaw]; infer_instance
  let m := fun x => α+β*party x+h x
  let u := fun z : ℝ × ℝ => z.2-m z.1
  let A (N : ℕ) := Ioc (0 : ℝ) (k N)
  let B (N : ℕ) := Ioo (-k N) (0 : ℝ)
  let pA (N : ℕ) := (μ (A N)).toReal
  let pB (N : ℕ) := (μ (B N)).toReal
  have hsmallδ : ∀ᶠ N in atTop, k N ≤ δ :=
    (hk0.eventually_lt_const hδ).mono (fun _ h => h.le)
  have hmass : ∀ᶠ N in atTop, c*k N ≤ pA N ∧ c*k N ≤ pB N := by
    filter_upwards [hsmallδ] with N hN
    have hh := repaired_rd_finite_bounds ν α β h c δ L σ2 hr (k N) ⟨hkpos N, hN⟩
    constructor
    · have hle := ENNReal.toReal_mono (measure_ne_top μ _) hh.1
      simpa only [ENNReal.toReal_ofReal (mul_pos hc (hkpos N)).le] using hle
    · have hle := ENNReal.toReal_mono (measure_ne_top μ _) hh.2.1
      simpa only [ENNReal.toReal_ofReal (mul_pos hc (hkpos N)).le] using hle
  have hAtop : Tendsto (fun N : ℕ => (N:ℝ)*pA N) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hnk.const_mul_atTop hc)
    filter_upwards [hmass] with N hN
    have hh := mul_le_mul_of_nonneg_left hN.1 (Nat.cast_nonneg N)
    nlinarith [hh]
  have hBtop : Tendsto (fun N : ℕ => (N:ℝ)*pB N) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hnk.const_mul_atTop hc)
    filter_upwards [hmass] with N hN
    have hh := mul_le_mul_of_nonneg_left hN.2 (Nat.cast_nonneg N)
    nlinarith [hh]
  have hzero : ∀ᵐ x ∂μ, x ≠ 0 := by rw [ae_iff]; simpa using hz
  have htie (i : ℕ) : ∀ᵐ ω ∂P, (sample i ω).1 ≠ 0 := by
    apply ae_of_ae_map (μ := P) (p := fun z : ℝ × ℝ => z.1 ≠ 0) (hiid.2.1 i).aemeasurable
    rw [hiid.2.2.1 i]
    exact ae_of_ae_map measurable_fst.aemeasurable hzero
  have hties := ae_all_iff.mpr htie
  intro ε hε
  let t := ε/8
  have ht : 0 < t := by dsimp [t]; positivity
  let bA := fun N : ℕ => ENNReal.ofReal (4/((N:ℝ)*pA N))
  let bB := fun N : ℕ => ENNReal.ofReal (4/((N:ℝ)*pB N))
  let dA := fun N : ℕ => ENNReal.ofReal ((4*σ2/t^2)/((N:ℝ)*pA N))
  let dB := fun N : ℕ => ENNReal.ofReal ((4*σ2/t^2)/((N:ℝ)*pB N))
  have hboundtop (p : ℕ → ℝ) (hp : Tendsto (fun N : ℕ => (N:ℝ)*p N) atTop atTop) (r : ℝ) :
      Tendsto (fun N : ℕ => ENNReal.ofReal (r/((N:ℝ)*p N))) atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop hp :
        Tendsto (fun N : ℕ => r/((N:ℝ)*p N)) atTop (nhds 0))
  have hba := hboundtop pA hAtop 4
  have hbb := hboundtop pB hBtop 4
  have hda := hboundtop pA hAtop (4*σ2/t^2)
  have hdb := hboundtop pB hBtop (4*σ2/t^2)
  apply tendsto_const_nhds.squeeze' (by simpa only [add_zero, bot_eq_zero] using (hba.add hbb).add ((hba.add hda).add (hbb.add hdb)))
    (Eventually.of_forall (fun _ => bot_le))
  have hLsmall : ∀ᶠ N in atTop, 2*L*k N < ε/2 := by
    have he : Tendsto (fun N => 2*L*k N) atTop (nhds 0) := by simpa using hk0.const_mul (2*L)
    exact he.eventually_lt_const (by positivity)
  filter_upwards [hsmallδ, hmass, hLsmall, eventually_ge_atTop 1] with N hkδ hmassN hLs hN
  have hsubA : A N ⊆ Icc (-δ) δ := by intro x hx; exact ⟨by linarith [hx.1], hx.2.trans hkδ⟩
  have hsubB : B N ⊆ Icc (-δ) δ := by intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpA : 0 < pA N := (mul_pos hc (hkpos N)).trans_le hmassN.1
  have hpB : 0 < pB N := (mul_pos hc (hkpos N)).trans_le hmassN.2
  let CA : Set Ω := {ω | sampleWindowCount sample (A N) N ω < (N:ℝ)*pA N/2}
  let CB : Set Ω := {ω | sampleWindowCount sample (B N) N ω < (N:ℝ)*pB N/2}
  let UA : Set Ω := {ω | t < |GP023B1b_sample_noiseSum sample (A N) u N ω / sampleWindowCount sample (A N) N ω|}
  let UB : Set Ω := {ω | t < |GP023B1b_sample_noiseSum sample (B N) u N ω / sampleWindowCount sample (B N) N ω|}
  have hcA : P CA ≤ bA N := iid_window_count_bound P ν sample hiid (A N) measurableSet_Ioc hpA N hN
  have hcB : P CB ≤ bB N := iid_window_count_bound P ν sample hiid (B N) measurableSet_Ioo hpB N hN
  have huA : P UA ≤ bA N+dA N := by
    have hw := GLP023B4c_T8_window_moments ν α β h c δ L σ2 hr hm (A N) measurableSet_Ioc hsubA
    have hh := GP023B1b_sample_local_noise_bound P ν sample hiid (A N) measurableSet_Ioc u
      hw.1 hw.2.1 hw.2.2.1 σ2 hw.2.2.2 hpA N hN t ht
    simpa only [bA, dA, pA, div_div, mul_assoc] using hh
  have huB : P UB ≤ bB N+dB N := by
    have hw := GLP023B4c_T8_window_moments ν α β h c δ L σ2 hr hm (B N) measurableSet_Ioo hsubB
    have hh := GP023B1b_sample_local_noise_bound P ν sample hiid (B N) measurableSet_Ioo u
      hw.1 hw.2.1 hw.2.2.1 σ2 hw.2.2.2 hpB N hN t ht
    simpa only [bB, dB, pB, div_div, mul_assoc] using hh
  calc
    _ ≤ P ((CA ∪ CB) ∪ (UA ∪ UB)) := by
      apply measure_mono_ae
      filter_upwards [hties] with ω htiesω
      intro he
      by_contra hn
      have hn' : ω ∉ CA ∧ ω ∉ CB ∧ ω ∉ UA ∧ ω ∉ UB := by
        have hh : (ω ∉ CA ∧ ω ∉ CB) ∧ (ω ∉ UA ∧ ω ∉ UB) := by simpa using hn
        exact ⟨hh.1.1, hh.1.2, hh.2.1, hh.2.2⟩
      have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hca : 0 < sampleWindowCount sample (A N) N ω :=
        (half_pos (mul_pos hNr hpA)).trans_le (le_of_not_gt hn'.1)
      have hcb : 0 < sampleWindowCount sample (B N) N ω :=
        (half_pos (mul_pos hNr hpB)).trans_le (le_of_not_gt hn'.2.1)
      have hg (x : ℝ) (hx : x ∈ Icc (-δ) δ) (habs : |x| ≤ k N) : |h x| ≤ L*k N := by
        have hx1 : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hh := hlip x hx1 0 (by norm_num)
        rw [h0, sub_zero, sub_zero] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left habs hL)
      have hsa := GLP023B4c_T8_side_bound sample h m L (α+β) (A N) (k N) N ω
        (fun x hx => hg x (hsubA hx) (by rw [abs_of_pos hx.1]; exact hx.2))
        (fun x hx => by simp [m, party, hx.1.le]) hca
      have hsb := GLP023B4c_T8_side_bound sample h m L α (B N) (k N) N ω
        (fun x hx => hg x (hsubB hx) (by rw [abs_of_neg hx.2]; linarith [hx.1]))
        (fun x hx => by simp [m, party, not_le.mpr hx.2]) hcb
      have hna : |GP023B1b_sample_noiseSum sample (A N) u N ω / sampleWindowCount sample (A N) N ω| ≤ t :=
        le_of_not_gt hn'.2.2.1
      have hnb : |GP023B1b_sample_noiseSum sample (B N) u N ω / sampleWindowCount sample (B N) N ω| ≤ t :=
        le_of_not_gt hn'.2.2.2
      have hrd := GP023B1b_rd_windows sample N (k N) (hkpos N) ω (fun i => htiesω i)
      change sampleRD sample k N ω = _ at hrd
      change ε < |sampleRD sample k N ω-β| at he
      rw [hrd] at he
      have habs := abs_sub
        (GP023B1b_sample_noiseSum sample (A N) Prod.snd N ω/sampleWindowCount sample (A N) N ω-(α+β))
        (GP023B1b_sample_noiseSum sample (B N) Prod.snd N ω/sampleWindowCount sample (B N) N ω-α)
      have hid (a b : ℝ) : (a-(α+β))-(b-α) = a-b-β := by ring
      rw [hid] at habs
      change _ ≤ t at hna hnb
      dsimp only [t] at hna hnb
      dsimp only [A, B] at hsa hsb hna hnb habs
      linarith
    _ ≤ (P CA+P CB)+(P UA+P UB) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ _ := add_le_add (add_le_add hcA hcB) (add_le_add huA huB)

theorem corrected_proposition2_proof {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (α β : ℝ) (h : ℝ → ℝ) (c δ L σ2 : ℝ)
    (hr : RepairedRegularity ν α β h c δ L σ2) (hiid : IIDSample P ν sample)
    (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N)
    (hk0 : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N : ℝ) * k N) atTop atTop) :
    let μ := marginLaw ν
    let m := fun x => α + β*party x + h x
    (∀ J, 1 ≤ J → MomentPositiveDefinite μ J ∧
      residualVariance μ J ≥ c*δ/(4*((J:ℝ)+1))) ∧
    (∀ J, 1 ≤ J → ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ p.eval 0 = 0 ∧
      supError h p ≤ 4*jacksonK*L/((J:ℝ)+1)) ∧
    (∀ J, 1 ≤ J → |populationCoefficient μ J m - β| ≤
      8*jacksonK*L / Real.sqrt (c*δ*((J:ℝ)+1))) ∧
    Tendsto (fun J => populationCoefficient μ J m) atTop (nhds β) ∧
    (∀ J, 1 ≤ J → ConvergesInProbability P (fun N => samplePolynomial sample N J) (populationCoefficient μ J m)) ∧
    (∀ k', 0 < k' → k' ≤ δ → |populationRD μ m k' - β| ≤ 2*L*k') ∧
    ConvergesInProbability P (sampleRD sample k) β ∧
    (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω)
        (populationCoefficient μ J m - β) ∧ |populationCoefficient μ J m - β| < ε) ∧
    (∀ degrees : ℕ → ℕ, Tendsto degrees atTop atTop →
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0) →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω -
        populationCoefficient μ (degrees N) m) 0 ∧
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω - sampleRD sample k N ω) 0) ∧
    (∃ degrees : ℕ → ℕ, (∀ N, 1 ≤ degrees N) ∧ Tendsto degrees atTop atTop ∧
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0)) := by
  dsimp only
  have hr' := hr
  rcases hr' with ⟨hp, hs, hz, hsq, hc, hδ, hδ1, hL, hσ, hdom, h0, hlip, hm, hvar⟩
  let μ := marginLaw ν
  let m := fun x => α+β*party x+h x
  have hpμ := GLP023B4c_marginal_probability ν hp
  have hv (J : ℕ) (hJ : 1 ≤ J) := GLP023B4c_T8_variance_lower ν α β h c δ L σ2 hr J hJ
  have hpd (J : ℕ) (hJ : 1 ≤ J) : MomentPositiveDefinite μ J := (hv J hJ).1
  have hpop := GLP023B4c_T8_population_limit ν α β h c δ L σ2 hr
  have hfixed (J : ℕ) (hJ : 1 ≤ J) := GLP023B4c_T8_fixed_limit P ν sample hiid hp hs hsq m hm hpd J hJ
  obtain ⟨g, hgc, hrg⟩ := GLP023B4c_T8_regularize ν α β h c δ L σ2 hr
  have hRD := GLP023B4c_T8_rd_limit P ν sample α β g c δ L σ2 hrg hgc.measurable hiid k hkpos hk0 hnk
  refine ⟨hv, ?_, ?_, hpop, hfixed, ?_, hRD, ?_, ?_, ?_⟩
  · intro J hJ
    exact GLP023B4c_T8_zero_approx h L hL h0 hlip J hJ
  · intro J hJ
    exact GLP023B4c_T8_population_rate ν α β h c δ L σ2 hr J hJ
  · intro k' hk' hkδ
    exact (repaired_rd_finite_bounds ν α β h c δ L σ2 hr k' ⟨hk', hkδ⟩).2.2.2
  · intro ε hε
    have hsmall : ∀ᶠ J in atTop, |populationCoefficient μ J m - β| < ε := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hpop.eventually (Metric.ball_mem_nhds β hε)
    obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hsmall
    refine ⟨J₀, ?_⟩
    intro J hJ0 hJ
    exact ⟨convergesInProbability_sub P _ _ _ _ (hfixed J hJ) hRD, hJ₀ J hJ0⟩
  · intro degrees hd hrate
    have htrack := GLP023B4c_T8_tracking_limit P ν sample hiid hp hs hsq m hm hpd degrees
      (hd.eventually (eventually_ge_atTop 1)) hrate
    refine ⟨htrack, ?_⟩
    have hsamp := GLP023B4c_T8_tracking_target P
      (fun N => samplePolynomial sample N (degrees N))
      (fun N => populationCoefficient μ (degrees N) m) β htrack (hpop.comp hd)
    simpa only [sub_self] using convergesInProbability_sub P _ _ β β hsamp hRD
  · exact GLP023B4c_T8_slow_degree (smallestMomentEigenvalue μ) (fun J hJ =>
      (GLP023B4c_rayleigh μ hpμ hs J (hpd J hJ)).1)

end

theorem iid_regression_matrix_bounds_proof {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (hprob : ProbabilityLaw ν)
    (hsupport : MarginSupport (marginLaw ν)) (hsq : Integrable (fun z => z.2^2) ν)
    (m : ℝ → ℝ) (hmean : ConditionalMean ν m) (J : ℕ) (hJ : 1 ≤ J)
    (hpd : MomentPositiveDefinite (marginLaw ν) J) (N : ℕ) (hN : 1 ≤ N) :
    let μ := marginLaw ν
    let M := ∫ z, z.2^2 ∂ν
    let ell := smallestMomentEigenvalue μ J
    let c := Classical.epsilon (PopNormal μ J m)
    let ΔG := fun ω j l => sampleGram sample N J ω j l-populationGram μ J j l
    let Δt := fun ω j => sampleCross sample N J ω j-populationCross ν J j
    0 < ell ∧
    (∫ ω, frobeniusSquared J (ΔG ω) ∂P) ≤ ((J:ℝ)+2)^2/(N:ℝ) ∧
    (∫ ω, vectorSquared J (Δt ω) ∂P) ≤ ((J:ℝ)+2)*M/(N:ℝ) ∧
    ell*vectorSquared J c ≤ M ∧
    (∀ ω, matrixOperatorNorm J (ΔG ω) ≤ ell/2 →
      Real.sqrt (vectorSquared J (fun j =>
        olsCoefficients (polynomialDesign J (fun i : Fin N => (sample i ω).1)
          (fun i => party (sample i ω).1)) (fun i => (sample i ω).2) j-c j)) ≤
      (2/ell)*(Real.sqrt (vectorSquared J (Δt ω))+
        matrixOperatorNorm J (ΔG ω)*Real.sqrt (M/ell))) := by
  exact GLP023B4c_matrix_contract P ν sample hiid hprob hsupport hsq m hmean J hJ hpd N hN

end
end AronowAudit.P023.Wave1
