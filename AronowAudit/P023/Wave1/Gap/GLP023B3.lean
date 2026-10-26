import AronowAudit.P023.P023_Audit
import AronowAudit.P023.Wave1.Gap.GP023B2b
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Tactic.FunProp

/-!
Population normal equations and the corrected P023-T7 bias theorem.
All integrals below are justified by boundedness on the margin support.
-/

namespace AronowAudit.P023.Wave1

noncomputable section
open scoped BigOperators
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
open MeasureTheory Set Filter
open scoped ENNReal Topology

local instance GLP023B3_decidable (p : Prop) : Decidable p := Classical.propDecidable p

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2048

/-! Supported functions and finite normal equations. -/

def GLP023B3_cpb_Bounded (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ B, ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ B

lemma GLP023B3_cpb_const (c : ℝ) : GLP023B3_cpb_Bounded (fun _ => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

lemma GLP023B3_cpb_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    GLP023B3_cpb_Bounded f := by
  refine ⟨hf.measurable, ?_⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.abs.continuousOn
  exact ⟨B, fun x hx => hB (mem_image_of_mem _ hx)⟩

lemma GLP023B3_cpb_add {f g : ℝ → ℝ}
    (hf : GLP023B3_cpb_Bounded f) (hg : GLP023B3_cpb_Bounded g) :
    GLP023B3_cpb_Bounded (fun x => f x + g x) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hf.1.add hg.1, B + C, fun x hx =>
    (abs_add_le _ _).trans (add_le_add (hB x hx) (hC x hx))⟩

lemma GLP023B3_cpb_sub {f g : ℝ → ℝ}
    (hf : GLP023B3_cpb_Bounded f) (hg : GLP023B3_cpb_Bounded g) :
    GLP023B3_cpb_Bounded (fun x => f x - g x) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hf.1.sub hg.1, B + C, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hB x hx) (hC x hx))⟩

lemma GLP023B3_cpb_mul {f g : ℝ → ℝ}
    (hf : GLP023B3_cpb_Bounded f) (hg : GLP023B3_cpb_Bounded g) :
    GLP023B3_cpb_Bounded (fun x => f x * g x) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0 (by norm_num))
  refine ⟨hf.1.mul hg.1, B * C, ?_⟩
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hB x hx) (hC x hx) (abs_nonneg _) hB0

lemma GLP023B3_cpb_square {f : ℝ → ℝ} (hf : GLP023B3_cpb_Bounded f) :
    GLP023B3_cpb_Bounded (fun x => f x ^ 2) := by
  simpa only [pow_two] using GLP023B3_cpb_mul hf hf

lemma GLP023B3_cpb_party : GLP023B3_cpb_Bounded party := by
  refine ⟨Measurable.ite measurableSet_Ici measurable_const measurable_const, 1, ?_⟩
  intro x _
  unfold party
  split_ifs <;> norm_num

lemma GLP023B3_cpb_poly (p : Polynomial ℝ) :
    GLP023B3_cpb_Bounded (fun x => p.eval x) :=
  GLP023B3_cpb_continuous p.continuous

lemma GLP023B3_cpb_integrable {μ : Measure ℝ} (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) {f : ℝ → ℝ} (hf : GLP023B3_cpb_Bounded f) :
    Integrable f μ := by
  letI : IsProbabilityMeasure μ := ⟨hp⟩
  obtain ⟨B, hB⟩ := hf.2
  have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hs
  apply (integrable_const B).mono' hf.1.aestronglyMeasurable
  filter_upwards [hx] with x hxs
  simpa only [Real.norm_eq_abs] using hB x hxs

lemma GLP023B3_cpb_sum {K : Type*} [Fintype K] (f : K → ℝ → ℝ)
    (hf : ∀ k, GLP023B3_cpb_Bounded (f k)) :
    GLP023B3_cpb_Bounded (fun x => ∑ k, f k x) := by
  classical
  choose B hB using fun k => (hf k).2
  refine ⟨Finset.measurable_sum _ (fun k _ => (hf k).1), ∑ k, B k, ?_⟩
  intro x hx
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun k _ => hB k x hx))

lemma GLP023B3_cpb_predict {K : Type*} [Fintype K]
    (X : ℝ → K → ℝ) (hX : ∀ j, GLP023B3_cpb_Bounded (fun x => X x j))
    (c : K → ℝ) : GLP023B3_cpb_Bounded (predict X c) := by
  exact GLP023B3_cpb_sum _ (fun j => GLP023B3_cpb_mul (hX j) (GLP023B3_cpb_const _))

lemma GLP023B3_cpb_design (J : ℕ) (j : Fin (J + 2)) :
    GLP023B3_cpb_Bounded (fun x => polynomialDesign J (fun x : ℝ => x) party x j) := by
  unfold polynomialDesign
  split_ifs
  · exact GLP023B3_cpb_const _
  · exact GLP023B3_cpb_party
  · exact GLP023B3_cpb_continuous (continuous_id.pow _)

/-- Finite-dimensional Gram inversion, stated directly in terms of integrals. -/
lemma GLP023B3_cpb_normal_exists {K : Type*} [Fintype K]
    (μ : Measure ℝ) (hp : ProbabilityLaw μ) (hs : MarginSupport μ)
    (X : ℝ → K → ℝ) (hX : ∀ j, GLP023B3_cpb_Bounded (fun x => X x j))
    (hpos : ∀ c : K → ℝ, c ≠ 0 → 0 < expectation μ (fun x => predict X c x ^ 2))
    (m : ℝ → ℝ) (hm : GLP023B3_cpb_Bounded m) :
    ∃ c : K → ℝ, ∀ j, expectation μ (fun x => X x j * (m x - predict X c x)) = 0 := by
  classical
  have hi (c : K → ℝ) (j : K) : Integrable (fun x => X x j * predict X c x) μ :=
    GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul (hX j)
      (GLP023B3_cpb_predict X hX c))
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
  rw [integral_sub (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul (hX j) hm))
    (hi c j), he, sub_self]

def GLP023B3_cpb_polyOf (J : ℕ) (a : Fin (J + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

lemma GLP023B3_cpb_polyOf_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (x : ℝ) :
    (GLP023B3_cpb_polyOf J a).eval x = ∑ i, a i * x ^ (i : ℕ) := by
  simp [GLP023B3_cpb_polyOf, Polynomial.eval_finset_sum]

lemma GLP023B3_cpb_polyOf_degree (J : ℕ) (a : Fin (J + 1) → ℝ) :
    (GLP023B3_cpb_polyOf J a).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma GLP023B3_cpb_expansion (p : Polynomial ℝ) (J : ℕ) (hp : p.natDegree ≤ J)
    (x : ℝ) : p.eval x = ∑ i : Fin (J + 1), p.coeff i * x ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < J + 1 by omega)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- Insert the treatment coefficient after the intercept. -/
def GLP023B3_cpb_embed (J : ℕ) (a : Fin (J + 1) → ℝ) (b : ℝ) : Fin (J + 2) → ℝ :=
  Fin.cases (a 0) (Fin.cases b (fun j => a j.succ))

lemma GLP023B3_cpb_embed_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (b x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (GLP023B3_cpb_embed J a b) x =
      (∑ i, a i * x ^ (i : ℕ)) + b * party x := by
  simp [predict, polynomialDesign, GLP023B3_cpb_embed, Fin.sum_univ_succ,
    Nat.add_sub_cancel, mul_comm]
  ring

lemma GLP023B3_cpb_embed_ne (J : ℕ) (a : Fin (J + 1) → ℝ) (ha : a ≠ 0) :
    GLP023B3_cpb_embed J a 0 ≠ 0 := by
  intro he
  apply ha
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrFun he 0
  · exact congrFun he j.succ.succ

lemma GLP023B3_cpb_projection_spec (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    IsProjection μ J (projection μ J) := by
  apply Classical.epsilon_spec
  have hpos (a : Fin (J + 1) → ℝ) (ha : a ≠ 0) :
      0 < expectation μ (fun x => predict (fun x (i : Fin (J + 1)) => x ^ (i : ℕ)) a x ^ 2) := by
    have h := hpd (GLP023B3_cpb_embed J a 0) (GLP023B3_cpb_embed_ne J a ha)
    simp_rw [GLP023B3_cpb_embed_eval] at h
    simpa only [zero_mul, add_zero, predict, mul_comm] using h
  obtain ⟨a, ha⟩ := GLP023B3_cpb_normal_exists μ hp hs
    (fun x (i : Fin (J + 1)) => x ^ (i : ℕ))
    (fun _ => GLP023B3_cpb_continuous (continuous_id.pow _)) hpos party GLP023B3_cpb_party
  refine ⟨GLP023B3_cpb_polyOf J a, GLP023B3_cpb_polyOf_degree J a, ?_⟩
  intro j hj
  have he := ha (⟨j, by omega⟩ : Fin (J + 1))
  simpa only [GLP023B3_cpb_polyOf_eval, predict, mul_comm] using he

lemma GLP023B3_cpb_integral_predict {K : Type*} [Fintype K]
    (μ : Measure ℝ) (hp : ProbabilityLaw μ) (hs : MarginSupport μ)
    (X : ℝ → K → ℝ) (hX : ∀ j, GLP023B3_cpb_Bounded (fun x => X x j))
    (f : ℝ → ℝ) (hf : GLP023B3_cpb_Bounded f) (c : K → ℝ) :
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
    exact (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hf (hX j))).const_mul _

lemma GLP023B3_cpb_test_poly (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (q : Polynomial ℝ) (hq : IsProjection μ J q)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
    expectation μ (fun x => (party x - q.eval x) * p.eval x) = 0 := by
  have hr := GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly q)
  have he : (fun x => (party x - q.eval x) * p.eval x) =
      (fun x => (party x - q.eval x) *
        predict (fun x (i : Fin (J + 1)) => x ^ (i : ℕ)) (fun i => p.coeff i) x) := by
    funext x
    rw [GLP023B3_cpb_expansion p J hdeg]
    simp only [predict, mul_comm]
  rw [he, GLP023B3_cpb_integral_predict μ hp hs
    (fun x (i : Fin (J + 1)) => x ^ (i : ℕ))
    (fun i => GLP023B3_cpb_continuous (continuous_id.pow (i : ℕ))) _ hr]
  apply Finset.sum_eq_zero
  intro j _
  rw [hq.2 j (by omega), mul_zero]

lemma GLP023B3_cpb_residual_predict (J : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ J) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party)
      (GLP023B3_cpb_embed J (fun i => -q.coeff i) 1) x = party x - q.eval x := by
  rw [GLP023B3_cpb_embed_eval, GLP023B3_cpb_expansion q J hq]
  simp only [neg_mul, Finset.sum_neg_distrib, one_mul]
  ring

lemma GLP023B3_cpb_residual_moments (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    IsProjection μ J (projection μ J) ∧
    0 < residualVariance μ J ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => popResidual μ J x * p.eval x) = 0) ∧
    expectation μ (popResidual μ J) = 0 ∧
    expectation μ (fun x => popResidual μ J x * party x) = residualVariance μ J := by
  have hq := GLP023B3_cpb_projection_spec μ hp hs J hpd
  have hr : GLP023B3_cpb_Bounded (popResidual μ J) :=
    GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly (projection μ J))
  have horth (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
      expectation μ (fun x => popResidual μ J x * p.eval x) = 0 :=
    GLP023B3_cpb_test_poly μ hp hs J _ hq p hdeg
  have hv : 0 < residualVariance μ J := by
    let c := GLP023B3_cpb_embed J (fun i => -(projection μ J).coeff i) 1
    have hc : c ≠ 0 := by
      intro he
      have h1 := congrFun he (⟨1, by omega⟩ : Fin (J + 2))
      change (1 : ℝ) = 0 at h1
      norm_num at h1
    have h := hpd c hc
    simpa only [c, GLP023B3_cpb_residual_predict J _ hq.1,
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
    rw [he, integral_add (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_square hr))
      (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr (GLP023B3_cpb_poly _)))]
    change residualVariance μ J + expectation μ _ = _
    rw [horth _ hq.1, add_zero]
  exact ⟨hq, hv, horth, hz, hD⟩

lemma GLP023B3_cpb_fwl (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J)
    (m : ℝ → ℝ) (hm : GLP023B3_cpb_Bounded m) :
    populationCoefficient μ J m = biasFunctional μ J m := by
  let X := polynomialDesign J (fun x : ℝ => x) party
  let c := Classical.epsilon (PopNormal μ J m)
  have hX := GLP023B3_cpb_design J
  have hc : PopNormal μ J m c :=
    Classical.epsilon_spec (GLP023B3_cpb_normal_exists μ hp hs X hX hpd m hm)
  obtain ⟨hq, hv, horth, hz, hD⟩ := GLP023B3_cpb_residual_moments μ hp hs J hpd
  have hr : GLP023B3_cpb_Bounded (popResidual μ J) :=
    GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly _)
  have he : GLP023B3_cpb_Bounded (fun x => m x - predict X c x) :=
    GLP023B3_cpb_sub hm (GLP023B3_cpb_predict X hX c)
  have hnormal : expectation μ (fun x => popResidual μ J x * (m x - predict X c x)) = 0 := by
    have htest := GLP023B3_cpb_integral_predict μ hp hs X hX _ he
      (GLP023B3_cpb_embed J (fun i => -(projection μ J).coeff i) 1)
    have heq : (fun x => (m x - predict X c x) *
        predict X (GLP023B3_cpb_embed J (fun i => -(projection μ J).coeff i) 1) x) =
        (fun x => popResidual μ J x * (m x - predict X c x)) := by
      funext x
      rw [GLP023B3_cpb_residual_predict J _ hq.1]
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
    rw [GLP023B3_cpb_integral_predict μ hp hs X hX _ hr c]
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
    rw [integral_sub (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr hm))
      (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr
        (GLP023B3_cpb_predict X hX c)))] at hnormal
    change expectation μ _ - expectation μ _ = 0 at hnormal
    rw [hpred] at hnormal
    exact sub_eq_zero.mp hnormal
  change c ⟨1, by omega⟩ = expectation μ _ / residualVariance μ J
  rw [heq, mul_div_cancel_right₀ _ (ne_of_gt hv)]

lemma GLP023B3_cpb_supError {h : ℝ → ℝ} (hb : GLP023B3_cpb_Bounded h)
    (p : Polynomial ℝ) :
    (∀ x ∈ Icc (-1 : ℝ) 1, |h x - p.eval x| ≤ supError h p) ∧ 0 ≤ supError h p := by
  obtain ⟨B, hB⟩ := (GLP023B3_cpb_sub hb (GLP023B3_cpb_poly p)).2
  have hbd : BddAbove ((fun x => |h x - p.eval x|) '' Icc (-1 : ℝ) 1) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  have hle (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : |h x - p.eval x| ≤ supError h p :=
    le_csSup hbd (mem_image_of_mem _ hx)
  exact ⟨hle, (abs_nonneg _).trans (hle 0 (by norm_num))⟩

theorem corrected_population_bias_proof (ν : Measure (ℝ × ℝ))
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
  have hh : GLP023B3_cpb_Bounded h := ⟨hm, hb⟩
  have hr : GLP023B3_cpb_Bounded (popResidual μ J) :=
    GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly _)
  have hfull : GLP023B3_cpb_Bounded (fun x => α + β * party x + h x) :=
    GLP023B3_cpb_add (GLP023B3_cpb_add (GLP023B3_cpb_const α)
      (GLP023B3_cpb_mul (GLP023B3_cpb_const β) GLP023B3_cpb_party)) hh
  obtain ⟨hq, hv, horth, hz, hD⟩ := GLP023B3_cpb_residual_moments μ hp hs J hpd
  have hfwl : b = biasFunctional μ J (fun x => α + β * party x + h x) :=
    GLP023B3_cpb_fwl μ hp hs J hpd _ hfull
  have hri := GLP023B3_cpb_integrable hp hs hr
  have hrDi := GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr GLP023B3_cpb_party)
  have hrhi := GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr hh)
  have hrr := GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_square hr)
  have hbias (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
      b - β = biasFunctional μ J (fun x => h x - p.eval x) := by
    rw [hfwl]
    exact residual_bias_integral_identity μ (popResidual μ J) h (fun x => p.eval x)
      α β v (ne_of_gt hv) hri hrDi hrhi
      (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr (GLP023B3_cpb_poly p)))
      hz hD (horth p hdeg)
  have hbias0 : b - β = biasFunctional μ J h := by
    simpa only [Polynomial.eval_zero, sub_zero] using hbias 0 (by simp)
  have hbounds (p : Polynomial ℝ) (hdeg : p.natDegree ≤ J) :
      |b - β| ≤ amplification μ J * supError h p ∧
      |b - β| ≤ rmsError μ h p / Real.sqrt v := by
    have ha := GLP023B3_cpb_sub hh (GLP023B3_cpb_poly p)
    have hprod := GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_mul hr ha)
    rw [hbias p hdeg]
    constructor
    · apply residual_uniform_error_bound μ (popResidual μ J) _ (supError h p) v hv hri.abs hprod
      have hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by rw [ae_iff]; exact hs
      filter_upwards [hx] with x hxs
      exact (GLP023B3_cpb_supError hh p).1 x hxs
    · exact residual_rms_error_bound μ (popResidual μ J) _ hrr
        (GLP023B3_cpb_integrable hp hs (GLP023B3_cpb_square ha)) hprod hv
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

Source: EpsilonEridani (https://github.com/eic/EpsilonEridani),
commit bfe8fdb3279de1c45eb1f5b9713f44f0c016f84c,
`EpsilonEridani.Mathematics.Calculus.Polynomial` and
`EpsilonEridani.Mathematics.SpecialFunctions.Legendre.Basic`.
Adapted to a local namespace.
See NOTICE at the repository root.
-/
open Polynomial
section GLP023B3_urcPort
open intervalIntegral

theorem GLP023B3_urc_integral_derivative_mul_derivative_mul_comm (w p q : ℝ[X]) {a b : ℝ} (ha : w.eval a = 0)
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


noncomputable def GLP023B3_urc_legendre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => C ((n + 2 : ℝ)⁻¹) *
      ((2 * n + 3 : ℝ[X]) * X * GLP023B3_urc_legendre (n + 1) - (n + 1 : ℝ[X]) * GLP023B3_urc_legendre n)


@[simp] theorem GLP023B3_urc_legendre_zero : GLP023B3_urc_legendre 0 = 1 := by rw [GLP023B3_urc_legendre]


@[simp] theorem GLP023B3_urc_legendre_one : GLP023B3_urc_legendre 1 = X := by rw [GLP023B3_urc_legendre]


theorem GLP023B3_urc_legendre_add_two (n : ℕ) : GLP023B3_urc_legendre (n + 2) = C ((n + 2 : ℝ)⁻¹) *
    ((2 * n + 3 : ℝ[X]) * X * GLP023B3_urc_legendre (n + 1) - (n + 1 : ℝ[X]) * GLP023B3_urc_legendre n) := by
  rw [GLP023B3_urc_legendre]


theorem GLP023B3_urc_add_two_mul_legendre_add_two (n : ℕ) : (n + 2 : ℝ[X]) * GLP023B3_urc_legendre (n + 2) =
    (2 * n + 3 : ℝ[X]) * X * GLP023B3_urc_legendre (n + 1) - (n + 1 : ℝ[X]) * GLP023B3_urc_legendre n := by
  have hcoeff : (n + 2 : ℝ[X]) = C (n + 2 : ℝ) := by
    rw [map_add, C_eq_natCast, C_ofNat]
  rw [GLP023B3_urc_legendre_add_two, hcoeff, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (by positivity), C_1,
    one_mul]


theorem GLP023B3_urc_add_two_mul_legendre_add_two_eval (n : ℕ) (x : ℝ) : (n + 2) * (GLP023B3_urc_legendre (n + 2)).eval x =
    (2 * n + 3) * x * (GLP023B3_urc_legendre (n + 1)).eval x - (n + 1) * (GLP023B3_urc_legendre n).eval x := by
  simpa using congrArg (eval x) (GLP023B3_urc_add_two_mul_legendre_add_two n)


@[simp] theorem GLP023B3_urc_legendre_eval_one (n : ℕ) : (GLP023B3_urc_legendre n).eval 1 = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have h := GLP023B3_urc_add_two_mul_legendre_add_two_eval n 1
    rw [h₀, h₁] at h
    exact mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) (by linear_combination h)


theorem GLP023B3_urc_legendre_comp_neg_X (n : ℕ) : (GLP023B3_urc_legendre n).comp (-X) = (-1) ^ n * GLP023B3_urc_legendre n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have hne : (n + 2 : ℝ[X]) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    refine mul_left_cancel₀ hne ?_
    have h := congrArg (·.comp (-X)) (GLP023B3_urc_add_two_mul_legendre_add_two n)
    simp only [mul_comp, sub_comp, add_comp, natCast_comp, ofNat_comp, one_comp, X_comp, h₀, h₁,
      Nat.cast_ofNat] at h
    linear_combination h - (-1) ^ n * GLP023B3_urc_add_two_mul_legendre_add_two n


@[simp] theorem GLP023B3_urc_legendre_eval_neg (n : ℕ) (x : ℝ) :
    (GLP023B3_urc_legendre n).eval (-x) = (-1) ^ n * (GLP023B3_urc_legendre n).eval x := by
  simpa using congrArg (eval x) (GLP023B3_urc_legendre_comp_neg_X n)


theorem GLP023B3_urc_add_two_mul_coeff_legendre_add_two (n k : ℕ) :
    (n + 2) * (GLP023B3_urc_legendre (n + 2)).coeff (k + 1) =
      (2 * n + 3) * (GLP023B3_urc_legendre (n + 1)).coeff k - (n + 1) * (GLP023B3_urc_legendre n).coeff (k + 1) := by
  have h := congrArg (coeff · (k + 1)) (GLP023B3_urc_add_two_mul_legendre_add_two n)
  simpa [add_mul, sub_mul, mul_assoc, coeff_X_mul] using h


private theorem GLP023B3_urc_coeff_legendre_of_lt {n k : ℕ} (h : n < k) : (GLP023B3_urc_legendre n).coeff k = 0 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [coeff_one, h.ne']
  | one => simp [coeff_X, h.ne]
  | more n h₀ h₁ =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h' := GLP023B3_urc_add_two_mul_coeff_legendre_add_two n k
    rw [h₀ (by omega), h₁ (by omega)] at h'
    exact (mul_eq_zero.mp (h'.trans (by ring))).resolve_left (by positivity)


@[simp] theorem GLP023B3_urc_coeff_legendre_self (n : ℕ) : (GLP023B3_urc_legendre n).coeff n = n.centralBinom / 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Nat.centralBinom]
  | more n _ h₁ =>
    have h := GLP023B3_urc_add_two_mul_coeff_legendre_add_two n (n + 1)
    rw [h₁, GLP023B3_urc_coeff_legendre_of_lt (n := n) (k := n + 1 + 1) (by omega)] at h
    have hc : ((n + 2 : ℕ) : ℝ) * (n + 2).centralBinom = 2 * (2 * (n + 1 : ℕ) + 1) *
        (n + 1).centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ (n + 1)
    push_cast at hc
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    rw [h, mul_zero, sub_zero, pow_succ 2 (n + 1)]
    field_simp
    linear_combination -hc

private theorem GLP023B3_urc_coeff_legendre_self_ne_zero (n : ℕ) : (GLP023B3_urc_legendre n).coeff n ≠ 0 := by
  rw [GLP023B3_urc_coeff_legendre_self]
  exact div_ne_zero (by exact_mod_cast n.centralBinom_ne_zero) (by positivity)


@[simp] theorem GLP023B3_urc_legendre_ne_zero (n : ℕ) : GLP023B3_urc_legendre n ≠ 0 := fun h =>
  GLP023B3_urc_coeff_legendre_self_ne_zero n (by rw [h, coeff_zero])


@[simp] theorem GLP023B3_urc_natDegree_legendre (n : ℕ) : (GLP023B3_urc_legendre n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _ h => GLP023B3_urc_coeff_legendre_of_lt (by exact_mod_cast h))
    (GLP023B3_urc_coeff_legendre_self_ne_zero n)


@[simp] theorem GLP023B3_urc_degree_legendre (n : ℕ) : (GLP023B3_urc_legendre n).degree = n :=
  (degree_eq_iff_natDegree_eq (GLP023B3_urc_legendre_ne_zero n)).mpr (GLP023B3_urc_natDegree_legendre n)


@[simp] theorem GLP023B3_urc_leadingCoeff_legendre (n : ℕ) :
    (GLP023B3_urc_legendre n).leadingCoeff = n.centralBinom / 2 ^ n := by
  rw [leadingCoeff, GLP023B3_urc_natDegree_legendre, GLP023B3_urc_coeff_legendre_self]


private theorem GLP023B3_urc_derivative_legendre_add_two_of {n : ℕ}
    (h : X * derivative (GLP023B3_urc_legendre (n + 1)) =
      derivative (GLP023B3_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B3_urc_legendre (n + 1)) :
    derivative (GLP023B3_urc_legendre (n + 2)) =
      X * derivative (GLP023B3_urc_legendre (n + 1)) + (n + 2 : ℝ[X]) * GLP023B3_urc_legendre (n + 1) := by
  have hd := congrArg derivative (GLP023B3_urc_add_two_mul_legendre_add_two n)
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast, derivative_ofNat,
    derivative_X, derivative_one, mul_zero, add_zero, zero_add, zero_mul, mul_one] at hd
  have hne : (n + 2 : ℝ[X]) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  refine mul_left_cancel₀ hne ?_
  linear_combination hd + (n + 1) * h

private theorem GLP023B3_urc_derivative_legendre_ladder (n : ℕ) :
    X * derivative (GLP023B3_urc_legendre (n + 1)) =
        derivative (GLP023B3_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B3_urc_legendre (n + 1) ∧
      (1 - X ^ 2) * derivative (GLP023B3_urc_legendre (n + 1)) =
        (n + 1 : ℝ[X]) * (GLP023B3_urc_legendre n - X * GLP023B3_urc_legendre (n + 1)) := by
  induction n with
  | zero => constructor <;> simp [sq]
  | succ n ih =>
    have hb := GLP023B3_urc_derivative_legendre_add_two_of ih.1
    have hr := GLP023B3_urc_add_two_mul_legendre_add_two n
    push_cast
    constructor
    · linear_combination X * hb - ih.2 - hr
    · linear_combination (1 - X ^ 2) * hb + X * ih.2 + X * hr


theorem GLP023B3_urc_derivative_legendre_succ (n : ℕ) :
    derivative (GLP023B3_urc_legendre (n + 1)) = X * derivative (GLP023B3_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B3_urc_legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := GLP023B3_urc_derivative_legendre_add_two_of (GLP023B3_urc_derivative_legendre_ladder n).1
    push_cast at h ⊢
    linear_combination h


theorem GLP023B3_urc_X_mul_derivative_legendre_succ (n : ℕ) :
    X * derivative (GLP023B3_urc_legendre (n + 1)) =
      derivative (GLP023B3_urc_legendre n) + (n + 1 : ℝ[X]) * GLP023B3_urc_legendre (n + 1) :=
  (GLP023B3_urc_derivative_legendre_ladder n).1


theorem GLP023B3_urc_one_sub_X_sq_mul_derivative_legendre_succ (n : ℕ) :
    (1 - X ^ 2) * derivative (GLP023B3_urc_legendre (n + 1)) =
      (n + 1 : ℝ[X]) * (GLP023B3_urc_legendre n - X * GLP023B3_urc_legendre (n + 1)) :=
  (GLP023B3_urc_derivative_legendre_ladder n).2


theorem GLP023B3_urc_derivative_one_sub_X_sq_mul_derivative_legendre (n : ℕ) :
    derivative ((1 - X ^ 2) * derivative (GLP023B3_urc_legendre n)) =
      -((n : ℝ[X]) * ((n : ℝ[X]) + 1)) * GLP023B3_urc_legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [GLP023B3_urc_one_sub_X_sq_mul_derivative_legendre_succ]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast, derivative_one,
      derivative_X, zero_mul, zero_add, one_mul]
    push_cast
    linear_combination -(n + 1 : ℝ[X]) * GLP023B3_urc_X_mul_derivative_legendre_succ n

section Orthogonality

open MeasureTheory intervalIntegral


theorem GLP023B3_urc_integral_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (GLP023B3_urc_legendre m).eval x * (GLP023B3_urc_legendre n).eval x = 0 := by
  have hs := GLP023B3_urc_integral_derivative_mul_derivative_mul_comm (1 - X ^ 2) (GLP023B3_urc_legendre m) (GLP023B3_urc_legendre n)
    (a := -1) (b := 1) (by norm_num) (by norm_num)
  have e : ∀ (k : ℕ) (p q : ℝ[X]) (x : ℝ), eval x (-((k : ℝ[X]) * (k + 1)) * p * q) =
      -((k : ℝ) * (k + 1)) * (eval x p * eval x q) := fun k p q x => by
    simp only [eval_mul, eval_neg, eval_natCast, eval_add, eval_one]
    ring
  rw [GLP023B3_urc_derivative_one_sub_X_sq_mul_derivative_legendre,
    GLP023B3_urc_derivative_one_sub_X_sq_mul_derivative_legendre, mul_comm (GLP023B3_urc_legendre m)] at hs
  simp_rw [e, mul_comm (eval _ (GLP023B3_urc_legendre n)), intervalIntegral.integral_const_mul] at hs
  have hmn : (m : ℝ) * (m + 1) ≠ n * (n + 1) := by
    intro he
    have : m * (m + 1) = n * (n + 1) := by exact_mod_cast he
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt
    · exact (Nat.mul_lt_mul'' hlt (Nat.succ_lt_succ hlt)).ne this
    · exact (Nat.mul_lt_mul'' hlt (Nat.succ_lt_succ hlt)).ne' this
  exact (mul_eq_zero.mp (by linear_combination hs : ((n : ℝ) * (n + 1) - m * (m + 1)) *
    ∫ x in (-1 : ℝ)..1, (GLP023B3_urc_legendre m).eval x * (GLP023B3_urc_legendre n).eval x = 0)).resolve_left
    (sub_ne_zero.mpr hmn.symm)


private theorem GLP023B3_urc_add_two_mul_integral_legendre_add_two_mul (n : ℕ) (q : ℝ[X]) :
    (n + 2) * ∫ x in (-1 : ℝ)..1, (GLP023B3_urc_legendre (n + 2)).eval x * q.eval x =
      (2 * n + 3) * (∫ x in (-1 : ℝ)..1, x * (GLP023B3_urc_legendre (n + 1)).eval x * q.eval x) -
        (n + 1) * ∫ x in (-1 : ℝ)..1, (GLP023B3_urc_legendre n).eval x * q.eval x := by
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  exact integral_congr fun x _ => by
    linear_combination q.eval x * GLP023B3_urc_add_two_mul_legendre_add_two_eval n x


theorem GLP023B3_urc_integral_legendre_mul_self (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (GLP023B3_urc_legendre n).eval x * (GLP023B3_urc_legendre n).eval x = 2 / (2 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
    simp only [GLP023B3_urc_legendre_one, eval_X, ← sq]
    rw [integral_pow]
    norm_num
  | more n _ h₁ =>
    -- pair the recurrence for `Pₙ₊₂` with `Pₙ₊₂`, and the one for `Pₙ₊₃` with `Pₙ₊₁`;
    -- both produce the mixed integral `K = ∫ x Pₙ₊₁ Pₙ₊₂`
    have hA := GLP023B3_urc_add_two_mul_integral_legendre_add_two_mul n (GLP023B3_urc_legendre (n + 2))
    have hB := GLP023B3_urc_add_two_mul_integral_legendre_add_two_mul (n + 1) (GLP023B3_urc_legendre (n + 1))
    rw [GLP023B3_urc_integral_legendre_mul_legendre_of_ne (by omega : n ≠ n + 2), mul_zero, sub_zero] at hA
    rw [GLP023B3_urc_integral_legendre_mul_legendre_of_ne (by omega : n + 1 + 2 ≠ n + 1), h₁, mul_zero] at hB
    have hK : ∫ x in (-1 : ℝ)..1, x * (GLP023B3_urc_legendre (n + 1 + 1)).eval x * (GLP023B3_urc_legendre (n + 1)).eval x =
        ∫ x in (-1 : ℝ)..1, x * (GLP023B3_urc_legendre (n + 1)).eval x * (GLP023B3_urc_legendre (n + 2)).eval x :=
      integral_congr fun x _ => by ring
    rw [hK] at hB
    set K := ∫ x in (-1 : ℝ)..1, x * (GLP023B3_urc_legendre (n + 1)).eval x * (GLP023B3_urc_legendre (n + 2)).eval x
    have h3 : (2 * n + 3 : ℝ) * (2 / (2 * n + 3)) = 2 := by field_simp
    push_cast at hB ⊢
    rw [eq_div_iff (by positivity)]
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    linear_combination (2 * n + 5) * hA - (2 * n + 3) * hB + (n + 2) * h3


theorem GLP023B3_urc_integral_legendre_mul_legendre (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (GLP023B3_urc_legendre m).eval x * (GLP023B3_urc_legendre n).eval x =
      if m = n then (2 / (2 * n + 1) : ℝ) else 0 := by
  split_ifs with h
  · subst h
    exact GLP023B3_urc_integral_legendre_mul_self m
  · exact GLP023B3_urc_integral_legendre_mul_legendre_of_ne h


end Orthogonality

end GLP023B3_urcPort

lemma GLP023B3_urc_even_at_zero (m : ℕ) :
    (GLP023B3_urc_legendre (2 * m)).eval 0 = (-1 : ℝ) ^ m * centralBinomial m := by
  induction m with
  | zero => norm_num [centralBinomial]
  | succ m ih =>
    have hr := GLP023B3_urc_add_two_mul_legendre_add_two_eval (2 * m) 0
    have hc := central_binomial_recurrence m
    rw [ih] at hr
    have hidx : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hidx, pow_succ]
    push_cast at hr
    apply mul_left_cancel₀ (by positivity : (2 * (m : ℝ) + 2) ≠ 0)
    linear_combination hr + (-1 : ℝ) ^ m * hc

lemma GLP023B3_urc_half_odd (m : ℕ) :
    (∫ x in (0 : ℝ)..1, (GLP023B3_urc_legendre (2 * m + 1)).eval x) =
      (-1 : ℝ) ^ m * centralBinomial m / (2 * (m : ℝ) + 2) := by
  let P := GLP023B3_urc_legendre (2 * m + 1)
  let A := (1 - X ^ 2) * derivative P
  have hd : (derivative P).eval 0 =
      (2 * (m : ℝ) + 1) * ((-1 : ℝ) ^ m * centralBinomial m) := by
    have h := congrArg (Polynomial.eval (0 : ℝ)) (GLP023B3_urc_derivative_legendre_succ (2 * m))
    simpa [P, GLP023B3_urc_even_at_zero] using h
  have hi : (∫ x in (0 : ℝ)..1, (derivative A).eval x) = A.eval 1 - A.eval 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub' _ (_root_.funext fun x => Polynomial.deriv _)
      (fun x _ => Polynomial.differentiableAt _) (Polynomial.continuous _).continuousOn]
  have he : (∫ x in (0 : ℝ)..1, (derivative A).eval x) =
      -((2 * (m : ℝ) + 1) * (2 * m + 2)) *
        ∫ x in (0 : ℝ)..1, P.eval x := by
    dsimp only [A, P]
    rw [GLP023B3_urc_derivative_one_sub_X_sq_mul_derivative_legendre]
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

lemma GLP023B3_urc_expectation (f : ℝ → ℝ) :
    expectation uniformMargins f = (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, f x := by
  unfold expectation uniformMargins
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

lemma GLP023B3_urc_inner (m n : ℕ) :
    expectation uniformMargins (fun x => (GLP023B3_urc_legendre m).eval x *
      (GLP023B3_urc_legendre n).eval x) =
      if m = n then (1 / (2 * (n : ℝ) + 1) : ℝ) else 0 := by
  rw [GLP023B3_urc_expectation, GLP023B3_urc_integral_legendre_mul_legendre]
  split_ifs <;> ring

lemma GLP023B3_urc_party_integral (p : Polynomial ℝ) :
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

lemma GLP023B3_urc_party_even (m : ℕ) :
    expectation uniformMargins (fun x => party x *
      (GLP023B3_urc_legendre (2 * m + 2)).eval x) = 0 := by
  let p := GLP023B3_urc_legendre (2 * m + 2)
  have hwhole : (∫ x in (-1 : ℝ)..1, p.eval x) = 0 := by
    simpa only [GLP023B3_urc_legendre_zero, eval_one, mul_one] using
      GLP023B3_urc_integral_legendre_mul_legendre_of_ne
        (m := 2 * m + 2) (n := 0) (by omega)
  have heven (x : ℝ) : p.eval (-x) = p.eval x := by
    simp [p, GLP023B3_urc_legendre_eval_neg, pow_add, pow_mul]
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
  rw [GLP023B3_urc_party_integral]
  change (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1, p.eval x) = 0
  linarith

lemma GLP023B3_urc_party_odd (m : ℕ) :
    expectation uniformMargins (fun x => party x *
      (GLP023B3_urc_legendre (2 * m + 1)).eval x) =
      (-1 : ℝ) ^ m * centralBinomial m / (4 * (m : ℝ) + 4) := by
  rw [GLP023B3_urc_party_integral, GLP023B3_urc_half_odd]
  field_simp
  <;> ring

def GLP023B3_urc_moment (k : ℕ) : ℝ :=
  expectation uniformMargins (fun x => party x * (GLP023B3_urc_legendre k).eval x)

def GLP023B3_urc_q (J : ℕ) : Polynomial ℝ :=
  ∑ k : Fin (J + 1), ((2 * (k : ℕ) + 1 : ℝ) * GLP023B3_urc_moment k) •
    GLP023B3_urc_legendre k

lemma GLP023B3_urc_q_degree (J : ℕ) : (GLP023B3_urc_q J).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  rw [Polynomial.smul_eq_C_mul]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    rw [GLP023B3_urc_natDegree_legendre]
    omega)

def GLP023B3_urc_pair (f : ℝ → ℝ) (hf : GLP023B3_cpb_Bounded f) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := expectation uniformMargins (fun x => f x * p.eval x)
  map_add' p q := by
    simp only [eval_add, mul_add]
    exact integral_add
      (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B3_cpb_mul hf (GLP023B3_cpb_poly p)))
      (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B3_cpb_mul hf (GLP023B3_cpb_poly q)))
  map_smul' r p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    change expectation uniformMargins (fun x => f x * (r * p.eval x)) = _
    simp_rw [show ∀ x, f x * (r * p.eval x) = r * (f x * p.eval x) by intro x; ring]
    exact integral_const_mul _ _

lemma GLP023B3_urc_q_inner (J : ℕ) (k : Fin (J + 1)) :
    expectation uniformMargins (fun x => (GLP023B3_urc_q J).eval x *
      (GLP023B3_urc_legendre k).eval x) = GLP023B3_urc_moment k := by
  let F := GLP023B3_urc_pair (fun x => (GLP023B3_urc_legendre k).eval x)
    (GLP023B3_cpb_poly _)
  have he : expectation uniformMargins (fun x => (GLP023B3_urc_q J).eval x *
      (GLP023B3_urc_legendre k).eval x) = F (GLP023B3_urc_q J) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [he]
  unfold GLP023B3_urc_q
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hF (i : Fin (J + 1)) : F (GLP023B3_urc_legendre i) =
      if i = k then 1 / (2 * (k : ℕ) + 1 : ℝ) else 0 := by
    change expectation uniformMargins _ = _
    rw [GLP023B3_urc_inner]
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

lemma GLP023B3_urc_q_spec (J : ℕ) : IsProjection uniformMargins J (GLP023B3_urc_q J) := by
  let r := fun x => party x - (GLP023B3_urc_q J).eval x
  have hr : GLP023B3_cpb_Bounded r :=
    GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly _)
  let F := GLP023B3_urc_pair r hr
  let S : Polynomial.Sequence ℝ := ⟨GLP023B3_urc_legendre, GLP023B3_urc_degree_legendre⟩
  have hspan : Submodule.span ℝ (S '' Set.Iic J) ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro p ⟨k, hk, rfl⟩
    change k ≤ J at hk
    change expectation uniformMargins (fun x => r x * (GLP023B3_urc_legendre k).eval x) = 0
    dsimp only [r]
    simp_rw [sub_mul]
    unfold expectation
    rw [integral_sub
      (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B3_cpb_mul GLP023B3_cpb_party (GLP023B3_cpb_poly _)))
      (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B3_cpb_mul (GLP023B3_cpb_poly _) (GLP023B3_cpb_poly _)))]
    change GLP023B3_urc_moment k - expectation uniformMargins _ = 0
    rw [GLP023B3_urc_q_inner J (⟨k, by omega⟩ : Fin (J + 1)), sub_self]
  refine ⟨GLP023B3_urc_q_degree J, ?_⟩
  intro j hj
  have hp : (Polynomial.X ^ j : Polynomial ℝ) ∈ Submodule.span ℝ (S '' Set.Iic J) := by
    rw [S.span_degreeLE (fun i _ => isUnit_iff_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr (S.ne_zero i)))]
    apply Polynomial.mem_degreeLE.mpr
    simpa only [Polynomial.degree_X_pow, Nat.cast_le] using hj
  have hh := hspan hp
  change expectation uniformMargins (fun x => r x * (X ^ j).eval x) = 0 at hh
  simpa only [eval_pow, eval_X] using hh

lemma GLP023B3_urc_square_zero (p : Polynomial ℝ)
    (hz : expectation uniformMargins (fun x => p.eval x ^ 2) = 0) : p = 0 := by
  have hint := GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
    (GLP023B3_cpb_square (GLP023B3_cpb_poly p))
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

lemma GLP023B3_urc_projection_eq (J : ℕ) : projection uniformMargins J = GLP023B3_urc_q J := by
  have hq := GLP023B3_urc_q_spec J
  have hp : IsProjection uniformMargins J (projection uniformMargins J) :=
    Classical.epsilon_spec ⟨_, hq⟩
  let p := projection uniformMargins J
  let q := GLP023B3_urc_q J
  have hd : (p - q).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le p q).trans (max_le hp.1 hq.1)
  have h1 := GLP023B3_cpb_test_poly uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J p hp (p - q) hd
  have h2 := GLP023B3_cpb_test_poly uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J q hq (p - q) hd
  apply sub_eq_zero.mp
  apply GLP023B3_urc_square_zero
  have he : (fun x => (p - q).eval x ^ 2) =
      (fun x => (party x - q.eval x) * (p - q).eval x -
        (party x - p.eval x) * (p - q).eval x) := by
    funext x
    simp only [eval_sub]
    ring
  unfold expectation at *
  rw [he, integral_sub
    (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B3_cpb_mul (GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly q))
        (GLP023B3_cpb_poly _)))
    (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B3_cpb_mul (GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly p))
        (GLP023B3_cpb_poly _))), h2, h1, sub_self]

def GLP023B3_urc_score (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * GLP023B3_urc_moment k ^ 2

lemma GLP023B3_urc_moment_zero : GLP023B3_urc_moment 0 = 1 / 2 := by
  unfold GLP023B3_urc_moment
  rw [GLP023B3_urc_party_integral]
  norm_num

lemma GLP023B3_urc_score_even (m : ℕ) : GLP023B3_urc_score (2 * m + 2) = 0 := by
  unfold GLP023B3_urc_score GLP023B3_urc_moment
  rw [GLP023B3_urc_party_even]
  ring

lemma GLP023B3_urc_score_odd (m : ℕ) :
    GLP023B3_urc_score (2 * m + 1) = (centralBinomial m ^ 2 - centralBinomial (m + 1) ^ 2) / 4 := by
  have hrec : centralBinomial (m + 1) =
      centralBinomial m * (2 * (m : ℝ) + 1) / (2 * m + 2) :=
    (eq_div_iff (by positivity)).mpr (central_binomial_recurrence m)
  have hsign : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
    norm_num
  unfold GLP023B3_urc_score GLP023B3_urc_moment
  rw [GLP023B3_urc_party_odd, hrec]
  push_cast
  rw [div_pow, mul_pow, hsign, one_mul]
  field_simp
  <;> ring

lemma GLP023B3_urc_partial_odd (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), GLP023B3_urc_score k) =
      1 / 2 - centralBinomial n ^ 2 / 4 := by
  induction n with
  | zero => norm_num [GLP023B3_urc_score, GLP023B3_urc_moment_zero, centralBinomial]
  | succ n ih =>
    have hi : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [hi, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      GLP023B3_urc_score_odd, GLP023B3_urc_score_even]
    ring

lemma GLP023B3_urc_partial_even (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 2), GLP023B3_urc_score k) =
      1 / 2 - centralBinomial (n + 1) ^ 2 / 4 := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Finset.sum_range_succ,
    GLP023B3_urc_partial_odd, GLP023B3_urc_score_odd]
  ring

lemma GLP023B3_urc_variance_sum (J : ℕ) : residualVariance uniformMargins J =
    1 / 2 - ∑ k ∈ Finset.range (J + 1), GLP023B3_urc_score k := by
  let q := GLP023B3_urc_q J
  have hq := GLP023B3_urc_q_spec J
  have horth := GLP023B3_cpb_test_poly uniformMargins uniform_law_normalized.1
    uniform_law_normalized.2 J q hq q hq.1
  have hDq : expectation uniformMargins (fun x => party x * q.eval x) =
      ∑ k ∈ Finset.range (J + 1), GLP023B3_urc_score k := by
    change GLP023B3_urc_pair party GLP023B3_cpb_party (GLP023B3_urc_q J) = _
    unfold GLP023B3_urc_q
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    change ((2 * (k : ℕ) + 1 : ℝ) * GLP023B3_urc_moment k) * GLP023B3_urc_moment k = _
    unfold GLP023B3_urc_score
    ring
  have hD : expectation uniformMargins party = 1 / 2 := by
    simpa only [GLP023B3_urc_moment, GLP023B3_urc_legendre_zero, eval_one, mul_one]
      using GLP023B3_urc_moment_zero
  have he : (fun x => (party x - q.eval x) ^ 2) =
      (fun x => party x - party x * q.eval x - (party x - q.eval x) * q.eval x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [party, hx] <;> ring
  unfold residualVariance popResidual
  rw [GLP023B3_urc_projection_eq]
  change expectation uniformMargins (fun x => (party x - q.eval x) ^ 2) = _
  unfold expectation
  rw [he, integral_sub
    (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B3_cpb_sub GLP023B3_cpb_party
        (GLP023B3_cpb_mul GLP023B3_cpb_party (GLP023B3_cpb_poly q))))
    (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
      (GLP023B3_cpb_mul (GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly q))
        (GLP023B3_cpb_poly q))),
    integral_sub
      (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2 GLP023B3_cpb_party)
      (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
        (GLP023B3_cpb_mul GLP023B3_cpb_party (GLP023B3_cpb_poly q)))]
  change expectation uniformMargins party - expectation uniformMargins _ - expectation uniformMargins _ = _
  rw [hD, hDq, horth, sub_zero]

lemma GLP023B3_urc_variance (J : ℕ) : residualVariance uniformMargins J =
    centralBinomial ((J + 1) / 2) ^ 2 / 4 := by
  rw [GLP023B3_urc_variance_sum]
  by_cases hmod : J % 2 = 0
  · have hlen : J + 1 = 2 * (J / 2) + 1 := by omega
    have hidx : (J + 1) / 2 = J / 2 := by omega
    rw [hidx, hlen, GLP023B3_urc_partial_odd]
    ring
  · have hlen : J + 1 = 2 * (J / 2) + 2 := by omega
    have hidx : (J + 1) / 2 = J / 2 + 1 := by omega
    rw [hidx, hlen, GLP023B3_urc_partial_even]
    ring

def GLP023B3_urc_q1 : Polynomial ℝ := C (1 / 2) + C (3 / 4) * X

def GLP023B3_urc_q7 : Polynomial ℝ := C (1 / 2) + C (1 / 4096) *
  (C 11025 * X - C 40425 * X ^ 3 + C 63063 * X ^ 5 - C 32175 * X ^ 7)

lemma GLP023B3_urc_finite_projection :
    projection uniformMargins 1 = GLP023B3_urc_q1 ∧
    projection uniformMargins 7 = GLP023B3_urc_q7 := by
  have hpoly (p q : Polynomial ℝ) (h : ∀ x > 0, p.eval x = q.eval x) : p = q := by
    apply sub_eq_zero.mp
    apply (p - q).eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).mono (fun x hx => by
      change (p - q).eval x = 0
      rw [eval_sub, h x hx.1, sub_self])
  constructor
  · apply hpoly
    intro x hx
    have he := (uniform_residual_symmetry_proof.2 x hx).1
    simp only [popResidual, party, if_pos hx.le] at he
    simp only [GLP023B3_urc_q1, eval_add, eval_C, eval_mul, eval_X]
    linarith
  · apply hpoly
    intro x hx
    have he := (uniform_residual_symmetry_proof.2 x hx).2
    simp only [popResidual, party, if_pos hx.le] at he
    simp only [GLP023B3_urc_q7, eval_add, eval_sub, eval_C, eval_mul, eval_pow, eval_X]
    linarith

lemma GLP023B3_urc_abs_positive (J : ℕ) (hJ : 1 ≤ J) :
    expectation uniformMargins (fun x => |popResidual uniformMargins J x|) =
      ∫ x in (0 : ℝ)..1, |popResidual uniformMargins J x| := by
  let f := fun x => |popResidual uniformMargins J x|
  have hiU := (GLP023B3_cpb_integrable uniform_law_normalized.1 uniform_law_normalized.2
    (GLP023B3_cpb_sub GLP023B3_cpb_party (GLP023B3_cpb_poly (projection uniformMargins J)))).abs
  have hiV : Integrable f ((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1)) :=
    (integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp hiU
  have hi : IntervalIntegrable f volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hiV
  have hie := (IntervalIntegrable.trans_iff (show (0 : ℝ) ∈ Set.uIcc (-1) 1 by norm_num)).mp hi
  have heven (x : ℝ) : f (-x) = f x := by
    by_cases hx : x = 0
    · simp [hx]
    · dsimp [f]
      rw [uniform_residual_symmetry_proof.1 J hJ x hx, abs_neg]
  have hneg : (∫ x in (-1 : ℝ)..0, f x) = ∫ x in (0 : ℝ)..1, f x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, f (-x) := by
        simpa only [neg_zero] using (intervalIntegral.integral_comp_neg f (a := 0) (b := 1)).symm
      _ = _ := by simp_rw [heven]
  change expectation uniformMargins f = _
  rw [GLP023B3_urc_expectation, ← intervalIntegral.integral_add_adjacent_intervals hie.1 hie.2, hneg]
  change (1 / 2 : ℝ) * ((∫ x in (0 : ℝ)..1, f x) + ∫ x in (0 : ℝ)..1, f x) = _
  ring

lemma GLP023B3_urc_abs_one :
    expectation uniformMargins (fun x => |popResidual uniformMargins 1 x|) = 5 / 24 := by
  rw [GLP023B3_urc_abs_positive 1 (by norm_num)]
  have hR (x : ℝ) (hx : 0 ≤ x) : popResidual uniformMargins 1 x = 1 / 2 - 3 / 4 * x := by
    simp only [popResidual, GLP023B3_urc_finite_projection.1, GLP023B3_urc_q1,
      eval_add, eval_C, eval_mul, eval_X, party, if_pos hx]
    ring
  have he : (∫ x in (0 : ℝ)..1, |popResidual uniformMargins 1 x|) =
      ∫ x in (0 : ℝ)..1, |1 / 2 - 3 / 4 * x| := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change |popResidual uniformMargins 1 x| = |1 / 2 - 3 / 4 * x|
    rw [hR x hx.1]
  rw [he]
  have hc : Continuous (fun x : ℝ => |1 / 2 - 3 / 4 * x|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a := 0) (b := 2 / 3))
    (hc.intervalIntegrable (μ := volume) (a := 2 / 3) (b := 1))]
  have hleft : (∫ x in (0 : ℝ)..(2 / 3), |1 / 2 - 3 / 4 * x|) =
      ∫ x in (0 : ℝ)..(2 / 3), (1 / 2 - 3 / 4 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3)] at hx
    exact abs_of_nonneg (by linarith [hx.2])
  have hright : (∫ x in (2 / 3 : ℝ)..1, |1 / 2 - 3 / 4 * x|) =
      ∫ x in (2 / 3 : ℝ)..1, -(1 / 2 - 3 / 4 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (2 / 3 : ℝ) ≤ 1)] at hx
    exact abs_of_nonpos (by linarith [hx.1])
  rw [hleft, hright, intervalIntegral.integral_neg]
  have hint (a b : ℝ) : (∫ x in a..b, (1 / 2 : ℝ) - 3 / 4 * x) =
      (b - a) / 2 - (3 / 4) * ((b ^ 2 - a ^ 2) / 2) := by
    have hmul : IntervalIntegrable (fun x : ℝ => (3 / 4 : ℝ) * x) volume a b := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      hmul,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  rw [hint, hint]
  norm_num


/-! Exact finite-degree integral certificates. -/
def GLP023B3_urc_R (x : ℝ) : ℝ :=
  1 / 2 - 11025 / 4096 * x + 40425 / 4096 * x ^ 3 -
    63063 / 4096 * x ^ 5 + 32175 / 4096 * x ^ 7

def GLP023B3_urc_A (x : ℝ) : ℝ :=
  x / 2 - 11025 / 8192 * x ^ 2 + 40425 / 16384 * x ^ 4 -
    63063 / 24576 * x ^ 6 + 32175 / 32768 * x ^ 8

lemma GLP023B3_urc_R_cont : Continuous GLP023B3_urc_R := by
  unfold GLP023B3_urc_R
  fun_prop

lemma GLP023B3_urc_int_R (a b : ℝ) :
    (∫ x in a..b, GLP023B3_urc_R x) = GLP023B3_urc_A b - GLP023B3_urc_A a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => ?_) (GLP023B3_urc_R_cont.intervalIntegrable a b)
  unfold GLP023B3_urc_A GLP023B3_urc_R
  convert (((((hasDerivAt_id x).div_const 2).sub
    ((hasDerivAt_pow 2 x).const_mul (11025 / 8192))).add
    ((hasDerivAt_pow 4 x).const_mul (40425 / 16384))).sub
    ((hasDerivAt_pow 6 x).const_mul (63063 / 24576))).add
    ((hasDerivAt_pow 8 x).const_mul (32175 / 32768)) using 1 <;>
      (try funext y) <;> dsimp <;> ring

lemma GLP023B3_urc_R_bound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |GLP023B3_urc_R x| ≤ 581 / 16 := by
  have h1 : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have h3 : |x ^ 3| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1
  have h5 : |x ^ 5| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1
  have h7 : |x ^ 7| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1
  simp only [abs_pow] at h3 h5 h7
  unfold GLP023B3_urc_R
  calc
    _ ≤ |1 / 2 - 11025 / 4096 * x + 40425 / 4096 * x ^ 3 - 63063 / 4096 * x ^ 5| +
        |32175 / 4096 * x ^ 7| := abs_add_le _ _
    _ ≤ (|1 / 2 - 11025 / 4096 * x + 40425 / 4096 * x ^ 3| + |63063 / 4096 * x ^ 5|) +
        |32175 / 4096 * x ^ 7| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|1 / 2 - 11025 / 4096 * x| + |40425 / 4096 * x ^ 3|) + |63063 / 4096 * x ^ 5|) +
        |32175 / 4096 * x ^ 7| := by linarith [abs_add_le (1 / 2 - 11025 / 4096 * x) (40425 / 4096 * x ^ 3)]
    _ ≤ (((|(1 / 2 : ℝ)| + |11025 / 4096 * x|) + |40425 / 4096 * x ^ 3|) +
        |63063 / 4096 * x ^ 5|) + |32175 / 4096 * x ^ 7| := by linarith [abs_sub (1 / 2 : ℝ) (11025 / 4096 * x)]
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      norm_num
      nlinarith

-- Homogeneous Bernstein coefficients: each signed coefficient is checked exactly below.
def GLP023B3_urc_bern (a b : ℝ) : Fin 8 → ℝ :=
  ![(1 / 2) * a ^ 0 * b ^ 0 + (-11025 / 4096) * a ^ 1 * b ^ 0 + (40425 / 4096) * a ^ 3 * b ^ 0 + (-63063 / 4096) * a ^ 5 * b ^ 0 + (32175 / 4096) * a ^ 7 * b ^ 0,
    (7 / 2) * a ^ 0 * b ^ 0 + (-33075 / 2048) * a ^ 1 * b ^ 0 + (-11025 / 4096) * a ^ 0 * b ^ 1 + (40425 / 1024) * a ^ 3 * b ^ 0 + (121275 / 4096) * a ^ 2 * b ^ 1 + (-63063 / 2048) * a ^ 5 * b ^ 0 + (-315315 / 4096) * a ^ 4 * b ^ 1 + (225225 / 4096) * a ^ 6 * b ^ 1,
    (21 / 2) * a ^ 0 * b ^ 0 + (-165375 / 4096) * a ^ 1 * b ^ 0 + (-33075 / 2048) * a ^ 0 * b ^ 1 + (121275 / 2048) * a ^ 3 * b ^ 0 + (121275 / 1024) * a ^ 2 * b ^ 1 + (121275 / 4096) * a ^ 1 * b ^ 2 + (-63063 / 4096) * a ^ 5 * b ^ 0 + (-315315 / 2048) * a ^ 4 * b ^ 1 + (-315315 / 2048) * a ^ 3 * b ^ 2 + (675675 / 4096) * a ^ 5 * b ^ 2,
    (35 / 2) * a ^ 0 * b ^ 0 + (-55125 / 1024) * a ^ 1 * b ^ 0 + (-165375 / 4096) * a ^ 0 * b ^ 1 + (40425 / 1024) * a ^ 3 * b ^ 0 + (363825 / 2048) * a ^ 2 * b ^ 1 + (121275 / 1024) * a ^ 1 * b ^ 2 + (40425 / 4096) * a ^ 0 * b ^ 3 + (-315315 / 4096) * a ^ 4 * b ^ 1 + (-315315 / 1024) * a ^ 3 * b ^ 2 + (-315315 / 2048) * a ^ 2 * b ^ 3 + (1126125 / 4096) * a ^ 4 * b ^ 3,
    (35 / 2) * a ^ 0 * b ^ 0 + (-165375 / 4096) * a ^ 1 * b ^ 0 + (-55125 / 1024) * a ^ 0 * b ^ 1 + (40425 / 4096) * a ^ 3 * b ^ 0 + (121275 / 1024) * a ^ 2 * b ^ 1 + (363825 / 2048) * a ^ 1 * b ^ 2 + (40425 / 1024) * a ^ 0 * b ^ 3 + (-315315 / 2048) * a ^ 3 * b ^ 2 + (-315315 / 1024) * a ^ 2 * b ^ 3 + (-315315 / 4096) * a ^ 1 * b ^ 4 + (1126125 / 4096) * a ^ 3 * b ^ 4,
    (21 / 2) * a ^ 0 * b ^ 0 + (-33075 / 2048) * a ^ 1 * b ^ 0 + (-165375 / 4096) * a ^ 0 * b ^ 1 + (121275 / 4096) * a ^ 2 * b ^ 1 + (121275 / 1024) * a ^ 1 * b ^ 2 + (121275 / 2048) * a ^ 0 * b ^ 3 + (-315315 / 2048) * a ^ 2 * b ^ 3 + (-315315 / 2048) * a ^ 1 * b ^ 4 + (-63063 / 4096) * a ^ 0 * b ^ 5 + (675675 / 4096) * a ^ 2 * b ^ 5,
    (7 / 2) * a ^ 0 * b ^ 0 + (-11025 / 4096) * a ^ 1 * b ^ 0 + (-33075 / 2048) * a ^ 0 * b ^ 1 + (121275 / 4096) * a ^ 1 * b ^ 2 + (40425 / 1024) * a ^ 0 * b ^ 3 + (-315315 / 4096) * a ^ 1 * b ^ 4 + (-63063 / 2048) * a ^ 0 * b ^ 5 + (225225 / 4096) * a ^ 1 * b ^ 6,
    (1 / 2) * a ^ 0 * b ^ 0 + (-11025 / 4096) * a ^ 0 * b ^ 1 + (40425 / 4096) * a ^ 0 * b ^ 3 + (-63063 / 4096) * a ^ 0 * b ^ 5 + (32175 / 4096) * a ^ 0 * b ^ 7]

set_option maxHeartbeats 1600000 in
lemma GLP023B3_urc_bern_identity (a b x : ℝ) :
    (b - a) ^ 7 * GLP023B3_urc_R x =
      ∑ k : Fin 8, GLP023B3_urc_bern a b k * (x - a) ^ (k : ℕ) * (b - x) ^ (7 - (k : ℕ)) := by
  simp [GLP023B3_urc_bern, GLP023B3_urc_R, Fin.sum_univ_succ]
  <;> ring

lemma GLP023B3_urc_bern_positive (a b s x : ℝ) (hab : a < b)
    (hc : ∀ k, 0 ≤ s * GLP023B3_urc_bern a b k) (hx : x ∈ Icc a b) :
    0 ≤ s * GLP023B3_urc_R x := by
  have hp : 0 ≤ ∑ k : Fin 8, (s * GLP023B3_urc_bern a b k) *
      (x - a) ^ (k : ℕ) * (b - x) ^ (7 - (k : ℕ)) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg
      (mul_nonneg (hc k) (pow_nonneg (sub_nonneg.mpr hx.1) _))
      (pow_nonneg (sub_nonneg.mpr hx.2) _))
  have he : (b - a) ^ 7 * (s * GLP023B3_urc_R x) =
      ∑ k : Fin 8, (s * GLP023B3_urc_bern a b k) * (x - a) ^ (k : ℕ) * (b - x) ^ (7 - (k : ℕ)) := by
    calc
      _ = s * ((b - a) ^ 7 * GLP023B3_urc_R x) := by ring
      _ = _ := by
        rw [GLP023B3_urc_bern_identity, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [← he] at hp
  exact (mul_nonneg_iff_of_pos_left (pow_pos (sub_pos.mpr hab) 7)).mp hp

def GLP023B3_urc_knot : ℕ → ℝ
  | 0 => 0
  | 1 => 223667342463690275375959 / 1000000000000000000000000
  | 2 => 223667342463690275375960 / 1000000000000000000000000
  | 3 => 541561142007372602962764 / 1000000000000000000000000
  | 4 => 541561142007372602962765 / 1000000000000000000000000
  | 5 => 802464642882394574652670 / 1000000000000000000000000
  | 6 => 802464642882394574652671 / 1000000000000000000000000
  | 7 => 961341201910221837812270 / 1000000000000000000000000
  | 8 => 961341201910221837812271 / 1000000000000000000000000
  | _ => 1

def GLP023B3_urc_sign : Fin 9 → ℝ := ![1, 0, -1, 0, 1, 0, -1, 0, 1]

set_option maxHeartbeats 4000000 in
lemma GLP023B3_urc_sign_certificate (i : Fin 9) :
    GLP023B3_urc_sign i = 0 ∨
      ∀ x ∈ Icc (GLP023B3_urc_knot i) (GLP023B3_urc_knot ((i : ℕ) + 1)),
        0 ≤ GLP023B3_urc_sign i * GLP023B3_urc_R x := by
  apply Or.inr
  intro x hx
  apply GLP023B3_urc_bern_positive _ _ _ _ ?_ ?_ hx
  · fin_cases i <;> norm_num [GLP023B3_urc_knot]
  · intro k
    fin_cases i <;> fin_cases k <;>
      norm_num [GLP023B3_urc_bern, GLP023B3_urc_knot, GLP023B3_urc_sign]

lemma GLP023B3_urc_segment (i : Fin 9) :
    let a := GLP023B3_urc_knot i
    let b := GLP023B3_urc_knot ((i : ℕ) + 1)
    let s := GLP023B3_urc_sign i
    let L := s * (GLP023B3_urc_A b - GLP023B3_urc_A a)
    let E := if s = 0 then (581 / 16) * (b - a) else 0
    L ≤ (∫ x in a..b, |GLP023B3_urc_R x|) ∧
      (∫ x in a..b, |GLP023B3_urc_R x|) ≤ L + E := by
  dsimp only
  let a := GLP023B3_urc_knot i
  let b := GLP023B3_urc_knot ((i : ℕ) + 1)
  let s := GLP023B3_urc_sign i
  change (s * (GLP023B3_urc_A b - GLP023B3_urc_A a) ≤
      ∫ x in a..b, |GLP023B3_urc_R x|) ∧
    (∫ x in a..b, |GLP023B3_urc_R x|) ≤ s * (GLP023B3_urc_A b - GLP023B3_urc_A a) +
      (if s = 0 then (581 / 16) * (b - a) else 0)
  have hab : a ≤ b := by fin_cases i <;> norm_num [a, b, GLP023B3_urc_knot]
  have hab01 : 0 ≤ a ∧ b ≤ 1 := by fin_cases i <;> norm_num [a, b, GLP023B3_urc_knot]
  have hs : s = -1 ∨ s = 0 ∨ s = 1 := by fin_cases i <;> norm_num [s, GLP023B3_urc_sign]
  have hS : Continuous (fun x => s * GLP023B3_urc_R x) := continuous_const.mul GLP023B3_urc_R_cont
  have hF := GLP023B3_urc_R_cont.abs
  have hI : (∫ x in a..b, s * GLP023B3_urc_R x) = s * (GLP023B3_urc_A b - GLP023B3_urc_A a) := by
    rw [intervalIntegral.integral_const_mul, GLP023B3_urc_int_R]
  have hlo : s * (GLP023B3_urc_A b - GLP023B3_urc_A a) ≤ ∫ x in a..b, |GLP023B3_urc_R x| := by
    rw [← hI]
    apply intervalIntegral.integral_mono_on hab (hS.intervalIntegrable a b) (hF.intervalIntegrable a b)
    intro x _
    rcases hs with hs | hs | hs <;> rw [hs]
    · simpa using neg_le_abs (GLP023B3_urc_R x)
    · simp
    · simpa using le_abs_self (GLP023B3_urc_R x)
  refine ⟨hlo, ?_⟩
  by_cases hs0 : s = 0
  · have hu := intervalIntegral.integral_mono_on hab (hF.intervalIntegrable (μ := volume) a b)
      (intervalIntegrable_const (μ := volume) (c := (581 / 16 : ℝ)))
      (fun x hx => GLP023B3_urc_R_bound x ⟨hab01.1.trans hx.1, hx.2.trans hab01.2⟩)
    rw [hs0, zero_mul, if_pos rfl, zero_add]
    calc
      _ ≤ ∫ _x in a..b, (581 / 16 : ℝ) := hu
      _ = (581 / 16 : ℝ) * (b - a) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  · have hc := (GLP023B3_urc_sign_certificate i).resolve_left hs0
    have heq : (∫ x in a..b, |GLP023B3_urc_R x|) = ∫ x in a..b, s * GLP023B3_urc_R x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      have hn := hc x hx
      change 0 ≤ s * GLP023B3_urc_R x at hn
      change |GLP023B3_urc_R x| = s * GLP023B3_urc_R x
      rcases hs with hs | hs | hs
      · rw [hs] at hn ⊢
        rw [neg_one_mul] at hn ⊢
        exact abs_of_nonpos (by linarith)
      · exact False.elim (hs0 hs)
      · rw [hs] at hn ⊢
        simpa only [one_mul] using abs_of_nonneg (by simpa only [one_mul] using hn)
    rw [heq, hI, if_neg hs0, add_zero]

set_option maxHeartbeats 4000000 in
lemma GLP023B3_urc_abs_seven :
    (47642006857252250 / 10000000000000000 : ℝ) < amplification uniformMargins 7 ∧
    amplification uniformMargins 7 < (47642006857252260 / 10000000000000000 : ℝ) := by
  let L : ℝ := ∑ i : Fin 9, GLP023B3_urc_sign i *
    (GLP023B3_urc_A (GLP023B3_urc_knot ((i : ℕ) + 1)) - GLP023B3_urc_A (GLP023B3_urc_knot i))
  let E : ℝ := ∑ i : Fin 9, if GLP023B3_urc_sign i = 0 then
    (581 / 16) * (GLP023B3_urc_knot ((i : ℕ) + 1) - GLP023B3_urc_knot i) else 0
  let I := ∫ x in (0 : ℝ)..1, |GLP023B3_urc_R x|
  have hsum : (∑ i : Fin 9, ∫ x in GLP023B3_urc_knot i..GLP023B3_urc_knot ((i : ℕ) + 1),
      |GLP023B3_urc_R x|) = I := by
    exact (Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      ∫ x in GLP023B3_urc_knot k..GLP023B3_urc_knot (k + 1), |GLP023B3_urc_R x|) 9).trans
      (intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => GLP023B3_urc_R_cont.abs.intervalIntegrable _ _))
  have hlo : L ≤ I := by
    rw [← hsum]
    exact Finset.sum_le_sum (fun i _ => (GLP023B3_urc_segment i).1)
  have hu : I ≤ L + E := by
    rw [← hsum]
    simpa only [L, E, ← Finset.sum_add_distrib] using
      Finset.sum_le_sum (fun i _ => (GLP023B3_urc_segment i).2)
  have he : expectation uniformMargins (fun x => |popResidual uniformMargins 7 x|) = I := by
    rw [GLP023B3_urc_abs_positive 7 (by norm_num)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    congr 1
    simp only [popResidual, GLP023B3_urc_finite_projection.2, GLP023B3_urc_q7,
      eval_add, eval_sub, eval_C, eval_mul, eval_pow, eval_X, party, if_pos hx.1]
    unfold GLP023B3_urc_R
    ring
  have hv : residualVariance uniformMargins 7 = 1225 / 65536 := by
    rw [GLP023B3_urc_variance]
    norm_num [centralBinomial, Nat.choose]
  rw [amplification, he, hv]
  have hL : (47642006857252250 / 10000000000000000 : ℝ) < L / (1225 / 65536) := by
    norm_num [L, GLP023B3_urc_sign, GLP023B3_urc_knot, GLP023B3_urc_A, Fin.sum_univ_succ]
  have hU : (L + E) / (1225 / 65536) < (47642006857252260 / 10000000000000000 : ℝ) := by
    norm_num [L, E, GLP023B3_urc_sign, GLP023B3_urc_knot, GLP023B3_urc_A, Fin.sum_univ_succ]
  exact ⟨hL.trans_le (div_le_div_of_nonneg_right hlo (by norm_num)),
    (div_le_div_of_nonneg_right hu (by norm_num)).trans_lt hU⟩

theorem uniform_residual_constants_proof :
    ProbabilityLaw uniformMargins ∧ MarginSupport uniformMargins ∧
    (∀ J, 1 ≤ J → residualVariance uniformMargins J = centralBinomial ((J + 1) / 2)^2 / 4) ∧
    (∀ x, (projection uniformMargins 1).eval x = projection1 x) ∧
    (∀ x, (projection uniformMargins 7).eval x = projection7 x) ∧
    residualVariance uniformMargins 1 = 1 / 16 ∧
    residualVariance uniformMargins 7 = 1225 / 65536 ∧
    expectation uniformMargins (fun x => |popResidual uniformMargins 1 x|) = 5 / 24 ∧
    amplification uniformMargins 1 = 10 / 3 ∧
    1 / Real.sqrt (residualVariance uniformMargins 1) = 4 ∧
    1 / Real.sqrt (residualVariance uniformMargins 7) = 256 / 35 ∧
    (47642006857252250 / 10000000000000000 : ℝ) < amplification uniformMargins 7 ∧
    amplification uniformMargins 7 < (47642006857252260 / 10000000000000000 : ℝ) := by
  have hv1 : residualVariance uniformMargins 1 = 1 / 16 := by
    rw [GLP023B3_urc_variance]
    norm_num [centralBinomial, Nat.choose]
  have hv7 : residualVariance uniformMargins 7 = 1225 / 65536 := by
    rw [GLP023B3_urc_variance]
    norm_num [centralBinomial, Nat.choose]
  refine ⟨uniform_law_normalized.1, uniform_law_normalized.2,
    fun J _ => GLP023B3_urc_variance J, ?_, ?_, hv1, hv7, GLP023B3_urc_abs_one,
    ?_, ?_, ?_, GLP023B3_urc_abs_seven⟩
  · intro x
    rw [GLP023B3_urc_finite_projection.1]
    simp [GLP023B3_urc_q1, projection1]
  · intro x
    rw [GLP023B3_urc_finite_projection.2]
    simp only [GLP023B3_urc_q7, projection7, eval_add, eval_sub, eval_C, eval_mul, eval_pow, eval_X]
    ring
  · rw [amplification, GLP023B3_urc_abs_one, hv1]
    norm_num
  · rw [hv1, (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr (by norm_num)]
    norm_num
  · rw [hv7, (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 1225 / 65536)
      (by norm_num : (0 : ℝ) ≤ 35 / 256)).mpr (by norm_num)]
    norm_num

end
end AronowAudit.P023.Wave1
