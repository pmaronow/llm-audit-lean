import AronowAudit.P023.P023_Audit
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
Population projection foundations. The supported-measure and bounded-degree
versions connect polynomial projections to density comparison and population
normal equations.
-/

namespace AronowAudit.P023.Wave1

noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter

local instance tc04_projection_decidable (p : Prop) : Decidable p := Classical.propDecidable p

set_option maxRecDepth 2048

theorem tc04_poly_integrable (p : Polynomial ℝ) :
    Integrable (fun x => p.eval x) uniformMargins := by
  exact p.continuous.integrableOn_Icc.smul_measure (by norm_num)

theorem tc04_piecewise_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => if 0 ≤ x then p.eval x else q.eval x) uniformMargins := by
  exact Integrable.piecewise measurableSet_Ici
    (tc04_poly_integrable p).integrableOn (tc04_poly_integrable q).integrableOn

theorem tc04_residual_mul_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => (party x - p.eval x) * q.eval x) uniformMargins := by
  convert tc04_piecewise_integrable ((1 - p) * q) (-p * q) using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [party, hx] <;> ring

theorem tc04_poly_mul_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => p.eval x * q.eval x) uniformMargins := by
  simpa only [Polynomial.eval_mul] using tc04_poly_integrable (p * q)

theorem tc04_poly_power_integrable (p : Polynomial ℝ) (j : ℕ) :
    Integrable (fun x => p.eval x * x ^ j) uniformMargins := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    tc04_poly_mul_integrable p (Polynomial.X ^ j)

theorem tc04_residual_power_integrable (p : Polynomial ℝ) (j : ℕ) :
    Integrable (fun x => (party x - p.eval x) * x ^ j) uniformMargins := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    tc04_residual_mul_integrable p (Polynomial.X ^ j)

theorem tc04_eq_interval (f : ℝ → ℝ) :
    expectation uniformMargins f = (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, f x := by
  unfold expectation uniformMargins
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  norm_num


def tc04_poly (J : ℕ) (a : Fin (J + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

theorem tc04_poly_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (x : ℝ) :
    (tc04_poly J a).eval x = ∑ i, a i * x ^ (i : ℕ) := by
  simp [tc04_poly, Polynomial.eval_finset_sum]

theorem tc04_poly_degree (J : ℕ) (a : Fin (J + 1) → ℝ) :
    (tc04_poly J a).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem tc04_poly_coeff (J : ℕ) (a : Fin (J + 1) → ℝ) (i : Fin (J + 1)) :
    (tc04_poly J a).coeff i = a i := by
  classical
  simp [tc04_poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    ← Fin.ext_iff]

theorem tc04_eval_expansion (p : Polynomial ℝ) (J : ℕ) (hp : p.natDegree ≤ J)
    (x : ℝ) : p.eval x = ∑ i : Fin (J + 1), p.coeff i * x ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < J + 1 by omega)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm
  

theorem tc04_test (J : ℕ) (p q : Polynomial ℝ)
    (hp : IsProjection uniformMargins J p) (hq : q.natDegree ≤ J) :
    expectation uniformMargins (fun x => (party x - p.eval x) * q.eval x) = 0 := by
  classical
  have he : (fun x => (party x - p.eval x) * q.eval x) =
      (fun x => ∑ i : Fin (J + 1), q.coeff i * ((party x - p.eval x) * x ^ (i : ℕ))) := by
    funext x
    rw [tc04_eval_expansion q J hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold expectation
  rw [he, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    change q.coeff i * expectation uniformMargins _ = 0
    rw [hp.2 i (by omega), mul_zero]
  · intro i _
    exact (tc04_residual_power_integrable p i).const_mul _

theorem tc04_square_zero (p : Polynomial ℝ)
    (hz : expectation uniformMargins (fun x => p.eval x ^ 2) = 0) : p = 0 := by
  have hint : Integrable (fun x => p.eval x ^ 2) uniformMargins := by
    apply (tc04_poly_integrable (p ^ 2)).congr
    exact Filter.Eventually.of_forall (fun x => Polynomial.eval_pow 2)
  have hae : ∀ᵐ x ∂uniformMargins, p.eval x = 0 := by
    have hs := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) hint).mp hz
    filter_upwards [hs] with x hx
    exact (sq_eq_zero_iff).mp hx
  have hae' : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1), p.eval x = 0 := by
    exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)).mp hae
  have heq : EqOn (fun x => p.eval x) (fun _ => (0 : ℝ)) (Icc (-1 : ℝ) 1) :=
    Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hae'
      p.continuous.continuousOn continuous_const.continuousOn
  apply p.eq_zero_of_infinite_isRoot
  exact (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
    (fun x hx => heq ⟨hx.1.le, hx.2.le⟩)

theorem tc04_unique (J : ℕ) (p q : Polynomial ℝ)
    (hp : IsProjection uniformMargins J p) (hq : IsProjection uniformMargins J q) : p = q := by
  have hdeg : (p - q).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le p q).trans (max_le hp.1 hq.1)
  have h1 := tc04_test J p (p - q) hp hdeg
  have h2 := tc04_test J q (p - q) hq hdeg
  have hs : expectation uniformMargins (fun x => (p - q).eval x ^ 2) = 0 := by
    have he : (fun x => (p - q).eval x ^ 2) =
        (fun x => (party x - q.eval x) * (p - q).eval x -
          (party x - p.eval x) * (p - q).eval x) := by
      funext x
      simp only [Polynomial.eval_sub]
      ring
    unfold expectation at *
    rw [he, integral_sub (tc04_residual_mul_integrable q (p - q))
      (tc04_residual_mul_integrable p (p - q)), h2, h1, sub_self]
  exact sub_eq_zero.mp (tc04_square_zero (p - q) hs)

theorem tc04_exists_core (μ : Measure ℝ)
    (hpoly : ∀ (p : Polynomial ℝ) (j : ℕ), Integrable (fun x => p.eval x * x ^ j) μ)
    (hparty : ∀ j : ℕ, Integrable (fun x => party x * x ^ j) μ)
    (hzero : ∀ p : Polynomial ℝ, expectation μ (fun x => p.eval x ^ 2) = 0 → p = 0)
    (J : ℕ) : ∃ p, IsProjection μ J p := by
  classical
  let A : (Fin (J + 1) → ℝ) →ₗ[ℝ] (Fin (J + 1) → ℝ) :=
    { toFun := fun a j => expectation μ (fun x => (tc04_poly J a).eval x * x ^ (j : ℕ))
      map_add' := by
        intro a b
        funext j
        have he : (fun x => (tc04_poly J (a + b)).eval x * x ^ (j : ℕ)) =
            (fun x => (tc04_poly J a).eval x * x ^ (j : ℕ) +
              (tc04_poly J b).eval x * x ^ (j : ℕ)) := by
          funext x
          simp [tc04_poly_eval, add_mul, Finset.sum_add_distrib]
        exact (congrArg (expectation μ) he).trans
          (integral_add (hpoly (tc04_poly J a) j)
            (hpoly (tc04_poly J b) j))
      map_smul' := by
        intro r a
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change expectation μ _ = r * expectation μ _
        have he : (fun x => (tc04_poly J (r • a)).eval x * x ^ (j : ℕ)) =
            (fun x => r * ((tc04_poly J a).eval x * x ^ (j : ℕ))) := by
          funext x
          simp only [tc04_poly_eval, Pi.smul_apply, smul_eq_mul]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
        rw [he]
        exact integral_const_mul _ _ }
  have hker : ∀ a, A a = 0 → a = 0 := by
    intro a ha
    have hs : expectation μ (fun x => (tc04_poly J a).eval x ^ 2) = 0 := by
      have he : (fun x => (tc04_poly J a).eval x ^ 2) =
          (fun x => ∑ j : Fin (J + 1), a j * ((tc04_poly J a).eval x * x ^ (j : ℕ))) := by
        funext x
        rw [pow_two, tc04_poly_eval J a x, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      unfold expectation
      rw [he, integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul]
        have hj : expectation μ
            (fun x => (tc04_poly J a).eval x * x ^ (j : ℕ)) = 0 := congrFun ha j
        change a j * expectation μ _ = 0
        rw [hj, mul_zero]
      · intro j _
        exact (hpoly (tc04_poly J a) j).const_mul _
    have hz := hzero (tc04_poly J a) hs
    funext i
    have hi := congrArg (fun p : Polynomial ℝ => p.coeff i) hz
    simpa only [tc04_poly_coeff, Polynomial.coeff_zero, Pi.zero_apply] using hi
  have hinj : Function.Injective A := by
    intro a b hab
    have hz := hker (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp hz
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj
    (fun j => expectation μ (fun x => party x * x ^ (j : ℕ)))
  refine ⟨tc04_poly J a, tc04_poly_degree J a, ?_⟩
  intro j hj
  have hm := congrFun ha (⟨j, by omega⟩ : Fin (J + 1))
  change expectation μ (fun x => (tc04_poly J a).eval x * x ^ j) =
    expectation μ (fun x => party x * x ^ j) at hm
  unfold expectation at *
  simp_rw [sub_mul]
  rw [integral_sub]
  · exact sub_eq_zero.mpr hm.symm
  · exact hparty j
  · exact hpoly _ j

theorem tc04_exists (J : ℕ) : ∃ p, IsProjection uniformMargins J p := by
  apply tc04_exists_core uniformMargins tc04_poly_power_integrable _ tc04_square_zero J
  intro j
  simpa using tc04_residual_power_integrable 0 j

theorem tc04_chosen_spec (J : ℕ) :
    IsProjection uniformMargins J (projection uniformMargins J) :=
  Classical.epsilon_spec (tc04_exists J)


theorem tc04_exists_degree_core (μ : Measure ℝ)
    (hpoly : ∀ (p : Polynomial ℝ) (j : ℕ), Integrable (fun x => p.eval x * x ^ j) μ)
    (hparty : ∀ j : ℕ, Integrable (fun x => party x * x ^ j) μ)
    (J : ℕ)
    (hzero : ∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => p.eval x ^ 2) = 0 → p = 0) : ∃ p, IsProjection μ J p := by
  classical
  let A : (Fin (J + 1) → ℝ) →ₗ[ℝ] (Fin (J + 1) → ℝ) :=
    { toFun := fun a j => expectation μ (fun x => (tc04_poly J a).eval x * x ^ (j : ℕ))
      map_add' := by
        intro a b
        funext j
        have he : (fun x => (tc04_poly J (a + b)).eval x * x ^ (j : ℕ)) =
            (fun x => (tc04_poly J a).eval x * x ^ (j : ℕ) +
              (tc04_poly J b).eval x * x ^ (j : ℕ)) := by
          funext x
          simp [tc04_poly_eval, add_mul, Finset.sum_add_distrib]
        exact (congrArg (expectation μ) he).trans
          (integral_add (hpoly (tc04_poly J a) j)
            (hpoly (tc04_poly J b) j))
      map_smul' := by
        intro r a
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change expectation μ _ = r * expectation μ _
        have he : (fun x => (tc04_poly J (r • a)).eval x * x ^ (j : ℕ)) =
            (fun x => r * ((tc04_poly J a).eval x * x ^ (j : ℕ))) := by
          funext x
          simp only [tc04_poly_eval, Pi.smul_apply, smul_eq_mul]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
        rw [he]
        exact integral_const_mul _ _ }
  have hker : ∀ a, A a = 0 → a = 0 := by
    intro a ha
    have hs : expectation μ (fun x => (tc04_poly J a).eval x ^ 2) = 0 := by
      have he : (fun x => (tc04_poly J a).eval x ^ 2) =
          (fun x => ∑ j : Fin (J + 1), a j * ((tc04_poly J a).eval x * x ^ (j : ℕ))) := by
        funext x
        rw [pow_two, tc04_poly_eval J a x, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      unfold expectation
      rw [he, integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul]
        have hj : expectation μ
            (fun x => (tc04_poly J a).eval x * x ^ (j : ℕ)) = 0 := congrFun ha j
        change a j * expectation μ _ = 0
        rw [hj, mul_zero]
      · intro j _
        exact (hpoly (tc04_poly J a) j).const_mul _
    have hz := hzero (tc04_poly J a) (tc04_poly_degree J a) hs
    funext i
    have hi := congrArg (fun p : Polynomial ℝ => p.coeff i) hz
    simpa only [tc04_poly_coeff, Polynomial.coeff_zero, Pi.zero_apply] using hi
  have hinj : Function.Injective A := by
    intro a b hab
    have hz := hker (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp hz
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj
    (fun j => expectation μ (fun x => party x * x ^ (j : ℕ)))
  refine ⟨tc04_poly J a, tc04_poly_degree J a, ?_⟩
  intro j hj
  have hm := congrFun ha (⟨j, by omega⟩ : Fin (J + 1))
  change expectation μ (fun x => (tc04_poly J a).eval x * x ^ j) =
    expectation μ (fun x => party x * x ^ j) at hm
  unfold expectation at *
  simp_rw [sub_mul]
  rw [integral_sub]
  · exact sub_eq_zero.mpr hm.symm
  · exact hparty j
  · exact hpoly _ j

end
end AronowAudit.P023.Wave1

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter
local instance tc04_supported_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Continuous functions on the supported interval are integrable. -/
theorem tc04_supported_continuous_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1) 1)) :
    Integrable f μ := by
  have hr : μ.restrict (Icc (-1 : ℝ) 1) = μ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hs)
  rw [← hr]
  exact hf.integrableOn_Icc

/-- Polynomial integrability under an arbitrary finite supported margin law. -/
theorem tc04_supported_poly_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (p : Polynomial ℝ) : Integrable (fun x => p.eval x) μ :=
  tc04_supported_continuous_integrable μ hs _ p.continuous.continuousOn

theorem tc04_supported_piecewise_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (p q : Polynomial ℝ) :
    Integrable (fun x => if 0 ≤ x then p.eval x else q.eval x) μ :=
  Integrable.piecewise measurableSet_Ici
    (tc04_supported_poly_integrable μ hs p).integrableOn
    (tc04_supported_poly_integrable μ hs q).integrableOn

theorem tc04_supported_residual_mul_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (p q : Polynomial ℝ) :
    Integrable (fun x => (party x-p.eval x)*q.eval x) μ := by
  convert tc04_supported_piecewise_integrable μ hs ((1-p)*q) (-p*q) using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [party,hx] <;> ring

theorem tc04_supported_square_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (p : Polynomial ℝ) :
    Integrable (fun x => (party x-p.eval x)^2) μ := by
  convert tc04_supported_piecewise_integrable μ hs ((1-p)^2) (p^2) using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [party,hx]

/-- Testing the normal equations against an arbitrary polynomial in their span. -/
theorem tc04_projection_test (μ : Measure ℝ) [IsFiniteMeasure μ] (hs : MarginSupport μ)
    (J : ℕ) (p q : Polynomial ℝ) (hp : IsProjection μ J p) (hq : q.natDegree ≤ J) :
    expectation μ (fun x => (party x-p.eval x)*q.eval x) = 0 := by
  classical
  have he : (fun x => (party x-p.eval x)*q.eval x) =
      (fun x => ∑ i : Fin (J+1), q.coeff i * ((party x-p.eval x)*x^(i:ℕ))) := by
    funext x
    rw [tc04_eval_expansion q J hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold expectation
  rw [he, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    change q.coeff i * expectation μ _ = 0
    rw [hp.2 i (by omega), mul_zero]
  · intro i _
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      (tc04_supported_residual_mul_integrable μ hs p (Polynomial.X^(i:ℕ))).const_mul (q.coeff i)

/-- Generic existence from polynomial square nondegeneracy. -/
theorem tc04_projection_exists (μ : Measure ℝ) [IsFiniteMeasure μ] (hs : MarginSupport μ)
    (hz : ∀ p : Polynomial ℝ, expectation μ (fun x => p.eval x^2)=0 → p=0)
    (J : ℕ) : ∃ p, IsProjection μ J p := by
  apply tc04_exists_core μ _ _ hz J
  · intro p j
    apply (tc04_supported_poly_integrable μ hs (p*Polynomial.X^j)).congr
    exact Filter.Eventually.of_forall (fun x => by simp)
  · intro j
    simpa using tc04_supported_residual_mul_integrable μ hs 0 (Polynomial.X^j)

/-- The chosen projection satisfies its defining equations. -/
theorem tc04_projection_spec (μ : Measure ℝ) [IsFiniteMeasure μ] (hs : MarginSupport μ)
    (hz : ∀ p : Polynomial ℝ, expectation μ (fun x => p.eval x^2)=0 → p=0)
    (J : ℕ) : IsProjection μ J (projection μ J) :=
  Classical.epsilon_spec (tc04_projection_exists μ hs hz J)


/-- Every solution of the projection equations is a least-squares minimizer. -/
theorem tc04_projection_minimum (μ : Measure ℝ) [IsFiniteMeasure μ] (hs : MarginSupport μ)
    (J : ℕ) (q p : Polynomial ℝ) (hq : IsProjection μ J q) (hp : p.natDegree ≤ J) :
    expectation μ (fun x => (party x-q.eval x)^2) ≤
      expectation μ (fun x => (party x-p.eval x)^2) := by
  have hd : (q-p).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le q p).trans (max_le hq.1 hp)
  have ho := tc04_projection_test μ hs J q (q-p) hq hd
  have hquad : Integrable (fun x => (q.eval x-p.eval x)^2) μ := by
    apply (tc04_supported_poly_integrable μ hs ((q-p)^2)).congr
    exact Filter.Eventually.of_forall (fun x => by simp)
  have hres := tc04_supported_square_integrable μ hs q
  have he : (fun x => (party x-p.eval x)^2) =
      (fun x => (party x-q.eval x)^2+(q.eval x-p.eval x)^2+
        2*((party x-q.eval x)*(q-p).eval x)) := by
    funext x
    simp only [Polynomial.eval_sub]
    ring
  have hn : 0 ≤ expectation μ (fun x => (q.eval x-p.eval x)^2) :=
    integral_nonneg (fun x => sq_nonneg _)
  unfold expectation at *
  have hsum : Integrable (fun x => (party x-q.eval x)^2+(q.eval x-p.eval x)^2) μ := hres.add hquad
  rw [he, integral_add hsum
    ((tc04_supported_residual_mul_integrable μ hs q (q-p)).const_mul 2),
    integral_add hres hquad, integral_const_mul, ho]
  linarith

end
end AronowAudit.P023.Wave1
