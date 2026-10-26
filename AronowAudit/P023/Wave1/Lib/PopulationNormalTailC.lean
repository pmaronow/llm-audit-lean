import AronowAudit.P023.Wave1.Lib.ProjectionCoreTailC

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter Polynomial
local instance tc04_normal_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A polynomial version of a design column with the party value fixed. -/
def tc04_column_polynomial (J : ℕ) (j : Fin (J+2)) (d : ℝ) : Polynomial ℝ :=
  if j.val=0 then 1 else if j.val=1 then C d else X^(j.val-1)

/-- The fitted polynomial on either side of zero. -/
def tc04_fit_polynomial (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ) : Polynomial ℝ :=
  ∑ j, C (a j)*tc04_column_polynomial J j d

theorem tc04_column_piecewise (J : ℕ) (j : Fin (J+2)) (x : ℝ) :
    polynomialDesign J (fun x : ℝ => x) party x j =
      if 0 ≤ x then (tc04_column_polynomial J j 1).eval x
        else (tc04_column_polynomial J j 0).eval x := by
  by_cases hj0 : j.val=0 <;> by_cases hj1 : j.val=1 <;> by_cases hx : 0 ≤ x <;>
    simp [polynomialDesign, tc04_column_polynomial, party, hx, hj0, hj1]

theorem tc04_fit_piecewise (J : ℕ) (a : Fin (J+2) → ℝ) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) a x =
      if 0 ≤ x then (tc04_fit_polynomial J a 1).eval x
        else (tc04_fit_polynomial J a 0).eval x := by
  simp_rw [predict, tc04_column_piecewise]
  by_cases hx : 0 ≤ x <;>
    simp [hx, tc04_fit_polynomial, Polynomial.eval_finsetSum, mul_comm]

theorem tc04_design_fit_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (j : Fin (J+2)) (a : Fin (J+2) → ℝ) :
    Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      predict (polynomialDesign J (fun x : ℝ => x) party) a x) μ := by
  convert tc04_supported_piecewise_integrable μ hs
    (tc04_column_polynomial J j 1 * tc04_fit_polynomial J a 1)
    (tc04_column_polynomial J j 0 * tc04_fit_polynomial J a 0) using 1
  funext x
  rw [tc04_column_piecewise, tc04_fit_piecewise]
  by_cases hx : 0 ≤ x <;> simp [hx]

theorem tc04_fit_square_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (a : Fin (J+2) → ℝ) :
    Integrable (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) a x^2) μ := by
  convert tc04_supported_piecewise_integrable μ hs
    ((tc04_fit_polynomial J a 1)^2) ((tc04_fit_polynomial J a 0)^2) using 1
  funext x
  rw [tc04_fit_piecewise]
  by_cases hx : 0 ≤ x <;> simp [hx]

/-- Design times a response continuous on the supported interval is integrable. -/
theorem tc04_design_response_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (j : Fin (J+2)) (m : ℝ → ℝ)
    (hm : ContinuousOn m (Icc (-1) 1)) :
    Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x j*m x) μ := by
  have h1 := tc04_supported_continuous_integrable μ hs
    (fun x => (tc04_column_polynomial J j 1).eval x*m x)
    ((tc04_column_polynomial J j 1).continuous.continuousOn.mul hm)
  have h0 := tc04_supported_continuous_integrable μ hs
    (fun x => (tc04_column_polynomial J j 0).eval x*m x)
    ((tc04_column_polynomial J j 0).continuous.continuousOn.mul hm)
  convert Integrable.piecewise (measurableSet_Ici (a := (0:ℝ))) h1.integrableOn h0.integrableOn using 1
  funext x
  rw [tc04_column_piecewise]
  by_cases hx : 0 ≤ x <;> simp [Set.piecewise,hx]

/-- Population normal equations have a solution under the actual full-rank premise. -/
theorem tc04_population_normal_exists (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J)
    (m : ℝ → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable
      (fun x => polynomialDesign J (fun x : ℝ => x) party x j*m x) μ) :
    ∃ a, PopNormal μ J m a := by
  let X := polynomialDesign J (fun x : ℝ => x) party
  let A : (Fin (J+2) → ℝ) →ₗ[ℝ] (Fin (J+2) → ℝ) :=
    { toFun := fun a j => expectation μ (fun x => X x j*predict X a x)
      map_add' := by
        intro a b
        funext j
        have he : (fun x => X x j*predict X (a+b) x) =
            (fun x => X x j*predict X a x+X x j*predict X b x) := by
          funext x
          simp [predict, mul_add, Finset.sum_add_distrib]
        exact (congrArg (expectation μ) he).trans
          (integral_add (tc04_design_fit_integrable μ hs J j a)
            (tc04_design_fit_integrable μ hs J j b))
      map_smul' := by
        intro r a
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change expectation μ _ = r*expectation μ _
        have he : (fun x => X x j*predict X (r • a) x) =
            (fun x => r*(X x j*predict X a x)) := by
          funext x
          simp only [predict, Pi.smul_apply, smul_eq_mul]
          simp_rw [← mul_assoc, mul_comm (X x _) r, mul_assoc]
          rw [← Finset.mul_sum]
          ring
        rw [he]
        exact integral_const_mul _ _ }
  have hker : ∀ a, A a=0 → a=0 := by
    intro a ha
    by_contra hn
    have hp := hpd a hn
    have he : (fun x => predict X a x^2) =
        (fun x => ∑ j, a j*(X x j*predict X a x)) := by
      funext x
      rw [pow_two, predict, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hz : expectation μ (fun x => predict X a x^2)=0 := by
      unfold expectation
      rw [he, integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul]
        have hj : expectation μ (fun x => X x j*predict X a x)=0 := congrFun ha j
        change a j*expectation μ _=0
        rw [hj, mul_zero]
      · intro j _
        exact (tc04_design_fit_integrable μ hs J j a).const_mul _
    exact (ne_of_gt hp) hz
  have hinj : Function.Injective A := by
    intro a b hab
    exact sub_eq_zero.mp (hker (a-b) (by rw [map_sub,hab,sub_self]))
  obtain ⟨a,ha⟩ := LinearMap.surjective_of_injective hinj
    (fun j => expectation μ (fun x => X x j*m x))
  refine ⟨a,?_⟩
  intro j
  change expectation μ (fun x => X x j*(m x-predict X a x))=0
  unfold expectation
  simp_rw [mul_sub]
  rw [integral_sub (hm j) (tc04_design_fit_integrable μ hs J j a)]
  exact sub_eq_zero.mpr (congrFun ha j).symm

/-- A normal-equation residual is orthogonal to every fitted vector. -/
theorem tc04_population_normal_test (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (m : ℝ → ℝ) (a b : Fin (J+2) → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable
      (fun x => polynomialDesign J (fun x : ℝ => x) party x j*m x) μ)
    (ha : PopNormal μ J m a) :
    expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) b x *
      (m x-predict (polynomialDesign J (fun x : ℝ => x) party) a x))=0 := by
  let X := polynomialDesign J (fun x : ℝ => x) party
  have he : (fun x => predict X b x*(m x-predict X a x)) =
      (fun x => ∑ j, b j*(X x j*(m x-predict X a x))) := by
    funext x
    rw [predict, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold expectation
  rw [he, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    rw [integral_const_mul]
    change b j*expectation μ _=0
    rw [ha j,mul_zero]
  · intro j _
    apply ((((hm j).sub (tc04_design_fit_integrable μ hs J j a)).const_mul (b j))).congr
    apply Filter.Eventually.of_forall
    intro x
    change b j*(X x j*m x-X x j*predict X a x)=b j*(X x j*(m x-predict X a x))
    ring


end
end AronowAudit.P023.Wave1
