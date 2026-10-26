import AronowAudit.P023.Wave1.Lib.PopulationNormalTailC

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter Polynomial
local instance tc04_fwl_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Embed polynomial coefficients into the full design with party coefficient zero. -/
def tc04_embed_polynomial (J : ℕ) (p : Polynomial ℝ) : Fin (J+2) → ℝ :=
  fun j => if j.val=0 then p.coeff 0 else if j.val=1 then 0 else p.coeff (j.val-1)

theorem tc04_embed_predict (J : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ J) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (tc04_embed_polynomial J p) x=p.eval x := by
  rw [tc04_eval_expansion p J hp]
  simp [predict, polynomialDesign, tc04_embed_polynomial, Fin.sum_univ_succ, mul_comm]

/-- Full design rank implies the polynomial projection equations have a solution. -/
theorem tc04_projection_spec_of_full_rank (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    IsProjection μ J (projection μ J) := by
  have hpoly : ∀ (p : Polynomial ℝ) (j : ℕ), Integrable (fun x => p.eval x*x^j) μ := by
    intro p j
    apply (tc04_supported_poly_integrable μ hs (p*X^j)).congr
    exact Filter.Eventually.of_forall (fun x => by simp)
  have hparty : ∀ j : ℕ, Integrable (fun x => party x*x^j) μ := by
    intro j
    simpa using tc04_supported_residual_mul_integrable μ hs 0 (X^j)
  apply Classical.epsilon_spec
  apply tc04_exists_degree_core μ hpoly hparty J
  intro p hp hz
  have ha0 : tc04_embed_polynomial J p=0 := by
    by_contra ha
    have hpos := hpd (tc04_embed_polynomial J p) ha
    simp_rw [tc04_embed_predict J p hp] at hpos
    exact (ne_of_gt hpos) hz
  apply Polynomial.funext
  intro x
  rw [← tc04_embed_predict J p hp x, ha0]
  simp [predict]

theorem tc04_fit_polynomial_degree (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ) :
    (tc04_fit_polynomial J a d).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  unfold tc04_column_polynomial
  split_ifs <;> simp_all
  omega

/-- The full fitted value is a nuisance polynomial plus its actual party coefficient. -/
theorem tc04_fit_decomposition (J : ℕ) (a : Fin (J+2) → ℝ) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) a x =
      (tc04_fit_polynomial J a 0).eval x+a ⟨1,by omega⟩*party x := by
  have hd : tc04_fit_polynomial J a 1-tc04_fit_polynomial J a 0=C (a ⟨1,by omega⟩) := by
    unfold tc04_fit_polynomial
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (⟨1,by omega⟩ : Fin (J+2))]
    · simp [tc04_column_polynomial]
    · intro j _ hj
      have hj' : j.val ≠ 1 := fun h => hj (Fin.ext h)
      by_cases h0 : j.val=0 <;> simp [tc04_column_polynomial,h0,hj']
    · simp
  have hd' : tc04_fit_polynomial J a 1=tc04_fit_polynomial J a 0+C (a ⟨1,by omega⟩) :=
    (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)
  rw [tc04_fit_piecewise]
  by_cases hx : 0 ≤ x <;> simp [hx,hd',party]

/-- A single design coefficient evaluates to its single column. -/
theorem tc04_predict_single (J : ℕ) (j : Fin (J+2)) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (Pi.single j 1) x =
      polynomialDesign J (fun x : ℝ => x) party x j := by
  simp [predict, Pi.single_apply]

/-- A polynomial projection residual has a nonzero coefficient vector in the full design. -/
def tc04_residual_vector (μ : Measure ℝ) (J : ℕ) : Fin (J+2) → ℝ :=
  Pi.single ⟨1,by omega⟩ 1-tc04_embed_polynomial J (projection μ J)

theorem tc04_residual_vector_eval (μ : Measure ℝ) (J : ℕ)
    (hp : IsProjection μ J (projection μ J)) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (tc04_residual_vector μ J) x =
      popResidual μ J x := by
  have he : ∀ a b : Fin (J+2) → ℝ,
      predict (polynomialDesign J (fun x : ℝ => x) party) (a-b) x =
        predict (polynomialDesign J (fun x : ℝ => x) party) a x-
        predict (polynomialDesign J (fun x : ℝ => x) party) b x := by
    intro a b
    simp [predict,mul_sub,Finset.sum_sub_distrib]
  rw [tc04_residual_vector,he,tc04_predict_single,tc04_embed_predict J _ hp.1]
  simp [polynomialDesign,popResidual]

/-- Full rank gives strictly positive residual treatment information. -/
theorem tc04_residual_variance_pos (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (hpd : MomentPositiveDefinite μ J) :
    0 < residualVariance μ J := by
  have hp := tc04_projection_spec_of_full_rank μ hs J hpd
  have hw : tc04_residual_vector μ J ≠ 0 := by
    intro hw
    have h := congrFun hw (⟨1,by omega⟩ : Fin (J+2))
    simp [tc04_residual_vector,tc04_embed_polynomial] at h
  have hpos := hpd (tc04_residual_vector μ J) hw
  simpa only [tc04_residual_vector_eval μ J hp, residualVariance] using hpos

/-- The full chosen normal equations imply the genuine population FWL identity. -/
theorem population_fwl (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hs : MarginSupport μ) (J : ℕ) (hJ : 1 ≤ J)
    (hpd : MomentPositiveDefinite μ J) (h : ℝ → ℝ)
    (hc : ContinuousOn h (Set.Icc (-1) 1)) :
    populationCoefficient μ J (fun x => 1/2+h x) = biasFunctional μ J h := by
  let m : ℝ → ℝ := fun x => 1/2+h x
  let X := polynomialDesign J (fun x : ℝ => x) party
  let a := Classical.epsilon (PopNormal μ J m)
  let q := projection μ J
  let r := popResidual μ J
  have hm : ∀ j : Fin (J+2), Integrable (fun x => X x j*m x) μ :=
    fun j => tc04_design_response_integrable μ hs J j m (continuousOn_const.add hc)
  have ha : PopNormal μ J m a := Classical.epsilon_spec
    (tc04_population_normal_exists μ hs J hpd m hm)
  have hq := tc04_projection_spec_of_full_rank μ hs J hpd
  have hv := tc04_residual_variance_pos μ hs J hpd
  have hi (p : Polynomial ℝ) : Integrable (fun x => r x*p.eval x) μ :=
    tc04_supported_residual_mul_integrable μ hs q p
  have hr : Integrable r μ := by simpa using hi 1
  have hr0 : expectation μ r=0 := by
    change expectation μ (fun x => party x-(projection μ J).eval x)=0
    simpa only [pow_zero,mul_one] using hq.2 0 (by omega)
  have hrD : Integrable (fun x => r x*party x) μ := by
    convert tc04_supported_piecewise_integrable μ hs (1-q) 0 using 1
    funext x
    dsimp [r,popResidual,q]
    by_cases hx : 0 ≤ x <;> simp [party,hx]
  have hrh : Integrable (fun x => r x*h x) μ := by
    have hpos := tc04_supported_continuous_integrable μ hs
      (fun x => (1-q.eval x)*h x) ((continuousOn_const.sub q.continuous.continuousOn).mul hc)
    have hneg := tc04_supported_continuous_integrable μ hs
      (fun x => -q.eval x*h x) (q.continuous.continuousOn.neg.mul hc)
    convert Integrable.piecewise (measurableSet_Ici (a := (0:ℝ))) hpos.integrableOn hneg.integrableOn using 1
    funext x
    dsimp [r,popResidual,q]
    by_cases hx : 0 ≤ x <;> simp [Set.piecewise,party,hx]
  have hrm : Integrable (fun x => r x*m x) μ := by
    have he : (fun x => r x*m x)=(fun x => (1/2:ℝ)*r x+r x*h x) := by
      funext x
      dsimp [m]
      ring
    rw [he]
    exact (hr.const_mul _).add hrh
  have hD : expectation μ (fun x => r x*party x)=residualVariance μ J := by
    have ho := tc04_projection_test μ hs J q q hq hq.1
    have he : (fun x => r x^2)=(fun x => r x*party x-r x*q.eval x) := by
      funext x
      dsimp [r,popResidual,q]
      ring
    unfold expectation at ho
    change (∫ x, r x*q.eval x ∂μ)=0 at ho
    unfold residualVariance expectation
    change (∫ x, r x*party x ∂μ)=∫ x, r x^2 ∂μ
    rw [he,integral_sub hrD (hi q),ho,sub_zero]
  let p := tc04_fit_polynomial J a 0
  have hp := tc04_fit_polynomial_degree J a 0
  have hrp := hi p
  have horth := tc04_projection_test μ hs J q p hq hp
  change expectation μ (fun x => r x*p.eval x)=0 at horth
  have ht := tc04_population_normal_test μ hs J m a (tc04_residual_vector μ J) hm ha
  simp_rw [tc04_residual_vector_eval μ J hq] at ht
  have he : (fun x => r x*(m x-predict X a x)) =
      (fun x => r x*m x-r x*p.eval x-a ⟨1,by omega⟩*(r x*party x)) := by
    funext x
    rw [tc04_fit_decomposition]
    dsimp [p]
    ring
  unfold expectation at ht
  change (∫ x, r x*(m x-predict X a x) ∂μ)=0 at ht
  have hsum : Integrable (fun x => r x*m x-r x*p.eval x) μ := hrm.sub hrp
  rw [he, integral_sub hsum (hrD.const_mul _),
    integral_sub hrm hrp,integral_const_mul] at ht
  change expectation μ (fun x => r x*m x)-expectation μ (fun x => r x*p.eval x)-
    a ⟨1,by omega⟩*expectation μ (fun x => r x*party x)=0 at ht
  rw [horth,hD,sub_zero] at ht
  have hm' : expectation μ (fun x => r x*m x)=expectation μ (fun x => r x*h x) := by
    have he : (fun x => r x*m x)=(fun x => (1/2:ℝ)*r x+r x*h x) := by
      funext x
      dsimp [m]
      ring
    unfold expectation at hr0 ⊢
    rw [he,integral_add (hr.const_mul _) hrh,integral_const_mul,hr0]
    ring
  rw [hm'] at ht
  change a ⟨1,by omega⟩=expectation μ (fun x => r x*h x)/residualVariance μ J
  apply (eq_div_iff (ne_of_gt hv)).mpr
  linarith

end
end AronowAudit.P023.Wave1
