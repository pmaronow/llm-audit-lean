import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.P011_BlockOLSCompletion
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- A normalized sum over the two Bool coordinates is the path witness's four-state mean. -/
private lemma sign_pair_average (f : ℝ → ℝ → ℝ) :
    (∑ u : Fin 2 → Bool, f (sign (u 0)) (sign (u 1))) /
        (Fintype.card (Fin 2 → Bool) : ℝ) = pathMean f := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, finTwoArrowEquiv, sign, pathMean]
  <;> ring

/-- Exact second moment of a sum of centered, independent uniform coordinates.
The proof includes the off-diagonal calculation, rather than assuming independence
of the block quadratic forms. -/
private lemma uniform_blocks_second_moment {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (K : ℕ) (f : A → ℝ) (v : ℝ)
    (hmean : (∑ a, f a) / (Fintype.card A : ℝ) = 0)
    (hsq : (∑ a, f a ^ 2) / (Fintype.card A : ℝ) = v) :
    (∑ u : Fin K → A, (∑ b, f (u b)) ^ 2) /
        (Fintype.card (Fin K → A) : ℝ) = (K : ℝ) * v := by
  classical
  let μ : Measure (Fin K → A) := (PMF.uniformOfFintype (Fin K → A)).toMeasure
  have hcoord (b : Fin K) : (∫ u, f (u b) ∂μ) = 0 := by
    change (∫ u, f (u b) ∂(PMF.uniformOfFintype (Fin K → A)).toMeasure) = 0
    rw [BlockOLSCompletion.uniform_evaluation_integral b f]
    exact hmean
  have hind : iIndepFun (fun (b : Fin K) (u : Fin K → A) => f (u b)) μ := by
    dsimp only [μ]
    have hp : (PMF.uniformOfFintype (Fin K → A)).toMeasure =
        Measure.pi (fun _ : Fin K => (PMF.uniformOfFintype A).toMeasure) := by
      apply Measure.ext_of_singleton
      intro u
      simp [Measure.pi_singleton, PMF.toMeasure_apply_singleton,
        PMF.uniformOfFintype_apply, Fintype.card_fun, ENNReal.inv_pow]
    rw [hp]
    exact iIndepFun_pi
      (μ := fun _ : Fin K => (PMF.uniformOfFintype A).toMeasure)
      (X := fun _ : Fin K => f) (fun _ => (measurable_of_finite f).aemeasurable)
  have hpair (i j : Fin K) :
      (∫ u, f (u i) * f (u j) ∂μ) = if i = j then v else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have h := (BlockOLSCompletion.uniform_evaluation_integral i
        (fun a => f a ^ 2)).trans hsq
      simpa only [μ, pow_two] using h
    · rw [if_neg hij]
      have hprod := (hind.indepFun hij).integral_fun_mul_eq_mul_integral
        (measurable_of_finite (fun u : Fin K → A => f (u i))).aestronglyMeasurable
        (measurable_of_finite (fun u : Fin K → A => f (u j))).aestronglyMeasurable
      rw [hprod, hcoord i, hcoord j, zero_mul]
  have hsecond : (∫ u, (∑ b, f (u b)) ^ 2 ∂μ) = (K : ℝ) * v := by
    calc
      (∫ u, (∑ b, f (u b)) ^ 2 ∂μ) =
          ∫ u, ∑ i, ∑ j, f (u i) * f (u j) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun u => by dsimp only; rw [pow_two, Finset.sum_mul_sum])
      _ = ∑ i, ∑ j, ∫ u, f (u i) * f (u j) ∂μ := by
        rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
        apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)
      _ = (K : ℝ) * v := by
        simp_rw [hpair]
        simp
  change (∫ u, (∑ b, f (u b)) ^ 2
    ∂(PMF.uniformOfFintype (Fin K → A)).toMeasure) = _ at hsecond
  rw [PMF.integral_eq_sum] at hsecond
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul] at hsecond
  rw [← Finset.mul_sum] at hsecond
  simpa only [div_eq_mul_inv, mul_comm] using hsecond

theorem n7_proof : N7 := by
  classical
  intro h2 k
  let S : (Fin 2 → Bool) → ℝ := fun u =>
    ∑ r, pathBlock 2 (sign (u 0)) (sign (u 1)) r
  let C : (Fin 2 → Bool) → ℝ := fun u =>
    quadratic (oracleMatrix pathGraph) (pathBlock 2 (sign (u 0)) (sign (u 1))) + 11 / 5
  have hS0 : (∑ u, S u) / (Fintype.card (Fin 2 → Bool) : ℝ) = 0 := by
    dsimp only [S]
    rw [sign_pair_average (fun u v => ∑ r, pathBlock 2 u v r)]
    exact (path_block_moments 2).2.1
  have hS2 : (∑ u, S u ^ 2) / (Fintype.card (Fin 2 → Bool) : ℝ) = 29 / 5 := by
    dsimp only [S]
    rw [sign_pair_average (fun u v => (∑ r, pathBlock 2 u v r) ^ 2)]
    exact (path_block_moments 2).2.2.1
  have hC0 : (∑ u, C u) / (Fintype.card (Fin 2 → Bool) : ℝ) = 0 := by
    dsimp only [C]
    rw [sign_pair_average (fun u v => quadratic (oracleMatrix pathGraph) (pathBlock 2 u v) + 11 / 5)]
    have hQ : pathMean (fun u v =>
        quadratic (oracleMatrix pathGraph) (pathBlock 2 u v)) = -11 / 5 := by
      convert (path_block_moments 2).2.2.2.1 using 1 <;> norm_num
    unfold pathMean at hQ ⊢
    linarith
  have hC2 : (∑ u, C u ^ 2) / (Fintype.card (Fin 2 → Bool) : ℝ) =
      28836 / 625 := by
    dsimp only [C]
    rw [sign_pair_average (fun u v => (quadratic (oracleMatrix pathGraph) (pathBlock 2 u v) + 11 / 5) ^ 2)]
    convert (path_block_moments 2).2.2.2.2.1 using 1 <;> norm_num
  have hK0 : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hSsource (u : Fin (k + 1) → Fin 2 → Bool) :
      betaHat (PF.model k) (pathSource (k + 1) u) =
        (∑ b, S (u b)) / (3 * ((k + 1 : ℕ) : ℝ)) := by
    change average (fun i => (1 : ℝ) * pathSource (k + 1) u i) = _
    simp only [one_mul, average]
    rw [((h2 (k + 1)).1 (pathSource (k + 1) u)).1]
    simp_rw [(h2 (k + 1)).2 u]
    push_cast
    rfl
  have hCsum (u : Fin (k + 1) → Fin 2 → Bool) :
      (∑ b, C (u b)) =
        (∑ b, quadratic (oracleMatrix pathGraph)
          (pathBlock 2 (sign (u b 0)) (sign (u b 1)))) +
        ((k + 1 : ℕ) : ℝ) * (11 / 5) := by
    simp only [C, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hCsource (u : Fin (k + 1) → Fin 2 → Bool) :
      pathQbar (k + 1) (pathSource (k + 1) u) + 11 / 5 =
        (∑ b, C (u b)) / ((k + 1 : ℕ) : ℝ) := by
    unfold pathQbar
    rw [((h2 (k + 1)).1 (pathSource (k + 1) u)).2.1]
    simp_rw [(h2 (k + 1)).2 u]
    rw [hCsum]
    field_simp [hK0]
    <;> ring
  constructor
  · unfold expectation
    change (∫ y, betaHat (PF.model k) y ^ 2
      ∂uniformLaw (pathSource (k + 1))) = _
    rw [uniform_integral (pathSource (k + 1)) (measurable_of_finite _)
      (fun y => betaHat (PF.model k) y ^ 2)
      (by unfold betaHat average weighted; fun_prop)]
    simp_rw [hSsource, div_pow]
    rw [← Finset.sum_div, div_right_comm,
      uniform_blocks_second_moment (k + 1) S (29 / 5) hS0 hS2]
    push_cast
    field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
    <;> ring
  · unfold expectation
    change (∫ y, (pathQbar (k + 1) y + 11 / 5) ^ 2
      ∂uniformLaw (pathSource (k + 1))) = _
    rw [uniform_integral (pathSource (k + 1)) (measurable_of_finite _)
      (fun y => (pathQbar (k + 1) y + 11 / 5) ^ 2)
      (by unfold pathQbar quadratic; fun_prop)]
    simp_rw [hCsource, div_pow]
    rw [← Finset.sum_div, div_right_comm,
      uniform_blocks_second_moment (k + 1) C (28836 / 625) hC0 hC2]
    push_cast
    field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
    <;> ring

end

end AronowAudit.P011.Wave1.PropositionOne
