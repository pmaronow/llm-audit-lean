import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.Matrix

/-!
# Measurability of the supported-design OLS bad set

This proof uses the entrywise inverse formula, including at singular matrices, and
measurability of parameterized Bochner integrals. No integrability of a random inverse
Gram matrix is asserted or needed.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- The box and the finitely many distinctness conditions are Borel. Also used in N19. -/
theorem measurableSet_designSet (n : ℕ) : MeasurableSet (designSet n) := by
  classical
  have hbox : MeasurableSet
      {x : Fin n → ℝ | ∀ i, 1 / (n : ℝ) ≤ x i ∧ x i ≤ 1} := by
    have hset : {x : Fin n → ℝ | ∀ i, 1 / (n : ℝ) ≤ x i ∧ x i ≤ 1} =
        ⋂ i : Fin n, {x : Fin n → ℝ | 1 / (n : ℝ) ≤ x i ∧ x i ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)
  have hinj : MeasurableSet {x : Fin n → ℝ | Function.Injective x} := by
    have hset : {x : Fin n → ℝ | Function.Injective x} =
        ⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ | x i = x j → i = j} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.Injective]
    rw [hset]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i = j
    · simpa [hij] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Fin n → ℝ)))
    · have h : MeasurableSet {x : Fin n → ℝ | x i = x j}ᶜ :=
        (measurableSet_eq_fun (f := fun x : Fin n → ℝ => x i) (g := fun x => x j)
          (measurable_pi_apply i) (measurable_pi_apply j)).compl
      convert h using 1
      ext x
      simp [hij]
  change MeasurableSet
    ({x : Fin n → ℝ | ∀ i, 1 / (n : ℝ) ≤ x i ∧ x i ≤ 1} ∩
      {x : Fin n → ℝ | Function.Injective x})
  exact hbox.inter hinj

private theorem measurable_olsCoef_vand (n d : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => olsCoef (vand d z.1) z.2) := by
  classical
  let A : ((Fin n → ℝ) × (Fin n → ℝ)) →
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun z => (vand d z.1).transpose * vand d z.1
  have hP : Continuous
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => vand d z.1) := by
    exact continuous_pi fun i => continuous_pi fun k =>
      (((continuous_apply i).comp continuous_fst).pow (k : ℕ))
  have hA : Continuous A := hP.matrix_transpose.matrix_mul hP
  have hAi (k l : Fin (d + 1)) : Measurable (fun z => (A z)⁻¹ k l) := by
    have hdet : Measurable (fun z => (A z).det⁻¹) := hA.matrix_det.measurable.inv
    have hadj : Measurable (fun z => (A z).adjugate k l) :=
      (hA.matrix_adjugate.matrix_elem k l).measurable
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
      Pi.mul_def] using hdet.mul hadj
  have hPy : Continuous
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (vand d z.1).transpose.mulVec z.2) :=
    hP.matrix_transpose.matrix_mulVec continuous_snd
  apply Measurable.of_eval
  intro k
  change Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    ∑ l : Fin (d + 1), ((A z)⁻¹ k l) * ((vand d z.1).transpose.mulVec z.2 l))
  exact Finset.measurable_sum Finset.univ fun l _ =>
    (hAi k l).mul (((continuous_apply l).comp hPy).measurable)

/-- Integrating a jointly measurable polynomial expression over a fixed interval is
measurable in its coefficient vector. The parameterized-integral theorem does not
require an integrability hypothesis on the parameter space. -/
private theorem measurable_regionInt_coeffPoly (d : ℕ) :
    Measurable (fun b : Fin (d + 1) → ℝ => regionInt (coeffPoly b) (coeffPoly b)) := by
  classical
  have heval : Measurable
      (fun z : (Fin (d + 1) → ℝ) × ℝ => (coeffPoly z.1).eval z.2) := by
    simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.measurable_sum Finset.univ fun k _ =>
      ((measurable_pi_apply k).comp measurable_fst).mul
        (measurable_snd.pow_const (k : ℕ))
  have hprod : StronglyMeasurable
      (fun z : (Fin (d + 1) → ℝ) × ℝ =>
        (coeffPoly z.1).eval z.2 * (coeffPoly z.1).eval z.2) :=
    (heval.mul heval).stronglyMeasurable
  exact (hprod.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) (1 / 2)))).measurable

theorem n17_proof : N17 := by
  intro t
  have hrisk : Measurable
      (fun z : (Fin (t ^ 4) → ℝ) × (Fin (t ^ 4) → ℝ) =>
        regionInt (olsPoly (t ^ 3) z.1 z.2) (olsPoly (t ^ 3) z.1 z.2)) :=
    (measurable_regionInt_coeffPoly (t ^ 3)).comp
      (measurable_olsCoef_vand (t ^ 4) (t ^ 3))
  exact ((measurableSet_designSet (t ^ 4)).preimage measurable_fst).inter
    (measurableSet_lt measurable_const hrisk)

end

end AronowAudit.P001.Wave1.SieveRate
