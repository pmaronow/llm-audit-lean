/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ComputationalStatistics.Core.EmpiricalMeasure
import AronowAudit.External.StatLean.ComputationalStatistics.ForMathlib.PiMoments
import AronowAudit.External.StatLean.ComputationalStatistics.Resampling.CategoricalCounts

/-!
# Finite-sample bootstrap identities

A bootstrap sample consists of `n` i.i.d. draws from the empirical measure
`𝔽ₙ` (ECS ch. 4). The theorem `resampleLaw_eq_map_indexResampling` identifies
resampling values with resampling indices uniformly.

Everything here is *conditional on the data*: `x` is a parameter and the only
randomness is the resampling law `Measure.pi (fun _ : Fin n => empiricalMeasure x)`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), ch. 4 pp. 83–86: the ECDF as population, the
resampling vector and its multinomial law (p. 84), bias correction
(§4.1, eqs. (4.1)–(4.5)), variance estimation (§4.2, eqs. (4.6)–(4.7)).
(`ECS §4.1–4.2`.)

**Bibliographic comments.** B. Efron, "Bootstrap methods: another look at the
jackknife," *Ann. Statist.* **7** (1979), 1–26 (the resampling vector is his
§2); Efron–Tibshirani, *An Introduction to the Bootstrap*, Chapman & Hall,
1993, ch. 10 (bias correction).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {n : ℕ} {x : Fin n → 𝓧} {g : 𝓧 → ℝ}




section RealData

variable {y : Fin n → ℝ}


end RealData

/-- **Value resampling is uniform index resampling** (ECS §2.5): the bootstrap
resampling law is the pushforward of uniform i.i.d. index draws through the
data. -/
theorem resampleLaw_eq_map_indexResampling [NeZero n] :
    (Measure.pi fun _ : Fin n => empiricalMeasure x)
      = (Measure.pi fun _ : Fin n => categorical fun _ : Fin n => (n : ℝ)⁻¹).map
          (fun a => x ∘ a) := by
  have hfac : (fun _ : Fin n => empiricalMeasure x)
      = fun _ : Fin n => (categorical fun _ : Fin n => (n : ℝ)⁻¹).map x :=
    funext fun _ => empiricalMeasure_eq_map_categorical
  rw [hfac, ← Measure.pi_map_pi (f := fun _ : Fin n => x)
    fun _ => (Measurable.of_discrete (f := x)).aemeasurable]
  rfl


end StatLean.ComputationalStatistics

