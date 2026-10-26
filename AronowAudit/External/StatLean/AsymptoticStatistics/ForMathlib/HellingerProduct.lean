/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.L2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Product-Hellinger inequality for iid products

For two probability measures dominated by a common σ-finite measure with densities
`p, q : Ω → ℝ≥0∞` (typed via `ENNReal` to match `Measure.rnDeriv`), the squared
Hellinger residual

```
‖√p.toReal - √q.toReal‖²_{L²(μ)}
```

and its `n`-fold-product counterpart

```
‖√(∏ⱼ pⱼ).toReal - √(∏ⱼ qⱼ).toReal‖²_{L²(μ^n)}
```

are related by

```
‖√∏p.toReal - √∏q.toReal‖²_{L²(μ^n)} ≤ n · ‖√p.toReal - √q.toReal‖²_{L²(μ)}
```

## Mathematical content

Define the *Hellinger affinity* `A := ∫ √(p · q).toReal dμ`. Then for probability
densities `p, q`:

1. `‖√p.toReal - √q.toReal‖²_{L²(μ)} = ∫ p.toReal + ∫ q.toReal - 2A = 2 - 2A`.
2. The affinity multiplies under iid products:
   `A(μ^n, ν^n, μ_dom^n) = A(μ, ν, μ_dom)^n` (via `lintegral_fintype_prod_eq_prod`
   applied to `∏ⱼ √(pⱼ qⱼ)`).
3. Bernoulli inequality `1 - A^n ≤ n · (1 - A)` for `0 ≤ A ≤ 1` (Cauchy-Schwarz).
4. Combining gives the squared `L²`-form, and `√n` after square-rooting.

The Bernoulli inequality used in this argument is proved below as
`one_sub_pow_le_nsmul_one_sub`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.HellingerProduct

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Pointwise / numerical lemma: Bernoulli `1 - x^n ≤ n(1-x)` for `x ∈ [0,1]`. -/

/-- Bernoulli-style inequality: `1 - x^n ≤ n(1-x)` for `x ∈ [0,1]`.

Proof: induction on `n`. The step uses
`1 - x^{n+1} = (1 - x^n) + x^n · (1 - x) ≤ n(1-x) + 1·(1-x) = (n+1)(1-x)`. -/
lemma one_sub_pow_le_nsmul_one_sub
    {x : ℝ} (hx_nn : 0 ≤ x) (hx_le : x ≤ 1) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx_n_nn : 0 ≤ x ^ n := pow_nonneg hx_nn n
      have hx_n_le : x ^ n ≤ 1 := pow_le_one₀ hx_nn hx_le
      have h_id : 1 - x ^ (n + 1) = (1 - x ^ n) + x ^ n * (1 - x) := by ring
      have h_term2 : x ^ n * (1 - x) ≤ 1 * (1 - x) :=
        mul_le_mul_of_nonneg_right hx_n_le (by linarith)
      have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [h_id, h_cast]
      have h_rhs : ((n : ℝ) + 1) * (1 - x) = (n : ℝ) * (1 - x) + 1 * (1 - x) := by
        ring
      rw [h_rhs]
      linarith

/-! ## Product affinity multiplicativity (toReal form).

For iid product measures with densities `p, q : Ω → ℝ≥0∞`, the Hellinger affinity
factors as a power:

```
∫ Real.sqrt ((∏ⱼ p(X j)).toReal * (∏ⱼ q(X j)).toReal) d(μ^n)
  = (∫ Real.sqrt (p ω . toReal * q ω . toReal) dμ) ^ n
```

(when both `p, q` are finite-valued so `.toReal` commutes with products).

The cleanest framing uses `ℝ≥0∞`-valued integrals of `√(p · q)` via
`ENNReal.toReal` and a finiteness side-condition, relating the `lintegral`
formulation to its `.toReal` form. -/


/-! ## Affinity-route bricks for the iid product Hellinger inequality

The tensorisation inequality
`(eLpNorm (√(∏p) − √(∏q)) 2 (ξ^n)).toReal ≤ √n · (eLpNorm (√p − √q) 2 ξ).toReal`
follows via the **Hellinger affinity** `A := ∫ √p · √q dξ ∈ [0, 1]`, with the canonical
chain
  per-sample residual sq = `2 − 2A`,
  product residual sq    = `2 − 2 Aⁿ`,
  Bernoulli `1 − Aⁿ ≤ n(1 − A)`,
take sqrt.
-/

open AsymptoticStatistics.ForMathlib.RnDerivSqrt


end AsymptoticStatistics.ForMathlib.HellingerProduct
