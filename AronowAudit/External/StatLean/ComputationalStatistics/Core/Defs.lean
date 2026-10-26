/-
Documentation corrected for llm-audit-lean.
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Computational statistics — core data model

The shared substrate for every sampling and resampling algorithm in the area:

* **`empiricalMeasure x`** — the discrete uniform distribution `(1/n)·Σᵢ δ_{xᵢ}`
  carried by a sample `x : Fin n → 𝓧` (ECS ch. 4, p. 83: "the observed sample can
  be considered to be the population");
* **`weightedMeasure w x`** — the weighted particle approximation `Σᵢ wᵢ·δ_{xᵢ}`
  of importance sampling and sequential Monte Carlo;
* **`categorical q`** — the discrete index measure on `Fin m`; for a simplex
  vector `q`, this is the law of a single draw in multinomial resampling;

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.2 (Monte Carlo estimation, eqs. (2.5)–(2.9)), §2.5
(random sampling from data), ch. 4 (the empirical population).

**Proof formalization notes.**

* Weights are **real** (`w : Fin n → ℝ`), converted by `ENNReal.ofReal`; negative
  weights are silently clipped to `0`, and the probability-measure instance in
  `Core/EmpiricalMeasure.lean` carries the simplex hypotheses explicitly.  This
  matches the simplex conventions of `StatLean.Bayesian.multinomialWeight`.
* Edge behaviour: for `n = 0`, `empiricalMeasure` is the zero measure
  (`(0 : ℝ≥0∞)⁻¹ = ∞` collapses against the empty sum); probability statements
  carry `[NeZero n]`.

**Bibliographic comments.** The empirical distribution as a surrogate population
is Efron's bootstrap principle (B. Efron, "Bootstrap methods: another look at the
jackknife," *Ann. Statist.* **7** (1979), 1–26); Monte Carlo estimation of
integrals goes back to Metropolis–Ulam (*J. Amer. Statist. Assoc.* **44** (1949),
335–341).
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **empirical measure** of a sample `x : Fin n → 𝓧`:

`empiricalMeasure x = (1/n) · Σᵢ Measure.dirac (x i)`

(ECS ch. 4, p. 83: the sample viewed as a finite population).  Edge behaviour:
for `n = 0` this is the zero measure; the `IsProbabilityMeasure` instance is
stated under `[NeZero n]` in `Core/EmpiricalMeasure.lean`. -/
noncomputable def empiricalMeasure {n : ℕ} (x : Fin n → 𝓧) : Measure 𝓧 :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)

/-- The **weighted empirical measure** `Σᵢ wᵢ · δ_{xᵢ}` of a weighted sample
(ECS §2.6; the particle approximation of sequential Monte Carlo).  Edge
behaviour: negative weights are clipped to `0` by `ENNReal.ofReal`; the
probability-measure statement carries `0 ≤ wᵢ` and `Σᵢ wᵢ = 1` explicitly. -/
noncomputable def weightedMeasure {n : ℕ} (w : Fin n → ℝ) (x : Fin n → 𝓧) :
    Measure 𝓧 :=
  ∑ i : Fin n, ENNReal.ofReal (w i) • Measure.dirac (x i)

/-- The **categorical measure** on `Fin m` with real weights `q`. Negative
entries are clipped to `0` by `ENNReal.ofReal`, so the total mass is
`ENNReal.ofReal (∑ i, max (q i) 0)`. It is a probability measure exactly when
`∑ i, max (q i) 0 = 1`. A simplex vector is sufficient but not necessary:
off-simplex inputs can also have clipped weights summing to `1`. For simplex
`q`, this is the law of a single particle index in multinomial resampling. -/
noncomputable def categorical {m : ℕ} (q : Fin m → ℝ) : Measure (Fin m) :=
  ∑ i : Fin m, ENNReal.ofReal (q i) • Measure.dirac i


/-- The categorical distribution is the weighted empirical measure of the
identity sample on the index set. -/
theorem categorical_eq_weightedMeasure {m : ℕ} (q : Fin m → ℝ) :
    categorical q = weightedMeasure q id := rfl

end StatLean.ComputationalStatistics
