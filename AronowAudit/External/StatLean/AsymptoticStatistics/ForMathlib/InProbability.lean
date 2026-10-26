/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.Prohorov

/-!
# Convergence and boundedness in probability (varying base)

For statistics `X k : Ω k → G` on per-index probability spaces `(Ω k, P k)`,
laws are compared through the pushforwards `(P k).map (X k)`.
Mathlib's `MeasureTheory.TendstoInMeasure` fixes a single base measure on a
single space; varying-base formulations allow both to depend on `k`.

Convergence to zero in probability is denoted `→ₚ 0`. Boundedness in
probability, `O_P(1)`, means uniform tightness of the family of laws.
-/

open MeasureTheory Filter Topology Set

namespace AsymptoticStatistics

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]


end AsymptoticStatistics
