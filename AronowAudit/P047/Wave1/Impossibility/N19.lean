import AronowAudit.P047.Wave1.Impossibility.N16
import Mathlib.Order.LiminfLimsup

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n19_proof : N19 := by
  intro c q hc hq hfinite α _hα hα2 hcoverage
  have hexact (n : ℕ) : 2 * c n - 1 ≤ q n := by
    apply remove_reciprocal_error (2 * c n - 1) (q n)
      (32 + (n : ℝ) * (n - 1))
    intro M
    have hM := hfinite n M
    have heq : (32 + (n : ℝ) * (n - 1)) / ((M : ℝ) + 1) =
        32 / ((M : ℝ) + 1) + (n : ℝ) * (n - 1) / ((M : ℝ) + 1) := by
      rw [add_div]
    rw [heq]
    linarith
  have hclower : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) c :=
    Filter.isBoundedUnder_of ⟨0, fun n => (hc n).1⟩
  have hqupper : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) q :=
    Filter.isBoundedUnder_of ⟨1, fun n => (hq n).2⟩
  constructor
  · by_contra! hbad
    let ε : ℝ := (1 - 2 * α - Filter.liminf q atTop) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hlt : 1 - α - ε < Filter.liminf c atTop := by linarith
    have htail : ∀ᶠ n : ℕ in atTop, 1 - α - ε < c n :=
      Filter.eventually_lt_of_lt_liminf hlt hclower
    have hqtail : ∀ᶠ n : ℕ in atTop, 1 - 2 * α - 2 * ε ≤ q n := by
      filter_upwards [htail] with n hn
      linarith [hexact n]
    have hlim : 1 - 2 * α - 2 * ε ≤ Filter.liminf q atTop :=
      Filter.le_liminf_of_le hqupper.isCoboundedUnder_ge hqtail
    dsimp [ε] at hlim
    linarith
  · linarith

end

end AronowAudit.P047.Wave1.Impossibility
