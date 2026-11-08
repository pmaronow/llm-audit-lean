import SAP.P004b.WH.W1.Leaves
import AronowAudit.P004.Wave1.FiniteConditioning.FC8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W1.P.T25_L1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical
noncomputable section

theorem coefficient_bound (p : ℝ) (hp : 0 < p ∧ p < 1)
    (N : ℕ) (hN : 0 < (N : ℝ)) (a : Bool) :
    |(bit a / ((N : ℝ) * p) - (1 - bit a) / ((N : ℝ) * (1 - p)))| ≤
      max (1 / p) (1 / (1 - p)) / (N : ℝ) := by
  have hp0 : 0 < 1 - p := sub_pos.mpr hp.2
  have hfactor :
      bit a / ((N : ℝ) * p) - (1 - bit a) / ((N : ℝ) * (1 - p)) =
        (1 / (N : ℝ)) * (bit a / p - (1 - bit a) / (1 - p)) := by
    field_simp [hN.ne', hp.1.ne', hp0.ne'] <;> ring
  have hbase : |bit a / p - (1 - bit a) / (1 - p)| ≤ max (1 / p) (1 / (1 - p)) := by
    cases a with
    | false =>
      have h := le_max_right (1 / p) (1 / (1 - p))
      change |bit false / p - (1 - bit false) / (1 - p)| ≤ _
      simp only [bit, Bool.false_eq_true, ite_false, zero_div, sub_zero]
      rw [zero_sub, abs_neg, abs_of_pos (one_div_pos.mpr hp0)]
      exact h
    | true =>
      have h := le_max_left (1 / p) (1 / (1 - p))
      change |bit true / p - (1 - bit true) / (1 - p)| ≤ _
      simp only [bit, ite_true, sub_self, zero_div, sub_zero]
      rw [abs_of_pos (one_div_pos.mpr hp.1)]
      exact h
  rw [hfactor, abs_mul, abs_of_pos (one_div_pos.mpr hN)]
  calc
    (1 / (N : ℝ)) * |bit a / p - (1 - bit a) / (1 - p)| ≤
        (1 / (N : ℝ)) * max (1 / p) (1 / (1 - p)) :=
      mul_le_mul_of_nonneg_left hbase (one_div_pos.mpr hN).le
    _ = max (1 / p) (1 / (1 - p)) / (N : ℝ) := by ring

end
end SAP.P004b.WH.W1.P.T25_L1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical

theorem SAP.P004b.WH.W1.T25_L1_proof : SAP.P004b.WH.W1.T25_L1 := by
  intro p μ1 μ0 D R hp hdiag hned
  rcases hned with ⟨ψ, g, G, hψ, hanti, hlim, hexp, hg, hNED⟩
  let C : ℝ := max (1 / p) (1 / (1 - p))
  have hp0 : 0 < 1 - p := sub_pos.mpr hp.2
  have hC : 0 < C := by
    dsimp [C]
    exact (one_div_pos.mpr hp.1).trans_le (le_max_left _ _)
  let α : ∀ N, Bool → ℝ := fun N a =>
    bit a / ((N : ℝ) * p) - (1 - bit a) / ((N : ℝ) * (1 - p))
  let β : ∀ N, Fin N → Bool → ℝ := fun N i a =>
    (μ1 - μ0) / (N : ℝ) -
      (bit a * μ1 / ((N : ℝ) * p) - (1 - bit a) * μ0 / ((N : ℝ) * (1 - p))) -
      nodeEffect (fun _ : Fin N => p) (R N) i / (N : ℝ)
  refine ⟨ψ, (fun N i => C * g N i / (N : ℝ)), C * G, hψ, hanti, hlim, hexp, ?_, ?_⟩
  · intro N i
    have hNnat : 0 < N := Nat.zero_lt_of_lt i.isLt
    have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr hNnat
    have hNge : 1 ≤ (N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNnat))
    constructor
    · exact div_pos (mul_pos hC (hg N i).1) hN
    · calc
        C * g N i / (N : ℝ) ≤ C * g N i :=
          div_le_self (mul_nonneg hC.le (hg N i).1.le) hNge
        _ ≤ C * G := mul_le_mul_of_nonneg_left (hg N i).2 hC.le
  · intro N i s hs
    have hNnat : 0 < N := Nat.zero_lt_of_lt i.isLt
    have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr hNnat
    have hNge : 1 ≤ (N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNnat))
    have hself : i ∈ AronowAudit.P004.ball (D N) i s := by
      simp only [AronowAudit.P004.ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hdiag N i]
      exact hs
    have hscore : expandedCenteredSummand p (R N) μ1 μ0 i =
        fun z => α N (z i) * R N i z + β N i (z i) := by
      funext z
      dsimp [expandedCenteredSummand, α, β]
      ring
    have hcoef : ∀ a, |α N a| ≤ C / (N : ℝ) := by
      intro a
      exact SAP.P004b.WH.W1.P.T25_L1.coefficient_bound p hp N hN a
    have hproj :=
      AronowAudit.P004.Wave1.FiniteConditioning.fc8_proof
        (fun _ : Fin N => p) (fun _ => hp) (AronowAudit.P004.ball (D N) i s) i hself
        (R N i) (α N) (β N i) (C / (N : ℝ)) hcoef
    change l2Norm (fun _ : Fin N => p)
      (fun z => expandedCenteredSummand p (R N) μ1 μ0 i z -
        conditionOn (fun _ : Fin N => p) (AronowAudit.P004.ball (D N) i s)
          (expandedCenteredSummand p (R N) μ1 μ0 i) z) ≤
      (C * g N i / (N : ℝ)) * ψ s
    rw [hscore]
    calc
      _ ≤ (C / (N : ℝ)) *
          l2Norm (fun _ : Fin N => p) (fun z => R N i z -
            conditionOn (fun _ : Fin N => p) (AronowAudit.P004.ball (D N) i s)
              (R N i) z) := hproj
      _ ≤ (C / (N : ℝ)) * (g N i * ψ s) :=
        mul_le_mul_of_nonneg_left (hNED N i s hs) (div_nonneg hC.le hN.le)
      _ = (C * g N i / (N : ℝ)) * ψ s := by ring

