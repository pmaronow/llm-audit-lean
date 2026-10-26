import AronowAudit.P004.Wave1.NedFarCovarianceBlueprint
import AronowAudit.P004.Wave1.FiniteConditioning.FC8

/-! E1: magnitude and conditional-projection bounds for the scaled residual score. -/

namespace AronowAudit.P004.Wave1.NedFarCovariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem e1_proof : E1 := by
  classical
  intro N p R B M μ1 μ0 hN hp hR hμ1 hμ0
  let q : ℝ := min p (1 - p)
  have hq : 0 < q := lt_min hp.1 (sub_pos.mpr hp.2)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1p : 0 < 1 - p := sub_pos.mpr hp.2
  let α : Bool → ℝ := fun a => (if a then 1 / p else -1 / (1 - p)) / (N : ℝ)
  let μ : Bool → ℝ := fun a => if a then μ1 else μ0
  let β : Bool → ℝ := fun a => -(α a * μ a)
  have hμ : ∀ a, |μ a| ≤ M := by
    intro a
    cases a
    · exact hμ0
    · exact hμ1
  have harm : ∀ a : Bool, |if a then 1 / p else -1 / (1 - p)| ≤ 1 / q := by
    intro a
    cases a
    · change |-1 / (1 - p)| ≤ 1 / q
      rw [abs_div, abs_neg, abs_one, abs_of_pos h1p]
      exact one_div_le_one_div_of_le hq (min_le_right p (1 - p))
    · change |1 / p| ≤ 1 / q
      rw [abs_div, abs_one, abs_of_pos hp.1]
      exact one_div_le_one_div_of_le hq (min_le_left p (1 - p))
  have hα : ∀ a, |α a| ≤ 1 / (q * (N : ℝ)) := by
    intro a
    calc
      |α a| = |if a then 1 / p else -1 / (1 - p)| / (N : ℝ) := by
        simp only [α, abs_div, abs_of_pos hN']
      _ ≤ (1 / q) / (N : ℝ) := div_le_div_of_nonneg_right (harm a) hN'.le
      _ = 1 / (q * (N : ℝ)) := by rw [div_div]
  have haffine : ∀ i : Fin N,
      nedEpsilon p R μ1 μ0 i = (fun z => α (z i) * R i z + β (z i)) := by
    intro i
    funext z
    cases hz : z i <;>
      simp [nedEpsilon, residualContrast, bit, hz, α, β, μ] <;> ring
  constructor
  · intro i z
    have hres : |R i z - μ (z i)| ≤ B + M := by
      calc
        |R i z - μ (z i)| = |R i z + -μ (z i)| := by rw [sub_eq_add_neg]
        _ ≤ |R i z| + |-μ (z i)| := abs_add_le _ _
        _ ≤ B + M := by simpa only [abs_neg] using add_le_add (hR i z) (hμ (z i))
    calc
      |nedEpsilon p R μ1 μ0 i z| = |α (z i) * (R i z - μ (z i))| := by
        rw [haffine i]
        congr 1
        dsimp only [β]
        ring
      _ = |α (z i)| * |R i z - μ (z i)| := abs_mul _ _
      _ ≤ (1 / (q * (N : ℝ))) * (B + M) :=
        mul_le_mul (hα (z i)) hres (abs_nonneg _) (by positivity)
      _ = (B + M) / (min p (1 - p) * N) := by dsimp only [q]; ring
  · intro i J hiJ
    have hproj : l2Norm (fun _ => p) (fun z => nedEpsilon p R μ1 μ0 i z -
        conditionOn (fun _ => p) J (nedEpsilon p R μ1 μ0 i) z) ≤
        (1 / (q * (N : ℝ))) *
          l2Norm (fun _ => p) (fun z => R i z - conditionOn (fun _ => p) J (R i) z) := by
      simpa only [haffine i] using
        (FiniteConditioning.fc8_proof (fun _ : Fin N => p) (fun _ => hp)
          J i hiJ (R i) α β (1 / (q * (N : ℝ))) hα)
    calc
      l2Norm (fun _ => p) (fun z => nedEpsilon p R μ1 μ0 i z -
          conditionOn (fun _ => p) J (nedEpsilon p R μ1 μ0 i) z)
          ≤ (1 / (q * (N : ℝ))) *
            l2Norm (fun _ => p) (fun z => R i z - conditionOn (fun _ => p) J (R i) z) := hproj
      _ = l2Norm (fun _ => p) (fun z => R i z - conditionOn (fun _ => p) J (R i) z) /
          (min p (1 - p) * N) := by dsimp only [q]; ring

end
end AronowAudit.P004.Wave1.NedFarCovariance
