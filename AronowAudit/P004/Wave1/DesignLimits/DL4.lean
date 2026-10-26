import AronowAudit.P004.Wave1.DesignLimits.DL1

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Sums, fixed scalar multiples, and deterministic null sequences in probability. -/
theorem dl4_proof : DL4 := by
  classical
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · intro U V hU hV ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hupper : Tendsto (fun N => prob (p N) (fun z => ε / 2 < |U N z|) +
        prob (p N) (fun z => ε / 2 < |V N z|)) atTop (nhds 0) := by
      simpa only [zero_add] using (hU (ε / 2) hhalf).add (hV (ε / 2) hhalf)
    have hbound : ∀ N, prob (p N) (fun z => ε < |U N z + V N z|) ≤
        prob (p N) (fun z => ε / 2 < |U N z|) +
          prob (p N) (fun z => ε / 2 < |V N z|) := by
      intro N
      apply prob_le_add_of_imp_finite (p N) (hp N)
      intro z hz
      by_cases hu : ε / 2 < |U N z|
      · exact Or.inl hu
      · right
        by_contra hv
        have hu' : |U N z| ≤ ε / 2 := le_of_not_gt hu
        have hv' : |V N z| ≤ ε / 2 := le_of_not_gt hv
        have habs : |U N z + V N z| ≤ |U N z| + |V N z| := abs_add_le _ _
        linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun N => prob_nonneg_finite (p N) (hp N) _) hbound
  · intro c U hU
    by_cases hc : c = 0
    · subst c
      intro ε hε
      have hzero : (fun N => prob (p N) (fun z => ε < |(0 : ℝ) * U N z|)) =
          (fun _ : ℕ => (0 : ℝ)) := by
        funext N
        simp only [zero_mul, abs_zero, not_lt_of_ge hε.le, if_false, prob, expect_const]
      rw [hzero]
      exact tendsto_const_nhds
    · intro ε hε
      have hcabs : 0 < |c| := abs_pos.mpr hc
      have heq : ∀ N, prob (p N) (fun z => ε < |c * U N z|) =
          prob (p N) (fun z => ε / |c| < |U N z|) := by
        intro N
        congr 1
        funext z
        apply propext
        rw [abs_mul, div_lt_iff₀ hcabs, mul_comm (|U N z|) (|c|)]
      simpa only [heq] using hU (ε / |c|) (div_pos hε hcabs)
  · intro a ha ε hε
    have habs : Tendsto (fun N => |a N|) atTop (nhds 0) := by
      simpa only [abs_zero] using ha.abs
    have hsmall : ∀ᶠ N in atTop, |a N| < ε :=
      habs.eventually (eventually_lt_nhds hε)
    have heq : (fun N => prob (p N) (fun _ => ε < |a N|)) =ᶠ[atTop]
        (fun _ : ℕ => (0 : ℝ)) := by
      filter_upwards [hsmall] with N hN
      simp only [prob, not_lt_of_ge hN.le, if_false, expect_const]
    exact (tendsto_congr' heq).2 tendsto_const_nhds

end
end AronowAudit.P004.Wave1.DesignLimits
