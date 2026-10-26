import AronowAudit.P001.Wave1.PolynomialBlpBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Uniform approximation and risk minimality control the entire degree tail. -/
theorem n5_proof : N5.{u} := by
  intro h1 h2 Ω _ μ _ X Y a b m hX hY hsupp hm hc p hpdeg hpmin ε hε
  have hab : a ≤ b := by
    obtain ⟨ω, hω⟩ := hsupp.exists
    exact hω.1.trans hω.2
  obtain ⟨hm2, hq2⟩ := h1 μ X Y a b m hX hsupp hm hc
  have hδ : 0 < Real.sqrt ε / 2 := div_pos (Real.sqrt_pos.2 hε) (by norm_num)
  obtain ⟨q, hq⟩ := weierstrass_approximation a b hab m hc (Real.sqrt ε / 2) hδ
  have hbound : ∀ᵐ ω ∂μ, (m (X ω) - q.eval (X ω)) ^ 2 ≤ ε / 4 := by
    filter_upwards [hsupp] with ω hω
    have herr : |m (X ω) - q.eval (X ω)| < Real.sqrt ε / 2 := hq (X ω) hω
    have hsqrt : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
    have habs : (m (X ω) - q.eval (X ω)) ^ 2 =
        |m (X ω) - q.eval (X ω)| ^ 2 := (sq_abs _).symm
    have hprod : 0 ≤ (Real.sqrt ε / 2 - |m (X ω) - q.eval (X ω)|) *
        (Real.sqrt ε / 2 + |m (X ω) - q.eval (X ω)|) :=
      mul_nonneg (sub_nonneg.mpr herr.le) (add_nonneg hδ.le (abs_nonneg _))
    nlinarith
  have hqerr : mean μ (fun ω => (m (X ω) - q.eval (X ω)) ^ 2) ≤ ε / 4 := by
    unfold mean
    calc
      (∫ ω, (m (X ω) - q.eval (X ω)) ^ 2 ∂μ) ≤ ∫ _ : Ω, ε / 4 ∂μ :=
        integral_mono_ae (hm2.sub (hq2 q)).integrable_sq (integrable_const _) hbound
      _ = ε / 4 := by simp
  refine ⟨q.natDegree, ?_⟩
  intro J' hJ'
  have hmin := hpmin J' q hJ'
  have hdecompP := h2 μ X Y m hX hY hm hm2 (fun x => (p J').eval x)
    (p J').continuous.measurable (hq2 (p J'))
  have hdecompQ := h2 μ X Y m hX hY hm hm2 (fun x => q.eval x)
    q.continuous.measurable (hq2 q)
  rw [hdecompP, hdecompQ] at hmin
  linarith

end

end AronowAudit.P001.Wave1.PolynomialBlp
