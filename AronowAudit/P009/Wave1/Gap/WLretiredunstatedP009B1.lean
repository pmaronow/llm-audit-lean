import AronowAudit.P009.Wave1.Gap.GLP0092B4

/-!
P009-T51: existential asymptotic sharpness with unchanged assignment laws,
bounded outcomes, degree bounds, restricted interference, and a centered
three-point limit.
-/

namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Proposition 11, in the existential form of Supplement A, pp. 36–38. -/
theorem chebyshev_asymptotic_sharpness
    (S : Study) (k α x : ℝ) (hk : 0 < k)
    (hA : ∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
      marginal (S.experiment t) i true ≤ 1 - k⁻¹)
    (hBER : ∀ t, Bernoulli (S.experiment t))
    (hα : 0 < α ∧ α < 1) (hx : 0 ≤ x ∧ x < 1) :
    ∃ y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ,
      let S' : Study :=
        {S with experiment := fun t => {S.experiment t with outcome := y t}}
      (∃ K q s, RegularSequence S' K q s) ∧ Restricted S' ∧
      BigO (fun t => dAvg (S'.experiment t))
        (fun t => Real.rpow (size S' t) x) ∧
      (x = 0 → BigO (fun t => dMax (S'.experiment t))
        (fun t => Real.sqrt (size S' t))) ∧
      InDistribution S'
        (fun t z => Real.sqrt (size S' t) /
          Real.sqrt (dAvg (S'.experiment t)) *
          (ht (S'.experiment t) z -
            mean (S'.experiment t).design (ht (S'.experiment t))))
        (sharpCDF α) := by
  exact chebyshev_asymptotic_sharpness_proof S k α x hk hA hBER hα hx

end
end AronowAudit.P009.Wave1
