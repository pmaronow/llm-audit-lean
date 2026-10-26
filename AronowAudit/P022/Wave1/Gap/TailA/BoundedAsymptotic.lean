import AronowAudit.P022.Wave1.Gap.GP022B1b

namespace AronowAudit.P022.Wave1.TailA

open Filter MeasureTheory in
open scoped BigOperators ENNReal NNReal Topology in
/-- P022-T3: condition 1 and bounded outcomes alone give the explicit limsup
bound in the corrected proof of Proposition 2. No weak limit or atom-value
hypotheses occur. -/
theorem bounded_direct_asymptotic_final :
    (∀ (S : ExperimentSequence)
      (θ ρ C : ℝ)
      (hθ : 0 < θ ∧ θ ≤ 1)
      (hρ : 0 < ρ ∧ ρ < 1)
      (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N) atTop (𝓝 (θ * ρ)))
      (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N) atTop (𝓝 θ))
      (hC : 0 ≤ C)
      (hy : ∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C),
      ∀ ε c, 0 < ε → 0 < c → c < min (θ * ρ) (θ * (1 - ρ)) → ∀ B,
      scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
        |estimatedVariance (S.design q) (rowOutcomes S true q)
          (rowOutcomes S false q) B π - populationBound (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) B|) ≤
        ENNReal.ofReal (16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * ε ^ 2))) :=
  AronowAudit.P022.Wave1.GP022B1b_asymptotic_rate

end AronowAudit.P022.Wave1.TailA
