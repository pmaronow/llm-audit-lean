import AronowAudit.P004.Wave1.PairedWitnessBlueprint

/-! # Refutation of the printed IPW bound and coverage assertion (P004-T35)

Supplement A Proposition 4 asserts, for every spatial population sequence and logistic
design satisfying its hypotheses, the unsigned printed second-moment bound under the
literal printed homophily antecedent, together with two literal Hájek-numerator coverage
clauses.

The target negates the full universal closure, with the `Space` binder and its two instance
binders inside the negation. The universe of `Space` is fixed to `0` (`Type`): refuting one
universe instance suffices to refute a universe-polymorphic assertion, and the Euclidean
witness lies in `Type`.

The paired spatial blocks, with `d = 0` and `h = 10`, satisfy every outer hypothesis.
Printed homophily is zero for every `N`, so the first conjunct gives an eventual upper
bound. At every positive even `N`, however, the true variance is `2/N` while the printed
bound is `1/N`. A cofinal set of even `N` contradicts the eventual bound. The coverage
conjuncts are not needed.
-/

namespace AronowAudit.P004.Wave1.IpwBoundCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.PairedWitness
open scoped BigOperators

/-- Negation of the full universal closure (universe `0`) of the printed
IPW second-moment bound and coverage assertion (P004-T35). -/
def Target : Prop :=
  ¬ (∀ {Space : ℕ → Type} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
      {k : ℕ} (P : PopulationSequence Space)
      (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
      (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ)
      (_hd : 0 ≤ d) (_hh : 0 ≤ h) (_hP : SpatialLocalConditions P)
      (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
      (_hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
      (_hlog : LogisticConditions O θ₀ Θ θhat)
      (_hoverlap : Overlap (fun N => propensities (O N) θ₀)),
      let p := fun N => propensities (O N) θ₀
      let R := circleSequence P d
      let B := spatialNeighborhoods P h
      let g := fun N => printedFits (p N) (R N) (O N)
      ((∀ N, 0 ≤ printedHomophilyQ (p N) (R N) (B N) (g N)) →
        ∀ᶠ N in atTop, variance (p N) (augmented (p N) (R N) (g N)) ≤
          printedSecondMomentBound (p N) (R N) (B N) (g N)) ∧
      (Nondegenerate (fun N => variance (p N) (augmented (p N) (R N) (g N))) →
        ∀ α : ℝ, 0 < α → α < 1/2 →
        PrintedCoverage (fun N => prob (p N) (fun z =>
          let phat := propensities (O N) (θhat N z)
          let ghat := fun i a => dot (O N i) (fittedBeta phat (R N) (O N) a z)
          normalQuantile (α/2) ≤ |(hajek (R N) z-ame (p N) (R N))/
            Real.sqrt (printedSAH phat (R N) (B N) ghat z)| ∧
          |(hajek (R N) z-ame (p N) (R N))/Real.sqrt (printedSAH phat (R N) (B N) ghat z)| ≤
            normalQuantile (1-α/2))) α ∧
        ((∀ N, 0 ≤ printedHomophilyQ (p N) (R N) (B N) (g N)) →
          PrintedCoverage (fun N => prob (p N) (fun z =>
            let phat := propensities (O N) (θhat N z)
            let ghat := fun i a => dot (O N i) (fittedBeta phat (R N) (O N) a z)
            let V := (sandwich z (weightedEpsilon phat (R N) ghat z)
              (uniformDistanceKernel (nodeSeparation (P N)) h)) 1 1
            normalQuantile (α/2) ≤ |(hajek (R N) z-ame (p N) (R N))/Real.sqrt V| ∧
              |(hajek (R N) z-ame (p N) (R N))/Real.sqrt V| ≤ normalQuantile (1-α/2))) α)))

/-- The component bounds imply the result. Instantiate the assumed universal assertion at the paired
witness, feed it the all-`N` zero printed homophily, and contradict its eventual bound at a
positive even `N`: `2/N ≤ 1/N` is false. -/
theorem assemble (l3 : LinePopulation.N3) (l4 : LinePopulation.N4) (l5 : LinePopulation.N5)
    (l6 : LinePopulation.N6) (l7 : LinePopulation.N7)
    (hPW1 : PW1) (hPW2 : PW2) (hPW3 : PW3) (hPW4 : PW4) (hPW5 : PW5) (hPW6 : PW6)
    (hPW7 : PW7) (hPW8 : PW8) (hPW9 : PW9) (hPW10 : PW10) (hPW11 : PW11) : Target := by
  intro H
  obtain ⟨hP, hWD, hloc, hlog, hov⟩ := guards l3 l4 l5 l6 l7 hPW1 hPW2 hPW4 hPW5 hPW6
  obtain ⟨hQ, hval⟩ := mismatch l3 hPW3 hPW7 hPW8 hPW9 hPW10 hPW11
  have h1 := (@H (fun _ => EuclideanSpace ℝ (Fin 2)) _ _ 1 pairedPop pairO pairTheta
    pairThetaSet pairThetaHat 0 10 le_rfl (by norm_num) hP hWD hloc hlog hov).1 hQ
  obtain ⟨N, hE, hN, hle⟩ := exists_even_pos_of_eventually h1
  obtain ⟨hv, hb, -⟩ := hval N hE hN
  rw [hv, hb] at hle
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff_of_pos_right hN'] at hle
  norm_num at hle

end
end AronowAudit.P004.Wave1.IpwBoundCoverage
