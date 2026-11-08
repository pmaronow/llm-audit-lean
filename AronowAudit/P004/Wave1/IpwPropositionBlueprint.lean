import AronowAudit.P004.Wave1.PairedWitnessBlueprint

/-! # Blueprint: refutation of `AronowAudit.P004.printed_ipw_proposition` (P004-T35)

Dossier group P004, record 4. The frozen contract (`AronowAudit/P004/P004_Spatial.lean`,
a `sorry` draft) is the conjunction of the printed linearization, the printed variance
equation (37)-(40) (unsigned pair term, literal `i` fit in the `j` residual), and the
standardized normal limit. Resolution: `refute` (map-P004; referee 1 accept, referee 2
accept with the full-universal-closure fix, applied here).

As for the sibling record `IpwBoundCoverage`, the target negates the full universal closure
with the `Space` binder and its instance binders inside the negation, at universe `0`.

Paper proof (map-P004 REPORT, record 4): the same paired witness satisfies every outer guard;
at every positive even `N` the true variance is `2/N` while `printedVarianceFormula` is `1/N`,
so the asserted eventual equality fails on a cofinal set. The linearization and CLT conjuncts
are never used (in particular the unproved draft `ipw_linearization_counterexample` is not
used).

The final declaration (writer) is `AronowAudit.P004.Wave1.printed_ipw_proposition_refuted`
in `AronowAudit/P004/Wave1/IpwProposition.lean`. All nodes are shared with record 3
(`LinePopulation.N3`-`N7`, `PairedWitness.PW1`-`PW11`); the only node specific to this record
is `PW11`.
-/

namespace AronowAudit.P004.Wave1.IpwProposition

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.PairedWitness
open scoped BigOperators

/-- Frozen target: the negation of the full universal closure (universe `0`) of the exact
recorded contract `AronowAudit.P004.printed_ipw_proposition`. -/
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
      LittleOp p (fun N z => augmented (p N) (R N) (g N) z-fittedIPW (R N) (O N) (θhat N) z)
        (fun N => (Real.sqrt N)⁻¹) ∧
      (∀ᶠ N in atTop, variance (p N) (augmented (p N) (R N) (g N)) =
        printedVarianceFormula (p N) (R N) (B N) (g N)) ∧
      (Nondegenerate (fun N => variance (p N) (augmented (p N) (R N) (g N))) →
        NormalLimit p (fun N z => (fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)) /
          Real.sqrt (variance (p N) (augmented (p N) (R N) (g N))))))

/-- Fidelity check: `Target` is literally the negation of the frozen contract at universe 0,
with every binder (including `Space` and its instances) inside the negation. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P004.printed_ipw_proposition.{0}) := Iff.rfl

/-- The nodes suffice (proved): instantiate at the paired witness and contradict the eventual
variance equality at a positive even `N` (`2/N = 1/N` is false). -/
theorem assemble (l3 : LinePopulation.N3) (l4 : LinePopulation.N4) (l5 : LinePopulation.N5)
    (l6 : LinePopulation.N6) (l7 : LinePopulation.N7)
    (hPW1 : PW1) (hPW2 : PW2) (hPW3 : PW3) (hPW4 : PW4) (hPW5 : PW5) (hPW6 : PW6)
    (hPW7 : PW7) (hPW8 : PW8) (hPW9 : PW9) (hPW10 : PW10) (hPW11 : PW11) : Target := by
  intro H
  obtain ⟨hP, hWD, hloc, hlog, hov⟩ := guards l3 l4 l5 l6 l7 hPW1 hPW2 hPW4 hPW5 hPW6
  obtain ⟨-, hval⟩ := mismatch l3 hPW3 hPW7 hPW8 hPW9 hPW10 hPW11
  have h2 := (@H (fun _ => EuclideanSpace ℝ (Fin 2)) _ _ 1 pairedPop pairO pairTheta
    pairThetaSet pairThetaHat 0 10 le_rfl (by norm_num) hP hWD hloc hlog hov).2.1
  obtain ⟨N, hE, hN, heq⟩ := exists_even_pos_of_eventually h2
  obtain ⟨hv, -, hf⟩ := hval N hE hN
  rw [hv, hf] at heq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_left_inj' hN'.ne'] at heq
  norm_num at heq

end
end AronowAudit.P004.Wave1.IpwProposition
