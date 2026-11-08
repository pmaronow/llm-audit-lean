import AronowAudit.P045.Wave1.MissingTiesBiasBlueprint

/-! Bridge the generic Option-valued deletion experiment to `deletionBias` (node N5).
The three node premises remain explicit; this file needs no node proof as an input. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.MissingTiesBias

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- Both generic ratios exist, and their expected contrast is the specialized one. -/
theorem n5_proof : N5 := by
  classical
  intro hN1 h01 h00 d hd
  have hmasks : (networkEdges printedNetwork).powersetCard d = deletionMasks d := rfl
  have hcells : ∀ R ∈ deletionMasks d, ∀ t : Fin 10,
      (univ.filter (fun i => deletedAdj R t i = true)).Nonempty ∧
      (univ \ insert t (univ.filter (fun i => deletedAdj R t i = true))).Nonempty := by
    intro R hR t
    exact (deletion_domain_certificate ⟨d, by omega⟩ R hR).2 t
  have heffect : effect yT28 .d01 .d00 = (23/80 : ℝ) := by
    calc
      _ = mean (fun i : Fin 10 => biasBaseline i / 4) := by
        rw [effect, ← mean_sub]
        congr 1
        funext i
        simp only [yT28]
        ring
      _ = mean biasBaseline / 4 := by
        simp only [mean, ← Finset.sum_div]
        ring
      _ = 23/80 := zero_deletion_hajek_counterexample.2.1
  constructor
  · intro R hR z hz
    have hRm : R ∈ deletionMasks d := by
      simpa only [hmasks] using hR
    obtain ⟨t, rfl⟩ := hN1.2 z hz
    have hc := hcells R hRm t
    change
      (hajekObserved (crMass 10 1) (exposure (deleteNetwork printedNetwork R))
        obsT28 .d01 (unitAssignment t)).isSome ∧
      (hajekObserved (crMass 10 1) (exposure (deleteNetwork printedNetwork R))
        obsT28 .d00 (unitAssignment t)).isSome
    rw [h01 R t hc.1, h00 R t hc.2]
    simp
  · have hmean :
        randomDeletionMean (crMass 10 1) printedNetwork yT28 .d01 .d00 d =
          average (deletionMasks d) (fun R => mean (deletionHajek R)) := by
      unfold randomDeletionMean
      rw [hmasks]
      unfold average
      apply congrArg (fun a : ℝ => a / (deletionMasks d).card)
      apply Finset.sum_congr rfl
      intro R hR
      dsimp only
      rw [hN1.1]
      apply congrArg (mean (I := Fin 10))
      funext t
      have hc := hcells R hR t
      change
        (hajekObserved (crMass 10 1) (exposure (deleteNetwork printedNetwork R))
          obsT28 .d01 (unitAssignment t)).getD 0 -
        (hajekObserved (crMass 10 1) (exposure (deleteNetwork printedNetwork R))
          obsT28 .d00 (unitAssignment t)).getD 0 = deletionHajek R t
      rw [h01 R t hc.1, h00 R t hc.2]
      simp only [Option.getD_some, deletionHajek]
    rw [hmean, heffect]
    rfl

end

end AronowAudit.P045.Wave1.MissingTiesBias
