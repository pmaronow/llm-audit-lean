import SAP.P061b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b.WH.W1.P.T19_L2

open Bridge
open scoped BigOperators Classical

theorem single_term {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) (hp : ∀ i, 0 < exposureProbability D g i d)
    (hn : SupportStable D g y) (i : Fin N) :
    HasFirstMoment D (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
        exposureProbability D g i d) ∧
      designMean D (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
        exposureProbability D g i d) = exposureMean D g y i d ^ 2 / 2 := by
  let A := Bridge.toAudit D
  let J : Ω → Prop := fun z => g i z = d
  let c : ℝ := AronowAudit.P061.epo A g y i d ^ 2 / 2 /
    AronowAudit.P061.pi A g i d
  have hpA : ∀ k, 0 < AronowAudit.P061.pi A g k d := by
    intro k
    simpa [A, Bridge.toAudit, AronowAudit.P061.pi,
      AronowAudit.P061.probability, exposureProbability, eventProbability] using hp k
  have hnA : AronowAudit.P061.NURVA A g y := by
    change ∀ k z w, 0 < D.p z → 0 < D.p w → g k z = g k w → y k z = y k w
    exact hn
  have he : ∀ z, AronowAudit.P061.Support A z →
      (if g i z = d then y i z ^ 2 / 2 else 0) /
          exposureProbability D g i d =
        if J z then c else 0 := by
    intro z hz
    by_cases hi : g i z = d
    · have hi' := (AronowAudit.P061.nurva_epo A g y hnA i d (hpA i) z hz hi).symm
      simp [J, c, hi, hi', exposureProbability, A, Bridge.toAudit,
        AronowAudit.P061.pi, AronowAudit.P061.probability, eventProbability]
    · simp [J, c, hi]
  have hInt : AronowAudit.P061.Integrable A
      (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
        exposureProbability D g i d) := by
    exact (AronowAudit.P061.integrable_support_congr A _ _ he).2
      (AronowAudit.P061.integrable_event A J c)
  have hExp : AronowAudit.P061.expectation A
      (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
        exposureProbability D g i d) =
      AronowAudit.P061.epo A g y i d ^ 2 / 2 := by
    rw [AronowAudit.P061.expectation_support_congr A _ _ he]
    change AronowAudit.P061.expectation A (fun z =>
      if J z then AronowAudit.P061.epo A g y i d ^ 2 / 2 /
        AronowAudit.P061.pi A g i d else 0) = _
    rw [AronowAudit.P061.expectation_event]
    change (AronowAudit.P061.epo A g y i d ^ 2 / 2 /
      AronowAudit.P061.pi A g i d) * AronowAudit.P061.probability A J = _
    rw [show AronowAudit.P061.probability A J = AronowAudit.P061.pi A g i d by rfl]
    exact div_mul_cancel₀ _ (hpA i).ne'
  constructor
  · exact (Bridge.moment_correspondence D _).2 hInt
  · rw [Bridge.mean_correspondence D]
    rw [hExp]
    rw [Bridge.exposure_correspondence]

end SAP.P061b.WH.W1.P.T19_L2

theorem SAP.P061b.WH.W1.T19_L2_proof : SAP.P061b.WH.W1.T19_L2 := by
  intro Ω N D g y d hp hn i j
  have hi := SAP.P061b.WH.W1.P.T19_L2.single_term D g y d hp hn i
  have hj := SAP.P061b.WH.W1.P.T19_L2.single_term D g y d hp hn j
  change HasFirstMoment D (fun z =>
      (if g i z = d then y i z ^ 2 / 2 else 0) / exposureProbability D g i d +
      (if g j z = d then y j z ^ 2 / 2 else 0) / exposureProbability D g j d) ∧
    designMean D (fun z =>
      (if g i z = d then y i z ^ 2 / 2 else 0) / exposureProbability D g i d +
      (if g j z = d then y j z ^ 2 / 2 else 0) / exposureProbability D g j d) =
      exposureMean D g y i d ^ 2 / 2 + exposureMean D g y j d ^ 2 / 2
  let A := Bridge.toAudit D
  have hfi : AronowAudit.P061.Integrable A
      (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
        exposureProbability D g i d) := (Bridge.moment_correspondence D _).mp hi.1
  have hfj : AronowAudit.P061.Integrable A
      (fun z => (if g j z = d then y j z ^ 2 / 2 else 0) /
        exposureProbability D g j d) := (Bridge.moment_correspondence D _).mp hj.1
  have hmi : AronowAudit.P061.expectation A
      (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
        exposureProbability D g i d) = exposureMean D g y i d ^ 2 / 2 := by
    have h := hi.2
    change designMean D _ = _ at h
    rw [Bridge.mean_correspondence D] at h
    exact h
  have hmj : AronowAudit.P061.expectation A
      (fun z => (if g j z = d then y j z ^ 2 / 2 else 0) /
        exposureProbability D g j d) = exposureMean D g y j d ^ 2 / 2 := by
    have h := hj.2
    change designMean D _ = _ at h
    rw [Bridge.mean_correspondence D] at h
    exact h
  constructor
  · apply (Bridge.moment_correspondence D _).2
    exact AronowAudit.P061.integrable_add A hfi hfj
  · rw [Bridge.mean_correspondence D]
    exact (AronowAudit.P061.expectation_add A hfi hfj).trans
      (congrArg₂ (· + ·) hmi hmj)
