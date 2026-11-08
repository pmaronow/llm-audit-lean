import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T4_L4

open SAP.P019a SAP.P019a.Bridge MeasureTheory
open Classical

theorem event_prob_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S)
    (D : WholeObservation → Prop) [DecidablePred D] :
    G.law.prob (fun ω => D (G.observable ω)) =
      S.law.prob (fun ω => D (S.wholeObservable ω)) := by
  have h := hrep.1 (fun o => if D o then 1 else 0)
  simpa [WholeMeasureLaw.prob, WholeMeasureLaw.mean, FiniteLaw.prob, FiniteLaw.mean] using h

theorem event_prob_zero_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : WholeMeasureLaw Ω) (D : Ω → Prop) [DecidablePred D]
    (hD : ∀ᵐ ω ∂P.measure, ¬ D ω) : P.prob D = 0 := by
  unfold WholeMeasureLaw.prob WholeMeasureLaw.mean
  apply integral_eq_zero_of_ae
  filter_upwards [hD] with ω hω
  simp [hω]

theorem finite_atom_le_prob {E : Type*} [Fintype E]
    (P : FiniteLaw E) (ω : E) (D : E → Prop) [DecidablePred D]
    (h : ∀ x, 0 < P.mass x → x = ω → D x) :
    P.mass ω ≤ P.prob D := by
  have hle := AronowAudit.P019.probability_mono (toLaw P)
    (fun x => x = ω) D (by
      intro x hx hxo
      exact h x hx hxo)
  have hs : P.prob (fun x => x = ω) = P.mass ω := by
    simp [FiniteLaw.prob, FiniteLaw.mean]
  rw [prob_eq] at hle
  rw [hs] at hle
  exact hle

theorem cell_moment_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (z y : Bool) (k : ℕ) :
    G.law.mean
      (fun ω => if G.cell z y ω then (G.V ω : ℝ)^k else 0) =
    S.law.mean
      (fun ω => if S.cell z y ω then (S.V ω : ℝ)^k else 0) := by
  classical
  unfold WholeMeasureStudy.cell Study.cell
  have h := hrep.1 (fun o =>
    @ite ℝ (o.2.2.2.1 = z ∧ o.2.2.1 = y)
      (Classical.propDecidable _) ((o.2.2.2.2 : ℝ)^k) 0)
  simp only [WholeMeasureStudy.observable, Study.wholeObservable] at h
  convert h using 1
  all_goals rfl

theorem cell_prob_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (z y : Bool) :
    G.law.prob (G.cell z y) = S.law.prob (S.cell z y) := by
  have h := cell_moment_eq G S hrep z y 0
  simpa [WholeMeasureLaw.prob, WholeMeasureLaw.mean, FiniteLaw.prob,
    FiniteLaw.mean, pow_zero] using h

theorem cell_first_moment_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (z y : Bool) :
    G.law.mean (fun ω => if G.cell z y ω then (G.V ω : ℝ) else 0) =
      S.law.mean (fun ω => if S.cell z y ω then (S.V ω : ℝ) else 0) := by
  simpa using cell_moment_eq G S hrep z y 1

theorem cell_second_moment_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (z y : Bool) :
    G.law.mean (fun ω => if G.cell z y ω then (G.V ω : ℝ)^2 else 0) =
      S.law.mean (fun ω => if S.cell z y ω then (S.V ω : ℝ)^2 else 0) := by
  exact cell_moment_eq G S hrep z y 2

theorem cell_conditional_variance_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (z y : Bool) :
    G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell z y) =
      S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y) := by
  have hp := cell_prob_eq G S hrep z y
  have h1 := cell_first_moment_eq G S hrep z y
  have h2 := cell_second_moment_eq G S hrep z y
  have hc1 : G.law.ce (fun ω => (G.V ω : ℝ)) (G.cell z y) =
      S.law.ce (fun ω => (S.V ω : ℝ)) (S.cell z y) := by
    unfold WholeMeasureLaw.ce FiniteLaw.ce
    rw [h1, hp]
  have hc2 : G.law.ce (fun ω => (G.V ω : ℝ)^2) (G.cell z y) =
      S.law.ce (fun ω => (S.V ω : ℝ)^2) (S.cell z y) := by
    unfold WholeMeasureLaw.ce FiniteLaw.ce
    rw [h2, hp]
  unfold WholeMeasureLaw.cv FiniteLaw.cv
  rw [hc2, hc1]

theorem bit_mean_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (useZ : Bool) :
    G.law.mean (fun ω => bitVal (if useZ then G.Z ω else G.Y ω)) =
      S.law.mean (fun ω => bitVal (if useZ then S.Z ω else S.Y ω)) := by
  have h := hrep.1 (fun o => bitVal (if useZ then o.2.2.2.1 else o.2.2.1))
  simpa [WholeMeasureStudy.observable, Study.wholeObservable] using h

theorem bit_variance_eq {E : Type*} [Fintype E]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : WholeMeasureStudy Ω) (S : Study E)
    (hrep : wholeRepresentation G S) (useZ : Bool) :
    G.law.variance (fun ω => bitVal (if useZ then G.Z ω else G.Y ω)) =
      S.law.variance (fun ω => bitVal (if useZ then S.Z ω else S.Y ω)) := by
  have hm := bit_mean_eq G S hrep useZ
  have hsquare : (fun ω => bitVal (if useZ then G.Z ω else G.Y ω)^2) =
      fun ω => bitVal (if useZ then G.Z ω else G.Y ω) := by
    funext ω
    cases useZ <;> cases G.Z ω <;> cases G.Y ω <;> norm_num [bitVal]
  have hsquareS : (fun ω => bitVal (if useZ then S.Z ω else S.Y ω)^2) =
      fun ω => bitVal (if useZ then S.Z ω else S.Y ω) := by
    funext ω
    cases useZ <;> cases S.Z ω <;> cases S.Y ω <;> norm_num [bitVal]
  unfold WholeMeasureLaw.variance FiniteLaw.variance
  rw [hsquare, hsquareS, hm]

end SAP.P019a.WH.W1.P.T4_L4

open SAP.P019a.WH.W1.P.T4_L4 SAP.P019a SAP.P019a.Bridge MeasureTheory
open Classical

theorem SAP.P019a.WH.W1.T4_L4_proof : SAP.P019a.WH.W1.T4_L4 := by
  intro Ω hΩ G N S hprob hmeas hbounded hstanding hrep
  classical
  rcases hstanding with ⟨hmonoG, hnoG, hindG, hnonG⟩
  have hmonoBadG : ∀ᵐ ω ∂G.law.measure,
      ¬ (G.Y ω = true ∧ G.X ω = false) := by
    filter_upwards [hmonoG] with ω hω
    intro hbad
    simp_all
  let monoBad : WholeObservation → Prop :=
    fun o => o.2.2.1 = true ∧ o.2.1 = false
  have hmonoBadZero : G.law.prob (fun ω => monoBad (G.observable ω)) = 0 := by
    apply event_prob_zero_of_ae G.law (fun ω => monoBad (G.observable ω))
    filter_upwards [hmonoBadG] with ω hω
    simpa [monoBad, WholeMeasureStudy.observable] using hω
  have hmonoBadS : S.law.prob (fun ω => monoBad (S.wholeObservable ω)) = 0 := by
    have h := event_prob_eq G S hrep monoBad
    rw [hmonoBadZero] at h
    exact h.symm
  have hmonoS : S.monotone := by
    intro ω hmass hy
    by_contra hx
    have hx' : S.X ω = false := by cases h : S.X ω <;> simp_all
    have hle := finite_atom_le_prob S.law ω
      (fun t => monoBad (S.wholeObservable t)) (by
        intro t ht htw
        subst t
        exact ⟨hy, hx'⟩)
    rw [hmonoBadS] at hle
    exact (not_lt_of_ge hle) hmass
  let noBad : WholeObservation → Prop := fun o =>
    ¬ ((o.2.2.2.2 : ℝ) = (o.1 : ℝ) + bitVal o.2.1 * bitVal o.2.2.2.1)
  have hnoBadG : ∀ᵐ ω ∂G.law.measure,
      (G.V ω : ℝ) = (G.W ω : ℝ) + bitVal (G.X ω) * bitVal (G.Z ω) := by
    filter_upwards [hnoG] with ω hω
    exact hω
  have hnoBadZero : G.law.prob (fun ω => noBad (G.observable ω)) = 0 := by
    apply event_prob_zero_of_ae G.law (fun ω => noBad (G.observable ω))
    filter_upwards [hnoBadG] with ω hω
    simp [noBad, WholeMeasureStudy.observable, hω]
  have hnoBadS : S.law.prob (fun ω => noBad (S.wholeObservable ω)) = 0 := by
    have h := event_prob_eq G S hrep noBad
    rw [hnoBadZero] at h
    exact h.symm
  have hnoS : S.noLiarsDesign := by
    intro ω hmass
    by_contra heq
    have hne : (S.V ω : ℝ) ≠ (S.W ω : ℝ) + bitVal (S.X ω)*bitVal (S.Z ω) := by
      exact fun heq' => heq heq'
    have hle := finite_atom_le_prob S.law ω
      (fun t => noBad (S.wholeObservable t)) (by
        intro t ht htw
        subst t
        exact hne)
    rw [hnoBadS] at hle
    exact (not_lt_of_ge hle) hmass
  have hindS : S.treatmentIndependent := by
    intro f z
    have hleft := hrep.1 (fun o =>
      if o.2.2.2.1 = z then f o.1 o.2.1 o.2.2.1 else 0)
    have hprobz := hrep.1 (fun o => if o.2.2.2.1 = z then 1 else 0)
    have hmeanf := hrep.1 (fun o => f o.1 o.2.1 o.2.2.1)
    have hG := hindG f z
    have hGprob : G.law.prob (fun ω => G.Z ω = z) =
        S.law.prob (fun ω => S.Z ω = z) := by
      change G.law.mean (fun ω => if G.Z ω = z then 1 else 0) =
        S.law.mean (fun ω => if S.Z ω = z then 1 else 0)
      exact hprobz
    have hGmean : G.law.mean (fun ω => f (G.W ω) (G.X ω) (G.Y ω)) =
        S.law.mean (fun ω => f (S.W ω) (S.X ω) (S.Y ω)) := by
      simpa [WholeMeasureStudy.observable, Study.wholeObservable] using hmeanf
    have hGleft : G.law.mean
        (fun ω => if G.Z ω = z then f (G.W ω) (G.X ω) (G.Y ω) else 0) =
        S.law.mean
        (fun ω => if S.Z ω = z then f (S.W ω) (S.X ω) (S.Y ω) else 0) := by
      exact hleft
    rw [hGleft, hGprob, hGmean] at hG
    exact hG
  have hcellProb : ∀ z y, 0 < S.law.prob (S.cell z y) := by
    intro z y
    have hp := cell_prob_eq G S hrep z y
    rw [← hp]
    exact hnonG.1 z y |>.1
  have hcellVar : ∀ z y, 0 < S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y) := by
    intro z y
    rw [← cell_conditional_variance_eq G S hrep z y]
    exact hnonG.1 z y |>.2
  have hvarZ : 0 < S.law.variance (fun ω => bitVal (S.Z ω)) := by
    have hGz : 0 < G.law.variance (fun ω => bitVal (G.Z ω)) := hnonG.2.1
    have hEq := bit_variance_eq G S hrep true
    have hEq' : G.law.variance (fun ω => bitVal (G.Z ω)) =
        S.law.variance (fun ω => bitVal (S.Z ω)) := by simpa using hEq
    rw [← hEq']
    exact hGz
  have hvarY : 0 < S.law.variance (fun ω => bitVal (S.Y ω)) := by
    have hGy : 0 < G.law.variance (fun ω => bitVal (G.Y ω)) := hnonG.2.2
    have hEq := bit_variance_eq G S hrep false
    have hEq' : G.law.variance (fun ω => bitVal (G.Y ω)) =
        S.law.variance (fun ω => bitVal (S.Y ω)) := by simpa using hEq
    rw [← hEq']
    exact hGy
  have hnonS : S.nondegenerate := ⟨
    (fun z y => ⟨hcellProb z y, hcellVar z y⟩), hvarZ, hvarY⟩
  exact ⟨hmonoS, hnoS, hindS, hnonS⟩

