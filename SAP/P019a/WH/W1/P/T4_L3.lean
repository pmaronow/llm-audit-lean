import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace SAP.P019a.WH.W1.P.T4_L3

open SAP.P019a SAP.P019a.WH.W1 MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
open Classical

/-- The real-mass law of a finite population, viewed as a measure. -/
def finiteLawMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : SAP.P019a.FiniteLaw α) : Measure α :=
  ∑ a, ENNReal.ofReal (P.mass a) • Measure.dirac a

lemma finiteLawMeasure_isFinite {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : SAP.P019a.FiniteLaw α) :
    IsFiniteMeasure (finiteLawMeasure P) := by
  classical
  haveI (a : α) : IsFiniteMeasure (Measure.dirac a) := isFiniteMeasure_dirac
  haveI (a : α) : IsFiniteMeasure (ENNReal.ofReal (P.mass a) • Measure.dirac a) :=
    Measure.smul_finite (Measure.dirac a) (by simp)
  unfold finiteLawMeasure
  infer_instance

lemma finiteLawMeasure_singleton {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : SAP.P019a.FiniteLaw α) (a : α) :
    finiteLawMeasure P {a} = ENNReal.ofReal (P.mass a) := by
  classical
  simp [finiteLawMeasure, Measure.dirac_apply, Set.indicator, eq_comm]

lemma finiteLawMeasure_integral {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : SAP.P019a.FiniteLaw α) (f : α → ℝ) :
    ∫ a, f a ∂finiteLawMeasure P = P.mean f := by
  classical
  unfold finiteLawMeasure
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac]
    simp [SAP.P019a.FiniteLaw.mean, P.nonneg, smul_eq_mul]
  · intro a ha
    apply Integrable.smul_measure
    · exact integrable_dirac (by simp)
    · simp

lemma finiteLawMeasure_iid {N n : ℕ} (P : SAP.P019a.FiniteLaw (Fin N)) :
    finiteLawMeasure (P.iid n) = Measure.pi (fun _ : Fin n => finiteLawMeasure P) := by
  classical
  haveI : IsFiniteMeasure (finiteLawMeasure P) := finiteLawMeasure_isFinite P
  apply Measure.ext_of_singleton
  intro s
  rw [finiteLawMeasure_singleton, Measure.pi_singleton]
  change ENNReal.ofReal (∏ i : Fin n, P.mass (s i)) =
    ∏ i : Fin n, finiteLawMeasure P {s i}
  simp_rw [finiteLawMeasure_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (f := fun i : Fin n => P.mass (s i))
    (by intro i hi; exact P.nonneg (s i))

lemma wholeObservable_measurable {E : Type*} [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (S : Study E) :
    Measurable S.wholeObservable := by
  exact measurable_of_finite _

lemma wholeObservable_map_eq {E : Type*} [MeasurableSpace E] {N : ℕ}
    (G : WholeMeasureStudy E) (S : Study (Fin N))
    (hprob : IsProbabilityMeasure G.law.measure)
    (hmeas : G.measurableData)
    (hone : ∀ f : WholeObservation → ℝ,
      G.law.mean (fun ω => f (G.observable ω)) =
        S.law.mean (fun ω => f (S.wholeObservable ω))) :
    Measure.map G.observable G.law.measure =
      Measure.map S.wholeObservable (finiteLawMeasure S.law) := by
  classical
  let μ := Measure.map G.observable G.law.measure
  let ν := Measure.map S.wholeObservable (finiteLawMeasure S.law)
  haveI : IsProbabilityMeasure G.law.measure := hprob
  have hmG : Measurable G.observable := by
    rcases hmeas with ⟨hW, hX, hY, hZ, hV⟩
    change Measurable (fun ω => (G.W ω, G.X ω, G.Y ω, G.Z ω, G.V ω))
    exact Measurable.prodMk hW (Measurable.prodMk hX (Measurable.prodMk hY (Measurable.prodMk hZ hV)))
  have hmS : Measurable S.wholeObservable := wholeObservable_measurable S
  haveI : IsFiniteMeasure (finiteLawMeasure S.law) := finiteLawMeasure_isFinite S.law
  haveI : SigmaFinite μ := by infer_instance
  haveI : SigmaFinite ν := by infer_instance
  apply Measure.ext_of_measureReal_singleton
  intro a
  have hmtest : Measurable (({a} : Set WholeObservation).indicator 1) :=
    (measurable_const : Measurable (fun _ : WholeObservation => (1 : ℝ))).indicator
      (measurableSet_singleton a)
  have hmom := hone (({a} : Set WholeObservation).indicator 1)
  calc
    μ.real {a} = ∫ y, ({a} : Set WholeObservation).indicator 1 y ∂μ := by
      symm
      rw [integral_indicator_one (measurableSet_singleton a), measureReal_def]
    _ = G.law.mean (fun ω => if G.observable ω = a then 1 else 0) := by
      dsimp [μ, WholeMeasureLaw.mean]
      rw [integral_map hmG.aemeasurable hmtest.aestronglyMeasurable]
      simp [Set.indicator, Set.mem_singleton_iff]
    _ = S.law.mean (fun ω => if S.wholeObservable ω = a then 1 else 0) := by
      simpa [Set.indicator, Set.mem_singleton_iff] using hmom
    _ = ∫ y, ({a} : Set WholeObservation).indicator 1 y ∂ν := by
      symm
      rw [show ν = Measure.map S.wholeObservable (finiteLawMeasure S.law) from rfl]
      rw [integral_map hmS.aemeasurable hmtest.aestronglyMeasurable]
      rw [finiteLawMeasure_integral]
      simp [Set.indicator, Set.mem_singleton_iff]
    _ = ν.real {a} := by
      rw [integral_indicator_one (measurableSet_singleton a), measureReal_def]

lemma observable_sample_map_eq {E : Type*} [MeasurableSpace E] {N : ℕ}
    (G : WholeMeasureStudy E) (S : Study (Fin N))
    (hprob : IsProbabilityMeasure G.law.measure)
    (hmeas : G.measurableData)
    (hone : ∀ f : WholeObservation → ℝ,
      G.law.mean (fun ω => f (G.observable ω)) =
        S.law.mean (fun ω => f (S.wholeObservable ω))) (n : ℕ) :
    Measure.map (fun s : Fin n → E => fun i => G.observable (s i))
        ((G.law.iid n).measure) =
      Measure.map (fun s : Fin n → Fin N => fun i => S.wholeObservable (s i))
        (finiteLawMeasure (S.law.iid n)) := by
  classical
  haveI : IsProbabilityMeasure G.law.measure := hprob
  have hmG : Measurable G.observable := by
    rcases hmeas with ⟨hW, hX, hY, hZ, hV⟩
    change Measurable (fun ω => (G.W ω, G.X ω, G.Y ω, G.Z ω, G.V ω))
    exact Measurable.prodMk hW (Measurable.prodMk hX (Measurable.prodMk hY (Measurable.prodMk hZ hV)))
  have hmS : Measurable S.wholeObservable := wholeObservable_measurable S
  haveI : IsFiniteMeasure (finiteLawMeasure S.law) := finiteLawMeasure_isFinite S.law
  have hG : Measure.map (fun s : Fin n → E => fun i => G.observable (s i))
      ((G.law.iid n).measure) = Measure.pi (fun _ : Fin n =>
        Measure.map G.observable G.law.measure) := by
    change Measure.map (fun s i => G.observable (s i))
        (Measure.pi (fun _ : Fin n => G.law.measure)) = _
    rw [Measure.pi_map_pi (fun _ => hmG.aemeasurable)]
  have hS : Measure.map (fun s : Fin n → Fin N => fun i => S.wholeObservable (s i))
      (finiteLawMeasure (S.law.iid n)) = Measure.pi (fun _ : Fin n =>
        Measure.map S.wholeObservable (finiteLawMeasure S.law)) := by
    rw [finiteLawMeasure_iid]
    exact Measure.pi_map_pi (fun _ => hmS.aemeasurable)
  calc
    Measure.map (fun s : Fin n → E => fun i => G.observable (s i))
        ((G.law.iid n).measure) = Measure.pi (fun _ : Fin n =>
          Measure.map G.observable G.law.measure) := hG
    _ = Measure.pi (fun _ : Fin n =>
          Measure.map S.wholeObservable (finiteLawMeasure S.law)) := by
      rw [wholeObservable_map_eq G S hprob hmeas hone]
    _ = Measure.map (fun s : Fin n → Fin N => fun i => S.wholeObservable (s i))
          (finiteLawMeasure (S.law.iid n)) := hS.symm

end
end SAP.P019a.WH.W1.P.T4_L3

open SAP.P019a.WH.W1.P.T4_L3

theorem SAP.P019a.WH.W1.T4_L3_proof : SAP.P019a.WH.W1.T4_L3 := by
  intro E hE G N S hprob hmeas hbounded hdesign hone
  constructor
  · exact hone
  · intro n f
    have hmap :=
      SAP.P019a.WH.W1.P.T4_L3.observable_sample_map_eq G S hprob hmeas hone n
    have hmG : Measurable G.observable := by
      rcases hmeas with ⟨hW, hX, hY, hZ, hV⟩
      change Measurable (fun ω => (G.W ω, G.X ω, G.Y ω, G.Z ω, G.V ω))
      exact Measurable.prodMk hW (Measurable.prodMk hX (Measurable.prodMk hY (Measurable.prodMk hZ hV)))
    have hmS : Measurable S.wholeObservable :=
      SAP.P019a.WH.W1.P.T4_L3.wholeObservable_measurable S
    have hmSampleG : Measurable (fun s : Fin n → E => fun i => G.observable (s i)) := by
      fun_prop
    have hmSampleS : Measurable (fun s : Fin n → Fin N => fun i => S.wholeObservable (s i)) := by
      fun_prop
    have hmeasf : Measurable f := measurable_of_countable f
    have hsmG : AEStronglyMeasurable f
        (Measure.map (fun s : Fin n → E => fun i => G.observable (s i))
          ((G.law.iid n).measure)) := by
      exact hmeasf.aestronglyMeasurable
    calc
      (G.law.iid n).mean (fun s => f (fun i => G.observable (s i))) =
          ∫ t, f t ∂Measure.map (fun s : Fin n → E => fun i => G.observable (s i))
            ((G.law.iid n).measure) := by
        dsimp [WholeMeasureLaw.mean, WholeMeasureLaw.iid]
        exact (integral_map hmSampleG.aemeasurable hsmG).symm
      _ = ∫ t, f t ∂Measure.map (fun s : Fin n → Fin N => fun i => S.wholeObservable (s i))
            (finiteLawMeasure (S.law.iid n)) := by rw [hmap]
      _ = (S.law.iid n).mean (fun s => f (fun i => S.wholeObservable (s i))) := by
        rw [integral_map hmSampleS.aemeasurable hmeasf.aestronglyMeasurable]
        exact SAP.P019a.WH.W1.P.T4_L3.finiteLawMeasure_integral _ _
