import SAP.P019a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W2.P.T11_L2

open MeasureTheory
open scoped BigOperators
open Classical

theorem sample_fiber_mass {Ω : Type*} [MeasurableSpace Ω]
    {J n : ℕ} (S : T11Population J Ω) (t : Fin n → T11Observation J) :
    (S.sampleLaw n).real {s | S.sampleObservations s = t} =
      (S.finiteStudy.law.iid n).mass t := by
  let f : (Fin n → Ω) → (Fin n → T11Observation J) := S.sampleObservations
  have hrect :
      {s : Fin n → Ω | f s = t} =
        Set.univ.pi (fun i => S.observe ⁻¹' {t i}) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [funext_iff]
    rfl
  change ((Measure.pi (fun _ : Fin n => S.law)) {s | f s = t}).toReal = _
  rw [hrect, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

theorem observation_measurable {Ω : Type*} [MeasurableSpace Ω]
    {J n : ℕ} (S : T11Population J Ω) :
    Measurable (S.sampleObservations (n := n)) := by
  apply measurable_pi_iff.2
  intro i
  exact S.measurable_observe.comp (measurable_pi_apply i)

theorem event_probability {Ω : Type*} [MeasurableSpace Ω]
    {J n : ℕ} (S : T11Population J Ω)
    (D : (Fin n → T11Observation J) → Prop) :
    (S.sampleLaw n).real {s | D (S.sampleObservations s)} =
      (S.finiteStudy.law.iid n).prob D := by
  let f : (Fin n → Ω) → (Fin n → T11Observation J) := S.sampleObservations
  let q : Finset (Fin n → T11Observation J) := Finset.univ.filter D
  haveI : IsProbabilityMeasure (S.sampleLaw n) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => S.law))
    infer_instance
  have hmeas : ∀ t ∈ q, MeasurableSet (f ⁻¹' {t}) := by
    intro t ht
    exact (observation_measurable S) (measurableSet_singleton t)
  have htop : ∀ t ∈ q, (S.sampleLaw n) (f ⁻¹' {t}) ≠ ⊤ := by
    intro t ht
    exact measure_ne_top _ _
  have hsum := sum_measureReal_preimage_singleton (μ := S.sampleLaw n)
    (s := q) (f := f) hmeas htop
  have hevent : f ⁻¹' (q : Set (Fin n → T11Observation J)) =
      {s | D (f s)} := by
    ext s
    simp [q]
  rw [hevent] at hsum
  calc
    (S.sampleLaw n).real {s | D (S.sampleObservations s)} =
        ∑ t ∈ q, (S.sampleLaw n).real (f ⁻¹' {t}) := hsum.symm
    _ = ∑ t ∈ q, (S.finiteStudy.law.iid n).mass t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sample_fiber_mass S t
    _ = (S.finiteStudy.law.iid n).prob D := by
      simp [q, FiniteLaw.prob, FiniteLaw.mean, FiniteLaw.iid,
        Finset.sum_filter]

end SAP.P019a.WH.W2.P.T11_L2

theorem SAP.P019a.WH.W2.T11_L2_proof : SAP.P019a.WH.W2.T11_L2 := by
  intro Ω _ J S n D
  exact SAP.P019a.WH.W2.P.T11_L2.event_probability S D
