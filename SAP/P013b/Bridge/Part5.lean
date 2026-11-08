import SAP.P013b.Defs
import SAP.P013b.Bridge.Part1
import AronowAudit.P013.P013_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013b.Bridge

open MeasureTheory Filter Finset
open scoped BigOperators Topology

theorem designMeasure_to {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (P : Design Ω) :
    designMeasure P = AronowAudit.P013.designMeasure (toDesign P) := rfl

/-- The source matrix-limit theorem for one pair of distinct exposure labels.
The zero outcome array is unused by that theorem. -/
theorem simulation_matrices_pair {Ω : Type*} {A : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {N K : ℕ}
    (P : Design Ω) (D : Ω → Fin N → Fin K) (d e : Fin K) (hne : d ≠ e)
    (Z : ℕ → A → Ω) (hm : ∀ r, Measurable (Z r)) (hi : ProbabilityTheory.iIndepFun Z μ)
    (hlaw : ∀ r, Measure.map (Z r) μ = designMeasure P) :
    ∀ᵐ a ∂μ, ∀ i j : Fin N,
      Tendsto (fun R : ℕ => ((∑ r ∈ range R,
        indicator D i d (Z r a) * indicator D j d (Z r a)) +
          (if i = j then 1 else 0)) / (R + 1 : ℝ)) atTop
        (𝓝 (∑ z, P.weight z * (indicator D i d z * indicator D j d z))) ∧
      Tendsto (fun R : ℕ => (∑ r ∈ range R,
        indicator D i d (Z r a) * indicator D j e (Z r a)) / (R : ℝ)) atTop
        (𝓝 (∑ z, P.weight z * (indicator D i d z * indicator D j e z))) :=
  AronowAudit.P013.simulation_matrices_almost_sure μ
    (toPopulation (P := P) (⟨D, fun _ _ => 0⟩ : Population P N K))
    d e hne Z hm hi hlaw

/-- All exposures on one almost-sure event. The same-exposure limit for `d` is the
first conjunct of the pair theorem after relabelling the exposures injectively into
`Fin (K + 1)` and pairing `d` with the unused label `Fin.last K`, so it also covers
`K = 1`; the cross limits are the pair theorem itself. -/
theorem simulation_matrices_iid : T20Statement := by
  intro Ω A _ _ _ _ μ _ N K P D Z hm hi hlaw
  rw [ae_all_iff]
  intro d
  let D' : Ω → Fin N → Fin (K + 1) := fun z i => (D z i).castSucc
  have hind : ∀ (i : Fin N) (c : Fin K), indicator D' i c.castSucc = indicator D i c := by
    intro i c
    funext z
    simp [indicator, D', Fin.castSucc_inj]
  have hS := simulation_matrices_pair μ P D' d.castSucc (Fin.last K)
    (Fin.castSucc_lt_last d).ne Z hm hi hlaw
  have hC : ∀ᵐ a ∂μ, ∀ e : Fin K, d ≠ e → ∀ i j : Fin N,
      Tendsto (fun R : ℕ => (∑ r ∈ range R,
        indicator D i d (Z r a) * indicator D j e (Z r a)) / (R : ℝ)) atTop
        (𝓝 (∑ z, P.weight z * (indicator D i d z * indicator D j e z))) := by
    rw [ae_all_iff]
    intro e
    by_cases hde : d = e
    · exact ae_of_all _ (fun _ h => absurd hde h)
    · filter_upwards [simulation_matrices_pair μ P D d e hde Z hm hi hlaw] with a ha _ i j
      exact (ha i j).2
  filter_upwards [hS, hC] with a hS hC i j
  refine ⟨?_, fun e he => hC e he i j⟩
  simpa only [hind] using (hS i j).1

end SAP.P013b.Bridge
