import AronowAudit.P004.P004_Spatial
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.AlmostEverywhereDepGraphCLT

/-!
The P004 bounded-degree dependency-graph central limit theorem follows from
the Stein-method theorem. The adapter supplies the almost-everywhere summand
bound without strengthening the graph or variance hypotheses.
-/
namespace AronowAudit.P004
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 500000

/-- T20, corrected bounded-degree dependency-graph CLT on arbitrary
probability spaces. Var(∑V)≥vN is imposed on the sum, and the common
summand bound and closed degree do not depend on N. -/
theorem corrected_dependency_clt {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) (hμ : ∀ N, IsProbabilityMeasure (μ N))
    (V : ∀ N, Fin N → Ω N → ℝ) (B : ∀ N, Fin N → Finset (Fin N))
    (hmeas : ∀ N i, Measurable (V N i))
    (hmean : ∀ N i, ∫ ω, V N i ω ∂μ N = 0)
    (hbound : ∃ M : ℝ, ∀ N i, ∀ᵐ ω ∂μ N, |V N i ω| ≤ M)
    (hdep : ∀ N, DependencyGraph (μ N) (V N) (B N))
    (hdegree : ∃ D : ℕ, ∀ N i, (B N i).card ≤ D)
    (hvar : ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop,
      v*N ≤ (∫ ω, (∑ i, V N i ω)^2 ∂μ N)) :
    ∀ x : ℝ, Tendsto (fun N => ((μ N) {ω |
      (∑ i, V N i ω) / Real.sqrt (∫ ω', (∑ i, V N i ω')^2 ∂μ N) ≤ x}).toReal)
        atTop (nhds (normalCDF x)) := by
  classical
  letI (N : ℕ) : IsProbabilityMeasure (μ N) := hμ N
  let Dep : ∀ N, Causalean.Mathlib.Probability.SteinMethod.DepGraph (V N) (μ N) := fun N => {
    G := fun i j => j ∈ B N i
    decG := inferInstance
    refl := (hdep N).1
    symm := fun i j hij => ((hdep N).2.1 i j).mp hij
    meas := hmeas N
    indep := (hdep N).2.2 }
  obtain ⟨D,hD⟩ := hdegree
  have hdeg (N : ℕ) (i : Fin N) : ((Dep N).nbhd i).card ≤ D := by
    have he : (Dep N).nbhd i = B N i := by
      ext j
      exact (Dep N).mem_nbhd_iff
    rw [he]
    exact hD N i
  obtain ⟨M,hM⟩ := hbound
  obtain ⟨c,hc,hcV⟩ := hvar
  intro x
  have hh := Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt_ae
    μ V Dep D hdeg M hM hmean
    (fun N => ∫ ω, (∑ i, V N i ω)^2 ∂μ N) (fun _ => rfl)
    c hc (by simpa only [Fintype.card_fin] using hcV)
    (by simp only [Fintype.card_fin]; exact tendsto_id) x
  refine hh.congr (fun N => ?_)
  simp only [Causalean.Mathlib.Probability.SteinMethod.depSum]
  rw [MeasureTheory.map_measureReal_apply
    ((Finset.measurable_sum Finset.univ (fun i _ => hmeas N i)).div_const _) measurableSet_Iic]
  rfl

end
end AronowAudit.P004
