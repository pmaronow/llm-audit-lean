import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

theorem T20_L1_proof : SAP.P004b.WH.W2.T20_L1 := by
  intro Ω inst μ hμ U B hmeas hmean hbound hdep hdegree hunit
  let V : ∀ N, Fin N → Ω N → ℝ := fun N i ω => Real.sqrt (N : ℝ) * U N i ω
  have hVmeas : ∀ N i, Measurable (V N i) := by
    intro N i
    dsimp [V]
    fun_prop
  have hVmean : ∀ N i, ∫ ω, V N i ω ∂μ N = 0 := by
    intro N i
    simp [V, integral_const_mul, hmean N i]
  obtain ⟨K, hK, hKbound⟩ := hbound
  have hVbound : ∃ M : ℝ, ∀ N i, ∀ᵐ ω ∂μ N, |V N i ω| ≤ M := by
    refine ⟨K, ?_⟩
    intro N i
    by_cases hN : 0 < N
    · filter_upwards [hKbound N hN i] with ω hω
      dsimp [V]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hN)
      calc
        Real.sqrt (N : ℝ) * |U N i ω| ≤ Real.sqrt (N : ℝ) * (K / Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hω (Real.sqrt_nonneg _)
        _ = K := by field_simp [ne_of_gt hs]
    · have hzero : N = 0 := by omega
      subst N
      exact Filter.Eventually.of_forall (fun ω => Fin.elim0 i)
  have hVdep : ∀ N, DependencyGraph (μ N) (V N) (B N) := by
    intro N
    rcases hdep N with ⟨hrefl, hsymm, hind⟩
    refine ⟨hrefl, hsymm, ?_⟩
    intro I J hIJ
    have htuples := hind I J hIJ
    have hscaleI : Measurable (fun t : I → ℝ => fun i => Real.sqrt (N : ℝ) * t i) := by
      fun_prop
    have hscaleJ : Measurable (fun t : J → ℝ => fun j => Real.sqrt (N : ℝ) * t j) := by
      fun_prop
    exact htuples.comp hscaleI hscaleJ
  have hVdegree : ∃ D : ℕ, ∀ N i, (B N i).card ≤ D := hdegree
  have hsumV (N : ℕ) (ω : Ω N) : (∑ i, V N i ω) = Real.sqrt (N : ℝ) * ∑ i, U N i ω := by
    simp [V, ← Finset.mul_sum]
  have hVsecond (N : ℕ) : ∫ ω, (∑ i, V N i ω)^2 ∂μ N = (N : ℝ) := by
    by_cases hN : N = 0
    · subst N
      simp [V]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      rw [show (fun ω => (∑ i, V N i ω)^2) =
        fun ω => (N : ℝ) * (∑ i, U N i ω)^2 by
          funext ω
          rw [hsumV, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]]
      rw [integral_const_mul, hunit N hNpos]
      simp
  have hVvar : ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop,
      v * N ≤ (∫ ω, (∑ i, V N i ω)^2 ∂μ N) := by
    refine ⟨1, by norm_num, Filter.Eventually.of_forall (fun N => ?_)⟩
    rw [hVsecond]
    simp
  have hclt := AronowAudit.P004.corrected_dependency_clt μ hμ V B
    hVmeas hVmean hVbound hVdep hVdegree hVvar
  have hevent : ∀ x : ℝ, (fun N => ((μ N) {ω | (∑ i, V N i ω) /
      Real.sqrt (∫ ω', (∑ i, V N i ω')^2 ∂μ N) ≤ x}).toReal) =ᶠ[atTop]
      (fun N => ((μ N) {ω | (∑ i, U N i ω) ≤ x}).toReal) := by
    intro y
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    have hNpos : 0 < N := hN
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hNpos)
    have hnorm (ω : Ω N) :
        (∑ i, V N i ω) / Real.sqrt (∫ ω', (∑ i, V N i ω')^2 ∂μ N) =
          ∑ i, U N i ω := by
      rw [hsumV, hVsecond]
      field_simp [ne_of_gt hs]
    have hsets : {ω : Ω N | (∑ i, V N i ω) /
        Real.sqrt (∫ ω', (∑ i, V N i ω')^2 ∂μ N) ≤ y} =
        {ω : Ω N | (∑ i, U N i ω) ≤ y} := by
      ext ω
      change (((∑ i, V N i ω) / Real.sqrt (∫ ω', (∑ i, V N i ω')^2 ∂μ N) ≤ y) ↔ (∑ i, U N i ω ≤ y))
      rw [hnorm]
    simp [hsets]
  intro x
  exact Filter.Tendsto.congr' (hevent x) (hclt x)

end
end SAP.P004b.WH.W2
