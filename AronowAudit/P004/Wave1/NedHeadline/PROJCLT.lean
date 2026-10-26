import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import AronowAudit.P004.Wave1.FiniteConditioning.FC1
import AronowAudit.P004.Wave1.FiniteConditioning.FC3
import AronowAudit.P004.Wave1.FiniteConditioning.FC5
import AronowAudit.P004.Wave1.FiniteConditioning.FC9
import AronowAudit.P004.P004_SpatialCLTCompletion
import Mathlib.Algebra.Order.Floor.Semiring

/-! Fixed-radius projections and the proved bounded-degree dependency-graph CLT.

The scores on a finite prefix are replaced by zero.  This gives the all-sample-size
bound required by `corrected_dependency_clt`; the original scores and their variance
standardization agree with this array eventually.  The graph itself is unchanged.
-/

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- The fixed-radius projected-score CLT, including absorption of finite prefixes. -/
theorem projclt_proof : PROJCLT := by
  classical
  unfold PROJCLT
  intro p hp X D ρ Cb M v hD hρ hcard hbound hmean hv hvar
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1 (hcard.and hbound)
  let Y : ∀ N, Fin N → Assignment N → ℝ := fun N i =>
    conditionOn (fun _ => p) (ball (D N) i ρ) (X N i)
  let V : ∀ N, Fin N → Assignment N → ℝ := fun N i z =>
    if L ≤ N then Y N i z else 0
  let B : ∀ N, Fin N → Finset (Fin N) := fun N i => ball (D N) i (2 * ρ)
  let μ : ∀ N, Measure (Assignment N) := fun N =>
    CLTCompletion.designMeasure (fun _ => p) (fun _ => hp)

  have hVeq (N : ℕ) (hN : L ≤ N) (i : Fin N) : V N i = Y N i := by
    funext z
    exact if_pos hN
  have hVmean (N : ℕ) (i : Fin N) : expect (fun _ => p) (V N i) = 0 := by
    by_cases hN : L ≤ N
    · rw [hVeq N hN]
      exact (FiniteConditioning.fc3_proof (fun _ => p) (fun _ => hp)
        (ball (D N) i ρ) (X N i)).trans (hmean N i)
    · simp only [V, if_neg hN, expect_const]
  have hSmean (N : ℕ) : expect (fun _ => p) (fun z => ∑ i, V N i z) = 0 := by
    rw [expect_sum]
    simp only [hVmean, Finset.sum_const_zero]
  have hsecond (N : ℕ) :
      (∫ z, (∑ i, V N i z)^2 ∂μ N) =
        variance (fun _ => p) (fun z => ∑ i, V N i z) := by
    rw [CLTCompletion.designMeasure_integral]
    simp only [variance, cov, hSmean, zero_mul, sub_zero, pow_two]

  have hfinite (N : ℕ) : FiniteDependencyGraph (fun _ => p) (V N) (B N) := by
    apply FiniteConditioning.fc9_proof (fun _ => p) (fun _ => hp) (V N)
      (fun i => (ball (D N) i ρ : Set (Fin N))) (B N)
    · intro i
      simp only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and,
        (hD N).2.1 i]
      linarith
    · intro i j
      simp only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hD N).2.2.1 i j]
    · intro i z z' hz
      dsimp only [V]
      split_ifs with hN
      · exact FiniteConditioning.fc1_proof (fun _ => p) (ball (D N) i ρ)
          (X N i) z z' hz
      · rfl
    · intro i j hji
      apply Set.disjoint_left.2
      intro k hki hkj
      have hi : D N i k ≤ ρ := by
        simpa only [Finset.mem_coe, ball, Finset.mem_filter, Finset.mem_univ, true_and]
          using hki
      have hj : D N j k ≤ ρ := by
        simpa only [Finset.mem_coe, ball, Finset.mem_filter, Finset.mem_univ, true_and]
          using hkj
      have hij : 2 * ρ < D N i j := by
        simpa only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
          using hji
      have ht := (hD N).2.2.2 i k j
      rw [(hD N).2.2.1 k j] at ht
      linarith

  have hdegree : ∀ N i, (B N i).card ≤ L + Nat.ceil Cb := by
    intro N i
    by_cases hN : L ≤ N
    · have hc : ((B N i).card : ℝ) ≤ Cb := (hL N hN).1 i
      have hc' : (B N i).card ≤ Nat.ceil Cb := by
        exact_mod_cast hc.trans (Nat.le_ceil Cb)
      omega
    · have hc : (B N i).card ≤ N := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Finset.card_le_card (Finset.subset_univ (B N i)))
      omega
  have hVbound : ∀ N i z, |V N i z| ≤ |M| := by
    intro N i z
    by_cases hN : L ≤ N
    · rw [hVeq N hN]
      exact (FiniteConditioning.fc5_proof (fun _ => p) (fun _ => hp)
        (ball (D N) i ρ) (X N i) M ((hL N hN).2 i) z).trans (le_abs_self M)
    · simp only [V, if_neg hN, abs_zero]
      exact abs_nonneg M

  have hfloor : ∀ᶠ N in atTop,
      v * N ≤ ∫ z, (∑ i, V N i z)^2 ∂μ N := by
    filter_upwards [eventually_ge_atTop L, hvar] with N hN hvarN
    rw [hsecond N]
    have heq : (fun z => ∑ i, V N i z) = (fun z => ∑ i, Y N i z) := by
      funext z
      exact Finset.sum_congr rfl (fun i _ => congrFun (hVeq N hN i) z)
    rw [heq]
    exact hvarN
  have hclt := corrected_dependency_clt μ
    (fun N => CLTCompletion.designMeasure_probability (fun _ => p) (fun _ => hp))
    V B (fun _ _ => measurable_of_finite _)
    (fun N i => by
      rw [CLTCompletion.designMeasure_integral]
      exact hVmean N i)
    ⟨|M|, fun N i => Filter.Eventually.of_forall (hVbound N i)⟩
    (fun N => CLTCompletion.finiteGraph_to_measureGraph (fun _ => p) (fun _ => hp)
      (V N) (B N) (hfinite N))
    ⟨L + Nat.ceil Cb, hdegree⟩ ⟨v, hv, hfloor⟩

  intro x
  have hlim : Tendsto (fun N => prob (fun _ => p) (fun z =>
      (∑ i, V N i z) /
        Real.sqrt (variance (fun _ => p) (fun z' => ∑ i, V N i z')) ≤ x))
      atTop (nhds (normalCDF x)) := by
    have hh := hclt x
    simp_rw [hsecond] at hh
    simpa only [μ, CLTCompletion.designMeasure_apply, Set.mem_setOf_eq] using hh
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop L] with N hN
  have heq : V N = Y N := by
    funext i
    exact hVeq N hN i
  simp only [heq, Y]

end
end AronowAudit.P004.Wave1.NedHeadline
