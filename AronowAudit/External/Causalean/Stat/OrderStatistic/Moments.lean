/-
Upstream project: Causalean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
module
public import AronowAudit.External.Causalean.Stat.OrderStatistic.SimplexIntegrals

/-!
# Exact moments of uniform order-statistic spacings

The adjacent interior gaps of an iid unit-uniform sample have a common exact
second moment.
-/

public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- Given [a finite dimension](hyp:n) and [a coordinate index](hyp:i), [the factorial-scaled second moment of that simplex coordinate has the stated exact value](goal). -/
theorem simplex_coordinate_second_moment (n : ℕ) (i : Fin n) :
    (n.factorial : ℝ) * (∫ z in spacingSimplex n, (z i) ^ 2 ∂volume) =
      (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      rw [simplex_coordinate_square_eq_first]
      change (m + 1).factorial *
        (∫ z in spacingSimplex (m + 1), (z (0 : Fin (m + 1))) ^ 2 ∂volume) = _
      rw [simplex_first_coordinate_square_slice]
      have hfactorial : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
      simp_rw [← mul_div_assoc]
      rw [intervalIntegral.integral_div]
      rw [unit_beta_square_integral]
      norm_num [hfactorial, Nat.factorial_succ]
      have hm : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- The finite spacing map is almost everywhere measurable under the iid uniform law. -/
private theorem firstNSpacings_aemeasurable (n : ℕ) :
    AEMeasurable (firstNSpacings n) (iidSample uniform01 n) := by
  classical
  have hsort : AEMeasurable (sortedSample n) (volume : Measure (Fin n → ℝ)) := by
    let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
      {x | Monotone (x ∘ σ)}
    have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
      have hc : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      exact (isClosed_monotone.preimage hc).measurableSet
    have hcover : (⋃ σ, s σ) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨Tuple.sort x, Tuple.monotone_sort x⟩
    have hpiece (σ : Equiv.Perm (Fin n)) :
        AEMeasurable (sortedSample n) (volume.restrict (s σ)) := by
      have hp : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      apply hp.aemeasurable.congr
      exact ae_restrict_of_forall_mem (hs σ) (fun x hx =>
        (show (fun x => x ∘ σ) x = sortedSample n x from
          (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hx))
    simpa only [hcover, Measure.restrict_univ] using (AEMeasurable.iUnion hpiece)
  have hsort' : AEMeasurable (sortedSample n) (iidSample uniform01 n) := by
    rw [iid_uniform_cube_law]
    exact hsort.restrict
  have hspacing : Measurable (orderedSpacings n) :=
    (orderedSpacings_measurePreserving n).measurable
  convert hspacing.aemeasurable.comp_aemeasurable hsort' using 1
  funext x
  exact firstNSpacings_eq_orderedSpacings n x

/-- Given [a finite sample size](hyp:n), [an adjacent-gap index](hyp:k), and [proof that the gap is interior](hyp:hk), [the squared sorted unit-uniform gap has the stated exact second moment](goal). -/
theorem uniform_gap_second_moment (n k : ℕ) (hk : k + 1 < n) :
    ∫ x, (sortedGap n k x) ^ 2 ∂iidSample uniform01 n =
      (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
  have hfirst := firstNSpacings_aemeasurable n
  let i : Fin n := ⟨k + 1, hk⟩
  have hgap (x : Fin n → ℝ) : sortedGap n k x = firstNSpacings n x i := by
    simp [sortedGap, firstNSpacings, i, hk]
  calc
    (∫ x, (sortedGap n k x) ^ 2 ∂iidSample uniform01 n) =
        ∫ z, (z i) ^ 2 ∂(iidSample uniform01 n).map (firstNSpacings n) := by
          rw [integral_map hfirst ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable]
          simp only [hgap]
    _ = (n.factorial : ℝ) *
        (∫ z in spacingSimplex n, (z i) ^ 2 ∂volume) := by
          rw [uniform_firstN_spacings_law, integral_smul_measure]
          simp
    _ = _ := simplex_coordinate_second_moment n i


end
end Causalean.Stat.OrderStatistic
