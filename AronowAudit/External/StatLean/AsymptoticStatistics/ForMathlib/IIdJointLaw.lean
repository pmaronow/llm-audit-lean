/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# iid joint-law bridge

The finite product law on `Fin n → 𝓧` equals the law of the corresponding
restriction of an infinite iid sequence:
```
Measure.pi (fun _ : Fin n => ν)
  = (Measure.infinitePi (fun _ : ℕ => ν)).map (fun ω i => ω i.val)
```
whenever `ν` is a probability measure.

The measure-on-set version transports probabilities of predicates on
`Fin n → 𝓧` along the truncation map.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics


/-- `Fin n` and the Finset-range coercion `↥(Finset.range n)` are canonically
equivalent (both are `{k : ℕ // k < n}` up to `Finset.mem_range`). Packaged
as an `Equiv` for use with `Measure.pi`'s reindexing lemmas. -/
def rangeEquivFin (n : ℕ) : ↥(Finset.range n) ≃ Fin n where
  toFun i := ⟨i.val, Finset.mem_range.mp i.prop⟩
  invFun i := ⟨i.val, Finset.mem_range.mpr i.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma rangeEquivFin_apply_val (n : ℕ) (i : ↥(Finset.range n)) :
    ((rangeEquivFin n) i).val = i.val := rfl

@[simp] lemma rangeEquivFin_symm_apply_val (n : ℕ) (i : Fin n) :
    ((rangeEquivFin n).symm i).val = i.val := rfl


/-- **iid product = finite restriction of the Kolmogorov extension (`infinitePi` version)**.

Uses `Measure.infinitePi`, the general `ι`-indexed product. This form is the natural
match for `ProbabilityTheory.iIndepFun_infinitePi`, which is stated for `infinitePi`.
-/
theorem pi_const_eq_infinitePi_map
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν)
      = (Measure.infinitePi (fun _ : ℕ => ν)).map
          (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) := by
  classical
  set ψ : (↥(Finset.range n) → 𝓧) → (Fin n → 𝓧) := fun f i =>
    f ((rangeEquivFin n).symm i) with hψ_def
  have hψ_meas : Measurable ψ := by
    refine Measurable.of_eval (fun i => ?_)
    exact measurable_pi_apply _
  have h_factor :
      (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
        = ψ ∘ (Finset.range n).restrict := by
    funext ω i; rfl
  have h_restrict_meas :
      Measurable ((Finset.range n).restrict : (ℕ → 𝓧) → (↥(Finset.range n) → 𝓧)) := by
    refine Measurable.of_eval (fun _ => ?_)
    exact measurable_pi_apply _
  have h_step1 : (Measure.infinitePi (fun _ : ℕ => ν)).map
        (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
      = ((Measure.infinitePi (fun _ : ℕ => ν)).map (Finset.range n).restrict).map ψ := by
    rw [h_factor, ← Measure.map_map hψ_meas h_restrict_meas]
  rw [h_step1, MeasureTheory.Measure.infinitePi_map_restrict]
  have h_ψ_eq : ψ = MeasurableEquiv.piCongrLeft (fun _ : Fin n => 𝓧)
      (rangeEquivFin n) := by
    funext f i
    rw [hψ_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [h_ψ_eq]
  have mp := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin n => ν) (rangeEquivFin n)
  exact mp.map_eq.symm


/-- **Pinf → Pⁿ measure-on-set bridge for varying truncation**.

For each `n`, the probability under `Measure.pi (fun _ : Fin n => ν)` of a
predicate on `Fin n → 𝓧` equals the probability under `Measure.infinitePi (const ν)`
of the predicate composed with the truncation `ω ↦ fun i : Fin n => ω i.val`. This
is the per-n measure-equality consequence of `pi_const_eq_infinitePi_map` plus
`Measure.map_apply`, packaged for use inside Slutsky-style `hDist`-arguments where
the base measure varies in `n` and the predicate is parametrised by `n`. -/
lemma pi_meas_eq_infinitePi_meas_of_truncate
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ)
    {s : Set (Fin n → 𝓧)} (hs : MeasurableSet s) :
    Measure.pi (fun _ : Fin n => ν) s
      = (Measure.infinitePi (fun _ : ℕ => ν))
          {ω | (fun i : Fin n => ω i.val) ∈ s} := by
  rw [pi_const_eq_infinitePi_map ν n]
  rw [Measure.map_apply (f := fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) ?_ hs]
  · rfl
  · refine Measurable.of_eval (fun _ => ?_)
    exact measurable_pi_apply _


end AsymptoticStatistics
