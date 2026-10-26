import AronowAudit.P001.Wave1.Lib.TailA.MatchingLaw

/-! Null location coincidences and null midpoint-comparison boundaries.
The finite measure is arbitrary, so the results also apply to conditional
uniform positions on a bounded window. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellBoundaries (p : Prop) : Decidable p :=
  Classical.propDecidable p

def markedPinnedScores {n : ℕ} (p : ℝ) (z : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases p z
set_option maxHeartbeats 1000000

theorem marked_coordinate_avoid (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) (hupdate : ∀ z x, f (Function.update z j x) = f z) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), z j ≠ f z := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) j
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) j
    have hm : MeasurableSet {q : ℝ × (Fin m → ℝ) |
        (e.symm q) j ≠ f (e.symm q)} :=
      (measurableSet_eq_fun ((measurable_pi_apply j).comp e.symm.measurable)
        (hf.comp e.symm.measurable)).compl
    have hp : ∀ᵐ q ∂μ.prod (Measure.pi (fun _ : Fin m => μ)),
        (e.symm q) j ≠ f (e.symm q) := by
      apply (Measure.ae_prod_iff_ae_ae hm).2
      apply (Measure.ae_ae_comm hm).2
      apply ae_of_all
      intro z
      have hc (x : ℝ) : f (j.insertNth x z) = f (j.insertNth 0 z) := by
        have hu := hupdate (j.insertNth (0 : ℝ) z) x
        simpa only [Fin.update_insertNth (α := fun _ : Fin (m+1) => ℝ)] using hu
      simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, hc] using
        μ.ae_ne (f (j.insertNth (0 : ℝ) z))
    have hp' : ∀ᵐ q ∂(Measure.pi (fun _ : Fin (m+1) => μ)).map e,
        (e.symm q) j ≠ f (e.symm q) := by
      rw [he.map_eq]
      exact hp
    have hpull := ae_of_ae_map e.measurable.aemeasurable hp'
    simpa only [e.symm_apply_apply] using hpull

theorem marked_coordinate_ne (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), z j ≠ z k := by
  apply marked_coordinate_avoid μ j (fun z => z k) (measurable_pi_apply k)
  intro z x
  exact Function.update_of_ne hjk.symm _ _


theorem marked_pinned_injective (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (n : ℕ) (p : ℝ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), Function.Injective (markedPinnedScores p z) := by
  have hfixed : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), ∀ i, z i ≠ p := by
    apply ae_all_iff.mpr
    intro i
    exact marked_coordinate_avoid μ i (fun _ => p) measurable_const (fun _ _ => rfl)
  have hvar : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), ∀ i j, i ≠ j → z i ≠ z j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact ae_of_all _ (fun _ h => False.elim (h hij))
    · exact (marked_coordinate_ne μ i j hij).mono (fun _ h _ => h)
  filter_upwards [hfixed,hvar] with z hf hv
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      rfl
    · intro h
      exact False.elim (hf j (by simpa [markedPinnedScores] using h.symm))
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact False.elim (hf i (by simpa [markedPinnedScores] using h))
    · intro h
      by_cases hij : i = j
      · exact congrArg Fin.succ hij
      · exact False.elim (hv i j hij (by simpa [markedPinnedScores] using h))

theorem marked_pin_update_other {n : ℕ} (p : ℝ) (z : Fin n → ℝ)
    (j : Fin n) (x : ℝ) (i : Fin (n+1)) (hi : i ≠ j.succ) :
    markedPinnedScores p (Function.update z j x) i = markedPinnedScores p z i := by
  revert hi
  refine Fin.cases ?_ (fun i => ?_) i
  · intro _
    rfl
  · intro hi
    simp only [markedPinnedScores,Fin.cases_succ]
    exact Function.update_of_ne (fun h => hi (congrArg Fin.succ h)) _ _

theorem marked_pinned_distance_ne_variable (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (p : ℝ) (i : Fin (n+1)) (j : Fin n)
    (k : Fin (n+1)) (hjk : j.succ ≠ k) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      |markedPinnedScores p z j.succ-markedPinnedScores p z i| ≠
        |markedPinnedScores p z k-markedPinnedScores p z i| := by
  by_cases hji : j.succ = i
  · subst i
    filter_upwards [marked_pinned_injective μ n p] with z hz
    intro h
    have he : markedPinnedScores p z k-markedPinnedScores p z j.succ = 0 :=
      abs_eq_zero.mp (by simpa [markedPinnedScores] using h.symm)
    exact hjk (hz (by linarith))
  have hm (l : Fin (n+1)) : Measurable (fun z : Fin n → ℝ => markedPinnedScores p z l) := by
    refine Fin.cases measurable_const (fun l => ?_) l
    change Measurable (fun z : Fin n → ℝ => z l)
    exact measurable_pi_apply l
  have hmirror : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      z j ≠ 2*markedPinnedScores p z i-markedPinnedScores p z k := by
    apply marked_coordinate_avoid μ j (fun z => 2*markedPinnedScores p z i-markedPinnedScores p z k)
      ((measurable_const.mul (hm i)).sub (hm k))
    intro z x
    rw [marked_pin_update_other p z j x i (Ne.symm hji),
      marked_pin_update_other p z j x k hjk.symm]
  filter_upwards [marked_pinned_injective μ n p,hmirror] with z hz hm
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hjk (hz (by linarith))
  · apply hm
    change markedPinnedScores p z j.succ =
      2*markedPinnedScores p z i-markedPinnedScores p z k
    linarith

/-- The entire pinned configuration avoids all assignment-comparison boundaries. -/
theorem marked_pinned_distances_unique (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (n : ℕ) (p : ℝ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), ∀ (i j k : Fin (n+1)), j ≠ k →
      |markedPinnedScores p z j-markedPinnedScores p z i| ≠ |markedPinnedScores p z k-markedPinnedScores p z i| := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  by_cases hjk : j = k
  · exact ae_of_all _ (fun _ h => False.elim (h hjk))
  suffices h : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      |markedPinnedScores p z j-markedPinnedScores p z i| ≠ |markedPinnedScores p z k-markedPinnedScores p z i| from
    h.mono (fun _ h _ => h)
  revert hjk
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun k => ?_) k
    · intro h
      exact False.elim (h rfl)
    · intro h
      exact (marked_pinned_distance_ne_variable μ p i k 0 (Ne.symm h)).mono
        (fun _ h => h.symm)
  · intro h
    exact marked_pinned_distance_ne_variable μ p i j k h


end AronowAudit.P001.TailA
