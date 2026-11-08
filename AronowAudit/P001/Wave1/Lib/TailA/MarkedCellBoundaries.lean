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

/-- Fixed-center distance ties have zero measure, including ties across the pin. -/
theorem marked_fixed_distance_boundary (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (p : ℝ) (j k : Fin n) (hjk : j ≠ k) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), |z j-p| ≠ |z k-p| := by
  have hmirror : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), z j ≠ 2*p-z k := by
    apply marked_coordinate_avoid μ j (fun z => 2*p-z k) (by fun_prop)
    intro z x
    simp only [Function.update_of_ne hjk.symm]
  filter_upwards [marked_coordinate_ne μ j k hjk,hmirror] with z hz hm
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hz (by linarith)
  · exact hm (by linarith)

/-- A query location cannot lie on the midpoint between another site and the pin. -/
theorem marked_pinned_midpoint_boundary (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (p : ℝ) (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), |p-z i| ≠ |z j-z i| := by
  have hjp := marked_coordinate_avoid μ j (fun _ => p) measurable_const (fun _ _ => rfl)
  have hmirror : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), z j ≠ 2*z i-p := by
    apply marked_coordinate_avoid μ j (fun z => 2*z i-p) (by fun_prop)
    intro z x
    simp only [Function.update_of_ne hij]
  filter_upwards [hjp,hmirror] with z hp hm
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hp (by linarith)
  · exact hm (by linarith)

/-- The same calculation for three distinct variable sites. -/
theorem marked_variable_midpoint_boundary (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (i j k : Fin n) (hjk : j ≠ k) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), |z j-z i| ≠ |z k-z i| := by
  by_cases hji : j = i
  · subst i
    filter_upwards [marked_coordinate_ne μ j k hjk] with z hz
    intro h
    have he : z k-z j = 0 := abs_eq_zero.mp (by simpa [markedPinnedScores] using h.symm)
    exact hz (by linarith)
  by_cases hki : k = i
  · subst i
    filter_upwards [marked_coordinate_ne μ j k hjk] with z hz
    intro h
    have he : z j-z k = 0 := abs_eq_zero.mp (by simpa [markedPinnedScores] using h)
    exact hz (by linarith)
  have hmirror : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), z j ≠ 2*z i-z k := by
    apply marked_coordinate_avoid μ j (fun z => 2*z i-z k) (by fun_prop)
    intro z x
    simp only [Function.update_of_ne (Ne.symm hji),Function.update_of_ne hjk.symm]
  filter_upwards [marked_coordinate_ne μ j k hjk,hmirror] with z hz hm
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hz (by linarith)
  · exact hm (by linarith)

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

/-- On a configuration outside the comparison boundaries, every comparison is locally
constant. This is the finite-partition approximation step at a fixed configuration. -/
theorem marked_comparisons_stable {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i j k, j ≠ k → |p j-p i| ≠ |p k-p i|) :
    ∀ᶠ q : Fin n → ℝ in 𝓝 p, ∀ i j k,
      (|q j-q i| ≤ |q k-q i| ↔ |p j-p i| ≤ |p k-p i|) := by
  simp only [Filter.eventually_all]
  intro i j k
  by_cases hjk : j = k
  · subst k
    exact Filter.Eventually.of_forall (fun _ => ⟨fun _ => le_rfl,fun _ => le_rfl⟩)
  have hc (l : Fin n) : ContinuousAt (fun q : Fin n → ℝ => |q l-q i|) p := by
    fun_prop
  rcases lt_or_gt_of_ne (hp i j k hjk) with h | h
  · filter_upwards [(hc j).eventually_lt (hc k) h] with q hq
    exact iff_of_true hq.le h.le
  · filter_upwards [(hc k).eventually_lt (hc j) h] with q hq
    exact iff_of_false (not_le_of_gt hq) (not_le_of_gt h)

/-- The original classical selector itself is stable; no equivariant tie rule is assumed. -/
theorem marked_nearest_stable {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (hp : ∀ i j k, j ≠ k → |p j-p i| ≠ |p k-p i|) :
    ∀ᶠ q : Fin n → ℝ in 𝓝 p, ∀ i, nearestDonor q r i = nearestDonor p r i := by
  filter_upwards [marked_comparisons_stable p hp] with q hq i
  rw [← matching_donor_choice_eq q r i, ← matching_donor_choice_eq p r i]
  congr 1
  funext j k
  exact congrArg (fun P : Prop => decide P) (propext (hq i j k))

theorem marked_weights_stable {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (hp : ∀ i j k, j ≠ k → |p j-p i| ≠ |p k-p i|) :
    ∀ᶠ q : Fin n → ℝ in 𝓝 p,
      ∀ j, donorReuseWeight q r j = donorReuseWeight p r j := by
  filter_upwards [marked_nearest_stable p r hp] with q hq j
  simp only [donorReuseWeight,hq]

theorem marked_weights_continuousAt {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (hp : ∀ i j k, j ≠ k → |p j-p i| ≠ |p k-p i|) (j : Fin n) :
    ContinuousAt (fun q => donorReuseWeight q r j) p := by
  have heq : (fun q => donorReuseWeight q r j) =ᶠ[𝓝 p]
      (fun _ => donorReuseWeight p r j) :=
    (marked_weights_stable p r hp).mono (fun _ h => h j)
  exact continuousAt_const.congr_of_eventuallyEq heq

/-- All copy-level comparisons are inherited from the original-site comparisons.
Consequently repeated copies do not create discontinuities in the aggregated weight. -/
theorem marked_bootstrap_weights_stable {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (hp : ∀ i j k, j ≠ k → |p j-p i| ≠ |p k-p i|) :
    ∀ᶠ q : Fin n → ℝ in 𝓝 p, ∀ (a : Fin n → Fin n) (j : Fin n),
      bootstrapOriginalReuse q r a j = bootstrapOriginalReuse p r a j := by
  filter_upwards [marked_comparisons_stable p hp] with q hq a j
  have hnear (i : Fin n) : nearestDonor (q ∘ a) (r ∘ a) i =
      nearestDonor (p ∘ a) (r ∘ a) i := by
    rw [← matching_donor_choice_eq (q ∘ a) (r ∘ a) i,
      ← matching_donor_choice_eq (p ∘ a) (r ∘ a) i]
    congr 1
    funext l k
    exact congrArg (fun P : Prop => decide P) (propext (hq (a i) (a l) (a k)))
  simp only [bootstrapOriginalReuse,donorReuseWeight,hnear]

theorem marked_bootstrap_weights_continuousAt {n : ℕ}
    (p : Fin n → ℝ) (r : Fin n → Bool)
    (hp : ∀ i j k, j ≠ k → |p j-p i| ≠ |p k-p i|)
    (a : Fin n → Fin n) (j : Fin n) :
    ContinuousAt (fun q => bootstrapOriginalReuse q r a j) p := by
  exact continuousAt_const.congr_of_eventuallyEq
    ((marked_bootstrap_weights_stable p r hp).mono (fun _ h => h a j))

end AronowAudit.P001.TailA
