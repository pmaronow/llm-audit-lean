import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T12_L1

open MeasureTheory
open scoped BigOperators
open SAP.P003a.WH.W2

attribute [local instance 0] Classical.propDecidable

/-- A finite law concentrated on `s` is the sum of its singleton masses on `s`.
This statement is valid for arbitrary sets, since the part outside `s` is null. -/
theorem toReal_measure_eq_atom_sum
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Finset ℝ)
    (hs : μ (s : Set ℝ) = 1) (A : Set ℝ) :
    (μ A).toReal =
      ∑ x : {x : ℝ // x ∈ (s : Set ℝ)},
        if x.1 ∈ A then (μ {x.1}).toReal else 0 := by
  classical
  let Ω := {x : ℝ // x ∈ (s : Set ℝ)}
  let w0 : ℝ → ℝ := fun x => (μ {x}).toReal
  have hsmeas : MeasurableSet (s : Set ℝ) := Finset.measurableSet s
  have hsc : μ (s : Set ℝ)ᶜ = 0 := by
    rw [measure_compl hsmeas (measure_ne_top μ _), measure_univ, hs]
    simp
  let t : Finset ℝ := s.filter (fun x => x ∈ A)
  have ht : (t : Set ℝ) = A ∩ (s : Set ℝ) := by
    ext x
    simp [t, and_comm]
  have hμA : μ A = μ (t : Set ℝ) := by
    apply le_antisymm
    · calc
        μ A ≤ μ ((t : Set ℝ) ∪ (s : Set ℝ)ᶜ) := by
          apply measure_mono
          intro x hx
          by_cases hxs : x ∈ (s : Set ℝ)
          · left
            rw [ht]
            exact ⟨hx, hxs⟩
          · exact Or.inr hxs
        _ ≤ μ (t : Set ℝ) + μ (s : Set ℝ)ᶜ := measure_union_le _ _
        _ = μ (t : Set ℝ) := by simp [hsc]
    · rw [ht]
      exact measure_mono Set.inter_subset_left
  have htoRealSum :
      (∑ x ∈ t, (μ {x}).toReal) =
        (∑ x ∈ t, μ {x}).toReal := by
    exact (ENNReal.toReal_sum (fun x hx => measure_ne_top μ {x})).symm
  have hfiniteSum :
      (∑ x ∈ t, μ {x}) = μ (t : Set ℝ) := MeasureTheory.sum_measure_singleton
  have hindex :
      (∑ x : Ω, if x.1 ∈ A then w0 x.1 else 0) =
        ∑ x ∈ t, w0 x := by
    calc
      _ = ∑ x ∈ s.attach, if x.1 ∈ A then w0 x.1 else 0 := by
        simp only [Finset.attach_eq_univ]
        rfl
      _ = ∑ x ∈ s, if x ∈ A then w0 x else 0 :=
        Finset.sum_attach s (fun x => if x ∈ A then w0 x else 0)
      _ = ∑ x ∈ t, w0 x := by
        simp only [t]
        rw [Finset.sum_filter]
  calc
    (μ A).toReal = (μ (t : Set ℝ)).toReal := by rw [hμA]
    _ = (∑ x ∈ t, μ {x}).toReal := by rw [hfiniteSum]
    _ = ∑ x ∈ t, (μ {x}).toReal := htoRealSum.symm
    _ = ∑ x : Ω, if x.1 ∈ A then (μ {x.1}).toReal else 0 := by
      rw [← hindex]

end SAP.P003a.WH.W2.P.T12_L1

open SAP.P003a.WH.W2.P.T12_L1

theorem SAP.P003a.WH.W2.T12_L1_proof : SAP.P003a.WH.W2.T12_L1 := by
  classical
  intro μ hμ s hs α hα hα1
  let Ω := {x : ℝ // x ∈ (s : Set ℝ)}
  let D : Ω → ℝ := fun x => x.1
  let w : Ω → ℝ := fun x => (μ {x.1}).toReal
  have hsumENN : (∑ x : Ω, μ {x.1}) = μ (s : Set ℝ) := by
    calc
      _ = ∑ x ∈ s.attach, μ {x.1} := by
        simp only [Finset.attach_eq_univ]
        rfl
      _ = ∑ x ∈ s, μ {x} := Finset.sum_attach s (fun x => μ {x})
      _ = μ (s : Set ℝ) := MeasureTheory.sum_measure_singleton
  have hsumToReal :
      (∑ x : Ω, (μ {x.1}).toReal) = (∑ x : Ω, μ {x.1}).toReal := by
    change (∑ x ∈ s.attach, (μ {x.1}).toReal) =
      (∑ x ∈ s.attach, μ {x.1}).toReal
    exact (ENNReal.toReal_sum (fun x hx => MeasureTheory.measure_ne_top μ {x.1})).symm
  have hn : (∑ x : Ω, w x) = 1 := by
    calc
      _ = (∑ x : Ω, μ {x.1}).toReal := by
        simpa only [w] using hsumToReal
      _ = (μ (s : Set ℝ)).toReal := by rw [hsumENN]
      _ = 1 := by rw [hs]; simp
  have hw : ∀ x : Ω, 0 ≤ w x := by
    intro x
    simp only [w]
    exact ENNReal.toReal_nonneg
  have htail (x : ℝ) : (μ (Set.Ici x)).toReal = finiteTail w D x := by
    rw [toReal_measure_eq_atom_sum μ s hs (Set.Ici x)]
    simp only [finiteTail, w, D, Set.mem_Ici]
    rfl
  have hreject :
      (μ {d | (μ (Set.Ici d)).toReal < α}).toReal =
        ∑ x : Ω, if finiteTail w D (D x) < α then w x else 0 := by
    rw [toReal_measure_eq_atom_sum μ s hs]
    apply Fintype.sum_congr
    intro x
    simp only [Set.mem_ofPred_eq, w, D]
    rw [← htail x.1]
  rw [hreject]
  exact (AronowAudit.P003.finite_tail_repair w D hw hn α ⟨hα, hα1⟩).2
