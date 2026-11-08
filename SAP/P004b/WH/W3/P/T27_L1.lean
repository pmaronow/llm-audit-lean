import SAP.P004b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical Topology
noncomputable section

private def atomPoint (N : ℕ) (j : Fin N) : EuclideanSpace ℝ (Fin 2) :=
  SAP.P004b.planePoint (((j : ℝ) + 1) * N^2) 0

private lemma separation_eq_dist {N : ℕ} (i j : Fin N) :
    SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i j =
      dist (atomPoint N i) (atomPoint N j) := by
  simp [SAP.P004b.nodeSeparation, SAP.P004b.sparsePopulation, SAP.P004b.planePoint,
    atomPoint]

private lemma atom_mem_region {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i j : Fin N) :
    atomPoint N j ∈ SAP.P004b.region (SAP.P004b.sparsePopulation N) i d ↔
      SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i j ≤ d := by
  change Metric.infDist (atomPoint N j) {atomPoint N i} ∈ Set.Icc 0 d ↔ _
  rw [Metric.infDist_singleton]
  have hdist : dist (atomPoint N j) (atomPoint N i) =
      SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i j := by
    rw [dist_comm, separation_eq_dist]
  rw [hdist]
  have hsep : 0 ≤ SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i j := by
    rw [← hdist]
    exact dist_nonneg
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨hsep, h⟩

private lemma region_measurable {N : ℕ} (i : Fin N) (d : ℝ) :
    MeasurableSet (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d) := by
  simp only [SAP.P004b.region, SAP.P004b.nodeDistance, SAP.P004b.sparsePopulation,
    Metric.infDist_singleton]
  exact measurableSet_Icc.preimage (measurable_id.dist measurable_const)

private lemma outcome_atom {N : ℕ} (j : Fin N) (z : SAP.P004b.Assignment N) :
    (SAP.P004b.sparsePopulation N).outcome (atomPoint N j) z = SAP.P004b.sparseTable N j z := by
  have hN : 0 < N := Nat.zero_lt_of_lt j.isLt
  have hp : Function.Injective (atomPoint N) := by
    intro a b hab
    apply (AronowAudit.P004.Wave1.T27_point_injective hN)
    simpa [atomPoint, SAP.P004b.planePoint, AronowAudit.P004.planePoint] using hab
  change (∑ x : Fin N, if atomPoint N j = atomPoint N x then
      SAP.P004b.sparseTable N x z else 0) = _
  simp only [hp.eq_iff]
  simp

private lemma mass_eq_card {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) :
    (SAP.P004b.sparsePopulation N).zeta
        (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d) =
      ((SAP.P004b.ball (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d).card : ENNReal) := by
  change (∑ j : Fin N, Measure.dirac (atomPoint N j))
      (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d) = _
  rw [Measure.finsetSum_apply]
  calc
    _ = ∑ j : Fin N, if SAP.P004b.nodeSeparation
          (SAP.P004b.sparsePopulation N) i j ≤ d then (1 : ENNReal) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Measure.dirac_apply]
      change (if atomPoint N j ∈ SAP.P004b.region (SAP.P004b.sparsePopulation N) i d
        then (1 : ENNReal) else 0) = _
      rw [atom_mem_region hN d hd i j]
    _ = ((SAP.P004b.ball (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d).card : ENNReal) := by
      simp [SAP.P004b.ball]

private lemma restrict_eq_sum {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) :
    (SAP.P004b.sparsePopulation N).zeta.restrict
        (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d) =
      ∑ j : Fin N, if SAP.P004b.nodeSeparation
          (SAP.P004b.sparsePopulation N) i j ≤ d then Measure.dirac (atomPoint N j) else 0 := by
  have hr : ((∑ j : Fin N, Measure.dirac (atomPoint N j)).restrict
      (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d)) =
      ∑ j : Fin N, (Measure.dirac (atomPoint N j)).restrict
        (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d) := by
    simpa only [Measure.restrictₗ_apply] using
      map_sum (Measure.restrictₗ (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d))
        (fun j : Fin N => Measure.dirac (atomPoint N j)) Finset.univ
  change (∑ j : Fin N, Measure.dirac (atomPoint N j)).restrict _ = _
  rw [hr]
  apply Finset.sum_congr rfl
  intro j hj
  rw [restrict_dirac' (region_measurable i d), atom_mem_region hN d hd i j]

private lemma restrict_eq_ball {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) :
    (SAP.P004b.sparsePopulation N).zeta.restrict
        (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d) =
      ∑ j ∈ SAP.P004b.ball
        (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d,
          Measure.dirac (atomPoint N j) := by
  rw [restrict_eq_sum hN d hd i]
  simp [SAP.P004b.ball, Finset.sum_filter]

private lemma mass_toReal_eq_card {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) :
    ((SAP.P004b.sparsePopulation N).zeta
      (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d)).toReal =
      ((SAP.P004b.ball (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d).card : ℝ) := by
  rw [mass_eq_card hN d hd i]
  simp

private lemma numerator_eq {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) (z : SAP.P004b.Assignment N) :
    (∫ x in SAP.P004b.region (SAP.P004b.sparsePopulation N) i d,
      (SAP.P004b.sparsePopulation N).outcome x z
        ∂(SAP.P004b.sparsePopulation N).zeta) =
      if SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i
          (⟨0, hN⟩ : Fin N) ≤ d then
        (1/4 + 3/4 * SAP.P004b.bit (z ⟨0, hN⟩)) else 0 := by
  let o : Fin N := ⟨0, hN⟩
  rw [show (∫ x in SAP.P004b.region (SAP.P004b.sparsePopulation N) i d,
      (SAP.P004b.sparsePopulation N).outcome x z
        ∂(SAP.P004b.sparsePopulation N).zeta) =
    ∫ x, (SAP.P004b.sparsePopulation N).outcome x z ∂
      ((SAP.P004b.sparsePopulation N).zeta.restrict
        (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d)) by rfl]
  rw [restrict_eq_ball hN d hd i]
  rw [MeasureTheory.integral_finsetSum_measure]
  · simp_rw [MeasureTheory.integral_dirac, outcome_atom]
    have hmem : o ∈ SAP.P004b.ball
        (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d ↔
          SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i o ≤ d := by
      simp [SAP.P004b.ball]
    by_cases h : o ∈ SAP.P004b.ball
        (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d
    · rw [Finset.sum_eq_single o]
      · have hs := hmem.mp h
        simp [SAP.P004b.sparseTable, o, hs]
      · intro j hj hjo
        have hj0 : j.val ≠ 0 := by
          intro hval
          apply hjo
          apply Fin.ext
          exact hval
        simp [SAP.P004b.sparseTable, hj0]
      · simp [h]
    · rw [Finset.sum_eq_zero]
      · have hs : ¬ SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i o ≤ d :=
          fun hc => h (hmem.mpr hc)
        simp [SAP.P004b.sparseTable, o, hs]
      · intro j hj
        have hjo : j ≠ o := by
          intro he
          subst j
          exact h hj
        have hj0 : j.val ≠ 0 := by
          intro hval
          apply hjo
          apply Fin.ext
          exact hval
        simp [SAP.P004b.sparseTable, hj0]
  · intro j hj
    exact MeasureTheory.integrable_dirac (by simp [outcome_atom])

private lemma ball_nonempty {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) : (SAP.P004b.ball (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d).Nonempty := by
  refine ⟨i, ?_⟩
  simp [SAP.P004b.ball, separation_eq_dist, hd]

private lemma well_defined {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d) :
    SAP.P004b.WellDefined (SAP.P004b.sparsePopulation N) d := by
  intro i
  refine ⟨region_measurable i d, ?_, ?_, ?_⟩
  · rw [mass_eq_card hN d hd i]
    exact_mod_cast (Finset.card_pos.mpr (ball_nonempty hN d hd i))
  · rw [mass_eq_card hN d hd i]
    exact ENNReal.natCast_lt_top _
  · intro z
    change Integrable (fun x => (SAP.P004b.sparsePopulation N).outcome x z)
      ((SAP.P004b.sparsePopulation N).zeta.restrict
        (SAP.P004b.region (SAP.P004b.sparsePopulation N) i d))
    rw [restrict_eq_ball hN d hd i]
    rw [MeasureTheory.integrable_finsetSum_measure]
    intro j hj
    exact MeasureTheory.integrable_dirac (by simp [outcome_atom])

private lemma circle_formula {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin N) (z : SAP.P004b.Assignment N) :
    SAP.P004b.circleAverage (SAP.P004b.sparsePopulation N) d i z =
      if SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i
          (⟨0, hN⟩ : Fin N) ≤ d then
        (1/4+3/4*SAP.P004b.bit (SAP.P004b.wholeFirst z)) /
          ((SAP.P004b.ball (SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N)) i d).card : ℝ)
      else 0 := by
  let o : Fin N := ⟨0, hN⟩
  rw [SAP.P004b.circleAverage, numerator_eq hN d hd i z, mass_toReal_eq_card hN d hd i]
  have hfirst : SAP.P004b.wholeFirst z = z o := by
    unfold SAP.P004b.wholeFirst
    rw [dif_pos hN]
  by_cases h : SAP.P004b.nodeSeparation (SAP.P004b.sparsePopulation N) i o ≤ d
  · simp [h, hfirst, o]
  · simp [h, hfirst, o]

end
end SAP.P004b.WH.W3.P.T27_L1

theorem SAP.P004b.WH.W3.T27_L1_proof : SAP.P004b.WH.W3.T27_L1 := by
  change SAP.P004b.WholeSparseDisks
  intro N hN d hd
  refine ⟨SAP.P004b.WH.W3.P.T27_L1.well_defined hN d hd, ?_⟩
  intro i z
  exact SAP.P004b.WH.W3.P.T27_L1.circle_formula hN d hd i z
