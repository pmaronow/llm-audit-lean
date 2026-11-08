import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T5_L1

open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section

private def areaTerm (q : Fin 6 → Bool → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment 2) (i : Fin 2) (j : Fin 6) : ℝ :=
  if x ∈ w1AreaBin (areaBinaryCenter i) j.val then
    if angularFraction (areaBinaryCenter i) x < q j (z i) then 1 else 0
  else 0

private theorem areaTerm_binary (q : Fin 6 → Bool → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment 2) (i : Fin 2) (j : Fin 6) :
    areaTerm q x z i j = 0 ∨ areaTerm q x z i j = 1 := by
  classical
  unfold areaTerm
  split_ifs <;> norm_num

private theorem areaTerm_support (q : Fin 6 → Bool → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment 2) (i : Fin 2) (j : Fin 6)
    (h : areaTerm q x z i j ≠ 0) : x ∈ w1AreaBin (areaBinaryCenter i) j.val := by
  classical
  unfold areaTerm at h
  split_ifs at h <;> simp_all

private theorem bin_support_unique (x : EuclideanSpace ℝ (Fin 2))
    (i k : Fin 2) (j l : Fin 6)
    (hij : x ∈ w1AreaBin (areaBinaryCenter i) j.val)
    (hkl : x ∈ w1AreaBin (areaBinaryCenter k) l.val) : (i,j) = (k,l) := by
  classical
  by_cases hik : i = k
  · subst k
    by_contra hneq
    have hjl : j ≠ l := by
      intro h
      exact hneq (Prod.ext rfl h)
    have hdis := (AronowAudit.P004.Wave1.AreaSum.a3_proof (areaBinaryCenter i)).2 hjl
    have hj : x ∈ AronowAudit.P004.Wave1.AreaSum.bin (areaBinaryCenter i) j := by
      simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using hij
    have hl : x ∈ AronowAudit.P004.Wave1.AreaSum.bin (areaBinaryCenter i) l := by
      simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using hkl
    exact (Set.disjoint_left.mp hdis) hj hl
  · have hdist : dist (areaBinaryCenter i) (areaBinaryCenter k) = 100 := by
      fin_cases i <;> fin_cases k <;>
        norm_num [SAP.P004a.areaBinaryCenter, SAP.P004a.planePoint,
          EuclideanSpace.dist_eq, Fin.sum_univ_succ] at *
    have hi6 : dist x (areaBinaryCenter i) ≤ 6 := by
      apply AronowAudit.P004.Wave1.AreaSum.bin_dist_le_six
      simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using hij
    have hk6 : dist x (areaBinaryCenter k) ≤ 6 := by
      apply AronowAudit.P004.Wave1.AreaSum.bin_dist_le_six
      simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using hkl
    have htri := dist_triangle (areaBinaryCenter i) x (areaBinaryCenter k)
    rw [hdist, dist_comm (areaBinaryCenter i) x] at htri
    nlinarith [hi6, hk6]

private theorem sum_binary_of_unique {α : Type*} [Fintype α] (f : α → ℝ)
    (hbin : ∀ a, f a = 0 ∨ f a = 1)
    (huniq : ∀ a b, f a ≠ 0 → f b ≠ 0 → a = b) :
    (∑ a, f a) = 0 ∨ (∑ a, f a) = 1 := by
  classical
  by_cases hex : ∃ a, f a ≠ 0
  · obtain ⟨a, ha⟩ := hex
    have hfa : f a = 1 := (hbin a).resolve_left ha
    have hzero : ∀ b, b ≠ a → f b = 0 := by
      intro b hba
      rcases hbin b with hb | hb
      · exact hb
      · have : a = b := huniq a b (by rw [hfa]; norm_num) (by rw [hb]; norm_num)
        exact False.elim (hba this.symm)
    rw [Finset.sum_eq_single a (by intro b hb hba; exact hzero b hba) (by simp)]
    simp [hfa]
  · left
    apply Finset.sum_eq_zero
    intro a ha
    rcases hbin a with h | h
    · exact h
    · exact False.elim (hex ⟨a, by rw [h]; norm_num⟩)

private theorem area_region_bin (q : Fin 6 → Bool → ℝ) (i : Fin 2) (j : Fin 6) :
    region (w1AreaPopulation q) i j = w1AreaBin (areaBinaryCenter i) j.val := by
  change AronowAudit.P004.region AronowAudit.P004.areaBinaryPopulation i (j : ℝ) =
    w1AreaBin (AronowAudit.P004.areaBinaryCenter i) j.val
  rw [AronowAudit.P004.Wave1.AreaSum.a2_proof.1 i j]
  rfl

private theorem area_region_whole (q : Fin 6 → Bool → ℝ) (i : Fin 2) :
    region (w1AreaPopulation q) i 6 = Metric.closedBall (areaBinaryCenter i) 6 := by
  change AronowAudit.P004.region AronowAudit.P004.areaBinaryPopulation i 6 = _
  exact AronowAudit.P004.Wave1.AreaSum.a2_proof.2 i

private theorem area_outcome_on_bin (q : Fin 6 → Bool → ℝ) (i : Fin 2) (j : Fin 6)
    (x : EuclideanSpace ℝ (Fin 2)) (z : Assignment 2)
    (hx : x ∈ w1AreaBin (areaBinaryCenter i) j.val) :
    (w1AreaPopulation q).outcome x z =
      if angularFraction (areaBinaryCenter i) x < q j (z i) then 1 else 0 := by
  classical
  change (∑ k : Fin 2, ∑ l : Fin 6, areaTerm q x z k l) = _
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_eq_single (i,j)]
  · simp [areaTerm, hx]
  · intro p hp hpi
    have hnot : x ∉ w1AreaBin (areaBinaryCenter p.1) p.2.val := by
      intro hpbin
      have heq := bin_support_unique x i p.1 j p.2 hx hpbin
      exact hpi heq.symm
    simp [areaTerm, hnot]
  · simp

private theorem area_outcome_binary (q : Fin 6 → Bool → ℝ) :
    ∀ x z, (w1AreaPopulation q).outcome x z = 0 ∨
      (w1AreaPopulation q).outcome x z = 1 := by
  classical
  intro x z
  change (∑ i : Fin 2, ∑ j : Fin 6, areaTerm q x z i j) = 0 ∨
    (∑ i : Fin 2, ∑ j : Fin 6, areaTerm q x z i j) = 1
  rw [← Fintype.sum_prod_type']
  apply sum_binary_of_unique
  · intro p
    exact areaTerm_binary q x z p.1 p.2
  · intro p r hp hr
    exact bin_support_unique x p.1 r.1 p.2 r.2
      (areaTerm_support q x z p.1 p.2 hp)
      (areaTerm_support q x z r.1 r.2 hr)

private theorem area_outcome_measurable (q : Fin 6 → Bool → ℝ) (z : Assignment 2) :
    Measurable (fun x : EuclideanSpace ℝ (Fin 2) => (w1AreaPopulation q).outcome x z) := by
  classical
  change Measurable (fun x => ∑ i : Fin 2, ∑ j : Fin 6, areaTerm q x z i j)
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  unfold areaTerm
  apply Measurable.ite
  · simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using
      (AronowAudit.P004.Wave1.AreaSum.measurableSet_bin (areaBinaryCenter i) j.val)
  · exact Measurable.ite
      (measurableSet_lt
        (AronowAudit.P004.Wave1.AreaSum.angularFraction_measurable (areaBinaryCenter i))
        measurable_const)
      measurable_const measurable_const
  · exact measurable_const

private theorem area_whole_volume (i : Fin 2) :
    volume (Metric.closedBall (areaBinaryCenter i) 6) = ENNReal.ofReal (36 * Real.pi) := by
  rw [EuclideanSpace.volume_closedBall_fin_two,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 6) 2,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6 ^ 2)]
  norm_num

private theorem area_bin_volume (i : Fin 2) (j : Fin 6) :
    volume (w1AreaBin (areaBinaryCenter i) j.val) =
      ENNReal.ofReal (Real.pi * (2 * (j : ℝ) + 1)) := by
  simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using
    (AronowAudit.P004.Wave1.AreaSum.a5_proof.1 (areaBinaryCenter i) j.val)

private theorem area_integrableOn (q : Fin 6 → Bool → ℝ) {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : volume s ≠ ⊤) (z : Assignment 2) :
    IntegrableOn (fun x => (w1AreaPopulation q).outcome x z) s volume := by
  apply Measure.integrableOn_of_bounded hs
    ((area_outcome_measurable q z).aestronglyMeasurable) (M := 1)
  filter_upwards with x
  rcases area_outcome_binary q x z with h | h <;> rw [h] <;> norm_num

theorem T5_L1_proof_aux : SAP.P004a.WH.W1.T5_L1 := by
  classical
  intro q hq
  let P := w1AreaPopulation q
  change
    (∀ x z, P.outcome x z = 0 ∨ P.outcome x z = 1) ∧
    (∀ z, Measurable (fun x => P.outcome x z)) ∧
    (∀ i (j : Fin 6) x z, x ∈ region P i j →
      P.outcome x z = if angularFraction (areaBinaryCenter i) x < q j (z i) then 1 else 0) ∧
    (∀ x z, (∀ i : Fin 2, x ∉ region P i 6) → P.outcome x z = 0) ∧
    (∀ j : Fin 6, WellDefined P j) ∧ WellDefined P 6 ∧
    (∀ i (j : Fin 6), region P i j = w1AreaBin (areaBinaryCenter i) j.val) ∧
    (∀ i, region P i 6 = ⋃ j : Fin 6, region P i j) ∧
    (∀ i, Pairwise (fun j k : Fin 6 => Disjoint (region P i j) (region P i k))) ∧
    (∀ i (j : Fin 6), P.zeta (region P i j) = ENNReal.ofReal (Real.pi * (2 * (j : ℝ) + 1))) ∧
    (∀ i, P.zeta (region P i 6) = ENNReal.ofReal (36 * Real.pi))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact area_outcome_binary q
  · intro z
    exact area_outcome_measurable q z
  · intro i j x z hx
    have hx' : x ∈ w1AreaBin (areaBinaryCenter i) j.val := by
      rw [area_region_bin q i j] at hx
      exact hx
    exact area_outcome_on_bin q i j x z hx'
  · intro x z hout
    change (∑ i : Fin 2, ∑ j : Fin 6, areaTerm q x z i j) = 0
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : x ∉ w1AreaBin (areaBinaryCenter p) j.val := by
      intro hmem
      have hbin : x ∈ AronowAudit.P004.Wave1.AreaSum.bin (areaBinaryCenter p) j := by
        simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using hmem
      have hdist := AronowAudit.P004.Wave1.AreaSum.bin_dist_le_six _ _ j hbin
      have hwhole : x ∈ region P p 6 := by
        rw [area_region_whole q p, Metric.mem_closedBall]
        exact hdist
      exact (hout p) hwhole
    simp [areaTerm, hnot]
  · intro j i
    rw [area_region_bin q i j]
    have hvol := area_bin_volume i j
    have hpos : 0 < Real.pi * (2 * (j : ℝ) + 1) := by positivity
    have hfin : volume (w1AreaBin (areaBinaryCenter i) j.val) ≠ ⊤ := by
      rw [hvol]
      exact ENNReal.ofReal_ne_top
    refine ⟨?_, ?_, ?_, fun z => area_integrableOn q hfin z⟩
    · simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using
        (AronowAudit.P004.Wave1.AreaSum.measurableSet_bin (areaBinaryCenter i) j.val)
    · rw [show P.zeta = volume from rfl, hvol]
      exact ENNReal.ofReal_pos.mpr hpos
    · rw [show P.zeta = volume from rfl, hvol]
      exact ENNReal.ofReal_lt_top
  · intro i
    rw [area_region_whole q i]
    have hvol := area_whole_volume i
    have hpos : 0 < 36 * Real.pi := by positivity
    have hfin : volume (Metric.closedBall (areaBinaryCenter i) 6) ≠ ⊤ := by
      rw [hvol]
      exact ENNReal.ofReal_ne_top
    refine ⟨measurableSet_closedBall, ?_, ?_, fun z => area_integrableOn q hfin z⟩
    · rw [show P.zeta = volume from rfl, hvol]
      exact ENNReal.ofReal_pos.mpr hpos
    · rw [show P.zeta = volume from rfl, hvol]
      exact ENNReal.ofReal_lt_top
  · exact area_region_bin q
  · intro i
    rw [area_region_whole q i]
    rw [(AronowAudit.P004.Wave1.AreaSum.a3_proof (areaBinaryCenter i)).1]
    exact Set.iUnion_congr fun j => (area_region_bin q i j).symm
  · intro i j k hjk
    rw [area_region_bin q i j, area_region_bin q i k]
    have hjk' : j ≠ k := hjk
    have hdis := (AronowAudit.P004.Wave1.AreaSum.a3_proof (areaBinaryCenter i)).2 hjk'
    simpa [w1AreaBin, AronowAudit.P004.Wave1.AreaSum.bin] using hdis
  · intro i j
    change volume (region P i j) = _
    rw [area_region_bin q i j]
    exact area_bin_volume i j
  · intro i
    change volume (region P i 6) = _
    rw [area_region_whole q i]
    exact area_whole_volume i

end
end SAP.P004a.WH.W1.P.T5_L1

theorem SAP.P004a.WH.W1.T5_L1_proof : SAP.P004a.WH.W1.T5_L1 :=
  SAP.P004a.WH.W1.P.T5_L1.T5_L1_proof_aux
