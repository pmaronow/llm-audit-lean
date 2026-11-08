import SAP.P037a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2.P.T5_L7

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

private theorem uniformInput_eq_closedProduct (n : ℕ) :
    SAP.P037a.uniformInputW2 n =
      Causalean.Stat.OrderStatistic.iidSample
        Causalean.Stat.OrderStatistic.uniform01 n := by
  change Measure.pi (fun _ : Fin n => SAP.P037a.uniformDraw) =
    Measure.pi (fun _ : Fin n => Causalean.Stat.OrderStatistic.uniform01)
  congr 1
  funext i
  change volume.restrict (Ioo (0 : ℝ) 1) = volume.restrict (Icc 0 1)
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc

private theorem sortedSample_aemeasurable (n : ℕ) :
    AEMeasurable (Causalean.Stat.OrderStatistic.sortedSample n)
      (volume : Measure (Fin n → ℝ)) := by
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
      AEMeasurable (Causalean.Stat.OrderStatistic.sortedSample n)
        (volume.restrict (s σ)) := by
    have hp : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
    apply hp.aemeasurable.congr
    exact ae_restrict_of_forall_mem (hs σ) (fun x hx =>
      (show (fun x => x ∘ σ) x = Causalean.Stat.OrderStatistic.sortedSample n x from
        (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hx))
  simpa only [hcover, Measure.restrict_univ] using (AEMeasurable.iUnion hpiece)

private theorem firstSpacings_aemeasurable (m : ℕ) :
    AEMeasurable (SAP.P037a.firstSpacingsW2 m)
      (SAP.P037a.uniformInputW2 m) := by
  have hsort : AEMeasurable (Causalean.Stat.OrderStatistic.sortedSample m)
      (SAP.P037a.uniformInputW2 m) := by
    rw [uniformInput_eq_closedProduct, Causalean.Stat.OrderStatistic.iid_uniform_cube_law]
    exact (sortedSample_aemeasurable m).restrict
  have hd := Causalean.Stat.OrderStatistic.orderedSpacings_measurePreserving m
  have hfun : SAP.P037a.firstSpacingsW2 m =
      Causalean.Stat.OrderStatistic.orderedSpacings m ∘
        Causalean.Stat.OrderStatistic.sortedSample m := by
    funext x
    exact Causalean.Stat.OrderStatistic.firstNSpacings_eq_orderedSpacings m x
  rw [hfun]
  exact hd.measurable.comp_aemeasurable hsort

private theorem firstSpacings_open_law (hvol : SAP.P037a.simplexVolumeFactsW2)
    (m : ℕ) :
    Measure.map (SAP.P037a.firstSpacingsW2 m) (SAP.P037a.uniformInputW2 m) =
      (m.factorial : ℝ≥0∞) • volume.restrict (SAP.P037a.openSimplex m) := by
  rw [uniformInput_eq_closedProduct]
  change Measure.map (Causalean.Stat.OrderStatistic.firstNSpacings m)
      (Causalean.Stat.OrderStatistic.iidSample
        Causalean.Stat.OrderStatistic.uniform01 m) = _
  rw [Causalean.Stat.OrderStatistic.uniform_firstN_spacings_law m]
  change (m.factorial : ℝ≥0∞) •
      volume.restrict (SAP.P037a.closedSimplexW2 m) = _
  rw [(hvol m).1]

private theorem prefix_sum_step {m : ℕ} (q : Fin (m+1) → ℝ)
    (i : Fin m) :
    Causalean.Stat.OrderStatistic.prefixCoordinates (m+1) q i.succ =
      Causalean.Stat.OrderStatistic.prefixCoordinates (m+1) q i.castSucc + q i.succ := by
  have hset : Finset.Iio (i.succ : Fin (m+1)) = Finset.Iic i.castSucc := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def,
      Fin.val_succ, Fin.val_castSucc]
    omega
  have hsum := Finset.sum_Iio_add_eq_sum_Iic (f := q) (i.succ : Fin (m+1))
  rw [hset] at hsum
  simpa [Causalean.Stat.OrderStatistic.prefixCoordinates] using hsum.symm

private theorem sorted_spacings_facts (k : ℕ) (x : Fin (k+1) → ℝ)
    (hq : SAP.P037a.firstSpacingsW2 (k+1) x ∈ SAP.P037a.openSimplex (k+1)) :
    StrictMono (SAP.P037a.sortedSampleW2 (k+1) x) ∧
    (∀ i, SAP.P037a.sortedSampleW2 (k+1) x i ∈ Ioo 0 1) ∧
    SAP.P037a.allSpacingsW2 (k+1) x (Fin.last (k+1)) =
      1 - SAP.P037a.sortedSampleW2 (k+1) x (Fin.last k) ∧
    (∀ i, 0 < SAP.P037a.allSpacingsW2 (k+1) x i) ∧
    ∑ i, SAP.P037a.allSpacingsW2 (k+1) x i = 1 := by
  let q := SAP.P037a.firstSpacingsW2 (k+1) x
  have hqpos : ∀ i, 0 < q i := hq.1
  have hqsum : ∑ i, q i < 1 := hq.2
  have hprefix :
      Causalean.Stat.OrderStatistic.prefixCoordinates (k+1) q =
        SAP.P037a.sortedSampleW2 (k+1) x := by
    change Causalean.Stat.OrderStatistic.prefixCoordinates (k+1)
        (Causalean.Stat.OrderStatistic.firstNSpacings (k+1) x) =
      Causalean.Stat.OrderStatistic.sortedSample (k+1) x
    rw [Causalean.Stat.OrderStatistic.firstNSpacings_eq_orderedSpacings]
    exact Causalean.Stat.OrderStatistic.prefixCoordinates_orderedSpacings (k+1)
      (Causalean.Stat.OrderStatistic.sortedSample (k+1) x)
  have hstrict : StrictMono (SAP.P037a.sortedSampleW2 (k+1) x) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    rw [← congrFun hprefix i.castSucc, ← congrFun hprefix i.succ]
    rw [prefix_sum_step q i]
    exact lt_add_of_pos_right _ (hqpos i.succ)
  have hinner : ∀ i, SAP.P037a.sortedSampleW2 (k+1) x i ∈ Ioo 0 1 := by
    intro i
    have hle : (∑ j ∈ Finset.Iic i, q j) ≤ ∑ j, q j :=
      Finset.sum_le_univ_sum_of_nonneg (fun j => (hqpos j).le)
    constructor
    · rw [← congrFun hprefix i]
      exact Finset.sum_pos (fun j _ => hqpos j) ⟨i, by simp⟩
    · rw [← congrFun hprefix i]
      exact lt_of_le_of_lt hle hqsum
  have hsumlast : ∑ i, q i = SAP.P037a.sortedSampleW2 (k+1) x (Fin.last k) := by
    have hlast := congrFun hprefix (Fin.last k)
    have hset : Finset.Iic (Fin.last k : Fin (k+1)) = Finset.univ := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last i
    simpa [Causalean.Stat.OrderStatistic.prefixCoordinates, hset] using hlast
  have hgap : SAP.P037a.allSpacingsW2 (k+1) x (Fin.last (k+1)) =
      1 - SAP.P037a.sortedSampleW2 (k+1) x (Fin.last k) := by
    rw [SAP.P037a.allSpacingsW2, SAP.P037a.WH.W2.append_lastW2, hsumlast]
  exact ⟨hstrict, hinner, hgap,
    SAP.P037a.WH.W2.positive_appendW2 (k+1) q hq,
    SAP.P037a.WH.W2.sum_appendW2 (k+1) q⟩

end SAP.P037a.WH.W2.P.T5_L7

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

theorem SAP.P037a.WH.W2.T5_L7_proof : SAP.P037a.WH.W2.T5_L7 := by
  intro hvol k
  have hfirst := SAP.P037a.WH.W2.P.T5_L7.firstSpacings_open_law hvol (k+1)
  have hfirst_meas := SAP.P037a.WH.W2.P.T5_L7.firstSpacings_aemeasurable (k+1)
  have hmap : Measure.map (SAP.P037a.allSpacingsW2 (k+1))
      (SAP.P037a.uniformInputW2 (k+1)) = SAP.P037a.simplexLaw (k+1) := by
    change Measure.map
        (SAP.P037a.appendSimplex (k+1) ∘ SAP.P037a.firstSpacingsW2 (k+1))
        (SAP.P037a.uniformInputW2 (k+1)) = _
    rw [← AEMeasurable.map_map_of_aemeasurable
      (SAP.P037a.WH.W2.measurable_appendW2 (k+1)).aemeasurable hfirst_meas,
      hfirst]
    rfl
  refine ⟨hmap, ?_⟩
  have hq : ∀ᵐ q ∂Measure.map (SAP.P037a.firstSpacingsW2 (k+1))
      (SAP.P037a.uniformInputW2 (k+1)), q ∈ SAP.P037a.openSimplex (k+1) := by
    rw [hfirst]
    exact Measure.ae_smul_measure
      (ae_restrict_mem (SAP.P037a.WH.W2.measurable_openSimplexW2 (k+1))) _
  have hx := MeasureTheory.ae_of_ae_map hfirst_meas hq
  filter_upwards [hx] with x hx
  exact SAP.P037a.WH.W2.P.T5_L7.sorted_spacings_facts k x hx
