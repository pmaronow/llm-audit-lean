import SAP.P029b.WH.W2.Leaves
import AronowAudit.P015.P015_ConvergenceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2.P.T27_L5

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

private instance : IsProbabilityMeasure cancelLawW2 := by
  unfold cancelLawW2
  infer_instance

private instance : IsProbabilityMeasure cancelSampleLawW2 := by
  unfold cancelSampleLawW2
  infer_instance

private lemma rate_error_tendsto (hcells : CancellationCellLimitsW2)
    (x z : Bool) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => cancelSampleLawW2
      {ω | ε ≤ dist (cancelRateW2 n ω x z) (if z then 2/3 else 1/3)})
      atTop (𝓝 0) := by
  exact (tendstoInMeasure_iff_dist.mp (hcells x z).2) ε hε

private def rateBad (n : ℕ) : Set CancelSpaceW2 :=
  ⋃ x : Bool, ⋃ z : Bool,
    {ω | (1 / 12 : ℝ) ≤ dist (cancelRateW2 n ω x z) (if z then 2/3 else 1/3)}

private lemma rateBad_measure_tendsto (hcells : CancellationCellLimitsW2) :
    Tendsto (fun n => cancelSampleLawW2 (rateBad n)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n =>
      ∑ x : Bool, ∑ z : Bool, cancelSampleLawW2
        {ω | (1 / 12 : ℝ) ≤ dist (cancelRateW2 n ω x z)
          (if z then 2/3 else 1/3)}) atTop (𝓝 0) := by
    have hz (x : Bool) : Tendsto (fun n => ∑ z : Bool, cancelSampleLawW2
        {ω | (1 / 12 : ℝ) ≤ dist (cancelRateW2 n ω x z)
          (if z then 2/3 else 1/3)}) atTop (𝓝 0) := by
      have h := tendsto_finsetSum Finset.univ (fun z _ =>
        rate_error_tendsto hcells x z (1 / 12) (by norm_num))
      simpa using h
    have h := tendsto_finsetSum Finset.univ (fun x _ => hz x)
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  unfold rateBad
  calc
    cancelSampleLawW2 (⋃ x : Bool, ⋃ z : Bool,
        {ω | (1 / 12 : ℝ) ≤ dist (cancelRateW2 n ω x z)
          (if z then 2/3 else 1/3)})
      ≤ ∑ x : Bool, cancelSampleLawW2 (⋃ z : Bool,
        {ω | (1 / 12 : ℝ) ≤ dist (cancelRateW2 n ω x z)
          (if z then 2/3 else 1/3)}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ x : Bool, ∑ z : Bool, cancelSampleLawW2
        {ω | (1 / 12 : ℝ) ≤ dist (cancelRateW2 n ω x z)
          (if z then 2/3 else 1/3)} := by
      apply Finset.sum_le_sum
      intro x hx
      exact measure_iUnion_fintype_le _ _

private lemma fit_good_measure_tendsto (hcells : CancellationCellLimitsW2) :
    Tendsto (fun n => cancelSampleLawW2 {ω | cancelFitGoodW2 n ω})
      atTop (𝓝 1) := by
  let good : ℕ → Set CancelSpaceW2 := fun n => {ω | cancelFitGoodW2 n ω}
  have hgmeas (n : ℕ) : MeasurableSet (good n) := by
    simp only [good, cancelFitGoodW2, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro x
    exact (measurableSet_lt measurable_const (cancel_rate_measurable n x false)).inter
      ((measurableSet_lt (cancel_rate_measurable n x false) (cancel_rate_measurable n x true)).inter
        (measurableSet_lt (cancel_rate_measurable n x true) measurable_const))
  have hsub (n : ℕ) : (good n)ᶜ ⊆ rateBad n := by
    intro ω hω
    by_contra hb
    have hnear (x z : Bool) :
        dist (cancelRateW2 n ω x z) (if z then 2/3 else 1/3) < (1/12 : ℝ) := by
      have hn : ω ∉ {ω | (1 / 12 : ℝ) ≤
          dist (cancelRateW2 n ω x z) (if z then 2/3 else 1/3)} := by
        intro hh
        apply hb
        exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨z, hh⟩⟩
      exact lt_of_not_ge hn
    have hgood : cancelFitGoodW2 n ω := by
      intro x
      have h0 := hnear x false
      have h1 := hnear x true
      simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h1
      have h0' : |cancelRateW2 n ω x false - (1 / 3 : ℝ)| < 1 / 12 := by
        simpa [Real.dist_eq] using h0
      have h1' : |cancelRateW2 n ω x true - (2 / 3 : ℝ)| < 1 / 12 := by
        simpa [Real.dist_eq] using h1
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · have hlo := (abs_lt.mp h0').1
        nlinarith
      · have hhi := (abs_lt.mp h0').2
        have hlo := (abs_lt.mp h1').1
        nlinarith
      · have hhi := (abs_lt.mp h1').2
        nlinarith
    exact hω hgood
  have hcompl : Tendsto (fun n => cancelSampleLawW2 (good n)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (rateBad_measure_tendsto hcells) (fun _ => zero_le)
    intro n
    exact measure_mono (hsub n)
  have hgood_eq (n : ℕ) : cancelSampleLawW2 (good n) =
      1 - cancelSampleLawW2 (good n)ᶜ := by
    have hc := measure_compl (hgmeas n).compl (measure_ne_top cancelSampleLawW2 (good n)ᶜ)
    simpa [measure_univ] using hc
  change Tendsto (fun n => cancelSampleLawW2 (good n)) atTop (𝓝 1)
  rw [show (fun n => cancelSampleLawW2 (good n)) =
      (fun n => 1 - cancelSampleLawW2 (good n)ᶜ) by funext n; exact hgood_eq n]
  have hlim := (ENNReal.continuous_sub_left
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).continuousAt.tendsto.comp hcompl
  convert hlim using 1
  · funext n
    rfl
  · simp

private lemma score_error_tendsto (hcells : CancellationCellLimitsW2) (i : ℕ) :
    TendstoInMeasure cancelSampleLawW2 (fun n => cancelFittedScoreW2 n i)
      atTop (fun _ => (1 / 3 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hdelta (x : Bool) : TendstoInMeasure cancelSampleLawW2
      (fun n ω => cancelRateW2 n ω x true - cancelRateW2 n ω x false)
      atTop (fun _ => (1 / 3 : ℝ)) := by
    have ht := AronowAudit.P015.ConvergenceCompletion.sub_limit cancelSampleLawW2
      (hcells x true).2 (hcells x false).2
    convert ht using 1 <;> norm_num
  have hx (x : Bool) : Tendsto (fun n => cancelSampleLawW2
      {ω | ε ≤ dist (cancelRateW2 n ω x true - cancelRateW2 n ω x false)
        (1 / 3 : ℝ)}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.mp (hdelta x)) ε hε
  have hsum : Tendsto (fun n => ∑ x : Bool, cancelSampleLawW2
      {ω | ε ≤ dist (cancelRateW2 n ω x true - cancelRateW2 n ω x false)
        (1 / 3 : ℝ)}) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun x _ => hx x)
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  calc
    cancelSampleLawW2 {ω | ε ≤ dist (cancelFittedScoreW2 n i ω) (1 / 3 : ℝ)}
      ≤ cancelSampleLawW2 (⋃ x : Bool,
        {ω | ε ≤ dist (cancelRateW2 n ω x true - cancelRateW2 n ω x false)
          (1 / 3 : ℝ)}) := by
        apply measure_mono
        intro ω hω
        by_contra hn
        have hgood : cancelFitGoodW2 n ω := by
          by_contra hg
          have hs : cancelFittedScoreW2 n i ω = 1 / 3 := by
            simp [cancelFittedScoreW2, hg]
          have he : ε ≤ 0 := by simpa [hs] using hω
          linarith
        have hmem : ω ∈ ⋃ x : Bool,
            {ω | ε ≤ dist (cancelRateW2 n ω x true - cancelRateW2 n ω x false)
              (1 / 3 : ℝ)} := by
          simp only [Set.mem_iUnion]
          refine ⟨(ω i).1.1, ?_⟩
          simpa [cancelFittedScoreW2, hgood] using hω
        exact hn hmem
    _ ≤ ∑ x : Bool, cancelSampleLawW2
        {ω | ε ≤ dist (cancelRateW2 n ω x true - cancelRateW2 n ω x false)
          (1 / 3 : ℝ)} := measure_iUnion_fintype_le _ _

private def cellObservation (n : ℕ) (ω : CancelSpaceW2) (x z t : Bool) : ℝ :=
  if t then cancelRateW2 n ω x z else cancelCellFractionW2 n ω x z

private def cellObservationLimit (z t : Bool) : ℝ :=
  if t then (if z then 2/3 else 1/3) else 1/4

private lemma cell_observation_tendsto (hcells : CancellationCellLimitsW2)
    (x z t : Bool) :
    TendstoInMeasure cancelSampleLawW2 (fun n ω => cellObservation n ω x z t)
      atTop (fun _ => cellObservationLimit z t) := by
  cases t
  · simpa [cellObservation, cellObservationLimit] using (hcells x z).1
  · simpa [cellObservation, cellObservationLimit] using (hcells x z).2

private def cellBad (n : ℕ) : Set CancelSpaceW2 :=
  ⋃ x : Bool, ⋃ z : Bool, ⋃ t : Bool,
    {ω | (1 / 100 : ℝ) ≤ dist (cellObservation n ω x z t)
      (cellObservationLimit z t)}

private def cellCentral (n : ℕ) : Set CancelSpaceW2 := (cellBad n)ᶜ

private lemma cell_bad_measure_tendsto (hcells : CancellationCellLimitsW2) :
    Tendsto (fun n => cancelSampleLawW2 (cellBad n)) atTop (𝓝 0) := by
  have herror (x z t : Bool) : Tendsto (fun n => cancelSampleLawW2
      {ω | (1 / 100 : ℝ) ≤ dist (cellObservation n ω x z t)
        (cellObservationLimit z t)}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.mp (cell_observation_tendsto hcells x z t))
      (1 / 100) (by norm_num)
  have ht (x z : Bool) : Tendsto (fun n => ∑ t : Bool, cancelSampleLawW2
      {ω | (1 / 100 : ℝ) ≤ dist (cellObservation n ω x z t)
        (cellObservationLimit z t)}) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun t _ => herror x z t)
    simpa using h
  have hz (x : Bool) : Tendsto (fun n => ∑ z : Bool, ∑ t : Bool,
      cancelSampleLawW2 {ω | (1 / 100 : ℝ) ≤
        dist (cellObservation n ω x z t) (cellObservationLimit z t)}) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun z _ => ht x z)
    simpa using h
  have hsum : Tendsto (fun n => ∑ x : Bool, ∑ z : Bool, ∑ t : Bool,
      cancelSampleLawW2 {ω | (1 / 100 : ℝ) ≤
        dist (cellObservation n ω x z t) (cellObservationLimit z t)}) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun x _ => hz x)
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  calc
    cancelSampleLawW2 (cellBad n) ≤
      ∑ x : Bool, cancelSampleLawW2 (⋃ z : Bool, ⋃ t : Bool,
        {ω | (1 / 100 : ℝ) ≤ dist (cellObservation n ω x z t)
          (cellObservationLimit z t)}) := by
        unfold cellBad
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ x : Bool, ∑ z : Bool, cancelSampleLawW2 (⋃ t : Bool,
        {ω | (1 / 100 : ℝ) ≤ dist (cellObservation n ω x z t)
          (cellObservationLimit z t)}) := by
        apply Finset.sum_le_sum
        intro x hx
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ x : Bool, ∑ z : Bool, ∑ t : Bool, cancelSampleLawW2
        {ω | (1 / 100 : ℝ) ≤ dist (cellObservation n ω x z t)
          (cellObservationLimit z t)} := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro z hz
        exact measure_iUnion_fintype_le _ _

private lemma cancel_fraction_measurable (n : ℕ) (x z : Bool) :
    Measurable (fun ω => cancelCellFractionW2 n ω x z) := by
  apply Measurable.div
  · apply Finset.measurable_sum
    intro i _
    exact (Measurable.of_discrete : Measurable (fun a : CancelAtomW2 =>
      if a.1.1 = x ∧ a.2 = z then (1 : ℝ) else 0)).comp
        (measurable_pi_apply i.val)
  · exact measurable_const

private lemma cell_observation_measurable (n : ℕ) (x z t : Bool) :
    Measurable (fun ω => cellObservation n ω x z t) := by
  cases t
  · exact cancel_fraction_measurable n x z
  · exact cancel_rate_measurable n x z

private lemma cell_bad_measurable (n : ℕ) : MeasurableSet (cellBad n) := by
  unfold cellBad
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro z
  apply MeasurableSet.iUnion
  intro t
  exact measurableSet_le measurable_const
    ((cell_observation_measurable n x z t).dist measurable_const)

private lemma cell_central_measure_tendsto (hcells : CancellationCellLimitsW2) :
    Tendsto (fun n => cancelSampleLawW2 (cellCentral n)) atTop (𝓝 1) := by
  have hcentral_eq (n : ℕ) : cancelSampleLawW2 (cellCentral n) =
      1 - cancelSampleLawW2 (cellBad n) := by
    have hc := measure_compl (cell_bad_measurable n)
      (measure_ne_top cancelSampleLawW2 (cellBad n))
    simpa [cellCentral, measure_univ] using hc
  change Tendsto (fun n => cancelSampleLawW2 (cellCentral n)) atTop (𝓝 1)
  rw [show (fun n => cancelSampleLawW2 (cellCentral n)) =
      (fun n => 1 - cancelSampleLawW2 (cellBad n)) by
        funext n
        exact hcentral_eq n]
  have hlim := (ENNReal.continuous_sub_left
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).continuousAt.tendsto.comp
      (cell_bad_measure_tendsto hcells)
  convert hlim using 1
  · funext n
    rfl
  · simp

private def cellCount (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) : ℝ :=
  ∑ i : Fin (n+1),
    if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0

private def cellSuccess (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) : ℝ :=
  ∑ i : Fin (n+1),
    if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then
      bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0

private def armWeightMass (n : ℕ) (ω : CancelSpaceW2) (z : Bool) : ℝ :=
  ∑ i : Fin (n+1),
    (1 / cancelFittedScoreW2 n i.val ω) *
      (if cancelZW2 i.val ω = z then (1 : ℝ) else 0)

private def armReceiptMass (n : ℕ) (ω : CancelSpaceW2) (z : Bool) : ℝ :=
  ∑ i : Fin (n+1),
    (1 / cancelFittedScoreW2 n i.val ω) *
      (if cancelZW2 i.val ω = z then
        bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0)

private lemma central_rate_close {n : ℕ} {ω : CancelSpaceW2}
    (hω : ω ∈ cellCentral n) (x z : Bool) :
    dist (cancelRateW2 n ω x z) (if z then 2/3 else 1/3) < (1 / 100 : ℝ) := by
  have hn : ω ∉ cellBad n := hω
  by_contra hnot
  apply hn
  unfold cellBad
  have hlarge : (1 / 100 : ℝ) ≤
      dist (cancelRateW2 n ω x z) (if z then 2/3 else 1/3) := le_of_not_gt hnot
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨z,
    Set.mem_iUnion.mpr ⟨true, by simpa [cellObservation, cellObservationLimit] using hlarge⟩⟩⟩

private lemma central_fraction_close {n : ℕ} {ω : CancelSpaceW2}
    (hω : ω ∈ cellCentral n) (x z : Bool) :
    dist (cancelCellFractionW2 n ω x z) (1 / 4 : ℝ) < (1 / 100 : ℝ) := by
  have hn : ω ∉ cellBad n := hω
  by_contra hnot
  apply hn
  unfold cellBad
  have hlarge : (1 / 100 : ℝ) ≤
      dist (cancelCellFractionW2 n ω x z) (1 / 4 : ℝ) := le_of_not_gt hnot
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨z,
    Set.mem_iUnion.mpr ⟨false, by simpa [cellObservation, cellObservationLimit] using hlarge⟩⟩⟩

private lemma cell_count_pos {n : ℕ} {ω : CancelSpaceW2}
    (hω : ω ∈ cellCentral n) (x z : Bool) : 0 < cellCount n ω x z := by
  have hf := central_fraction_close hω x z
  have habs : |cancelCellFractionW2 n ω x z - (1 / 4 : ℝ)| < 1 / 100 := by
    simpa [Real.dist_eq] using hf
  have hlow : (24 / 100 : ℝ) < cancelCellFractionW2 n ω x z := by
    have h := (abs_lt.mp habs).1
    norm_num at h ⊢
    linarith
  have hfrac : cancelCellFractionW2 n ω x z = cellCount n ω x z / (n + 1 : ℝ) := by
    rfl
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hmul := (lt_div_iff₀ hN).mp (by simpa [hfrac] using hlow)
  nlinarith

private lemma arm_weight_mass_cells {n : ℕ} {ω : CancelSpaceW2} {z : Bool}
    (hfit : cancelFitGoodW2 n ω) :
    armWeightMass n ω z =
      ∑ x : Bool, cellCount n ω x z /
        (cancelRateW2 n ω x true - cancelRateW2 n ω x false) := by
  have hpoint (i : Fin (n+1)) :
      (1 / cancelFittedScoreW2 n i.val ω) *
        (if cancelZW2 i.val ω = z then (1 : ℝ) else 0) =
      ∑ x : Bool, if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
        1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false) else 0 := by
    cases hx : (ω i.val).1.1 <;> cases hz : cancelZW2 i.val ω <;> cases z <;>
      simp [cancelFittedScoreW2, hfit, hx, hz]
  calc
    armWeightMass n ω z = ∑ i : Fin (n+1), ∑ x : Bool,
        if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
          1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false) else 0 := by
      unfold armWeightMass
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = ∑ x : Bool, ∑ i : Fin (n+1),
        if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
          1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false) else 0 :=
      Finset.sum_comm
    _ = ∑ x : Bool, cellCount n ω x z /
        (cancelRateW2 n ω x true - cancelRateW2 n ω x false) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
            1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false) else 0)
          = (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧
              cancelZW2 i.val ω = z then (1 : ℝ) else 0) *
              (1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                split_ifs <;> simp
        _ = cellCount n ω x z /
            (cancelRateW2 n ω x true - cancelRateW2 n ω x false) := by
              have hd : cancelRateW2 n ω x true - cancelRateW2 n ω x false ≠ 0 := by
                have hx := hfit x
                linarith [hx.1, hx.2.1]
              have hcnt :
                  (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧
                    cancelZW2 i.val ω = z then (1 : ℝ) else 0) =
                    cellCount n ω x z := by
                unfold cellCount
                apply Finset.sum_congr rfl
                intro i hi
                rfl
              rw [hcnt]
              field_simp [hd]

private lemma arm_receipt_mass_cells {n : ℕ} {ω : CancelSpaceW2} {z : Bool}
    (hfit : cancelFitGoodW2 n ω) :
    armReceiptMass n ω z =
      ∑ x : Bool, cellSuccess n ω x z /
        (cancelRateW2 n ω x true - cancelRateW2 n ω x false) := by
  have hpoint (i : Fin (n+1)) :
      (1 / cancelFittedScoreW2 n i.val ω) *
        (if cancelZW2 i.val ω = z then
          bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0) =
      ∑ x : Bool, if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
        (1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) *
          bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0 := by
    cases hx : (ω i.val).1.1 <;> cases hz : cancelZW2 i.val ω <;> cases z <;>
      simp [cancelFittedScoreW2, hfit, hx, hz]
  calc
    armReceiptMass n ω z = ∑ i : Fin (n+1), ∑ x : Bool,
        if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
          (1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) *
            bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0 := by
      unfold armReceiptMass
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = ∑ x : Bool, ∑ i : Fin (n+1),
        if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
          (1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) *
            bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0 :=
      Finset.sum_comm
    _ = ∑ x : Bool, cellSuccess n ω x z /
        (cancelRateW2 n ω x true - cancelRateW2 n ω x false) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ cancelZW2 i.val ω = z then
            (1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) *
              bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0)
          = (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧
              cancelZW2 i.val ω = z then
                bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0) *
              (1 / (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                split_ifs <;> simp [mul_comm]
        _ = cellSuccess n ω x z /
            (cancelRateW2 n ω x true - cancelRateW2 n ω x false) := by
              have hd : cancelRateW2 n ω x true - cancelRateW2 n ω x false ≠ 0 := by
                have hx := hfit x
                linarith [hx.1, hx.2.1]
              have hsucc :
                  (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧
                    cancelZW2 i.val ω = z then
                      bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0) =
                    cellSuccess n ω x z := by
                unfold cellSuccess
                apply Finset.sum_congr rfl
                intro i hi
                rfl
              rw [hsucc]
              field_simp [hd]

private lemma cell_success_eq_rate_mul_count {n : ℕ} {ω : CancelSpaceW2}
    (hω : ω ∈ cellCentral n) (x z : Bool) :
    cellSuccess n ω x z = cancelRateW2 n ω x z * cellCount n ω x z := by
  have hc := cell_count_pos hω x z
  calc
    cellSuccess n ω x z =
        (cellSuccess n ω x z / cellCount n ω x z) * cellCount n ω x z := by
          field_simp [ne_of_gt hc]
    _ = cancelRateW2 n ω x z * cellCount n ω x z := by rfl

private lemma arm_receipt_mass_weighted_rates {n : ℕ} {ω : CancelSpaceW2}
    (hω : ω ∈ cellCentral n) (hfit : cancelFitGoodW2 n ω) (z : Bool) :
    armReceiptMass n ω z =
      ∑ x : Bool, cancelRateW2 n ω x z *
        (cellCount n ω x z /
          (cancelRateW2 n ω x true - cancelRateW2 n ω x false)) := by
  rw [arm_receipt_mass_cells hfit]
  apply Finset.sum_congr rfl
  intro x hx
  rw [cell_success_eq_rate_mul_count hω x z]
  have hd : cancelRateW2 n ω x true - cancelRateW2 n ω x false ≠ 0 := by
    have hfitx := hfit x
    linarith [hfitx.1, hfitx.2.1]
  field_simp [hd]
  <;> ring

private lemma arm_means_eq_masses (n : ℕ) (ω : CancelSpaceW2) (z : Bool) :
    sampleArm (fun i : Fin (n+1) => 1 / cancelFittedScoreW2 n i.val ω)
      (fun i => bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)))
      (fun i => cancelZW2 i.val ω) z =
    armReceiptMass n ω z / armWeightMass n ω z := by
  rfl

private lemma cell_central_defined {n : ℕ} {ω : CancelSpaceW2}
    (hω : ω ∈ cellCentral n) :
    SampleDefined (fun i : Fin (n+1) => 1 / cancelFittedScoreW2 n i.val ω)
      (fun i => (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω))
      (fun i => cancelZW2 i.val ω) := by
  have hrate_bounds (x : Bool) :
      0 < cancelRateW2 n ω x false ∧ cancelRateW2 n ω x false < 1/2 ∧
      1/2 < cancelRateW2 n ω x true ∧ cancelRateW2 n ω x true < 1 := by
    have h0 := central_rate_close hω x false
    have h1 := central_rate_close hω x true
    have ha0 : |cancelRateW2 n ω x false - (1 / 3 : ℝ)| < 1 / 100 := by
      simpa [Real.dist_eq] using h0
    have ha1 : |cancelRateW2 n ω x true - (2 / 3 : ℝ)| < 1 / 100 := by
      simpa [Real.dist_eq] using h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hl := (abs_lt.mp ha0).1
      norm_num at hl ⊢
      linarith
    · have hh := (abs_lt.mp ha0).2
      norm_num at hh ⊢
      linarith
    · have hl := (abs_lt.mp ha1).1
      norm_num at hl ⊢
      linarith
    · have hh := (abs_lt.mp ha1).2
      norm_num at hh ⊢
      linarith
  have hfit : cancelFitGoodW2 n ω := by
    intro x
    have hb := hrate_bounds x
    refine ⟨hb.1, ?_, hb.2.2.2⟩
    linarith [hb.2.1, hb.2.2.1]
  have hscorepos (x : Bool) :
      0 < cancelRateW2 n ω x true - cancelRateW2 n ω x false := by
    have hb := hrate_bounds x
    linarith [hb.2.1, hb.2.2.1]
  have hdenom (z : Bool) : 0 < armWeightMass n ω z := by
    rw [arm_weight_mass_cells hfit]
    apply Finset.sum_pos
    · intro x hx
      exact div_pos (cell_count_pos hω x z) (hscorepos x)
    · exact Finset.univ_nonempty
  have htreated :
      (1 / 2 : ℝ) < armReceiptMass n ω true / armWeightMass n ω true := by
    apply (lt_div_iff₀ (hdenom true)).2
    rw [arm_receipt_mass_weighted_rates hω hfit true,
      arm_weight_mass_cells hfit]
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro x hx
    exact mul_lt_mul_of_pos_right (hrate_bounds x).2.2.1
      (div_pos (cell_count_pos hω x true) (hscorepos x))
  have hcontrol :
      armReceiptMass n ω false / armWeightMass n ω false < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (hdenom false)).2
    rw [arm_receipt_mass_weighted_rates hω hfit false,
      arm_weight_mass_cells hfit]
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro x hx
    exact mul_lt_mul_of_pos_right (hrate_bounds x).2.1
      (div_pos (cell_count_pos hω x false) (hscorepos x))
  unfold SampleDefined
  refine ⟨?_, ?_⟩
  · intro z
    change armWeightMass n ω z ≠ 0
    exact ne_of_gt (hdenom z)
  · rw [arm_means_eq_masses n ω true, arm_means_eq_masses n ω false]
    linarith [htreated, hcontrol]


end
end SAP.P029b.WH.W2.P.T27_L5

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

theorem SAP.P029b.WH.W2.T27_L5_proof : SAP.P029b.WH.W2.T27_L5 := by
  intro hcells
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact SAP.P029b.WH.W2.P.T27_L5.score_error_tendsto hcells i
  · exact SAP.P029b.WH.W2.P.T27_L5.fit_good_measure_tendsto hcells
  · have hsubset (n : ℕ) : SAP.P029b.WH.W2.P.T27_L5.cellCentral n ⊆ {ω |
        SampleDefined (fun i : Fin (n+1) => 1/cancelFittedScoreW2 n i.val ω)
          (fun i => (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω))
          (fun i => cancelZW2 i.val ω)} := by
      intro ω hω
      exact SAP.P029b.WH.W2.P.T27_L5.cell_central_defined hω
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (SAP.P029b.WH.W2.P.T27_L5.cell_central_measure_tendsto hcells)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1))
      (fun n => measure_mono (hsubset n))
    intro n
    calc
      cancelSampleLawW2 {ω |
          SampleDefined (fun i : Fin (n+1) => 1/cancelFittedScoreW2 n i.val ω)
            (fun i => (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω))
            (fun i => cancelZW2 i.val ω)}
        ≤ cancelSampleLawW2 Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
