import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L3

open MeasureTheory
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

open SAP.P004b

theorem rectangle_closed (a b c d : ℝ) :
    IsClosed (SAP.P004b.rectangle a b c d) := by
  change IsClosed ({x : EuclideanSpace ℝ (Fin 2) | a ≤ x 0} ∩
    ({x | x 0 ≤ b} ∩ ({x | c ≤ x 1} ∩ {x | x 1 ≤ d})))
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
    ((isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) continuous_const).inter
      ((isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).inter
        (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const)))

theorem family_node_closed (L : ℝ) (hL : 2 ≤ L) (i : Fin 3) :
    IsClosed ((SAP.P004b.polygonRangeFamily L hL).node i) := by
  fin_cases i <;> exact rectangle_closed _ _ _ _

theorem family_region (L : ℝ) (hL : 2 ≤ L) (i : Fin 3) :
    region (SAP.P004b.polygonRangeFamily L hL) i 0 =
      (SAP.P004b.polygonRangeFamily L hL).node i := by
  ext x
  change Metric.infDist x ((SAP.P004b.polygonRangeFamily L hL).node i) ∈ Set.Icc 0 0 ↔ _
  rw [Set.Icc_self, Set.mem_singleton_iff]
  exact ((family_node_closed L hL i).mem_iff_infDist_zero
    ((SAP.P004b.polygonRangeFamily L hL).node_nonempty i)).symm

theorem family_node_mass (L : ℝ) (hL : 2 ≤ L) (i : Fin 3) :
    volume ((SAP.P004b.polygonRangeFamily L hL).node i) =
      if i = 2 then ENNReal.ofReal (L+1) else 1 := by
  fin_cases i
  · change volume (AronowAudit.P004.rectangle 0 1 0 1) = 1
    rw [AronowAudit.P004.Wave1.spacing_rectangle_volume 0 1 0 1 (by norm_num) (by norm_num)]
    norm_num
  · change volume (AronowAudit.P004.rectangle L (L+1) 0 1) = 1
    rw [AronowAudit.P004.Wave1.spacing_rectangle_volume L (L+1) 0 1 (by linarith) (by norm_num)]
    have harea : ((L+1)-L)*(1-0) = 1 := by ring
    rw [harea]
    norm_num
  · change volume (AronowAudit.P004.rectangle 0 (L+1) 2 3) = ENNReal.ofReal (L+1)
    rw [AronowAudit.P004.Wave1.spacing_rectangle_volume 0 (L+1) 2 3 (by linarith) (by norm_num)]
    have harea : ((L+1)-0)*(3-2) = L+1 := by ring
    rw [harea]

theorem family_node_mass_pos (L : ℝ) (hL : 2 ≤ L) (i : Fin 3) :
    0 < volume ((SAP.P004b.polygonRangeFamily L hL).node i) := by
  rw [family_node_mass L hL i]
  split_ifs
  · exact ENNReal.ofReal_pos.mpr (by linarith)
  · norm_num

theorem family_node_mass_finite (L : ℝ) (hL : 2 ≤ L) (i : Fin 3) :
    volume ((SAP.P004b.polygonRangeFamily L hL).node i) < ⊤ := by
  rw [family_node_mass L hL i]
  split_ifs <;> simp

theorem family_outcome_on_node (L : ℝ) (hL : 2 ≤ L) (i : Fin 3)
    (z : Assignment 3) (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ (SAP.P004b.polygonRangeFamily L hL).node i) :
    (SAP.P004b.polygonRangeFamily L hL).outcome x z =
      if i = 2 then 0 else bit (z 2) := by
  fin_cases i
  · change x ∈ SAP.P004b.rectangle 0 1 0 1 at hx
    simp [SAP.P004b.polygonRangeFamily, hx]
  · change x ∈ SAP.P004b.rectangle L (L+1) 0 1 at hx
    simp [SAP.P004b.polygonRangeFamily, hx]
  · change x ∈ SAP.P004b.rectangle 0 (L+1) 2 3 at hx
    have hnot : x ∉ SAP.P004b.rectangle 0 1 0 1 ∪
        SAP.P004b.rectangle L (L+1) 0 1 := by
      intro h
      rcases h with h | h
      · have hlow := h.2.2.2
        have hupp := hx.2.2.1
        linarith
      · have hlow := h.2.2.2
        have hupp := hx.2.2.1
        linarith
    change (if x ∈ SAP.P004b.rectangle 0 1 0 1 ∪
      SAP.P004b.rectangle L (L+1) 0 1 then bit (z 2) else 0) = 0
    rw [if_neg hnot]

theorem family_wellDefined (L : ℝ) (hL : 2 ≤ L) :
    WellDefined (SAP.P004b.polygonRangeFamily L hL) 0 := by
  intro i
  rw [family_region L hL]
  have hmeas : MeasurableSet ((SAP.P004b.polygonRangeFamily L hL).node i) :=
    (family_node_closed L hL i).measurableSet
  refine ⟨hmeas, family_node_mass_pos L hL i, family_node_mass_finite L hL i, ?_⟩
  intro z
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) =>
      if i = 2 then (0 : ℝ) else bit (z 2))
      ((SAP.P004b.polygonRangeFamily L hL).node i) :=
    integrableOn_const (family_node_mass_finite L hL i).ne
  exact hc.congr_fun (fun x hx =>
    (family_outcome_on_node L hL i z x hx).symm) hmeas

theorem family_average (L : ℝ) (hL : 2 ≤ L) (i : Fin 3) (z : Assignment 3) :
    circleAverage (SAP.P004b.polygonRangeFamily L hL) 0 i z =
      if i = 2 then 0 else bit (z 2) := by
  have hout : Set.EqOn
      (fun x => (SAP.P004b.polygonRangeFamily L hL).outcome x z)
      (fun _ => if i = 2 then (0 : ℝ) else bit (z 2))
      ((SAP.P004b.polygonRangeFamily L hL).node i) :=
    fun x hx => family_outcome_on_node L hL i z x hx
  rw [circleAverage, family_region L hL,
    setIntegral_congr_fun (family_node_closed L hL i).measurableSet hout]
  change (∫ _ in (SAP.P004b.polygonRangeFamily L hL).node i,
      if i = 2 then (0 : ℝ) else bit (z 2)) /
      (volume ((SAP.P004b.polygonRangeFamily L hL).node i)).toReal = _
  simp only [setIntegral_const, measureReal_def, smul_eq_mul]
  exact mul_div_cancel_left₀ _ (ENNReal.toReal_ne_zero.mpr
    ⟨(ne_of_gt (family_node_mass_pos L hL i)),
      (family_node_mass_finite L hL i).ne⟩)

end
end SAP.P004b.WH.W2.P.T16_L3

theorem SAP.P004b.WH.W2.T16_L3_proof : SAP.P004b.WH.W2.T16_L3 := by
  intro L hL
  refine ⟨SAP.P004b.WH.W2.P.T16_L3.family_wellDefined L hL, ?_⟩
  intro z
  refine ⟨?_, ?_, ?_⟩
  · simpa using SAP.P004b.WH.W2.P.T16_L3.family_average L hL 0 z
  · simpa using SAP.P004b.WH.W2.P.T16_L3.family_average L hL 1 z
  · simpa using SAP.P004b.WH.W2.P.T16_L3.family_average L hL 2 z
