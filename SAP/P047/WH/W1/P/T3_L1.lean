import SAP.P047.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P047.WH.W1.P.T3_L1

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

private def b (v : ℝ) : Bool := decide (v ≤ (1 / 2 : ℝ))

private theorem nnreal_half_cast :
    ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) := by
  rw [show (1 / 2 : ℝ≥0) = 2⁻¹ by norm_num]
  exact ENNReal.coe_inv_two

private theorem fairBool_true_singleton :
    AronowAudit.P047.fairBool {true} = (1 / 2 : ℝ≥0∞) := by
  rw [AronowAudit.P047.fairBool]
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem
    (p := _) (hs := measurableSet_singleton true) (hx := by simp) (hy := by simp)]
  norm_num [unitInterval.toNNReal]
  exact nnreal_half_cast

private theorem fairBool_false_singleton :
    AronowAudit.P047.fairBool {false} = (1 / 2 : ℝ≥0∞) := by
  rw [AronowAudit.P047.fairBool]
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem
    (p := _) (hs := measurableSet_singleton false) (hx := by simp) (hy := by simp)]
  norm_num [unitInterval.toNNReal, unitInterval.symm]
  exact nnreal_half_cast

private theorem ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
  norm_num [Real.toNNReal]
  exact nnreal_half_cast

private theorem measurable_b : Measurable b := by
  exact measurable_to_bool (f := b) (by
    have hpre : b ⁻¹' ({true} : Set Bool) = Set.Iic (1 / 2 : ℝ) := by
      ext v
      simp [b]
    rw [hpre]
    exact measurableSet_Iic)

private theorem uniform01_map_b :
    AronowAudit.P047.uniform01.map b = AronowAudit.P047.fairBool := by
  apply Measure.ext_of_singleton
  intro a
  cases a
  · have hpre : b ⁻¹' ({false} : Set Bool) = (Set.Iic (1 / 2 : ℝ))ᶜ := by
      ext v
      simp [b]
    rw [Measure.map_apply measurable_b (measurableSet_singleton false), hpre]
    have hhalf : AronowAudit.P047.uniform01 (Set.Iic (1 / 2 : ℝ)) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [AronowAudit.P047.Wave1.Impossibility.uniform01_Iic (1 / 2 : ℝ) (by norm_num) (by norm_num)]
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hhalf]
    rw [fairBool_false_singleton, ofReal_half]
    norm_num
  · have hpre : b ⁻¹' ({true} : Set Bool) = Set.Iic (1 / 2 : ℝ) := by
      ext v
      simp [b]
    rw [Measure.map_apply measurable_b (measurableSet_singleton true), hpre,
      AronowAudit.P047.Wave1.Impossibility.uniform01_Iic (1 / 2 : ℝ) (by norm_num) (by norm_num)]
    rw [fairBool_true_singleton, ofReal_half]

private theorem fairBool_prod_eq_map :
    AronowAudit.P047.fairBool.prod AronowAudit.P047.fairBool =
      (AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01).map
        (fun v : ℝ × ℝ => (b v.1, b v.2)) := by
  rw [← uniform01_map_b]
  calc
    (AronowAudit.P047.uniform01.map b).prod (AronowAudit.P047.uniform01.map b) =
        (AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01).map (Prod.map b b) :=
      Measure.map_prod_map (μa := AronowAudit.P047.uniform01)
        (μc := AronowAudit.P047.uniform01) (f := b) (g := b) measurable_b measurable_b
    _ = (AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01).map
        (fun v : ℝ × ℝ => (b v.1, b v.2)) := by rfl

theorem measurable_seedMap : Measurable
    (fun z : ℝ × ℝ × ℝ => (z.1, (b z.2.1, b z.2.2))) :=
  measurable_fst.prodMk
    ((measurable_b.comp measurable_snd.fst).prodMk
      (measurable_b.comp measurable_snd.snd))

theorem seed_triple_eq_map :
    AronowAudit.P047.uniform01.prod
        (AronowAudit.P047.fairBool.prod AronowAudit.P047.fairBool) =
      (AronowAudit.P047.uniform01.prod
        (AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01)).map
        (fun z : ℝ × ℝ × ℝ => (z.1, (b z.2.1, b z.2.2))) := by
  rw [fairBool_prod_eq_map]
  calc
    AronowAudit.P047.uniform01.prod
        ((AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01).map
          (fun v : ℝ × ℝ => (b v.1, b v.2))) =
      (AronowAudit.P047.uniform01.prod
        (AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01)).map
        (Prod.map id (fun v : ℝ × ℝ => (b v.1, b v.2))) := by
          simpa only [Measure.map_id] using
            (Measure.map_prod_map (μa := AronowAudit.P047.uniform01)
              (μc := AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01)
              (f := id) (g := fun v : ℝ × ℝ => (b v.1, b v.2))
              measurable_id (measurable_b.prodMap measurable_b))
    _ = (AronowAudit.P047.uniform01.prod
        (AronowAudit.P047.uniform01.prod AronowAudit.P047.uniform01)).map
        (fun z : ℝ × ℝ × ℝ => (z.1, (b z.2.1, b z.2.2))) := by rfl

end

end SAP.P047.WH.W1.P.T3_L1

open MeasureTheory

theorem SAP.P047.WH.W1.T3_L1_proof : SAP.P047.WH.W1.T3_L1 := by
  unfold SAP.P047.WH.W1.T3_L1
  rw [SAP.P047.Bridge.baselineLaw_eq]
  rw [AronowAudit.P047.baselineLaw, AronowAudit.P047.Wave1.Impossibility.genMeasure]
  rw [SAP.P047.WH.W1.P.T3_L1.seed_triple_eq_map]
  rw [Measure.map_map AronowAudit.P047.measurable_baseline_map
    SAP.P047.WH.W1.P.T3_L1.measurable_seedMap]
  congr 1
  funext z
  simp [AronowAudit.P047.Wave1.Impossibility.gen, SAP.P047.WH.W1.P.T3_L1.b]
