import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T4_L2

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

noncomputable section

def oneDensity (x : ℝ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (Real.exp (-x)) else 0

def orthantDensity (k : ℕ) (x : Fin k → ℝ) : ℝ≥0∞ :=
  if ∀ i, 0 < x i then ENNReal.ofReal (Real.exp (-(∑ i, x i))) else 0

lemma measurable_oneDensity : Measurable oneDensity := by
  unfold oneDensity
  exact (Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const)

lemma measurable_orthantDensity (k : ℕ) : Measurable (orthantDensity k) := by
  unfold orthantDensity
  apply (Measurable.ite ?_ (by fun_prop) measurable_const)
  have hs : {x : Fin k → ℝ | ∀ i, 0 < x i} =
      ⋂ i : Fin k, {x : Fin k → ℝ | 0 < x i} := by
    ext x
    simp
  rw [hs]
  exact MeasurableSet.iInter fun i : Fin k =>
    measurableSet_lt measurable_const
      (show Measurable (fun x : Fin k → ℝ => x i) from measurable_pi_apply i)

lemma expMeasure_one_eq : expMeasure 1 = volume.withDensity oneDensity := by
  unfold expMeasure gammaMeasure
  apply withDensity_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  change exponentialPDF 1 x = oneDensity x
  rw [exponentialPDF_eq]
  by_cases hp : 0 < x
  · simp [oneDensity, hp, hp.le]
  · have hxle : x ≤ 0 := le_of_not_gt hp
    have hxne : x ≠ 0 := hx
    have hn : x < 0 := by
      rcases hxle.eq_or_lt with h | h
      · exact False.elim (hxne h)
      · exact h
    have hn' : ¬ 0 ≤ x := not_le.mpr hn
    simp [oneDensity, hp, hn']

lemma map_density_equiv {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hvol : MeasurePreserving e (volume : Measure α) (volume : Measure β))
    (f : α → ℝ≥0∞) :
    (volume.withDensity f).map e = volume.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply f (hs.preimage e.measurable),
    withDensity_apply (fun y => f (e.symm y)) hs]
  simpa only [MeasurableEquiv.symm_apply_apply] using
    hvol.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun y => f (e.symm y)) s

lemma orthantDensity_succ_factor (k : ℕ) (x : ℝ) (y : Fin k → ℝ) :
    orthantDensity (k+1)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) (Fin.last k)).symm (x,y)) =
      oneDensity x * orthantDensity k y := by
  let z : Fin (k+1) → ℝ :=
    Fin.snoc (α := fun _ : Fin (k+1) => ℝ) y x
  have hz : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ)
      (Fin.last k)).symm (x,y) = z := by
    ext i
    simp [z, MeasurableEquiv.piFinSuccAbove]
  have hpos : (∀ i : Fin (k+1), 0 < z i) ↔
      0 < x ∧ ∀ i : Fin k, 0 < y i := by
    rw [Fin.forall_iff_succAbove (Fin.last k)]
    simp [z]
  have hsum : (∑ i : Fin (k+1), z i) = (∑ i : Fin k, y i) + x := by
    rw [Fin.sum_univ_succAbove _ (Fin.last k)]
    simp [z, Fin.snoc_last, Fin.snoc_castSucc, Fin.succAbove_last_apply, add_comm]
  have hexp : Real.exp (-(∑ i : Fin k, y i + x)) =
      Real.exp (-x) * Real.exp (-(∑ i : Fin k, y i)) := by
    rw [show -(∑ i : Fin k, y i + x) = (-x) + -(∑ i : Fin k, y i) by ring,
      Real.exp_add]
  rw [hz]
  simp only [orthantDensity, oneDensity]
  by_cases hpall : ∀ i : Fin (k+1), 0 < z i
  · have hp := hpos.mp hpall
    rw [if_pos hpall, if_pos hp.1, if_pos hp.2, hsum, hexp,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  · rw [if_neg hpall]
    by_cases hx : 0 < x
    · by_cases hy : ∀ i : Fin k, 0 < y i
      · exact False.elim (hpall (hpos.mpr ⟨hx, hy⟩))
      · rw [if_pos hx, if_neg hy]
        simp
    · simp [hx]

lemma fin_exp_density : ∀ k : ℕ,
    Measure.pi (fun _ : Fin k => expMeasure 1) =
      volume.withDensity (orthantDensity k) := by
  intro k
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  induction k with
  | zero =>
      have hpi : Measure.pi (fun _ : Fin 0 => expMeasure 1) = volume := by
        rw [Measure.pi_of_empty, Measure.volume_pi_eq_dirac]
      rw [hpi]
      have hd : orthantDensity 0 = (fun _ : Fin 0 → ℝ => (1 : ℝ≥0∞)) := by
        funext x
        simp [orthantDensity]
      rw [hd]
      exact (withDensity_one (μ := volume)).symm
  | succ k ih =>
      let e : (Fin (k+1) → ℝ) ≃ᵐ (ℝ × (Fin k → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) (Fin.last k)
      have hvol : MeasurePreserving e (volume : Measure (Fin (k+1) → ℝ)) volume := by
        simpa [e] using
          (volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) (Fin.last k))
      have hleft :
          (Measure.pi (fun _ : Fin (k+1) => expMeasure 1)).map e =
            (expMeasure 1).prod (Measure.pi (fun _ : Fin k => expMeasure 1)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => expMeasure 1)
            (Fin.last k)).map_eq
      have hright :
          (volume.withDensity (orthantDensity (k+1))).map e =
            (expMeasure 1).prod (Measure.pi (fun _ : Fin k => expMeasure 1)) := by
        rw [map_density_equiv e hvol]
        rw [show (fun z : ℝ × (Fin k → ℝ) =>
            orthantDensity (k+1) (e.symm z)) =
              (fun z => oneDensity z.1 * orthantDensity k z.2) by
              funext z
              exact orthantDensity_succ_factor k z.1 z.2]
        rw [ih, expMeasure_one_eq]
        rw [Measure.volume_eq_prod]
        rw [prod_withDensity measurable_oneDensity (measurable_orthantDensity k)]
      have hmap :
          (Measure.pi (fun _ : Fin (k+1) => expMeasure 1)).map e =
            (volume.withDensity (orthantDensity (k+1))).map e := hleft.trans hright.symm
      have hinj := congrArg (Measure.map e.symm) hmap
      simpa [Measure.map_map] using hinj

lemma expMeasureProduct_density (n : ℕ) :
    exponentialProduct n = volume.withDensity (orthantDensity (n+2)) := by
  simpa [exponentialProduct] using fin_exp_density (n+2)

end

end SAP.P037a.WH.W1.P.T4_L2

theorem SAP.P037a.WH.W1.T4_L2_proof : SAP.P037a.WH.W1.T4_L2 := by
  intro n
  rw [SAP.P037a.WH.W1.P.T4_L2.expMeasureProduct_density]
  have hS : MeasurableSet (SAP.P037a.positiveOrthant n) := by
    unfold SAP.P037a.positiveOrthant
    change MeasurableSet {e : Fin (n+2) → ℝ | ∀ i, 0 < e i}
    rw [show {e : Fin (n+2) → ℝ | ∀ i, 0 < e i} =
        ⋂ i : Fin (n+2), {e : Fin (n+2) → ℝ | 0 < e i} by
          ext e
          simp]
    exact MeasurableSet.iInter fun i : Fin (n+2) =>
      measurableSet_lt
        (show Measurable (fun _ : Fin (n+2) → ℝ => (0 : ℝ)) from measurable_const)
        (show Measurable (fun e : Fin (n+2) → ℝ => e i) from measurable_pi_apply i)
  rw [← MeasureTheory.withDensity_indicator hS]
  congr 1
  funext e
  by_cases hp : ∀ i, 0 < e i <;>
    simp [SAP.P037a.WH.W1.P.T4_L2.orthantDensity, SAP.P037a.positiveOrthant,
      Set.indicator, hp]

