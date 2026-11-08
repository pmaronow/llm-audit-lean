import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W1.P.T22_L2V2

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

noncomputable section

private def covCell {Ω E : Type*} [MeasurableSpace Ω] (X : Ω → E) (x : E) : Set Ω :=
  {ω | X ω = x}

private def armCell {Ω E : Type*} [MeasurableSpace Ω]
    (X : Ω → E) (D : Ω → ℝ) (d : ℝ) (x : E) : Set Ω :=
  {ω | X ω = x ∧ D ω = d}

private def observed {Ω : Type*} (Y0 Y1 D : Ω → ℝ) : Ω → ℝ :=
  fun ω => Y1 ω * D ω + Y0 ω * (1 - D ω)

private lemma covCell_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] {X : Ω → E} (hX : Measurable X) (x : E) :
    MeasurableSet (covCell X x) := by
  exact hX (measurableSet_singleton x)

private lemma armCell_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] {X : Ω → E} {D : Ω → ℝ}
    (hX : Measurable X) (hD : Measurable D) (d : ℝ) (x : E) :
    MeasurableSet (armCell X D d x) := by
  exact (hX (measurableSet_singleton x)).inter (hD (measurableSet_singleton d))

private lemma armMass_lower_bound {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D) (hb : ∀ ω, D ω = 0 ∨ D ω = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ x, 0 < probability μ (covCell X x) →
      ε < W1CellPropensity μ X D x ∧ W1CellPropensity μ X D x < 1 - ε)
    (d : ℝ) (hd : d = 0 ∨ d = 1) (x : E)
    (hq : 0 < probability μ (covCell X x)) :
    ε * probability μ (covCell X x) ≤ probability μ (armCell X D d x) := by
  let q := probability μ (covCell X x)
  let r1 := W1JointMass μ X D 1 x
  let r0 := W1JointMass μ X D 0 x
  have hqsplit : q = r1 + r0 := by
    exact binary_cell_split μ X D hX hD hb x
  have hp : W1CellPropensity μ X D x = r1 / q := by
    change (if 0 < probability μ (covCell X x) then _ else _) = _
    rw [if_pos hq]
    rfl
  have hnonneg1 : 0 ≤ r1 := ENNReal.toReal_nonneg
  have hnonneg0 : 0 ≤ r0 := ENNReal.toReal_nonneg
  have hqpos : 0 < q := hq
  rcases hd with hd0 | hd1
  · subst d
    have hup : r1 / q < 1 - ε := by rw [← hp]; exact (hpos x hq).2
    have hr : ε * q ≤ r0 := by
      have hc : r1 < (1 - ε) * q := (div_lt_iff₀ hqpos).mp hup
      nlinarith [hqsplit, hc]
    change ε * q ≤ r0
    simpa [r0, armCell, W1JointMass] using hr
  · subst d
    have hlo : ε < r1 / q := by rw [← hp]; exact (hpos x hq).1
    have hr : ε * q ≤ r1 := by
      have : ε * q < r1 := (lt_div_iff₀ hqpos).mp hlo
      linarith
    change ε * q ≤ r1
    simpa [r1, armCell, W1JointMass] using hr

private lemma weighted_arm_mean_bound {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D) (hb : ∀ ω, D ω = 0 ∨ D ω = 1)
    (Y0 Y1 Yd : Ω → ℝ) (d ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ x, 0 < probability μ (covCell X x) →
      ε < W1CellPropensity μ X D x ∧ W1CellPropensity μ X D x < 1 - ε)
    (hd : d = 0 ∨ d = 1)
    (hobs : ∀ ω, D ω = d → observed Y0 Y1 D ω = Yd ω)
    (x : E) (hq : 0 < probability μ (covCell X x)) :
    ε * (|W1ArmMean μ X Y0 Y1 D d x| * probability μ (covCell X x)) ≤
      ∫ ω in armCell X D d x, |Yd ω| ∂μ := by
  let A := armCell X D d x
  let q := probability μ (covCell X x)
  let r := probability μ A
  let N := ∫ ω in A, observed Y0 Y1 D ω ∂μ
  have hAmeas : MeasurableSet A := armCell_measurable hX hD d x
  have hrpos : 0 < r := by
    have hlower := armMass_lower_bound μ X D hX hD hb ε hε hpos d hd x hq
    dsimp [r, q] at *
    exact lt_of_lt_of_le (mul_pos hε hq) hlower
  have hmean : W1ArmMean μ X Y0 Y1 D d x = N / r := by
    change (if 0 < probability μ (armCell X D d x) then _ else _) = _
    rw [if_pos hrpos]
    rfl
  have hN : N = ∫ ω in A, Yd ω ∂μ := by
    dsimp [N]
    apply setIntegral_congr_fun hAmeas
    intro ω hω
    exact hobs ω hω.2
  have hnorm : |N| ≤ ∫ ω in A, |Yd ω| ∂μ := by
    rw [hN]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := μ.restrict A) Yd)
  have hden : ε * q ≤ r := by
    exact armMass_lower_bound μ X D hX hD hb ε hε hpos d hd x hq
  have hfactor : ε * (|N| / r * q) ≤ |N| := by
    have hmul' : ε * q * |N| ≤ r * |N| :=
      mul_le_mul_of_nonneg_right hden (abs_nonneg N)
    calc
      ε * (|N| / r * q) = (ε * q * |N|) / r := by
        field_simp [ne_of_gt hrpos]
      _ ≤ (r * |N|) / r := div_le_div_of_nonneg_right hmul' hrpos.le
      _ = |N| := by field_simp [ne_of_gt hrpos]
  have hmeanabs : |W1ArmMean μ X Y0 Y1 D d x| = |N| / r := by
    rw [hmean, abs_div, abs_of_pos hrpos]
  calc
    ε * (|W1ArmMean μ X Y0 Y1 D d x| * q)
        = ε * (|N| / r * q) := by rw [hmeanabs]
    _ ≤ |N| := hfactor
    _ ≤ ∫ ω in A, |Yd ω| ∂μ := hnorm

private lemma cell_union {Ω E : Type*} [MeasurableSpace Ω] (X : Ω → E) :
    (⋃ x : E, covCell X x) = Set.univ := by
  ext ω
  simp [covCell]

private lemma covCells_pairwise_disjoint {Ω E : Type*} [MeasurableSpace Ω] (X : Ω → E) :
    Pairwise (fun x y => Disjoint (covCell X x) (covCell X y)) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro ω hx hy
  exact hxy (hx.symm.trans hy)

private lemma abs_cell_integrals_summable {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Integrable Y μ) :
    Summable (fun x : E => ∫ ω in covCell X x, |Y ω| ∂μ) := by
  have hnorm : Integrable (fun ω => |Y ω|) μ := by
    simpa only [Real.norm_eq_abs] using hY.norm
  have hunion : IntegrableOn (fun ω => |Y ω|) (⋃ x : E, covCell X x) μ := by
    rw [cell_union X]
    exact hnorm.integrableOn
  have hsum := hasSum_integral_iUnion
    (fun x => covCell_measurable hX x)
    (covCells_pairwise_disjoint X)
    hunion
  exact hsum.summable

private lemma arm_mean_integrable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D) (hb : ∀ ω, D ω = 0 ∨ D ω = 1)
    (Y0 Y1 Yd : Ω → ℝ) (d : ℝ) (hd : d = 0 ∨ d = 1)
    (hYd : Integrable Yd μ)
    (hobs : ∀ ω, D ω = d → observed Y0 Y1 D ω = Yd ω)
    (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ x, 0 < probability μ (covCell X x) →
      ε < W1CellPropensity μ X D x ∧ W1CellPropensity μ X D x < 1 - ε) :
    Integrable (W1ArmMean μ X Y0 Y1 D d ∘ X) μ := by
  let m := W1ArmMean μ X Y0 Y1 D d
  let f := m ∘ X
  have hm : Measurable m := measurable_of_countable m
  have hf : Measurable f := hm.comp hX
  have hcell (x : E) : IntegrableOn f (covCell X x) μ := by
    have hconst : IntegrableOn (fun _ : Ω => m x) (covCell X x) μ :=
      integrableOn_const (μ := μ) (s := covCell X x) (by
        exact measure_ne_top μ (covCell X x))
    apply hconst.congr_fun
    · intro ω hω
      change X ω = x at hω
      simp [f, m, hω]
    · exact covCell_measurable hX x
  have hcellIntegral (x : E) :
      ∫ ω in covCell X x, ‖f ω‖ ∂μ = |m x| * probability μ (covCell X x) := by
    calc
      ∫ ω in covCell X x, ‖f ω‖ ∂μ =
          ∫ ω in covCell X x, (|m x| : ℝ) ∂μ := by
            apply setIntegral_congr_fun (covCell_measurable hX x)
            intro ω hω
            change X ω = x at hω
            simp [f, hω, Real.norm_eq_abs]
      _ = |m x| * probability μ (covCell X x) := by
        simp [probability, Measure.real, integral_const, smul_eq_mul, mul_comm]
  have hcellBound (x : E) :
      |m x| * probability μ (covCell X x) ≤
        (ε⁻¹) * (∫ ω in covCell X x, |Yd ω| ∂μ) := by
    by_cases hq : 0 < probability μ (covCell X x)
    · have hbound := weighted_arm_mean_bound μ X D hX hD hb Y0 Y1 Yd d ε hε hpos hd hobs x hq
      have habs : Integrable (fun ω => |Yd ω|) μ := by
        simpa only [Real.norm_eq_abs] using hYd.norm
      have hsubset : armCell X D d x ⊆ covCell X x := by
        intro ω hω
        exact hω.1
      have hmono :
          ∫ ω in armCell X D d x, |Yd ω| ∂μ ≤
            ∫ ω in covCell X x, |Yd ω| ∂μ :=
        setIntegral_mono_set (habs.integrableOn (s := covCell X x))
          (ae_of_all _ fun ω => abs_nonneg (Yd ω))
          (ae_of_all μ fun ω hω => hsubset hω)
      have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
      have := mul_le_mul_of_nonneg_left (hbound.trans hmono) hεinv.le
      have hcancel : ε⁻¹ * (ε * (|m x| * probability μ (covCell X x))) =
          |m x| * probability μ (covCell X x) := by field_simp
      rw [hcancel] at this
      simpa [m] using this
    · have hq0 : probability μ (covCell X x) = 0 :=
        le_antisymm (not_lt.mp hq) ENNReal.toReal_nonneg
      have hqMeasure : μ (covCell X x) = 0 := by
        by_contra hne
        have hp : 0 < (μ (covCell X x)).toReal :=
          ENNReal.toReal_pos hne (measure_ne_top μ (covCell X x))
        have hpq : 0 < probability μ (covCell X x) := by
          simpa [probability] using hp
        rw [hq0] at hpq
        exact (lt_irrefl 0) hpq
      have harm0 : probability μ (armCell X D d x) = 0 := by
        have hsub : armCell X D d x ⊆ covCell X x := by
          intro ω hω
          exact hω.1
        have hmeasure : μ (armCell X D d x) ≤ μ (covCell X x) := measure_mono hsub
        have hzero : μ (armCell X D d x) = 0 := by
          apply le_antisymm
          · simpa [hqMeasure] using hmeasure
          · exact bot_le
        simp [probability, hzero]
      have hnot : ¬ 0 < probability μ (armCell X D d x) := by
        rw [harm0]
        exact lt_irrefl 0
      have hm0 : m x = 0 := by
        change (if 0 < probability μ (armCell X D d x) then _ else _) = 0
        rw [if_neg hnot]
      rw [hm0, hq0]
      simp only [abs_zero, zero_mul]
      exact mul_nonneg (inv_pos.mpr hε).le
        (setIntegral_nonneg (covCell_measurable hX x)
          (fun ω _ => abs_nonneg (Yd ω)))
  have hsumAbs : Summable (fun x : E => |m x| * probability μ (covCell X x)) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg)
      hcellBound
    exact (abs_cell_integrals_summable μ X hX Yd hYd).mul_left ε⁻¹
  have hsumNorm : Summable (fun x : E => ∫ ω in covCell X x, ‖f ω‖ ∂μ) := by
    apply hsumAbs.congr
    intro x
    exact (hcellIntegral x).symm
  have hIntOn : IntegrableOn f (Set.univ : Set Ω) μ := by
    have h := integrableOn_iUnion_of_summable_integral_norm
      (s := covCell X) hcell hsumNorm
    simpa [cell_union X] using h
  change Integrable f (μ.restrict Set.univ) at hIntOn
  simpa [f, m] using hIntOn

end
end SAP.P001b.WH.W1.P.T22_L2V2

open SAP.P001b.WH.W1.P.T22_L2V2

theorem SAP.P001b.WH.W1.T22_L2V2_proof : SAP.P001b.WH.W1.T22_L2V2 := by
  intro Ω E _ _ _ _ μ hμ X hX Y0 Y1 D hY0m hY1m hDm hY0i hY1i hb hpositivity
  obtain ⟨ε, hε, hpos⟩ := hpositivity
  have hobs0 : ∀ ω, D ω = 0 → observed Y0 Y1 D ω = Y0 ω := by
    intro ω hD
    simp [observed, hD]
  have hobs1 : ∀ ω, D ω = 1 → observed Y0 Y1 D ω = Y1 ω := by
    intro ω hD
    simp [observed, hD]
  constructor
  · exact arm_mean_integrable μ X D hX hDm hb Y0 Y1 Y0 0 (Or.inl rfl) hY0i hobs0 ε hε hpos
  · exact arm_mean_integrable μ X D hX hDm hb Y0 Y1 Y1 1 (Or.inr rfl) hY1i hobs1 ε hε hpos

 
