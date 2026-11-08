import SAP.P027a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1.P.T1_L1

open SAP.P027a
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

private def phaseCell (g : Fin 4) : Set ℝ :=
  Set.Ico (fourLeft 2 10 g) (fourLeft 2 10 g + if g.val % 2 = 0 then 2 else 10)

private lemma phaseCell_subset (g : Fin 4) :
    phaseCell g ⊆ Set.Ico (0 : ℝ) 24 := by
  intro u hu
  fin_cases g <;> norm_num [phaseCell, fourLeft] at hu ⊢ <;> constructor <;> linarith

private lemma phaseCell_partition (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 24) :
    ∃! g : Fin 4, u ∈ phaseCell g := by
  have hu0 : 0 ≤ u := hu.1
  have hu24 : u < 24 := hu.2
  by_cases h02 : u < 2
  · refine ⟨0, ?_, ?_⟩
    · norm_num [phaseCell, fourLeft]
      exact ⟨hu0, h02⟩
    · intro g hg
      fin_cases g <;> simp [phaseCell, fourLeft] at hg ⊢ <;> linarith
  · have h2 : 2 ≤ u := le_of_not_gt h02
    by_cases h12 : u < 12
    · refine ⟨1, ?_, ?_⟩
      · norm_num [phaseCell, fourLeft]
        exact ⟨h2, h12⟩
      · intro g hg
        fin_cases g <;> simp [phaseCell, fourLeft] at hg ⊢ <;> linarith
    · have h12' : 12 ≤ u := le_of_not_gt h12
      by_cases h14 : u < 14
      · refine ⟨2, ?_, ?_⟩
        · norm_num [phaseCell, fourLeft]
          exact ⟨h12', h14⟩
        · intro g hg
          fin_cases g <;> simp [phaseCell, fourLeft] at hg ⊢ <;> linarith
      · have h14' : 14 ≤ u := le_of_not_gt h14
        refine ⟨3, ?_, ?_⟩
        · norm_num [phaseCell, fourLeft]
          exact ⟨h14', hu24⟩
        · intro g hg
          fin_cases g <;> simp [phaseCell, fourLeft] at hg ⊢ <;> linarith

private lemma start_probability :
    IsProbabilityMeasure (wholeStartMeasure 24) := by
  constructor
  have hvol : volume (Set.Ico (0 : ℝ) 24) = ENNReal.ofReal 24 := by
    rw [Real.volume_Ico]
    norm_num
  simp only [wholeStartMeasure, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter, hvol]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)


private lemma normalized_length (d : ℝ) (_hd : 0 ≤ d) :
    (ENNReal.ofReal (24 : ℝ))⁻¹ * ENNReal.ofReal d = ENNReal.ofReal (d / 24) := by
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (24 : ℝ))]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (24 : ℝ)⁻¹)]
  congr 1
  field_simp

private lemma ofReal_one_twelfth :
    ENNReal.ofReal (1 / 12 : ℝ) = (12 : ENNReal)⁻¹ := by
  rw [show (1 / 12 : ℝ) = (12 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (12 : ℝ))]
  norm_num

private lemma phaseCell_mass (g : Fin 4) :
    wholeStartMeasure 24 (phaseCell g) = ENNReal.ofReal (periodic8.weight g) := by
  have hsub := phaseCell_subset g
  have hmeas : MeasurableSet (phaseCell g) := measurableSet_Ico
  rw [wholeStartMeasure, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply hmeas, Set.inter_eq_left.mpr hsub]
  simp only [phaseCell]
  rw [Real.volume_Ico]
  fin_cases g <;> simp [fourLeft, periodic8, fourPhase]
  · have h := normalized_length 2 (by norm_num)
    norm_num at h
    rw [ofReal_one_twelfth] at h
    exact h
  · have h := normalized_length 10 (by norm_num)
    norm_num at h
    exact h
  · have h := normalized_length 2 (by norm_num)
    norm_num at h
    rw [ofReal_one_twelfth] at h
    exact h
  · have h := normalized_length 10 (by norm_num)
    norm_num at h
    exact h

end SAP.P027a.WH.W1.P.T1_L1

open SAP.P027a.WH.W1.P.T1_L1
open SAP.P027a
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem SAP.P027a.WH.W1.T1_L1_proof : SAP.P027a.WH.W1.T1_L1 := by
  classical
  unfold SAP.P027a.WH.W1.T1_L1 SAP.P027a.FourPhaseStartWhole
  dsimp only
  have hL : (2 : ℝ) * ((2 : ℝ) + 10) = 24 := by norm_num
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · convert SAP.P027a.WH.W1.P.T1_L1.start_probability using 1 <;> rw [hL]

  · intro u hu
    have hu' : u ∈ Set.Ico (0 : ℝ) 24 := by simpa [hL] using hu
    exact SAP.P027a.WH.W1.P.T1_L1.phaseCell_partition u hu'
  · intro g
    simpa [phaseCell, hL] using SAP.P027a.WH.W1.P.T1_L1.phaseCell_mass g
  · intro g u hu
    have hu' : fourLeft 2 10 g ≤ u ∧
        u < fourLeft 2 10 g + (if g.val % 2 = 0 then 2 else 10) := hu
    funext k
    change decide (SAP.P027a.systematicSelected periodicSize8 2 u k) =
      decide (k.val % 4 = g.val)
    have ha := AronowAudit.P027.periodic8_systematic g u hu' k
    apply decide_eq_decide.mpr
    simpa [SAP.P027a.systematicSelected, SAP.P027a.periodicSize8,
      SAP.P027a.cumulativeLeft, SAP.P027a.periodic8, SAP.P027a.fourPhase,
      AronowAudit.P027.systematicSelected, AronowAudit.P027.periodicSize8,
      AronowAudit.P027.cumulativeLeft, AronowAudit.P027.periodic8,
      AronowAudit.P027.fourPhase] using ha
  · intro F
    let ν : Measure ℝ := wholeStartMeasure (2 * (2 + 10))
    letI : IsProbabilityMeasure ν := by
      change IsProbabilityMeasure (wholeStartMeasure (2 * (2 + 10)))
      rw [hL]
      exact SAP.P027a.WH.W1.P.T1_L1.start_probability
    let cell : Fin 4 → Set ℝ := phaseCell
    let s : ℝ → Fin 8 → Bool := fun u k => decide (systematicSelected periodicSize8 2 u k)
    have hcompl : ν (Set.Ico (0 : ℝ) (2 * (2 + 10)))ᶜ = 0 := by
      simp [ν, wholeStartMeasure]
    have hsub : ∀ g, cell g ⊆ Set.Ico (0 : ℝ) (2 * (2 + 10)) := by
      intro g
      change phaseCell g ⊆ Set.Ico (0 : ℝ) (2 * (2 + 10))
      rw [hL]
      exact SAP.P027a.WH.W1.P.T1_L1.phaseCell_subset g
    have hpart : ∀ u ∈ Set.Ico (0 : ℝ) (2 * (2 + 10)), ∃! g, u ∈ cell g := by
      intro u hu
      have hu' : u ∈ Set.Ico (0 : ℝ) 24 := by
        simpa [hL] using hu
      exact SAP.P027a.WH.W1.P.T1_L1.phaseCell_partition u hu' 
    have hsel : ∀ g u, u ∈ cell g →
        s u = periodic8.selected g := by
      intro g u hu
      have hu' : fourLeft 2 10 g ≤ u ∧
          u < fourLeft 2 10 g + (if g.val % 2 = 0 then 2 else 10) := hu
      funext k
      change decide (SAP.P027a.systematicSelected periodicSize8 2 u k) =
        decide (k.val % 4 = g.val)
      have ha := AronowAudit.P027.periodic8_systematic g u hu' k
      apply decide_eq_decide.mpr
      simpa [SAP.P027a.systematicSelected, SAP.P027a.periodicSize8,
        SAP.P027a.cumulativeLeft, SAP.P027a.periodic8, SAP.P027a.fourPhase,
        AronowAudit.P027.systematicSelected, AronowAudit.P027.periodicSize8,
        AronowAudit.P027.cumulativeLeft, AronowAudit.P027.periodic8,
        AronowAudit.P027.fourPhase] using ha
    have hmass (g : Fin 4) : ν (cell g) = ENNReal.ofReal (periodic8.weight g) := by
      change wholeStartMeasure (2 * (2 + 10)) (phaseCell g) = _
      rw [hL]
      exact SAP.P027a.WH.W1.P.T1_L1.phaseCell_mass g
    have hstat := AronowAudit.P027.Wave1.UniformStart.n5_proof
      ν (Set.Ico (0 : ℝ) (2 * (2 + 10))) hcompl cell (fun _ => measurableSet_Ico)
      hsub hpart (fun u => F (s u)) (fun g => F (periodic8.selected g))
      (fun g u hu => congrArg F (hsel g u hu))
    refine ⟨hstat.1, hstat.2.trans ?_⟩
    unfold expect
    apply Finset.sum_congr rfl
    intro g _
    have hw : 0 ≤ periodic8.weight g := by
      fin_cases g <;> norm_num [periodic8, fourPhase]
    rw [hmass g, ENNReal.toReal_ofReal hw]
