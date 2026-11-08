import SAP.P027a.WH.W1.Leaves
import AronowAudit.P027.Wave1.UniformStart
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1.P.T10_L1

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

private def cell (g : Fin 4) : Set ℝ :=
  Set.Ico (fourLeft 1 3 g) (fourLeft 1 3 g + if g.val % 2 = 0 then 1 else 3)

private def sample (u : ℝ) (k : Fin 8) : Bool :=
  decide (systematicSelected randomSize8 2 u k)

private lemma normalized_isProbability : IsProbabilityMeasure (wholeStartMeasure 8) := by
  constructor
  simp [wholeStartMeasure, Real.volume_Ico]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma sample_eq_selected (g : Fin 4) (u : ℝ) (hu : u ∈ cell g) :
    (fun k => sample u k) = random8.selected g := by
  funext k
  have huA : AronowAudit.P027.fourLeft 1 3 g ≤ u ∧
      u < AronowAudit.P027.fourLeft 1 3 g +
        (if g.val % 2 = 0 then 1 else 3) := by
    simpa [fourLeft, AronowAudit.P027.fourLeft, cell] using hu
  have hsys := AronowAudit.P027.random8_systematic g u huA
  have hiff : systematicSelected randomSize8 2 u k ↔
      random8.selected g k = true := by
    simpa [SAP.P027a.systematicSelected, SAP.P027a.cumulativeLeft,
      SAP.P027a.randomSize8, SAP.P027a.random8, SAP.P027a.fourPhase,
      AronowAudit.P027.systematicSelected, AronowAudit.P027.cumulativeLeft,
      AronowAudit.P027.randomSize8, AronowAudit.P027.random8,
      AronowAudit.P027.fourPhase] using hsys k
  change decide (systematicSelected randomSize8 2 u k) = random8.selected g k
  cases hb : random8.selected g k <;>
    cases hd : decide (systematicSelected randomSize8 2 u k) <;>
    simp_all

private lemma cell_subset (g : Fin 4) : cell g ⊆ Set.Ico (0 : ℝ) 8 := by
  intro u hu
  fin_cases g <;> norm_num [cell, fourLeft] at hu ⊢ <;> constructor <;> linarith

private lemma cell_partition :
    ∀ u ∈ Set.Ico (0 : ℝ) 8, ∃! g : Fin 4, u ∈ cell g := by
  intro u hu
  have hcover : ∃ g : Fin 4, u ∈ cell g := by
    by_cases h1 : u < 1
    · exact ⟨0, by norm_num [cell, fourLeft]; exact ⟨hu.1, h1⟩⟩
    by_cases h4 : u < 4
    · exact ⟨1, by norm_num [cell, fourLeft]; exact ⟨by linarith, h4⟩⟩
    by_cases h5 : u < 5
    · exact ⟨2, by norm_num [cell, fourLeft]; exact ⟨by linarith, h5⟩⟩
    · exact ⟨3, by norm_num [cell, fourLeft]; exact ⟨by linarith, hu.2⟩⟩
  obtain ⟨g, hg⟩ := hcover
  refine ⟨g, hg, ?_⟩
  intro j hj
  apply Fin.ext
  fin_cases g <;> fin_cases j <;>
    norm_num [cell, fourLeft] at hg hj ⊢ <;> linarith

private lemma cell_mass (ν : Measure ℝ) (L : ℝ)
    (hν : ν = wholeStartMeasure L) (hL : L = 8) (g : Fin 4) :
    ν (cell g) = ENNReal.ofReal (random8.weight g) := by
  have hmeas : MeasurableSet (cell g) := measurableSet_Ico
  have hsub := cell_subset g
  rw [hν, wholeStartMeasure, Measure.smul_apply, smul_eq_mul,
    hL, Measure.restrict_apply hmeas, Set.inter_eq_left.mpr hsub]
  simp only [cell, Real.volume_Ico]
  fin_cases g <;> norm_num [fourLeft, random8, fourPhase] <;>
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)] <;> norm_num <;>
    rw [ENNReal.div_eq_inv_mul] <;> simp [mul_comm]

end
end SAP.P027a.WH.W1.P.T10_L1

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge AronowAudit.P027
attribute [local instance] Classical.propDecidable

theorem SAP.P027a.WH.W1.T10_L1_proof : SAP.P027a.WH.W1.T10_L1 := by
  change SAP.P027a.FourPhaseStartWhole SAP.P027a.random8 SAP.P027a.randomSize8 1 3
  dsimp only [SAP.P027a.FourPhaseStartWhole]
  simp only [show (2 : ℝ) * (1 + 3) = 8 by norm_num]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · let ν : Measure ℝ := SAP.P027a.wholeStartMeasure 8
    change IsProbabilityMeasure ν
    simpa [ν] using SAP.P027a.WH.W1.P.T10_L1.normalized_isProbability
  · intro u hu
    exact SAP.P027a.WH.W1.P.T10_L1.cell_partition u hu
  · intro g
    let ν : Measure ℝ := SAP.P027a.wholeStartMeasure 8
    change ν (SAP.P027a.WH.W1.P.T10_L1.cell g) = ENNReal.ofReal (SAP.P027a.random8.weight g)
    apply SAP.P027a.WH.W1.P.T10_L1.cell_mass ν 8 rfl rfl g
  · intro g u hu
    exact SAP.P027a.WH.W1.P.T10_L1.sample_eq_selected g u hu
  · intro F
    let ν : Measure ℝ := SAP.P027a.wholeStartMeasure 8
    change Integrable (fun u => F (SAP.P027a.WH.W1.P.T10_L1.sample u)) ν ∧
      (∫ u, F (SAP.P027a.WH.W1.P.T10_L1.sample u) ∂ν) =
        SAP.P027a.expect SAP.P027a.random8
          (fun g => F (SAP.P027a.random8.selected g))
    haveI : IsProbabilityMeasure ν := by
      simpa [ν] using SAP.P027a.WH.W1.P.T10_L1.normalized_isProbability
    have hS : ν (Set.Ico (0 : ℝ) 8)ᶜ = 0 := by
      simp [ν, SAP.P027a.wholeStartMeasure]
    have hpart : ∀ u ∈ Set.Ico (0 : ℝ) 8,
        ∃! g : Fin 4, u ∈ SAP.P027a.WH.W1.P.T10_L1.cell g :=
      SAP.P027a.WH.W1.P.T10_L1.cell_partition
    have hsub : ∀ g : Fin 4,
        SAP.P027a.WH.W1.P.T10_L1.cell g ⊆ Set.Ico (0 : ℝ) 8 :=
      SAP.P027a.WH.W1.P.T10_L1.cell_subset
    have hI : ∀ g : Fin 4, MeasurableSet (SAP.P027a.WH.W1.P.T10_L1.cell g) :=
      fun _ => measurableSet_Ico
    have hconst (g : Fin 4) (u : ℝ)
        (hu : u ∈ SAP.P027a.WH.W1.P.T10_L1.cell g) :
        F (SAP.P027a.WH.W1.P.T10_L1.sample u) =
          F (SAP.P027a.random8.selected g) := by
      exact congrArg F (SAP.P027a.WH.W1.P.T10_L1.sample_eq_selected g u hu)
    have hstat := AronowAudit.P027.Wave1.UniformStart.n5_proof
      ν (Set.Ico (0 : ℝ) 8) hS SAP.P027a.WH.W1.P.T10_L1.cell hI hsub hpart
      (fun u => F (SAP.P027a.WH.W1.P.T10_L1.sample u))
      (fun g => F (SAP.P027a.random8.selected g)) hconst
    refine ⟨hstat.1, ?_⟩
    rw [hstat.2]
    have hm (g : Fin 4) : (ν (SAP.P027a.WH.W1.P.T10_L1.cell g)).toReal =
        SAP.P027a.random8.weight g := by
      rw [SAP.P027a.WH.W1.P.T10_L1.cell_mass ν 8 rfl rfl g]
      apply ENNReal.toReal_ofReal
      simp [SAP.P027a.random8, SAP.P027a.fourPhase]
      positivity
    simp_rw [hm]
    rfl
