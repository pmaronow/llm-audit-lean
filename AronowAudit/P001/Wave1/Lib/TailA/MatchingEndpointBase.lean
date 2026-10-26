import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellMoments
import Mathlib.Probability.Independence.InfinitePi

/-! The expectation obstruction and the canonical matching experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

universe u
local instance instDecidableMatchingEndpointBase (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- A nonnegative sequence cannot converge in probability to a constant larger
than the limit of its expectations.  A bounded indicator gives the lower bound. -/
theorem nonnegative_expectation_gap {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : ℕ → Ω → ℝ)
    (hmeas : ∀ n, Measurable (V n)) (hint : ∀ n, Integrable (V n) μ)
    (h0 : ∀ n ω, 0 ≤ V n ω) (a b : ℝ)
    (hmean : Tendsto (fun n => mean μ (V n)) atTop (nhds b)) (hba : b < a) :
    ¬ CP μ V a := by
  intro hcp
  have hb : 0 ≤ b := ge_of_tendsto' hmean (fun n => integral_nonneg (h0 n))
  let t : ℝ := (a+b)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hbt : b < t := by dsimp [t]; linarith
  have hta : t < a := by dsimp [t]; linarith
  let E : ℕ → Set Ω := fun n => {ω | a-t ≤ dist (V n ω) a}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_le measurable_const ((hmeas n).dist measurable_const)
  have hlower (n : ℕ) : t*(1-prob μ (E n)) ≤ mean μ (V n) := by
    have hi : Integrable ((E n)ᶜ.indicator (fun _ : Ω => t)) μ :=
      (integrable_const t).indicator (hE n).compl
    have hle : (∫ ω, (E n)ᶜ.indicator (fun _ : Ω => t) ω ∂μ) ≤ mean μ (V n) := by
      apply integral_mono hi (hint n)
      intro ω
      by_cases hω : ω ∈ E n
      · simpa only [Set.indicator_of_notMem (show ω ∉ (E n)ᶜ from fun h => h hω)] using h0 n ω
      · rw [Set.indicator_of_mem (Set.mem_compl hω)]
        have hd : |V n ω-a| < a-t := by
          simpa only [E,Set.mem_setOf_eq,not_le,Real.dist_eq] using hω
        have hh := (abs_lt.mp hd).1
        linarith
    simpa only [integral_indicator_const t (hE n).compl,smul_eq_mul,
      measureReal_compl (hE n),probReal_univ,prob,measureReal_def,measure_univ,
      ENNReal.toReal_one,mul_comm] using hle
  have hl : Tendsto (fun n => t*(1-prob μ (E n))) atTop (nhds (t*(1-0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub (hcp (a-t) (by linarith)))
  have htb : t ≤ b := by
    have hh := le_of_tendsto_of_tendsto' hl hmean hlower
    simpa only [sub_zero,mul_one] using hh
  exact (not_le_of_gt hbt) htb

def matchingCanonicalLaw : Measure (ℕ → MatchUnit) :=
  Measure.infinitePi (fun _ => matchingUnitLaw)

instance instProbabilityMatchingCanonicalLaw : IsProbabilityMeasure matchingCanonicalLaw := by
  unfold matchingCanonicalLaw
  infer_instance


theorem matching_endpoint_constants_positive : 0 < matchA ∧ 0 < matchB ∧ 0 < matchVB := by
  obtain ⟨hs,hs1,_,_,_⟩ := hot_deck_bootstrap_constant_inequalities
  have hd : 0 < 2-matchS := by linarith
  have hA : 0 < matchA := by
    unfold matchA
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ hd hs).mpr
    nlinarith [sq_nonneg (matchS-1)]
  have hB : 0 < matchB := by
    unfold matchB
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (by positivity : 0 < 2*(2-matchS)) (by positivity : 0 < 2*matchS)).mpr
    nlinarith [sq_nonneg (matchS-1)]
  refine ⟨hA,hB,?_⟩
  have hlog : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  unfold matchVB
  have : 0 < matchB*(2*Real.log 3-3/2) := mul_pos hB (by linarith)
  linarith

end AronowAudit.P001.TailA
