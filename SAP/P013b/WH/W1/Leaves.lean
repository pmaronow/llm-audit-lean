import SAP.P013b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013b.WH.W1

open MeasureTheory Filter Finset
open scoped BigOperators Topology ENNReal

noncomputable section

/-- The two supported assignments have equal, strictly positive design weights. -/
def t20FairDesign : Design (Fin 2) where
  weight := fun _ => 1 / 2
  positive := by intro z; norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- One unit, its own binary assignment as exposure, and zero potential outcomes. -/
def t20FairPopulation : Population t20FairDesign 1 2 where
  exposure := fun z _ => z
  outcome := fun _ _ => 0

/-- Every replicate reuses the same fair binary sample point. -/
def t20RepeatedDraws : ℕ → Fin 2 → Fin 2 := fun _ b => b

/-- A direct counterexample proves the refutation; no unproved leaves are needed.
Finite sums give the exact probabilities and the simulated entries. At the two
sample points the smoothed entries are respectively 1 and `1 / (n + 2)`.
Use the reciprocal limit and uniqueness of real limits, then intersect the
result with the hypothetical probability-one event of the printed limits. -/
theorem T20_assembly : T20WholeStatement := by
  classical
  let P := t20FairDesign
  let F := t20FairPopulation
  let Z := t20RepeatedDraws
  let μ := designMeasure P
  have hprob : IsProbabilityMeasure μ := by
    constructor
    norm_num [μ, P, designMeasure, t20FairDesign, Fin.sum_univ_succ,
      Measure.add_apply, Measure.smul_apply]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have : IsProbabilityMeasure μ := hprob
  have hpi : ∀ (i : Fin 1) (d : Fin 2), pi F i d = (1 / 2 : ℝ) := by
    intro i d
    fin_cases d <;>
      norm_num [F, t20FairPopulation, pi, expectation, indicator,
        t20FairDesign, Fin.sum_univ_succ]
  have hpos : ∀ d, Positivity F d := by
    intro d i
    rw [hpi i d]
    norm_num
  have hexact : jointPi F 0 0 0 0 = (1 / 2 : ℝ) := by
    norm_num [F, t20FairPopulation, jointPi, expectation, indicator,
      t20FairDesign, Fin.sum_univ_succ]
  have hcross : jointPi F 0 0 0 1 = 0 := by
    norm_num [F, t20FairPopulation, jointPi, expectation, indicator,
      t20FairDesign, Fin.sum_univ_succ]
  have hzero : ∀ b n, t20CrossEntry F 0 1 Z b n 0 0 = 0 := by
    intro b n
    fin_cases b <;>
      simp [t20CrossEntry, F, Z, t20FairPopulation, t20RepeatedDraws, indicator]
  have hlim : ∀ b, Tendsto (fun n : ℕ => t20SmoothedEntry F 0 Z b n 0 0)
      atTop (𝓝 (if b = 0 then (1 : ℝ) else 0)) := by
    intro b
    fin_cases b
    · have heq : (fun n : ℕ => t20SmoothedEntry F 0 Z 0 n 0 0) =
          fun _ => (1 : ℝ) := by
        funext n
        simp [t20SmoothedEntry, F, Z, t20FairPopulation, t20RepeatedDraws,
          indicator, Nat.cast_add, Nat.cast_one]
        have hn : (n + 2 : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      change Tendsto (fun n : ℕ => t20SmoothedEntry F 0 Z 0 n 0 0) atTop (𝓝 (1 : ℝ))
      rw [heq]
      exact tendsto_const_nhds
    · have hinv : Tendsto (fun n : ℕ => 1 / (n + 2 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (tendsto_add_atTop_iff_nat 2).2
            (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [t20SmoothedEntry, F, Z, t20FairPopulation, t20RepeatedDraws,
        indicator] using hinv
  have hfail : ∀ b, ¬ Tendsto (fun n : ℕ => t20SmoothedEntry F 0 Z b n 0 0)
      atTop (𝓝 (jointPi F 0 0 0 0)) := by
    intro b hb
    have heq := tendsto_nhds_unique (hlim b) hb
    rw [hexact] at heq
    fin_cases b <;> norm_num at heq
  have hnot : ∀ b, ¬ T20MatrixLimits F 0 1 Z b := by
    intro b hb
    exact hfail b (hb 0 0).1
  have hnotae : ¬ (∀ᵐ b ∂μ, T20MatrixLimits F 0 1 Z b) := by
    intro h
    obtain ⟨b, hb⟩ := h.exists
    exact hnot b hb
  refine ⟨P, F, Z, ?_, ?_, ?_, hpos, hprob, ?_, ?_, ?_, hexact,
    hcross, hzero, hlim, hfail, Filter.Eventually.of_forall hnot, hnotae⟩
  · intro z
    rfl
  · intro z i
    rfl
  · intro i d
    rfl
  · intro r
    exact measurable_id
  · intro r
    exact Measure.map_id
  · intro r b
    rfl

end

end SAP.P013b.WH.W1
