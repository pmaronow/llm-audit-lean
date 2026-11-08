import SAP.P027a.Defs.WholeW2
import SAP.P027a.Bridge
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B1
import AronowAudit.P027.Wave1.UniformStart.N5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W2

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory
open SAP.P027a SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

/-- T11 needs no new mathematical leaf. Existing cross-moment and Proposition 1
proofs give all identities; finite sums give integrability, and the positive
population-size square permits the fixed-population equivalence. -/
theorem T11_assembly : T11WholeStatement := by
  have havg : WholeOutcomeAverage := by
    intro U Ω Ξ _ _ _ μ _ D hv hp hu x hx β ε hε
    have hcore := AronowAudit.P027.outcome_averaged_conservativity μ
      (toAudit D hv) hp hu x hx β ε hε
    have hi : Integrable (fun ξ => biasA D (rawOutcomes x β ε ξ)) μ := by
      unfold biasA
      apply integrable_finsetSum
      intro k _
      apply integrable_finsetSum
      intro l _
      split_ifs with hkl
      · exact (AronowAudit.P027.raw_model_cross_moment μ x β ε hε k l hkl.1).1
      · exact integrable_const 0
    have hb (y : U → ℝ) : meanSamplingBias D y =
        biasA D y/(Fintype.card U : ℝ)^2 :=
      AronowAudit.P027.mean_bias_identity (toAudit D hv) hp y
    refine ⟨?_, hcore.1, hi, ?_, hcore.2⟩
    · intro k
      change (∫ ξ, β*x k + ε k ξ ∂μ) = β*x k
      rw [integral_add (integrable_const _) (hε.1 k).1,
        integral_const, show (∫ ξ, ε k ξ ∂μ) = 0 from (hε.1 k).2]
      simp
    · simp_rw [hb]
      exact hi.div_const _
  have hfixed : WholePopulationwiseConservativity := by
    intro U Ω _ _ D hv hp hu y
    have hb : meanSamplingBias D y = biasA D y/(Fintype.card U : ℝ)^2 :=
      AronowAudit.P027.mean_bias_identity (toAudit D hv) hp y
    have hn : 0 < (Fintype.card U : ℝ)^2 :=
      sq_pos_of_pos (by exact_mod_cast hu)
    have he : 0 ≤ meanSamplingBias D y ↔ 0 ≤ biasA D y := by
      rw [hb]
      exact (le_div_iff₀ hn).trans (by simp)
    refine ⟨hb, he, fun hs => he.mpr ?_⟩
    exact AronowAudit.P027.biasA_same_sign (toAudit D hv) hp y hs
  refine ⟨havg, hfixed, ?_⟩
  have hv : Valid random8 := valid_fromAudit AronowAudit.P027.random8
  have hp : Positive random8 := AronowAudit.P027.random8_positive
  have hx : ∀ k, 1 ≤ randomSize8 k := AronowAudit.P027.random8_counterexample.1
  have hc : biasA random8 randomSize8 = 176 :=
    AronowAudit.P027.random8_outcome_coefficient.1
  have hneg : biasA random8 randomOutcome8 = -16 :=
    AronowAudit.P027.random8_counterexample.2.1
  refine ⟨hv, hp, hx, hc, AronowAudit.P027.random8_outcome_coefficient.2,
    AronowAudit.P027.random8_counterexample.2.1, ?_, ?_⟩
  · have hb := (hfixed random8 hv hp (by decide) randomOutcome8).1
    rw [hb, hneg]
    norm_num
  · intro Ξ _ μ _ ε hε
    have he (β : ℝ) := havg μ random8 hv hp (by decide) randomSize8 hx β ε hε
    constructor
    · intro β
      have ha := (he β).2.2.2.2.1
      have hb := (he β).2.2.2.2.2.2.1
      rw [hc] at ha hb
      constructor
      · simpa only [mul_comm] using ha
      · simpa only [Fintype.card_fin, Nat.cast_ofNat, show (8:ℝ)^2 = 64 by norm_num,
          mul_comm] using hb
    · have ha := (he (3/2)).2.2.2.2.1
      rw [hc] at ha
      norm_num at ha ⊢
      exact ha

/-- Exact half-open start-cell selection for the repaired eight-unit vector.
Prove the prefix sums are 0 for unit 0 and 1+(k-1)/7 for k>0. The skip is 1;
the grid point u selects unit 0 and u+1 selects precisely unit g+1 when
g/7 <= u < (g+1)/7. Finite cases and linear arithmetic prove the endpoints too.
The premise is inhabited for every g (take u=g/7). -/
def T13_L1 : Prop :=
  ∀ (g : Fin 7) (u : ℝ), u ∈ certaintyCell8 g →
    systematicSample certaintyProb8 2 u = certainty8.selected g

/-- Independent full-vector rejection sampling. Acceptance positivity is
proved in the assembly from the all-zero NB atom, rather than imposed on the
whole target. For n prior rejections and an accepted vector in B, use the
finite-cylinder formula for infinitePi to obtain (1-p)^n P(B inter F).
Sum these disjoint first-success events: the geometric series gives
P(B inter F)/p and a null nontermination event. First-success events are
measurable countable intersections/unions; use them also to prove measurability
of redrawSizeOutput, including its explicit default. Extensionality of measures
then identifies its pushforward with the conditional measure. This step uses
only a probability law and 0<p<=1, and applies to p=1 as well.
Useful exact donors: MeasureTheory.Measure.infinitePi_pi,
MeasureTheory.measure_iUnion, ENNReal.tsum_geometric, measurable_to_countable',
MeasureTheory.Measure.ext_of_singleton, ProbabilityTheory.cond_apply, and
AronowAudit.P027.Wave1.all_pps_product_probability. Work directly in ENNReal
to avoid unnecessary real-conversion limits. Expected proof size: 150–300 lines. -/
def T13_L2 : Prop :=
  ∀ {N : ℕ}, 2 ≤ N → ∀ m : ℕ, 0 < m → m < N →
    0 < nbProductLawN N (feasibleSizeVectors N m) →
      (∀ᵐ w ∂redrawSizeSequenceLaw N, ∃ n, w n ∈ feasibleSizeVectors N m) ∧
      Measurable (redrawSizeOutput N m) ∧
      (redrawSizeSequenceLaw N).map (redrawSizeOutput N m) = acceptedSizeLaw N m

/-- The only new leaves are exact cell selection and the first-acceptance law.
Cap regularity, automatic integrability, all donor applications and normalization
of the accepted size law are proved here. -/
theorem T13_assembly (h1 : T13_L1) (h2 : T13_L2) : T13WholeStatement := by
  have hstart : IsProbabilityMeasure systematicStartLaw := by
    constructor
    simp [systematicStartLaw, Real.volume_Ico]
  have hfeas : PPSFeasibility := by
    intro N hN m hm hmN x hx
    exact ⟨fun Ω _ D hv hpi => AronowAudit.P027.pps_feasibility_necessary hN m hm hmN x hx
      (toAudit D hv) hpi, AronowAudit.P027.capped_pps_exists hN m hm hmN x hx⟩
  have hcap : WholeCapRegularity := by
    intro N x hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold ppsCapSum
      fun_prop
    · intro a b hab
      exact Finset.sum_le_sum (fun k _ =>
        min_le_min_left 1 (mul_le_mul_of_nonneg_right hab (hx k).le))
    · simp [ppsCapSum]
    · intro c hc
      have hk (k : Fin N) : 1 ≤ c*x k := by
        apply (div_le_iff₀ (hx k)).mp
        exact le_trans (Finset.single_le_sum
          (fun a _ => (one_div_pos.mpr (hx a)).le) (Finset.mem_univ k)) hc
      simp [ppsCapSum, fun k => min_eq_left (hk k)]
  have hsys : WholeSystematicConstruction := by
    intro N hN m hm hmN π hp hs
    have h := AronowAudit.P027.Wave1.systematic_probability_construction_proof
      hN m hm hmN π hp hs
    have hE (k : Fin N) : MeasurableSet {u : ℝ | systematicSelected π m u k} :=
      AronowAudit.P027.Wave1.systematic_selection_measurable π m hm hs k
    refine ⟨hstart, h.1, ?_, ?_⟩
    · intro k
      refine ⟨hE k, ?_, h.2 k⟩
      exact (integrable_const (1:ℝ)).indicator (hE k)
    · intro k l
      let E : Set ℝ := {u | systematicSelected π m u k} ∩
        {u | systematicSelected π m u l}
      have hmE : MeasurableSet E := (hE k).inter (hE l)
      have hf : (fun u : ℝ =>
          (if systematicSelected π m u k then (1:ℝ) else 0) *
          (if systematicSelected π m u l then (1:ℝ) else 0)) =
          E.indicator (fun _ => (1:ℝ)) := by
        funext u
        by_cases hk : systematicSelected π m u k <;>
          by_cases hl : systematicSelected π m u l <;> simp [E, hk, hl]
      constructor
      · rw [hf]
        exact (integrable_const (1:ℝ)).indicator hmE
      · change (∫ u, ((fun v : ℝ =>
            (if systematicSelected π m v k then (1:ℝ) else 0) *
            (if systematicSelected π m v l then (1:ℝ) else 0)) u)
            ∂systematicStartLaw) = (systematicStartLaw E).toReal
        rw [hf, integral_indicator_const 1 hmE]
        simp [measureReal_def]
  have hspec : WholePPSSpecializations := by
    intro N hN m hm hmN x hx
    have hs : 0 < ∑ a, x a := lt_of_lt_of_le (hx ⟨0, by omega⟩)
      (Finset.single_le_sum (fun k _ => (hx k).le) (Finset.mem_univ _))
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
    have hex := AronowAudit.P027.capped_pps_exists hN m hm hmN x hx
    constructor
    · intro hf
      refine ⟨div_pos hmR hs, hsys hN m hm hmN (printedPPS m x) ?_ ?_⟩
      · intro k
        exact ⟨div_pos (mul_pos hmR (hx k)) hs,
          (div_le_iff₀ hs).mpr (by simpa using hf k)⟩
      · have hsum : (∑ k, min 1 ((m:ℝ)/(∑ a, x a)*x k)) = m := (hex.2 hf).1
        have heq (k : Fin N) : min 1 ((m:ℝ)/(∑ a, x a)*x k) = printedPPS m x k :=
          (hex.2 hf).2 k
        simpa only [heq] using hsum
    · obtain ⟨c, hc, hsum⟩ := hex.1
      refine ⟨c, hc, hsum, hsys hN m hm hmN _ ?_ hsum⟩
      intro k
      exact ⟨lt_min (by norm_num) (mul_pos hc (hx k)), min_le_left _ _⟩
  have hw : WholeCertainty8 := by
    have hd := AronowAudit.P027.redistributed_witness
    have hp := AronowAudit.P027.certainty8_probabilities
    have hsub (g : Fin 7) : certaintyCell8 g ⊆ Set.Ico (0:ℝ) 1 := by
      intro u hu
      have hg0 : 0 ≤ (g:ℝ) := Nat.cast_nonneg _
      have hg1 : (g:ℝ)+1 ≤ 7 := by exact_mod_cast Nat.succ_le_of_lt g.isLt
      constructor <;> dsimp [certaintyCell8] at hu <;> linarith [hu.1, hu.2]
    have hpart : ∀ u ∈ Set.Ico (0:ℝ) 1, ∃! g : Fin 7, u ∈ certaintyCell8 g := by
      intro u hu
      have hcover : ∃ g : Fin 7, u ∈ certaintyCell8 g := by
        by_cases h0 : u < 1/7
        · exact ⟨0, by norm_num [certaintyCell8]; exact ⟨hu.1, h0⟩⟩
        by_cases h1 : u < 2/7
        · exact ⟨1, by norm_num [certaintyCell8]; exact ⟨le_of_not_gt h0, h1⟩⟩
        by_cases h2 : u < 3/7
        · exact ⟨2, by norm_num [certaintyCell8]; exact ⟨le_of_not_gt h1, h2⟩⟩
        by_cases h3 : u < 4/7
        · exact ⟨3, by norm_num [certaintyCell8]; exact ⟨le_of_not_gt h2, h3⟩⟩
        by_cases h4 : u < 5/7
        · exact ⟨4, by norm_num [certaintyCell8]; exact ⟨le_of_not_gt h3, h4⟩⟩
        by_cases h5 : u < 6/7
        · exact ⟨5, by norm_num [certaintyCell8]; exact ⟨le_of_not_gt h4, h5⟩⟩
        · exact ⟨6, by norm_num [certaintyCell8]; exact ⟨le_of_not_gt h5, hu.2⟩⟩
      obtain ⟨g, hg⟩ := hcover
      refine ⟨g, hg, ?_⟩
      intro j hj
      apply Fin.ext
      have hgj : g.val = j.val := by
        rcases lt_trichotomy g.val j.val with hlt | heq | hlt
        · have hi : (g:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hlt
          dsimp [certaintyCell8] at hg hj
          linarith [hg.2, hj.1]
        · exact heq
        · have hi : (j:ℝ)+1 ≤ (g:ℝ) := by exact_mod_cast hlt
          dsimp [certaintyCell8] at hg hj
          linarith [hj.2, hg.1]
      exact hgj.symm
    have hmass (g : Fin 7) : (systematicStartLaw (certaintyCell8 g)).toReal = 1/7 := by
      have hmcell : MeasurableSet (certaintyCell8 g) := measurableSet_Ico
      rw [systematicStartLaw, Measure.restrict_apply hmcell,
        Set.inter_eq_left.mpr (hsub g)]
      change (volume (Set.Ico ((g:ℝ)/7) (((g:ℝ)+1)/7))).toReal = 1/7
      rw [Real.volume_Ico]
      have he : ((g:ℝ)+1)/7-(g:ℝ)/7 = 1/7 := by ring
      rw [he]
      norm_num
    refine ⟨valid_fromAudit AronowAudit.P027.certainty8, hp.1, hd.1, hd.2.2,
      hp.2.1, hp.2.2, hd.2.1, by norm_num, h1, hmass, ?_⟩
    intro F
    have hcompl : systematicStartLaw (Set.Ico (0:ℝ) 1)ᶜ = 0 := by
      simp [systematicStartLaw]
    have hstat := AronowAudit.P027.Wave1.UniformStart.n5_proof
      systematicStartLaw (Set.Ico (0:ℝ) 1) hcompl certaintyCell8
      (fun _ => measurableSet_Ico) hsub hpart
      (fun u => F (systematicSample certaintyProb8 2 u))
      (fun g => F (certainty8.selected g)) (fun g u hu => congrArg F (h1 g u hu))
    refine ⟨hstat.1, hstat.2.trans ?_⟩
    simp_rw [hmass]
    rfl
  have hr : WholeRedrawRecipe := by
    intro N hN m hm hmN
    have hp : IsProbabilityMeasure (nbProductLawN N) :=
      AronowAudit.P027.Wave1.all_pps_product_probability N
    have hF : MeasurableSet (feasibleSizeVectors N m) := (Set.to_countable _).measurableSet
    have hz : (fun _ : Fin N => 0) ∈ feasibleSizeVectors N m := by
      intro k
      simp only [Nat.cast_zero, add_zero, mul_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact_mod_cast hmN.le
    have hsingle : 0 < nbProductLawN N {fun _ : Fin N => 0} := by
      have hrpos : 0 < (nbProductLawN N {fun _ : Fin N => 0}).toReal := by
        change 0 < (AronowAudit.P027.nbProductLawN N {fun _ : Fin N => 0}).toReal
        rw [AronowAudit.P027.Wave1.all_pps_product_singleton_real]
        exact Finset.prod_pos (fun k _ => AronowAudit.P027.Wave1.all_pps_nbMass_pos 0)
      exact (ENNReal.toReal_pos_iff.mp hrpos).1
    have hpos : 0 < nbProductLawN N (feasibleSizeVectors N m) :=
      lt_of_lt_of_le hsingle (measure_mono (Set.singleton_subset_iff.mpr hz))
    have hc : IsProbabilityMeasure (acceptedSizeLaw N m) :=
      cond_isProbabilityMeasure (ne_of_gt hpos)
    have hseq : IsProbabilityMeasure (redrawSizeSequenceLaw N) := by
      unfold redrawSizeSequenceLaw
      infer_instance
    obtain ⟨hae, hmout, hmap⟩ := h2 hN m hm hmN hpos
    refine ⟨hp, hpos, hc, ?_, hseq, hae, hmout, hmap⟩
    intro B _hB
    rw [acceptedSizeLaw, cond_apply hF, ENNReal.toReal_mul, ENNReal.toReal_inv,
      Set.inter_comm]
    ring
  exact ⟨hfeas, hcap, hsys, hspec, hw, hr⟩

end
end SAP.P027a.WH.W2
