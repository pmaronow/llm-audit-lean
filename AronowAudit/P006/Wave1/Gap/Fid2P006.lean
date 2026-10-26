import AronowAudit.P006.Wave1.CorrectedRanking.N1
import AronowAudit.P006.Wave1.CorrectedRanking.N3
import AronowAudit.P006.Wave1.CorrectedRanking.N6

/-! P006-T13: corrected ranking with integrable treated estimator residuals. -/

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

local instance instDecidableFid2P006 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The outcome/design assumptions, with no evaluated-estimator integrability requirement. -/
structure T13_OutcomeStanding {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) : Prop where
  px_probability : IsProbabilityMeasure E.PX
  means_measurable : Measurable E.μ0 ∧ Measurable E.μ1
  means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX
  law_probability : ∀ π, Admissible π → IsProbabilityMeasure (E.law π)
  measurable_units : ∀ π, Admissible π → ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i)
  integrable_units : ∀ π, Admissible π → ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π)
  covariate_law : ∀ π, Admissible π → ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX
  potential_law_fixed : ∀ π π', Admissible π → Admissible π' → ∀ i,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω))
      (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω)) (E.law π) (E.law π')
  iid_independent : ∀ π, Admissible π →
    iIndepFun (fun i ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω)) (E.law π)
  iid_identical : ∀ π, Admissible π → ∀ i j,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω))
      (fun ω => (E.X j ω, E.Y0 j ω, E.Y1 j ω, E.T π j ω)) (E.law π) (E.law π)
  conditional_means : ∀ π, Admissible π → ∀ i,
    (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ0 (E.X i ω)) ∧
    (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ1 (E.X i ω))
  bernoulli : ∀ π, Admissible π → ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω))
  ignorability : ∀ π, Admissible π → ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
    (E.law π)[(fun ω => bit (E.T π i ω) *
      B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) *
        (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
          (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω)

/-- A proof-only experiment with the same outcomes and design and a zero estimator. -/
def T13_zeroEstimator {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) : Experiment Ω C n :=
  { E with μhat := fun _ _ _ => 0 }

lemma T13_zeroEstimator_standing {Ω : Type v} {C : Type u}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : T13_OutcomeStanding E) :
    Standing (T13_zeroEstimator E) := by
  refine {
    px_probability := hD.px_probability
    means_measurable := hD.means_measurable
    means_integrable := hD.means_integrable
    law_probability := hD.law_probability
    measurable_units := hD.measurable_units
    integrable_units := ?_
    covariate_law := hD.covariate_law
    potential_law_fixed := hD.potential_law_fixed
    iid_independent := hD.iid_independent
    iid_identical := hD.iid_identical
    conditional_means := hD.conditional_means
    bernoulli := hD.bernoulli
    ignorability := hD.ignorability }
  intro π hπ i
  exact ⟨(hD.integrable_units π hπ i).1, (hD.integrable_units π hπ i).2,
    integrable_zero _ _ _⟩

/-- The treated-outcome moment uses no property of the original estimator. -/
lemma T13_outcome_moment {Ω : Type v} {C : Type u}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : T13_OutcomeStanding E)
    (π : C → ℝ) (hπ : Admissible π) (i : Fin n) :
    (E.law π)[fun ω => bit (E.T π i ω) * E.Y1 i ω | E.covariateSigma i]
      =ᵐ[E.law π] fun ω => π (E.X i ω) * E.μ1 (E.X i ω) :=
  CorrectedRanking.n1_proof (T13_zeroEstimator E) (T13_zeroEstimator_standing E hD) π hπ i

/-- Residual integrability suffices for the integrability and conditional mean of the reward. -/
lemma T13_reward_moment {Ω : Type v} {C : Type u}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : T13_OutcomeStanding E)
    (hR : ∀ π, Admissible π → ∀ i,
      Integrable (fun ω => bit (E.T π i ω) *
        (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 {π | Admissible π})
    (π : C → ℝ) (hπ : Admissible π) (i : Fin n) :
    Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) (E.law π) ∧
    (E.law π)[fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω) | E.covariateSigma i]
      =ᵐ[E.law π] fun ω => E.τ (E.X i ω) * π (E.X i ω) := by
  let μ := E.law π
  let T : Ω → ℝ := fun ω => bit (E.T π i ω)
  let b : Ω → ℝ := fun ω => E.μ0 (E.X i ω)
  let a : Ω → ℝ := fun ω => T ω * E.Y1 i ω
  let d : Ω → ℝ := fun ω => T ω * b ω
  let c : Ω → ℝ := fun ω => T ω * (E.μhat π ω (E.X i ω) - b ω)
  haveI : IsProbabilityMeasure μ := hD.law_probability π hπ
  have hT := (hD.measurable_units π hπ i).2.2.2
  have hb : Integrable b μ :=
    ((hD.covariate_law π hπ i).comp hD.means_measurable.1).integrable_iff.2
      hD.means_integrable.1
  have hbsm : StronglyMeasurable[E.covariateSigma i] b :=
    (hD.means_measurable.1.comp (comap_measurable (E.X i))).stronglyMeasurable
  have ha : Integrable a μ :=
    CorrectedRanking.integrable_bit_mul hT (hD.integrable_units π hπ i).2
  have hd : Integrable d μ := CorrectedRanking.integrable_bit_mul hT hb
  have hc : Integrable c μ := hR π hπ i
  have hTi : Integrable T μ := CorrectedRanking.integrable_bit hT
  have hpull : μ[d | E.covariateSigma i] =ᵐ[μ] fun ω => b ω * π (E.X i ω) := by
    have hmul : Integrable (b * T) μ :=
      hd.congr (Eventually.of_forall fun ω => by show T ω * b ω = b ω * T ω; ring)
    have h := condExp_mul_of_stronglyMeasurable_left hbsm hmul hTi
    have hB := hD.bernoulli π hπ i
    have hcomm : μ[d | E.covariateSigma i] =ᵐ[μ] μ[b * T | E.covariateSigma i] := by
      apply condExp_congr_ae
      exact Eventually.of_forall (fun ω => mul_comm _ _)
    filter_upwards [hcomm, h, hB] with ω hcomm h hB
    simpa only [Pi.mul_apply, T] using hcomm.trans (h.trans (congrArg (fun z => b ω * z) hB))
  have hcond : μ[(a - d) - c | E.covariateSigma i] =ᵐ[μ]
      fun ω => (π (E.X i ω) * E.μ1 (E.X i ω) - b ω * π (E.X i ω)) - 0 := by
    have hsub1 := condExp_sub ha hd (E.covariateSigma i)
    have hsub2 := condExp_sub (ha.sub hd) hc (E.covariateSigma i)
    have hA := T13_outcome_moment E hD π hπ i
    have hC := hU π hπ i
    filter_upwards [hsub1, hsub2, hA, hpull, hC] with ω hsd hsc hA hd hC
    simp only [Pi.sub_apply] at hsd hsc
    rw [hsc, hsd, hA, hd, hC]
  have hrewrite : (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω)) =
      (a - d) - c := by
    funext ω
    dsimp [a, d, c, T, b]
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit] <;> ring
  constructor
  · rw [hrewrite]
    exact (ha.sub hd).sub hc
  · rw [hrewrite]
    filter_upwards [hcond] with ω h
    rw [h]
    dsimp [b, Experiment.τ]
    ring

/-- Expected weighted reward and the normalized reference-measure identity. -/
lemma T13_score_identity {Ω : Type v} {C : Type u}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P0 : Measure C) [IsProbabilityMeasure P0]
    (hD : T13_OutcomeStanding E) (hac : P0 ≪ E.PX) (hτ : Integrable E.τ P0)
    (hR : ∀ π, Admissible π → ∀ i,
      Integrable (fun ω => bit (E.T π i ω) *
        (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 {π | Admissible π})
    (hreward : ∀ π, Admissible π → ∀ i,
      Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω)) (E.law π))
    (π : C → ℝ) (hπ : Admissible π) :
    E.expectedWeightedTT (referenceWeight n P0 E.PX) π =
      (n : ℝ) * (∫ x, E.τ x * π x * referenceWeight n P0 E.PX x ∂E.PX) ∧
    (n : ℝ) * (∫ x, E.τ x * π x * referenceWeight n P0 E.PX x ∂E.PX) =
      ∫ x, E.τ x * π x ∂P0 := by
  haveI : IsProbabilityMeasure E.PX := hD.px_probability
  haveI : IsProbabilityMeasure (E.law π) := hD.law_probability π hπ
  let g := referenceWeight n P0 E.PX
  have hg : Measurable g :=
    measurable_const.mul (Measure.measurable_rnDeriv P0 E.PX).ennreal_toReal
  have hτm : Measurable E.τ := hD.means_measurable.2.sub hD.means_measurable.1
  have hτπ : Integrable (fun x => E.τ x * π x) P0 := by
    apply hτ.mul_bdd hπ.1.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 x).1]
      exact (hπ.2 x).2)
  have hRN := CorrectedRanking.n3_proof P0 E.PX hac n E.hn (fun x => E.τ x * π x) hτπ
  have hunit (i : Fin n) :
      (∫ ω, (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω) ∂E.law π) =
        ∫ x, E.τ x * π x * referenceWeight n P0 E.PX x ∂E.PX := by
    let Z : Ω → ℝ := fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω)
    let G : Ω → ℝ := fun ω => g (E.X i ω)
    have hX := (hD.measurable_units π hπ i).1
    have hm : E.covariateSigma i ≤ (inferInstance : MeasurableSpace Ω) := hX.comap_le
    have hG : StronglyMeasurable[E.covariateSigma i] G :=
      (hg.comp (comap_measurable (E.X i))).stronglyMeasurable
    have hmoment := T13_reward_moment E hD hR hU π hπ i
    have hZ : Integrable Z (E.law π) := hmoment.1
    have hGZ : Integrable (G * Z) (E.law π) := by
      refine (hreward π hπ i).congr (Eventually.of_forall fun ω => ?_)
      show (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω) = G ω * Z ω
      simp only [G, Z, g]
      ring
    have hpull := condExp_mul_of_stronglyMeasurable_left hG hGZ hZ
    have hmean := hmoment.2
    have hCE : (E.law π)[fun ω => Z ω * G ω | E.covariateSigma i] =ᵐ[E.law π]
        fun ω => E.τ (E.X i ω) * π (E.X i ω) * g (E.X i ω) := by
      have hcomm : (E.law π)[fun ω => Z ω * G ω | E.covariateSigma i] =ᵐ[E.law π]
          (E.law π)[G * Z | E.covariateSigma i] := by
        apply condExp_congr_ae
        exact Eventually.of_forall (fun ω => mul_comm _ _)
      filter_upwards [hcomm, hpull, hmean] with ω hcomm hpull hmean
      rw [hcomm, hpull]
      simp only [Pi.mul_apply]
      rw [hmean]
      dsimp [G]
      ring
    calc
      _ = ∫ ω, (E.law π)[fun η => Z η * G η | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp hm).symm
      _ = ∫ ω, E.τ (E.X i ω) * π (E.X i ω) * g (E.X i ω) ∂E.law π := integral_congr_ae hCE
      _ = _ := ((hD.covariate_law π hπ i).comp ((hτm.mul hπ.1).mul hg)).integral_eq
  refine ⟨?_, hRN.2⟩
  unfold Experiment.expectedWeightedTT wWeightedTT
  rw [integral_finsetSum Finset.univ (fun i _ => hreward π hπ i)]
  simp_rw [hunit]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The measurable positive-effect rule attains the finite maximum. -/
lemma T13_optimum {Ω : Type v} {C : Type u}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P0 : Measure C) [IsProbabilityMeasure P0]
    (hD : T13_OutcomeStanding E) (hac : P0 ≪ E.PX) (hτ : Integrable E.τ P0)
    (hR : ∀ π, Admissible π → ∀ i,
      Integrable (fun ω => bit (E.T π i ω) *
        (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 {π | Admissible π})
    (hreward : ∀ π, Admissible π → ∀ i,
      Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω)) (E.law π)) :
    IsBest {π | Admissible π} (E.expectedWeightedTT (referenceWeight n P0 E.PX))
      (positiveRule E.τ) ∧
    bestValue {π | Admissible π} (E.expectedWeightedTT (referenceWeight n P0 E.PX)) =
      ∫ x, positivePart (E.τ x) ∂P0 := by
  have hτm : Measurable E.τ := hD.means_measurable.2.sub hD.means_measurable.1
  have hstar : Admissible (positiveRule E.τ) := by
    refine ⟨?_, ?_⟩
    · exact Measurable.ite (measurableSet_lt measurable_const hτm) measurable_const measurable_const
    · intro x
      by_cases h : 0 < E.τ x <;> simp [positiveRule, h]
  have hid (π : C → ℝ) (hπ : Admissible π) :
      E.expectedWeightedTT (referenceWeight n P0 E.PX) π = ∫ x, E.τ x * π x ∂P0 := by
    have h := T13_score_identity E P0 hD hac hτ hR hU hreward π hπ
    exact h.1.trans h.2
  have hint (π : C → ℝ) (hπ : Admissible π) : Integrable (fun x => E.τ x * π x) P0 := by
    apply hτ.mul_bdd hπ.1.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 x).1]
      exact (hπ.2 x).2)
  have hpart : Integrable (fun x => positivePart (E.τ x)) P0 := by
    simpa only [positivePart_eq_max] using hτ.pos_part
  have hstarval : E.expectedWeightedTT (referenceWeight n P0 E.PX) (positiveRule E.τ) =
      ∫ x, positivePart (E.τ x) ∂P0 := by
    rw [hid _ hstar]
    rfl
  have hbest : IsBest {π | Admissible π}
      (E.expectedWeightedTT (referenceWeight n P0 E.PX)) (positiveRule E.τ) := by
    refine ⟨hstar, ?_⟩
    intro π hπ
    rw [hid π hπ, hstarval]
    exact integral_mono (hint π hπ) hpart (fun x => pointwise_policy_gain_le _ _ (hπ.2 x))
  exact ⟨hbest, (bestValue_eq hbest).trans hstarval⟩

/-- The five corrected ranking conclusions with treated-residual assumptions. -/
theorem T13_corrected_ranking_treated_residuals :
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] {Ω : Fin K → Type v}
    [∀ k, MeasurableSpace (Ω k)]
    (nk : Fin K → ℕ) (E : (k : Fin K) → Experiment (Ω k) C (nk k))
    (P0 : Measure C) (hP0 : IsProbabilityMeasure P0)
    (hD : ∀ k, T13_OutcomeStanding (E k))
    (hmu0 : ∀ j k, (E j).μ0 = (E k).μ0)
    (hac : ∀ k, P0 ≪ (E k).PX)
    (hτ : ∀ k, Integrable (E k).τ P0)
    (hR : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => bit ((E k).T π i ω) *
        ((E k).μhat π ω ((E k).X i ω) -
          (E k).μ0 ((E k).X i ω))) ((E k).law π))
    (hU : ∀ k, TreatedUnbiased (E k) (E k).μ0 {π | Admissible π})
    (hreward : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => ((E k).observed π ω i -
        (E k).μhat π ω ((E k).X i ω)) * bit ((E k).T π i ω) *
        referenceWeight (nk k) P0 (E k).PX ((E k).X i ω)) ((E k).law π)),
    (∀ k π, Admissible π →
      (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX) π =
        (nk k : ℝ) * (∫ x, (E k).τ x * π x *
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) ∧
      (nk k : ℝ) * (∫ x, (E k).τ x * π x *
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) =
        (∫ x, (E k).τ x * π x ∂P0)) ∧
    (∀ k, IsBest {π | Admissible π}
      ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (positiveRule (E k).τ) ∧
      bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, positivePart ((E k).τ x) ∂P0)) ∧
    UniformRankPreservation (fun _ => {π | Admissible π})
      (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (fun k => (E k).τ) ∧
    ((∀ k x, 0 ≤ (E k).τ x) →
      (∀ k, bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, (E k).τ x ∂P0)) ∧
      RelativeRankPreservation P0 (fun _ => {π | Admissible π})
        (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
        (fun k => (E k).τ))  := by
  intro K C _ Ω _ nk E P0 hP0 hD _hmu0 hac hτ hR hU hreward
  have hbest := fun k => T13_optimum (E k) P0 (hD k) (hac k) (hτ k)
    (hR k) (hU k) (hreward k)
  refine ⟨fun k π hπ => T13_score_identity (E k) P0 (hD k) (hac k) (hτ k)
    (hR k) (hU k) (hreward k) π hπ, hbest, ?_⟩
  exact CorrectedRanking.n6_proof P0
    (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
    (fun k => (E k).τ) hτ (fun k => (hbest k).2)

end
end AronowAudit.P006.Wave1
