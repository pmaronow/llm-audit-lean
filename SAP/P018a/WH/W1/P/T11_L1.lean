import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W1.P.T11_L1

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open AronowAudit.P018
open AronowAudit.P018.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

local instance sign_fairProbability : IsProbabilityMeasure SAP.P018a.fairLaw := by
  change IsProbabilityMeasure AronowAudit.P018.fairLaw
  exact printed_fair_probability

local instance sign_unitProbability {N : ℕ} :
    IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin N => SAP.P018a.fairLaw))
  infer_instance

lemma signKernel_toKernel :
    SAP.P018a.Bridge.toKernel SAP.P018a.signKernel = AronowAudit.P018.signKernel := rfl

lemma sign_standing : SAP.P018a.Standing SAP.P018a.signKernel := by
  apply (SAP.P018a.Bridge.kernel_assumptions_agree SAP.P018a.signKernel).mpr
  rw [signKernel_toKernel]
  exact appendixB_standing

lemma sign_beta_zero : SAP.P018a.populationBeta SAP.P018a.signKernel = 0 := by
  unfold SAP.P018a.populationBeta SAP.P018a.populationGram
    SAP.P018a.meanVec SAP.P018a.meanMat SAP.P018a.score
  change ((AronowAudit.P018.populationGram
      (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel))⁻¹).mulVec
    (AronowAudit.P018.meanVec
      ((SAP.P018a.Bridge.toKernel SAP.P018a.signKernel).μ.prod
        (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel).μ)
      (fun uv => AronowAudit.P018.score
        ((SAP.P018a.Bridge.toKernel SAP.P018a.signKernel).X uv.1 uv.2)
        ((SAP.P018a.Bridge.toKernel SAP.P018a.signKernel).Y uv.1 uv.2))) = 0
  rw [signKernel_toKernel]
  exact appendixB_populationBeta

lemma sign_populationGram : SAP.P018a.populationGram SAP.P018a.signKernel = 1 := by
  unfold SAP.P018a.populationGram SAP.P018a.meanMat SAP.P018a.outer
  change AronowAudit.P018.populationGram
    (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel) = 1
  rw [signKernel_toKernel]
  exact appendixB_populationGram

lemma eps_form {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    epsilon signKernel ω d =
      signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) := by
  simp only [epsilon, populationResidual]
  rw [sign_beta_zero]
  simp [dot, signKernel]

lemma printed_endpoints_lt_sap {N : ℕ} (d : Dyad N) : firstUnit d < secondUnit d := by
  exact Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)

lemma members_endpoints {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [members_card]
    simp [ne_of_lt (printed_endpoints_lt_sap d)]

lemma eps_indicator_sum {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    epsilon signKernel ω d =
      ∑ i : Fin N, (if i ∈ members d then (1 : ℝ) else 0) * signValue (ω i) := by
  have hs : (∑ i : Fin N,
      (if i ∈ members d then (1 : ℝ) else 0) * signValue (ω i)) =
      ∑ i ∈ members d, signValue (ω i) := by
    calc
      _ = ∑ i : Fin N, if i ∈ members d then signValue (ω i) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : i ∈ members d <;> simp [h]
      _ = _ := appendixB_indicator_sum (members d) (fun i => signValue (ω i))
  rw [eps_form, hs, members_endpoints d]
  rw [Finset.sum_pair (ne_of_lt (printed_endpoints_lt_sap d))]

lemma eps_integral_zero {N : ℕ} (d : Dyad N) :
    (∫ ω, epsilon signKernel ω d ∂ unitSampleLaw signKernel N) = 0 := by
  simp_rw [eps_form]
  rw [integral_add]
  · have h1 : (∫ ω, SAP.P018a.signValue (ω (firstUnit d))
        ∂SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = 0 := by
      have h := appendixB_coord_mean (firstUnit d)
      change (∫ ω, SAP.P018a.signValue (ω (firstUnit d))
        ∂SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = 0 at h
      exact h
    have h2 : (∫ ω, SAP.P018a.signValue (ω (secondUnit d))
        ∂SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = 0 := by
      have h := appendixB_coord_mean (secondUnit d)
      change (∫ ω, SAP.P018a.signValue (ω (secondUnit d))
        ∂SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = 0 at h
      exact h
    rw [h1, h2]
    norm_num
  · exact printed_finite_integrable _ _
  · exact printed_finite_integrable _ _

lemma eps_product_integral {N : ℕ} (d f : Dyad N) :
    (∫ ω, epsilon signKernel ω d * epsilon signKernel ω f
      ∂ unitSampleLaw signKernel N) = ((members d ∩ members f).card : ℝ) := by
  simp_rw [eps_indicator_sum]
  have hp : (∫ ω, (∑ i : Fin N,
        (if i ∈ members d then (1 : ℝ) else 0) * SAP.P018a.signValue (ω i)) *
      (∑ j : Fin N, (if j ∈ members f then (1 : ℝ) else 0) * SAP.P018a.signValue (ω j))
      ∂SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) =
      ∑ i : Fin N, (if i ∈ members d then (1 : ℝ) else 0) *
        (if i ∈ members f then (1 : ℝ) else 0) := by
    have h := appendixB_linear_product (N := N)
          (fun i => if i ∈ members d then (1 : ℝ) else 0)
          (fun i => if i ∈ members f then (1 : ℝ) else 0)
    change (∫ ω, (∑ i : Fin N,
        (if i ∈ members d then (1 : ℝ) else 0) * SAP.P018a.signValue (ω i)) *
      (∑ j : Fin N, (if j ∈ members f then (1 : ℝ) else 0) * SAP.P018a.signValue (ω j))
      ∂SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = _ at h
    exact h
  have hs : (∑ i : Fin N,
      (if i ∈ members d then (1 : ℝ) else 0) *
        (if i ∈ members f then (1 : ℝ) else 0)) =
      ((members d ∩ members f).card : ℝ) := by
    calc
      _ = ∑ i : Fin N, if i ∈ members d ∩ members f then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hd : i ∈ members d <;> by_cases hf : i ∈ members f <;>
          simp [hd, hf]
      _ = ∑ i ∈ members d ∩ members f, (1 : ℝ) :=
        appendixB_indicator_sum (members d ∩ members f) (fun _ => 1)
      _ = _ := by simp
  rw [hp]
  exact hs

lemma design_const {N : ℕ} : SAP.P018a.design SAP.P018a.signKernel (N := N) =
    fun _ : Fin N → Bool => fun _ : SAP.P018a.Dyad N =>
      (![ (1 : ℝ) ] : SAP.P018a.Vec 1) := by
  funext ω d
  simp [SAP.P018a.design, SAP.P018a.signKernel]

lemma designSigma_bot {N : ℕ} : designSigma signKernel (N := N) = ⊥ := by
  rw [designSigma, design_const]
  exact MeasurableSpace.comap_const _

lemma conditionalMean_eq_zero {N : ℕ} (d : Dyad N) :
    conditionalResidualMean signKernel d = fun _ => 0 := by
  letI : IsProbabilityMeasure (unitSampleLaw signKernel N) := by
    unfold unitSampleLaw signKernel
    infer_instance
  simp only [conditionalResidualMean, designSigma_bot, MeasureTheory.condExp_bot]
  simp [eps_integral_zero]

lemma conditionalCov_eq_intersection {N : ℕ} (d f : Dyad N) :
    conditionalResidualCov signKernel d f =
      fun _ => ((members d ∩ members f).card : ℝ) := by
  letI : IsProbabilityMeasure (unitSampleLaw signKernel N) := by
    unfold unitSampleLaw signKernel
    infer_instance
  rw [conditionalResidualCov, designSigma_bot,
    conditionalMean_eq_zero, conditionalMean_eq_zero]
  simp only [sub_zero, MeasureTheory.condExp_bot]
  rw [eps_product_integral]

lemma unconditionalCov_eq_intersection {N : ℕ} (d f : Dyad N) :
    ProbabilityTheory.covariance (fun ω => epsilon signKernel ω d)
      (fun ω => epsilon signKernel ω f) (unitSampleLaw signKernel N) =
        ((members d ∩ members f).card : ℝ) := by
  letI : IsProbabilityMeasure (unitSampleLaw signKernel N) := by
    unfold unitSampleLaw signKernel
    infer_instance
  simp only [ProbabilityTheory.covariance, eps_integral_zero, sub_zero]
  rw [eps_product_integral]

lemma conditionalTerm_eq_intersection {N : ℕ} (d f : Dyad N) :
    conditionalTerm signKernel d f =
      ((members d ∩ members f).card : ℝ) • (1 : Mat 1) := by
  letI : IsProbabilityMeasure (unitSampleLaw signKernel N) := by
    unfold unitSampleLaw signKernel
    infer_instance
  ext a b
  fin_cases a
  fin_cases b
  simp only [conditionalTerm, meanMat]
  simp_rw [conditionalCov_eq_intersection]
  have hprob : (unitSampleLaw signKernel N).real Set.univ = 1 := probReal_univ
  simp_rw [design_const]
  rw [integral_const, hprob]
  simp [outer]

lemma conditionalRow_eq {N : ℕ} (hN : 3 ≤ N) (d : Dyad N) :
    W1ConditionalRow signKernel d = !![2 * (N : ℝ) - 2] := by
  have hinj : Function.Injective (members : Dyad N → Finset (Fin N)) := by
    intro x y h
    exact Subtype.ext h
  have hself : ((members d ∩ members d).card : ℝ) = 2 := by
    simp [Finset.inter_self, members_card]
  have hneighbor : ∀ f, f ∈ neighbors d → ((members d ∩ members f).card : ℝ) = 1 := by
    intro f hf
    have hf' : f ≠ d ∧ (members d ∩ members f).Nonempty := by
      simpa [neighbors] using hf
    have hdf : d ≠ f := fun h => hf'.1 h.symm
    have hc := intersection_count members members_card hinj d f
    rw [if_pos hf'.2, if_neg hdf] at hc
    norm_num at hc
    exact_mod_cast hc
  have hcount : (neighbors d).card = 2 * (N - 2) :=
    (AronowAudit.P018.Wave1.dyad_counts_proof N (by omega)).2.1 d
  have hsum : (∑ f ∈ neighbors d, ((members d ∩ members f).card : ℝ)) =
      ((neighbors d).card : ℝ) := by
    calc
      _ = ∑ f ∈ neighbors d, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro f hf
        exact hneighbor f hf
      _ = _ := by simp
  have hcountR : ((neighbors d).card : ℝ) = 2 * ((N : ℝ) - 2) := by
    rw [hcount]
    have hsub : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      exact_mod_cast Nat.cast_sub (show 2 ≤ N by omega)
    rw [Nat.cast_mul, Nat.cast_ofNat, hsub]
  rw [W1ConditionalRow]
  calc
    _ = (((members d ∩ members d).card : ℝ) • (1 : Mat 1)) +
        ∑ f ∈ neighbors d, ((members d ∩ members f).card : ℝ) • (1 : Mat 1) := by
      simp only [conditionalTerm_eq_intersection]
    _ = (2 : ℝ) • (1 : Mat 1) +
        ((neighbors d).card : ℝ) • (1 : Mat 1) := by
      rw [hself]
      have hsumM : (∑ f ∈ neighbors d,
          ((members d ∩ members f).card : ℝ) • (1 : Mat 1)) =
          ((neighbors d).card : ℝ) • (1 : Mat 1) := by
        rw [← Finset.sum_smul, hsum]
      rw [hsumM]
    _ = !![2 * (N : ℝ) - 2] := by
      rw [hcountR]
      ext a b
      fin_cases a
      fin_cases b
      simp [Matrix.one_apply]
      ring

lemma repeatedL_single {N : ℕ} :
    repeatedL (singleRecord signKernel) N = Dreal N := by
  unfold repeatedL singleRecord
  simp only [Nat.cast_one]
  change (∑ d : Dyad N, (1 : ℝ)) = Dreal N
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul, mul_one]
  simp [Dyad, dyads, Dreal, Finset.card_powersetCard, Nat.cast_choose_two]

lemma repeatedGram_single {N : ℕ} (ω : Fin N → Bool) :
    repeatedGram (singleRecord signKernel) ω = sampleGram (design signKernel ω) := by
  unfold repeatedGram sampleGram
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ _ : Fin 1, outer (design signKernel ω d) (design signKernel ω d)) = _
  rw [Fin.sum_univ_one]

lemma repeatedXY_single {N : ℕ} (ω : Fin N → Bool) :
    (∑ d : Dyad N, ∑ t,
      score (repeatedX (singleRecord signKernel) ω d t)
        (repeatedY (singleRecord signKernel) ω d t)) =
      ∑ d : Dyad N, score (design signKernel ω d) (response signKernel ω d) := by
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ _ : Fin 1, score (design signKernel ω d) (response signKernel ω d)) = _
  rw [Fin.sum_univ_one]

lemma repeatedScore_single {N : ℕ} (ω : Fin N → Bool) :
    repeatedBlockScore (singleRecord signKernel)
      (sampleOLS (design signKernel ω) (response signKernel ω)) ω =
      (fun d => score (design signKernel ω d)
        (fittedResidual (design signKernel ω) (response signKernel ω) d)) := by
  funext d
  change (∑ t : Fin 1, score (design signKernel ω d)
      (response signKernel ω d -
        dot (design signKernel ω d) (sampleOLS (design signKernel ω) (response signKernel ω)))) =
    score (design signKernel ω d)
      (response signKernel ω d -
        dot (design signKernel ω d) (sampleOLS (design signKernel ω) (response signKernel ω)))
  rw [Fin.sum_univ_one]

lemma weightedGram_one {N : ℕ} (ω : Fin N → Bool) :
    weightedGram signKernel (fun _ : Dyad N => 1) ω = sampleGram (design signKernel ω) := by
  simp [weightedGram, sampleGram]

lemma reductions {N : ℕ} (ω : Fin N → Bool) :
    repeatedOLS (singleRecord signKernel) ω = sampleOLS (design signKernel ω)
        (response signKernel ω) ∧
    repeatedVariance (singleRecord signKernel) ω =
        sampleVariance members (design signKernel ω) (response signKernel ω) ∧
    weightedOLS signKernel (fun _ : Dyad N => 1) ω =
        sampleOLS (design signKernel ω) (response signKernel ω) ∧
    weightedVariance signKernel (fun _ : Dyad N => 1) ω =
        sampleVariance members (design signKernel ω) (response signKernel ω) := by
  have hro : repeatedOLS (singleRecord signKernel) ω =
      sampleOLS (design signKernel ω) (response signKernel ω) := by
    unfold repeatedOLS sampleOLS
    rw [repeatedGram_single, repeatedXY_single]
  have hrvar : repeatedVariance (singleRecord signKernel) ω =
      sampleVariance members (design signKernel ω) (response signKernel ω) := by
    unfold repeatedVariance sampleVariance
    rw [repeatedGram_single, hro, repeatedScore_single]
  have hwo : weightedOLS signKernel (fun _ : Dyad N => 1) ω =
      sampleOLS (design signKernel ω) (response signKernel ω) := by
    unfold weightedOLS sampleOLS
    rw [weightedGram_one]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    simp [score]
  have hwvar : weightedVariance signKernel (fun _ : Dyad N => 1) ω =
      sampleVariance members (design signKernel ω) (response signKernel ω) := by
    unfold weightedVariance sampleVariance
    rw [weightedGram_one, hwo]
    congr 1
    funext d
    simp [fittedResidual, score]
  exact ⟨hro, hrvar, hwo, hwvar⟩

end SAP.P018a.WH.W1.P.T11_L1

namespace SAP.P018a.WH.W1
open SAP.P018a.WH.W1.P.T11_L1
open AronowAudit.P018.Wave1

theorem T11_L1_proof : SAP.P018a.WH.W1.T11_L1 := by
  change W1T11ScalarMoments
  refine ⟨sign_standing, sign_beta_zero, ?_⟩
  intro N hN
  refine ⟨?_, ?_, sign_populationGram, repeatedL_single, ?_⟩
  · intro ω
    have h := printed_fit (by omega) ω
    change sampleOLS (design signKernel ω) (response signKernel ω) 0 =
      2 / (N : ℝ) * ∑ i, signValue (ω i) at h
    exact h
  · intro d
    refine ⟨?_, conditionalRow_eq hN d, ?_⟩
    · rw [conditionalMean_eq_zero]
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · intro f
      refine ⟨unconditionalCov_eq_intersection d f, ?_⟩
      rw [conditionalCov_eq_intersection]
      exact Filter.Eventually.of_forall (fun _ => rfl)
  · intro ω
    exact reductions ω

end SAP.P018a.WH.W1
