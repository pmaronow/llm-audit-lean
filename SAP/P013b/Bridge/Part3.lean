import SAP.P013b.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b.Bridge
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

theorem translation_error_mean_zero {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ)
    (hd : ∀ i, 0 < pi F i d) :
    expectation P (translationError F d h c) = 0 ∧
    expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      expectation P (differenceTotal F d g) + c * N ∧
    expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      potentialTotal F d + c * N ∧
    expectation P (htCount F d) = N := by
  exact AronowAudit.P013.translation_error_mean_zero (toPopulation F) d g h c hd

theorem fixed_translation_mean_zero {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d e : Fin K) (c : ℝ)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) (hN : 0 < N) (hne : d ≠ e) :
    expectation P (fun z => c * (htCount F d z - N)) = 0 ∧
    expectation P (fun z => c * (htCount F d z - htCount F e z) / N) = 0 := by
  exact AronowAudit.P013.fixed_translation_mean_zero (toPopulation F) d e c hd he hN hne

theorem fixed_count_calibration {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d : Fin K) (m : ℕ) (hm : 1 ≤ m)
    (hcount : ∀ z, ∑ i, indicator F.exposure i d z = (m : ℝ))
    (hmarg : ∀ i, pi F i d = (m : ℝ) / N) (g : Fin N → ℝ) (c : ℝ) :
    ∀ z, htCount F d z = N ∧
      differenceTotal (shiftPopulation F c) d g z = differenceTotal F d g z + c * N := by
  exact AronowAudit.P013.fixed_count_calibration (toPopulation F) hN d m hm hcount hmarg g c

theorem two_report_hypotheses (world : Fin 3) :
    (∀ i d, (twoWearPopulation world).outcome i d = 0 ∨
      (twoWearPopulation world).outcome i d = 1) ∧
    (∀ i d, pi (twoWearPopulation world) i d = 1/2 ∧
      0 < pi (twoWearPopulation world) i d ∧ pi (twoWearPopulation world) i d < 1) ∧
    (∀ z i, observed (recordedPopulation (twoWearPopulation world) twoRecording) z i =
      ∑ d, indicator (twoWearPopulation world).exposure i d z *
        (recordedPopulation (twoWearPopulation world) twoRecording).outcome i d) := by
  exact AronowAudit.P013.two_report_hypotheses world

theorem two_report_data_same (world : Fin 3) :
    recordedData (twoWearPopulation world) twoRecording =
      recordedData (twoWearPopulation 0) twoRecording := by
  exact AronowAudit.P013.two_report_data_same world

theorem two_report_estimator (world : Fin 3) (z : Fin 2 × Fin 2) :
    htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 z =
      (z.1.val : ℝ) := by
  exact AronowAudit.P013.two_report_estimator world z

theorem two_report_moments (world : Fin 3) :
    expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/2 ∧
    variance twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/4 ∧
    causalEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 = 1/2 := by
  exact AronowAudit.P013.two_report_moments world

theorem two_wearing_effects_and_losses (world : Fin 3) :
    causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 1/2 else if world = 1 then 1 else 0) ∧
    lostMean (twoWearPopulation world) twoRecording 0 =
      (if world = 2 then 1/2 else 0) ∧
    lostMean (twoWearPopulation world) twoRecording 1 =
      (if world = 1 then 1/2 else 0) := by
  exact AronowAudit.P013.two_wearing_effects_and_losses world

theorem two_report_biases (world : Fin 3) :
    expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 0 else if world = 1 then -(1/2) else 1/2) := by
  exact AronowAudit.P013.two_report_biases world

theorem two_report_nonidentification  :
    ¬ ∃ h : ((Fin 2 × Fin 2) → Fin 2 → Fin 2 × ℝ × Bool) → ℝ,
      ∀ world : Fin 3,
        h (recordedData (twoWearPopulation world) twoRecording) =
          causalEffect (twoWearPopulation world) 1 0 := by
  exact AronowAudit.P013.two_report_nonidentification

theorem two_respondent_comparison (world : Fin 3) :
    (∀ z, htEffect twoRespondentPopulation 1 0 z = 2 * (z.1.val : ℝ)) ∧
    expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) = 1 ∧
    (∀ z, htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 z =
      (1/2) * htEffect twoRespondentPopulation 1 0 z) ∧
    expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 1/2 else if world = 1 then 0 else 1) := by
  exact AronowAudit.P013.two_respondent_comparison world

theorem corrected_recorded_outcome {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) :
    expectation P (htMean (recordedPopulation F R) d) =
      potentialMean (recordedPopulation F R) d ∧
    expectation P (htEffect (recordedPopulation F R) d e) =
      causalEffect (recordedPopulation F R) d e ∧
    (∀ a, potentialMean (recordedPopulation F R) a = potentialMean F a - lostMean F R a) ∧
    causalEffect (recordedPopulation F R) d e =
      causalEffect F d e - lostMean F R d + lostMean F R e ∧
    expectation P (htEffect (recordedPopulation F R) d e) - causalEffect F d e =
      lostMean F R e - lostMean F R d ∧
    (expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e ↔
      lostMean F R d = lostMean F R e) ∧
    (expectation P (htMean (recordedPopulation F R) d) = potentialMean F d ↔
      lostMean F R d = 0) ∧
    (∀ a, (∀ i, 0 ≤ F.outcome i a) → 0 ≤ lostMean F R a ∧
      (lostMean F R a = 0 ↔ ∀ i, R i a = false → F.outcome i a = 0)) := by
  exact AronowAudit.P013.corrected_recorded_outcome (toPopulation F) R hN d e hne hd he

theorem no_lost_wearing_suffices {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e)
    (hyd : ∀ i, 0 ≤ F.outcome i d) (hye : ∀ i, 0 ≤ F.outcome i e)
    (hzd : ∀ i, R i d = false → F.outcome i d = 0)
    (hze : ∀ i, R i e = false → F.outcome i e = 0) :
    expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e := by
  exact AronowAudit.P013.no_lost_wearing_suffices (toPopulation F) R hN d e hne hd he hyd hye hzd hze

theorem dropping_zero_outcomes {N K : ℕ} (D : Fin N → Fin K)
    (w G : Fin N → ℝ) (S SR : Finset (Fin N)) (hsub : SR ⊆ S)
    (hS : 0 < S.card) (hSR : 0 < SR.card) (_hw : ∀ i ∈ S, 0 < w i)
    (hkeep : ∀ i ∈ S, G i ≠ 0 → i ∈ SR) (d e : Fin K) :
    (∀ a, recordedNumerator D w G a SR = recordedNumerator D w G a S) ∧
    recordedNumerator D w G d S / S.card =
      (SR.card : ℝ) / S.card * (recordedNumerator D w G d SR / SR.card) ∧
    (recordedNumerator D w G d S - recordedNumerator D w G e S) / S.card =
      (SR.card : ℝ) / S.card *
        ((recordedNumerator D w G d SR - recordedNumerator D w G e SR) / SR.card) ∧
    (0 < recordedDenominator D w d SR →
      recordedNumerator D w G d S / recordedDenominator D w d S =
        (recordedDenominator D w d SR / recordedDenominator D w d S) *
          (recordedNumerator D w G d SR / recordedDenominator D w d SR)) := by
  exact AronowAudit.P013.dropping_zero_outcomes D w G S SR hsub hS hSR _hw hkeep d e

theorem public_reconstruction_HT_scaling {N K : ℕ} (D : Fin N → Fin K)
    (w G : Fin N → ℝ) (S item survey : Finset (Fin N))
    (hi : item ⊆ S) (hs : survey ⊆ S) (hS : S.card = 2050)
    (hitem : item.card = 1708) (hsurvey : survey.card = 1899)
    (hw : ∀ i ∈ S, 0 < w i)
    (hki : ∀ i ∈ S, G i ≠ 0 → i ∈ item)
    (hks : ∀ i ∈ S, G i ≠ 0 → i ∈ survey) (d e : Fin K) :
    (recordedNumerator D w G d S - recordedNumerator D w G e S)/2050 =
      (854/1025) * ((recordedNumerator D w G d item - recordedNumerator D w G e item)/1708) ∧
    (recordedNumerator D w G d S - recordedNumerator D w G e S)/2050 =
      (1899/2050) * ((recordedNumerator D w G d survey - recordedNumerator D w G e survey)/1899) := by
  exact AronowAudit.P013.public_reconstruction_HT_scaling D w G S item survey hi hs hS hitem hsurvey hw hki hks d e

theorem hajek_exclusion_no_common_factor  :
    let D : Fin 3 → Fin 2 := fun i => if i = 2 then 0 else 1
    let w : Fin 3 → ℝ := fun _ => 2
    let G : Fin 3 → ℝ := fun i => if i = 1 then 0 else 1
    let S : Finset (Fin 3) := univ
    let SR : Finset (Fin 3) := {0,2}
    (∀ i ∈ S, G i ≠ 0 → i ∈ SR) ∧
    recordedDenominator D w 1 SR / recordedDenominator D w 1 S = 1/2 ∧
    recordedDenominator D w 0 SR / recordedDenominator D w 0 S = 1 ∧
    (¬ ∃ c : ℝ,
      recordedNumerator D w G 1 S / recordedDenominator D w 1 S -
        recordedNumerator D w G 0 S / recordedDenominator D w 0 S =
      c * (recordedNumerator D w G 1 SR / recordedDenominator D w 1 SR -
        recordedNumerator D w G 0 SR / recordedDenominator D w 0 SR)) := by
  exact AronowAudit.P013.hajek_exclusion_no_common_factor

theorem school_support_counterexample  :
    schoolBadHosts.card = 28 ∧ schoolBadHosts ∈ schoolCSupport ∧
    (∀ z ∈ schoolBSupport, blockSchoolHosts z ≠ schoolBadHosts) ∧
    uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) =
      1/7648690600760440 ∧
    0 < uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) ∧
    uniformSchoolProbability schoolBSupport (fun z => blockSchoolHosts z = schoolBadHosts) = 0 := by
  exact AronowAudit.P013.school_support_counterexample

theorem school_example_potential_hypotheses (a b : School) (hab : a ≠ b) :
    (∀ i d, schoolPotentialOutcome a b i d = 0 ∨ schoolPotentialOutcome a b i d = 1) ∧
    (∑ i, schoolPotentialOutcome a b i true) = 2 ∧
    (∀ i, schoolPotentialOutcome a b i false = 0) ∧
    (∀ {α : Type*} (hosts : α → School → Bool) z i,
      schoolExampleObserved hosts a b z i = schoolHostBit hosts z i * schoolActiveOutcome a b i) := by
  exact AronowAudit.P013.school_example_potential_hypotheses a b hab

theorem school_two_HT_reduction {α : Type*} (hosts : α → School → Bool)
    (a b : School) (hab : a ≠ b) (z : α) :
    schoolTwoHT hosts a b z = 2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) ∧
    (∑ i : School, schoolActiveOutcome a b i) = 2 := by
  exact AronowAudit.P013.school_two_HT_reduction hosts a b hab z

theorem school_two_variance_reduction {α : Type*} (hosts : α → School → Bool)
    (a b : School) (hab : a ≠ b) (q : ℝ) (z : α) :
    schoolTwoVarianceInput hosts a b q z =
      2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) +
        8 * schoolHostBit hosts z a * schoolHostBit hosts z b * ((q - 1/4)/q) := by
  exact AronowAudit.P013.school_two_variance_reduction hosts a b hab q z

theorem school_two_moments {α : Type*} (S : Finset α)
    (hosts : α → School → Bool) (a b : School) (hab : a ≠ b) (p q : ℝ)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2)
    (hb : uniformSchoolProbability S (fun z => hosts z b = true) = 1/2)
    (hp : uniformSchoolProbability S (fun z => hosts z a = true ∧ hosts z b = true) = p) :
    uniformSchoolMean S (schoolTwoHT hosts a b) = 2 ∧
    uniformSchoolVariance S (schoolTwoHT hosts a b) = 8*p ∧
    uniformSchoolMean S (schoolTwoVarianceInput hosts a b q) = 2+8*p*((q-1/4)/q) := by
  exact AronowAudit.P013.school_two_moments S hosts a b hab p q ha hb hp

theorem school_correct_joint_unbiased {α : Type*} (S : Finset α)
    (hosts : α → School → Bool) (a b : School) (hab : a ≠ b) (p : ℝ) (hpos : 0 < p)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2)
    (hb : uniformSchoolProbability S (fun z => hosts z b = true) = 1/2)
    (hp : uniformSchoolProbability S (fun z => hosts z a = true ∧ hosts z b = true) = p) :
    uniformSchoolMean S (schoolTwoVarianceInput hosts a b p) =
      uniformSchoolVariance S (schoolTwoHT hosts a b) := by
  exact AronowAudit.P013.school_correct_joint_unbiased S hosts a b hab p hpos ha hb hp

theorem school_wrong_joint_counterexample  :
    uniformSchoolMean schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 2 ∧
    uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 4/3 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (0,1) (27/110)) = 160/81 ∧
    uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) = 2 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) = 53/27 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) <
        uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) ∧
    uniformSchoolVariance schoolCSupport (schoolTwoHT schoolCHosts (0,0) (0,1)) = 108/55 ∧
    uniformSchoolMean schoolCSupport
      (schoolTwoVarianceInput schoolCHosts (0,0) (0,1) (27/110)) = 108/55 := by
  exact AronowAudit.P013.school_wrong_joint_counterexample

theorem school_wrong_joint_biases  :
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (0,1) (27/110)) -
      uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 52/81 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) -
      uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) = -(1/27) := by
  exact AronowAudit.P013.school_wrong_joint_biases

theorem school_assignment_counts  :
    schoolBSupport.card = 6^14 ∧ schoolBSupport.card = 78364164096 ∧
    schoolCSupport.card = Nat.choose 56 28 ∧ schoolCSupport.card = 7648690600760440 := by
  exact AronowAudit.P013.school_assignment_counts

theorem school_B_embeds_C (z : Fin 14 → Finset (Fin 4)) (hz : z ∈ schoolBSupport) :
    blockSchoolHosts z ∈ schoolCSupport := by
  exact AronowAudit.P013.school_B_embeds_C z hz

end
end SAP.P013b.Bridge
