import SAP.P037b.Defs.WholeW2
import SAP.P037b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b.WH.W2
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Marginalize the three peer-free blocks of the legal four-block design.
Split the fair school indicator, apply
`AronowAudit.P037.product_design_coordinate_mean` to block zero, and transport
its subtype sum to `seedSubsets 12 6`. The other blocks have total mass one.
The treated label is never zero. This is a finite sum calculation, about
100--180 lines, with no enumeration of the full four-block support. -/
def T22_L1 : Prop :=
  ∀ (self peers refs : Finset (Fin 12)) (k : Fin 5),
    eventProbability cutoffDesignW2 (fun z => cutoffExposureW2 self peers refs z = k) =
      localExposureProbability5 12 6 self peers refs k

/-- Prove the joint four-cutoff event is nondegenerate and supply its witnesses.
From positive exact probabilities choose one supported assignment per indirect
label using `AronowAudit.P037.Wave1.analysis_prob_positive_iff`. Use
`balancedScheduleCountW2` below to repeat each representative 2500 times;
compute all four counts exactly. A constant sequence at the control
representative has the other three frequencies zero. Every product mass is
positive. Apply `AronowAudit.P037.Wave1.estimated_cutoff_event_pos` to these two
witnesses, and use `iidTotalW2` and the complementary event for the strict upper
bound. Do not assume independence of the four counts. About 140--240 lines. -/
def T22_L2 : Prop := T22JointCutoffW2

/-- A filtered count is bounded by the number of draws. -/
theorem hitCount_leW2 {Ω : Type} {J : ℕ} (E : Ω → Prop) (z : Fin J → Ω) : hitCountW2 E z ≤ J := by
  simpa [hitCountW2] using Finset.card_filter_le (Finset.univ : Finset (Fin J))
    (fun j => E (z j))
/-- Every finite product law used below is normalized. -/
theorem iidTotalW2 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω) (J : ℕ) : (∑ z : Fin J → Ω, iidMassW2 P.mass z) = 1 := by
  unfold iidMassW2
  rw [AronowAudit.P037.finite_product_factorization]
  simp [P.total]
/-- Equal events have equal probabilities under the finite product law. -/
theorem iidProbabilityCongrW2 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ) (J : ℕ)
    (E F : (Fin J → Ω) → Prop) (h : ∀ draws, E draws ↔ F draws) : iidProbabilityW2 mass J E = iidProbabilityW2 mass J F := by
  unfold iidProbabilityW2 iidExpectationW2
  apply Finset.sum_congr rfl
  intro draws _
  apply congrArg (fun x : ℝ => iidMassW2 mass draws * x)
  by_cases he : E draws
  · simp only [he, (h draws).mp he, ite_true]
  · have hf : ¬F draws := fun hf => he ((h draws).mpr hf)
    simp only [he, hf, ite_false]
/-- Event probabilities of labels can be written with the label type's own decision procedure. This avoids reducing a finite support to compare instances. -/
theorem labelProbabilityW2 {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (P : ProbabilityDesign Ω) (D : Ω → K) (k : K) : eventProbability P (fun z => D z = k) = ∑ z, P.mass z * (if D z = k then (1 : ℝ) else 0) := by
  unfold eventProbability
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun x : ℝ => P.mass z * x)
  exact ite_cond_congr rfl
/-- Direct label counts and generic event counts agree, regardless of the inferred decision procedures of their extensionally identical filters. -/
theorem estimatedFrequencyW2 {Ω I : Type} {J : ℕ} (D : Ω → I → Fin 5)
    (draws : Fin J → Ω) (i : I) (k : Fin 4) : estimatedExposureW2 D draws i k = frequencyW2 (fun z => D z i = k.castSucc) draws := by
  unfold estimatedExposureW2 frequencyW2 hitCountW2
  apply congrArg (fun n : ℕ => (n : ℝ) / J)
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Binomial law in the package's finite product notation. Keep the draw count abstract while transporting the donor, to avoid expanding a large finite type. -/
theorem iidBinomialW2 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (E : Ω → Prop) (J r : ℕ) : iidProbabilityW2 P.mass J (fun draws => hitCountW2 E draws = r) = (Nat.choose J r : ℝ) * (eventProbability P E)^r * (1-eventProbability P E)^(J-r) := by
  calc
    _ = ∑ draws : Fin J → Ω, (∏ j, P.mass (draws j)) * (if (Finset.univ.filter (fun j => E (draws j))).card = r then (1 : ℝ) else 0) := by
      unfold iidProbabilityW2 iidExpectationW2 iidMassW2 hitCountW2
      apply Finset.sum_congr rfl
      intro draws _
      apply congrArg (fun x : ℝ => (∏ j, P.mass (draws j)) * x)
      exact ite_cond_congr rfl
    _ = _ := by
      simpa only [eventProbability, AronowAudit.P037.sampleProb, Bridge.toProject] using
        AronowAudit.P037.Wave1.exposureMC_count (Bridge.toProject P) E J r
/-- Transport the scalar cutoff bound with an abstract draw count, keeping finite
type instance comparison small before specializing to 10000. -/
theorem iidCountCutoffBoundsW2 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (E : Ω → Prop) (J t : ℕ) (ht : 0 < t) (htJ : t ≤ J)
    (hp : 0 < eventProbability P E) (hq : eventProbability P E < 1) :
    0 < iidProbabilityW2 P.mass J (fun draws => t ≤ hitCountW2 E draws) ∧
    iidProbabilityW2 P.mass J (fun draws => t ≤ hitCountW2 E draws) < 1 := by
  have he : iidProbabilityW2 P.mass J (fun draws => t ≤ hitCountW2 E draws) =
      ∑ draws : Fin J → Ω, (∏ j, P.mass (draws j)) *
        (if t ≤ (Finset.univ.filter (fun j => E (draws j))).card then (1 : ℝ) else 0) := by
    unfold iidProbabilityW2 iidExpectationW2 iidMassW2 hitCountW2
    apply Finset.sum_congr rfl
    intro draws _
    apply congrArg (fun x : ℝ => (∏ j, P.mass (draws j)) * x)
    exact ite_cond_congr rfl
  rw [he]
  exact AronowAudit.P037.Wave1.estimated_cutoff_random_bounds
    (Bridge.toProject P) E hp hq J t ht htJ

/-- A normalized finite design gives nonnegative probability to every event. -/
theorem eventNonnegativeW2 {Ω : Type} [Fintype Ω]
    (P : ProbabilityDesign Ω) (E : Ω → Prop) : 0 ≤ eventProbability P E := by
  unfold eventProbability
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (P.positive z).le (by split_ifs <;> norm_num)

/-- A nondegenerate membership event prevents almost sure constancy of the full set. -/
theorem nonconstantFromMembershipW2 {Ω I : Type} [Fintype Ω]
    (P : ProbabilityDesign Ω) (M : Ω → Set I) (i : I)
    (hpos : 0 < eventProbability P (fun z => i ∈ M z))
    (hlt : eventProbability P (fun z => i ∈ M z) < 1) :
    ¬AlmostSurelyConstantW2 P M := by
  rintro ⟨A, hA⟩
  have hall : ∀ z, M z = A := by
    by_contra hn
    obtain ⟨z, hz⟩ := not_forall.mp hn
    have hnotpos : 0 < eventProbability P (fun z => M z ≠ A) :=
      (AronowAudit.P037.Wave1.analysis_prob_positive_iff
        (Bridge.toProject P) (fun z => M z ≠ A)).mpr ⟨z, hz⟩
    have hb : eventProbability P (fun z => M z = A) +
        eventProbability P (fun z => M z ≠ A) ≤ 1 :=
      AronowAudit.P037.Wave1.analysis_disjoint_bound (Bridge.toProject P)
        (fun z => M z = A) (fun z => M z ≠ A) (fun _ he hn => hn he)
    linarith
  by_cases hi : i ∈ A
  · have hp : eventProbability P (fun z => i ∈ M z) = 1 := by
      simpa [eventProbability, hall, hi] using P.total
    linarith
  · have hp : eventProbability P (fun z => i ∈ M z) = 0 := by
      simp [eventProbability, hall, hi]
    linarith

/-- Deterministic schedule of four consecutive blocks, each of length 2500.
This definition concerns a supported witness, not the independent simulation law. -/
def balancedScheduleW2 (j : Fin 10000) : Fin 4 :=
  ⟨j.val / 2500, by have := j.isLt; omega⟩

/-- The schedule uses each label exactly 2500 times, by the existing interval census. -/
theorem balancedScheduleCountW2 (k : Fin 4) :
    (Finset.univ.filter (fun j : Fin 10000 => balancedScheduleW2 j = k)).card = 2500 := by
  have he : (Finset.univ.filter (fun j : Fin 10000 => balancedScheduleW2 j = k)) =
      Finset.univ.filter (fun j => 2500*k.val ≤ j.val ∧ j.val < 2500*(k.val+1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    change j.val / 2500 = k.val ↔ _
    omega
  rw [he, AronowAudit.P037.Wave1.cutoff_interval_card]
  all_goals have := k.isLt; omega

/-- Four supported states giving C,S,NI,I for both focal networks at once. -/
def commonRepresentativeW2 (k : Fin 4) : CutoffAssignmentsW2 :=
  ((![false,true,true,true] : Fin 4 → Bool) k, fun _ =>
    ⟨(![{0,1,2,3,4,5}, {6,7,8,9,10,11}, {1,6,7,8,9,10}, {0,6,7,8,9,10}] :
      Fin 4 → Finset (Fin 12)) k, by fin_cases k <;> norm_num⟩)

/-- Check the labels of these four small local states. -/
theorem commonRepresentativeLabelW2 (i : Fin 2) (k : Fin 4) :
    cutoffNetworkW2 (commonRepresentativeW2 k) i = k.castSucc := by
  fin_cases i <;> fin_cases k <;>
    norm_num [commonRepresentativeW2, cutoffNetworkW2, cutoffExposureW2,
      localTreatedLabel, Finset.disjoint_insert_right]

/-- A fixed supported simulation passes all four estimated cutoffs for both students. -/
theorem commonSimulationW2 :
    ∃ draws : Fin 10000 → CutoffAssignmentsW2,
      ∀ (i : Fin 2) (k : Fin 4), estimatedExposureW2 cutoffNetworkW2 draws i k = 1/4 := by
  let draws : Fin 10000 → CutoffAssignmentsW2 := fun j =>
    commonRepresentativeW2 (balancedScheduleW2 j)
  refine ⟨draws, ?_⟩
  intro i k
  have he : (Finset.univ.filter (fun j : Fin 10000 =>
      cutoffNetworkW2 (draws j) i = k.castSucc)) =
      Finset.univ.filter (fun j => balancedScheduleW2 j = k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [draws]
    rw [commonRepresentativeLabelW2]
    exact Fin.castSucc_inj
  unfold estimatedExposureW2
  rw [he, balancedScheduleCountW2]
  norm_num

/-- The native prediction mean is precisely the project's released-code mean.
This transports a definition; it asserts no execution of the R scripts. -/
theorem predictionCorrespondenceW2 {Ω I : Type} [Fintype I]
    (estimated : I → Fin 4 → ℝ) (seed outcome baseline screen : Ω → I → Prop)
    (z : Ω) (prediction : I → Fin 4 → ℝ) (k : Fin 4) :
    analysisPredictionMeanW2 estimated seed outcome baseline screen z prediction k =
      AronowAudit.P037.codeAnalysisPredictionMean estimated seed outcome baseline screen z
        prediction k := rfl

/-- Assemble the corrected canonical claim. The leaves handle the block marginal
and simultaneous simulated screen; all support, binomial, seed-exclusion,
nonconstancy, explicit mask examples, and denominator arguments are proved here. -/
theorem T22_assembly (h1 : T22_L1) (h2 : T22_L2) : T22WholeStatement_W2 := by
  refine ⟨Bridge.T22_correspondence.{0,0,0,0,0}, ?_, ?_, ?_, ?_, h2, ?_, ?_, ?_⟩
  · intro Ω I _ P D J hJ draws i k hp
    have he := AronowAudit.P037.Wave1.exposureMC_zero (Bridge.toProject P)
      (fun z => D z i = k) hp
    simp [frequencyW2, hitCountW2, he]
  · intro Ω I _ P D i
    have hall : (∑ k : Fin 5, eventProbability P (fun z => D z i = k)) = 1 := by
      simp_rw [labelProbabilityW2]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
      exact P.total
    have hind := hall
    rw [Fin.sum_univ_castSucc] at hind
    change (∑ k : Fin 4, eventProbability P (fun z => D z i = k.castSucc)) +
      eventProbability P (fun z => D z i = 4) = 1 at hind
    refine ⟨hall, hind, ?_⟩
    have hn := eventNonnegativeW2 P (fun z => D z i = 4)
    linarith
  · have hc := Bridge.T21_correspondence
    dsimp [T22StrictW2]
    have hπ (k : Fin 4) : eventProbability cutoffDesignW2 (fun z =>
          cutoffExposureW2 ∅ {0,1,2,3,4,5} {0} z = k.castSucc) =
          (![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k := by
      rw [h1]
      have hk := hc.1.2.1 k.castSucc
      fin_cases k <;> simpa using hk
    refine ⟨?_, ?_, ?_⟩
    · intro k
      dsimp only
      rw [hπ]
      exact hc.1.2.2.1 k
    · intro h
      have hh := h 1
      dsimp only at hh
      rw [hπ] at hh
      norm_num at hh
    · obtain ⟨z, hz, hv⟩ := hc.2.1
      let draws : Fin 10000 → CutoffAssignmentsW2 := fun j =>
        liftCutoffAssignmentW2 (z j) (hz j)
      have hfreq (k : Fin 4) : estimatedExposureW2 (fun w (_ : Unit) =>
            cutoffExposureW2 ∅ {0,1,2,3,4,5} {0} w) draws () k =
            (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k := by
        simp only [estimatedExposureW2, draws, cutoffExposureW2, liftCutoffAssignmentW2]
        exact hv k
      refine ⟨draws, hfreq, ?_, ?_⟩
      · intro k
        dsimp only
        rw [hfreq]
        fin_cases k <;> norm_num
      · intro h
        have hh := h 1
        dsimp only at hh
        rw [hfreq] at hh
        norm_num at hh
  · intro Ω I _ P D i k
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      exact iidBinomialW2 P (fun z => D z i = k.castSucc) 10000 r
    · intro draws
      refine ⟨?_, (AronowAudit.P037.cutoff_integer_rule
        (hitCountW2 (fun z => D z i = k.castSucc) draws) (hitCount_leW2 _ _)).1⟩
      dsimp only [frequencyW2]
      ring
    · intro hi
      have hp := (hi k).1
      have hq := (hi k).2
      have hb :
          0 < iidProbabilityW2 P.mass 10000
            (fun draws => 101 ≤ hitCountW2 (fun z => D z i = k.castSucc) draws) ∧
          iidProbabilityW2 P.mass 10000
            (fun draws => 101 ≤ hitCountW2 (fun z => D z i = k.castSucc) draws) < 1 := by
        exact iidCountCutoffBoundsW2 P (fun z => D z i = k.castSucc)
          10000 101 (by omega) (by omega) hp hq
      have he : iidProbabilityW2 P.mass 10000
          (fun draws => frequencyW2 (fun z => D z i = k.castSucc) draws > 1/100) =
          iidProbabilityW2 P.mass 10000
            (fun draws => 101 ≤ hitCountW2 (fun z => D z i = k.castSucc) draws) := by
        apply iidProbabilityCongrW2
        intro draws
        exact (AronowAudit.P037.cutoff_integer_rule
          (hitCountW2 (fun z => D z i = k.castSucc) draws) (hitCount_leW2 _ _)).1
      rw [he]
      exact hb
    · intro draws h
      have hk := h k
      rw [estimatedFrequencyW2] at hk ⊢
      exact (AronowAudit.P037.cutoff_integer_rule
        (hitCountW2 (fun z => D z i = k.castSucc) draws) (hitCount_leW2 _ _)).2
          ((AronowAudit.P037.cutoff_integer_rule
            (hitCountW2 (fun z => D z i = k.castSucc) draws) (hitCount_leW2 _ _)).1.mp hk)
  · intro Ω I _ P D estimated outcome baseline screen i
    dsimp only
    let M := analysisPopulation estimated (fun z i => D z i = 4) outcome baseline screen
    have hb : eventProbability P (fun z => i ∈ M z) +
        eventProbability P (fun z => D z i = 4) ≤ 1 :=
      AronowAudit.P037.Wave1.analysis_disjoint_bound (Bridge.toProject P)
        (fun z => i ∈ M z) (fun z => D z i = 4) (fun _ hi => hi.2.1)
    have hu : eventProbability P (fun z => i ∈ M z) ≤
        1-eventProbability P (fun z => D z i = 4) := by linarith
    refine ⟨?_, ?_, hu, ?_, @measurable_from_top Ω (Set I) ⊤ _⟩
    · intro z j hj
      exact hj.2.1
    · exact AronowAudit.P037.code_analysis_seed_exclusion (Bridge.toProject P)
        estimated (fun z i => D z i = 4) outcome baseline screen i
    · intro hD hM
      have hlt : eventProbability P (fun z => i ∈ M z) < 1 := by linarith
      exact ⟨hM, hu, by linarith, hlt, nonconstantFromMembershipW2 P M i hM hlt⟩
  · dsimp [T22MaskExamplesW2]
    refine ⟨?_, ?_⟩
    · change eventProbability cutoffDesignW2
        (fun z => cutoffExposureW2 {2} {0,1} {0} z = 4) = 1/4
      rw [h1]
      exact Bridge.T21_correspondence.1.2.2.2.2.2.1 4
    · obtain ⟨draws, hdraws⟩ := commonSimulationW2
      let a : CutoffAssignmentsW2 := (true, fun _ => ⟨{2,3,4,5,6,7}, by norm_num⟩)
      let b : CutoffAssignmentsW2 := (true, fun _ => ⟨{3,4,5,6,7,8}, by norm_num⟩)
      have hest : estimatedExposureW2 cutoffNetworkW2 draws =
          (fun (_ : Fin 2) (_ : Fin 4) => (1/4 : ℝ)) := by
        funext i k
        exact hdraws i k
      have hnever (z : CutoffAssignmentsW2) : cutoffNetworkW2 z 0 ≠ 4 := by
        simp only [cutoffNetworkW2]
        unfold cutoffExposureW2 localTreatedLabel
        simp only [Finset.disjoint_empty_right, not_true_eq_false, ite_false]
        split_ifs <;> norm_num
      refine ⟨draws, hdraws, ?_, a, b, ?_, ?_, ?_, ?_⟩
      · intro z
        rw [hest]
        ext i
        fin_cases i <;>
          norm_num [analysisFinsetW2, analysisPopulation, exposureProbabilityCutoff, hnever]
      · norm_num [a, cutoffNetworkW2, cutoffExposureW2, localTreatedLabel,
          Finset.disjoint_insert_right]
      · norm_num [b, cutoffNetworkW2, cutoffExposureW2, localTreatedLabel,
          Finset.disjoint_insert_right]
      · rw [hest]
        ext i
        fin_cases i <;>
          norm_num [analysisFinsetW2, analysisPopulation, exposureProbabilityCutoff,
            a, cutoffNetworkW2, cutoffExposureW2, localTreatedLabel,
            Finset.disjoint_insert_right]
      · rw [hest]
        ext i
        fin_cases i <;>
          norm_num [analysisFinsetW2, analysisPopulation, exposureProbabilityCutoff,
            b, cutoffNetworkW2, cutoffExposureW2, localTreatedLabel,
            Finset.disjoint_insert_right]
  · intro Ω I _ _ P D J hJ draws outcome baseline peerConflict schoolMean z prediction k
    dsimp only
    intro hA
    have hB : (Finset.univ.filter (fun i =>
        ∀ l : Fin 4, 0 < eventProbability P (fun w => D w i = l.castSucc))).Nonempty := by
      obtain ⟨i, hi⟩ := hA
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      have hm := (Finset.mem_filter.mp hi).2
      have hsub : analysisPopulation (estimatedExposureW2 D draws)
          (fun z i => D z i = 4) outcome baseline
          (fun z i => peerConflict = false ∨ passesConflictThreshold (schoolMean z i)) z ⊆
          positiveExposurePopulation
            (fun i l => eventProbability P (fun w => D w i = l.castSucc)) := by
        have hest : estimatedExposureW2 D draws =
            (fun i (k : Fin 4) => ((Finset.univ.filter
              (fun j => D (draws j) i = k.castSucc)).card : ℝ) / J) := by
          funext i k
          rfl
        rw [hest]
        exact (Bridge.T22_correspondence.{0,0,0,0,0}.1 P D J hJ draws
          (fun z i => D z i = 4) outcome baseline
          (fun z i => peerConflict = false ∨ passesConflictThreshold (schoolMean z i)) z).2.2.2.2.1
      exact fun l => (hsub hm l).1
    exact ⟨rfl, Nat.cast_pos.mpr (Finset.card_pos.mpr hA), hB, rfl,
      Nat.cast_pos.mpr (Finset.card_pos.mpr hB)⟩

end SAP.P037b.WH.W2
