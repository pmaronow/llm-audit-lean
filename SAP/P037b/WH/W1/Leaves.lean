import SAP.P037b.Defs.WholeW1
import SAP.P037b.Bridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P037b.WH.W1
open scoped BigOperators
attribute [local instance] Classical.propDecidable
/-- Marginalize the three peer-free blocks of the legal four-block design. Prove by splitting the fair school indicator, applying `AronowAudit.P037.product_design_coordinate_mean` to block zero, and converting its subtype sum to `seedSubsets 12 6`. The other blocks have total mass one. The treated label is never zero, which also handles the control coordinate. Expected size: 100--180 lines; no enumeration of the full design. -/
def T22_L1 : Prop := ∀ (self peers refs : Finset (Fin 12)) (k : Fin 5),
    eventProbability cutoffDesignW1 (fun z => cutoffExposureW1 self peers refs z = k) = localExposureProbability5 12 6 self peers refs k
/-- Nondegeneracy of the simultaneous four-cutoff event under the actual product law. For each positive coordinate choose a supported assignment with that label using `AronowAudit.P037.Wave1.analysis_prob_positive_iff`. Repeat each of the four chosen assignments 2500 times, giving a passing sequence with positive product mass. A constant supported sequence fails the screen. Use `AronowAudit.P037.Wave1.estimated_cutoff_event_pos`, product normalization and the complementary event to get the strict upper bound. The four scalar events alone do not suffice. Expected size: 120--220 lines. -/
def T22_L2 : Prop := T22JointCutoffW1
/-- A supported common simulation giving frequency 1/4 for all four indirect labels of both focal networks. Use four consecutive intervals of length 2500: control, then treated first-block selections {6,7,8,9,10,11}, {1,6,7,8,9,10}, {0,6,7,8,9,10}; complete the other blocks with any legal six-of-twelve subsets. None of the three treated subsets contains eligible focal student 2. Compute labels by simplification, then counts with `AronowAudit.P037.Wave1.cutoff_interval_card`. This is a deterministic witness, not a change to the independent-draw law. Expected size: 80--160 lines. -/
def T22_L3 : Prop := ∃ draws : Fin 10000 → CutoffAssignmentsW1,
    ∀ (i : Fin 2) (k : Fin 4), estimatedExposureW1 cutoffNetworkW1 draws i k = 1/4
/-- Counts and uniform pair marginal for the rare-exposure witness. Use `AronowAudit.P037.Wave1.rare_probability_block_card`, the subtype/powerset sum correspondence, and `AronowAudit.P037.Wave1.rare_design_referent_mean` to count the 126 first-block subsets containing 0. Pair with the 252 second block choices. A five-element subset avoiding {0,...,4} equals {5,...,9}, by `Finset.eq_of_subset_of_card_le`; this gives the named unique avoiding pair. Partition the 63504 pairs into avoidance, referent hit and nonreferent-only hit. For the uniform pair marginal, split the fair school indicator and apply `AronowAudit.P037.product_design_coordinate_pair` to the two equality indicators; each singleton block has probability 1/252. Expected size: 180--300 lines. -/
def T29_L1 : Prop := (∀ s : RarePairW1,
    (∑ z : RareSeedAssignments, rareAssignmentMass z * (if (z.2 0, z.2 1) = s then (1 : ℝ) else 0)) = 1/63504) ∧ (Finset.univ.filter rareAvoidsPairW1).card = 1 ∧ (∀ s, rareAvoidsPairW1 s ↔ s = rareAvoidingPairW1) ∧ (Finset.univ.filter (fun s : RarePairW1 => (0 : Fin 10) ∈ s.1.val)).card = 31752 ∧ (Finset.univ.filter (fun s : RarePairW1 =>
    (0 : Fin 10) ∉ s.1.val ∧ ¬rareAvoidsPairW1 s)).card = 31751
/-- The actual rare-exposure design, packaged for the general Monte Carlo donors. -/
noncomputable def rareDesignW1 : ProbabilityDesign RareSeedAssignments where
  mass := rareAssignmentMass
  positive := fun _ => by norm_num [rareAssignmentMass]
  total := Bridge.T29_correspondence.1.1
/-- A filtered count is bounded by the number of draws. -/
theorem hitCount_leW1 {Ω : Type} {J : ℕ} (E : Ω → Prop) (z : Fin J → Ω) : hitCountW1 E z ≤ J := by
  simpa [hitCountW1] using Finset.card_filter_le (Finset.univ : Finset (Fin J))
    (fun j => E (z j))
/-- Every finite product law used below is normalized. -/
theorem iidTotalW1 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω) (J : ℕ) : (∑ z : Fin J → Ω, iidMassW1 P.mass z) = 1 := by
  unfold iidMassW1
  rw [AronowAudit.P037.finite_product_factorization]
  simp [P.total]
/-- Equal events have equal probabilities under the finite product law. -/
theorem iidProbabilityCongrW1 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ) (J : ℕ)
    (E F : (Fin J → Ω) → Prop) (h : ∀ draws, E draws ↔ F draws) : iidProbabilityW1 mass J E = iidProbabilityW1 mass J F := by
  unfold iidProbabilityW1 iidExpectationW1
  apply Finset.sum_congr rfl
  intro draws _
  apply congrArg (fun x : ℝ => iidMassW1 mass draws * x)
  by_cases he : E draws
  · simp only [he, (h draws).mp he, ite_true]
  · have hf : ¬F draws := fun hf => he ((h draws).mpr hf)
    simp only [he, hf, ite_false]
/-- Event probabilities of labels can be written with the label type's own decision procedure. This avoids reducing a finite support to compare instances. -/
theorem labelProbabilityW1 {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (P : ProbabilityDesign Ω) (D : Ω → K) (k : K) : eventProbability P (fun z => D z = k) = ∑ z, P.mass z * (if D z = k then (1 : ℝ) else 0) := by
  unfold eventProbability
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun x : ℝ => P.mass z * x)
  exact ite_cond_congr rfl
/-- Direct label counts and generic event counts agree, regardless of the inferred decision procedures of their extensionally identical filters. -/
theorem estimatedFrequencyW1 {Ω I : Type} {J : ℕ} (D : Ω → I → Fin 5)
    (draws : Fin J → Ω) (i : I) (k : Fin 4) : estimatedExposureW1 D draws i k = frequencyW1 (fun z => D z i = k.castSucc) draws := by
  unfold estimatedExposureW1 frequencyW1 hitCountW1
  apply congrArg (fun n : ℕ => (n : ℝ) / J)
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Binomial law in the package's finite product notation. Keep the draw count abstract while transporting the donor, to avoid expanding a large finite type. -/
theorem iidBinomialW1 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (E : Ω → Prop) (J r : ℕ) : iidProbabilityW1 P.mass J (fun draws => hitCountW1 E draws = r) = (Nat.choose J r : ℝ) * (eventProbability P E)^r * (1-eventProbability P E)^(J-r) := by
  calc
    _ = ∑ draws : Fin J → Ω, (∏ j, P.mass (draws j)) * (if (Finset.univ.filter (fun j => E (draws j))).card = r then (1 : ℝ) else 0) := by
      unfold iidProbabilityW1 iidExpectationW1 iidMassW1 hitCountW1
      apply Finset.sum_congr rfl
      intro draws _
      apply congrArg (fun x : ℝ => (∏ j, P.mass (draws j)) * x)
      exact ite_cond_congr rfl
    _ = _ := by
      simpa only [eventProbability, AronowAudit.P037.sampleProb, Bridge.toProject] using
        AronowAudit.P037.Wave1.exposureMC_count (Bridge.toProject P) E J r
/-- Mean and actual variance of the empirical frequency, transported before specializing the sample count or the supported design. -/
theorem iidMomentsW1 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (E : Ω → Prop) (J : ℕ) (hJ : 0 < J) : iidExpectationW1 P.mass J (frequencyW1 E) = eventProbability P E ∧ iidVarianceW1 P.mass J (frequencyW1 E) = eventProbability P E * (1-eventProbability P E) / J := by
  have hm : iidExpectationW1 P.mass J (frequencyW1 E) = eventProbability P E ∧ iidExpectationW1 P.mass J (fun draws =>
        (frequencyW1 E draws - eventProbability P E)^2) = eventProbability P E * (1-eventProbability P E) / J := by
    simpa only [iidExpectationW1, iidMassW1, frequencyW1, hitCountW1,
      eventProbability, AronowAudit.P037.sampleProb, Bridge.toProject] using
        AronowAudit.P037.Wave1.exposureMC_moments (Bridge.toProject P) E J hJ
  refine ⟨hm.1, ?_⟩
  unfold iidVarianceW1
  rw [hm.1]
  exact hm.2
/-- A defined finite frequency is zero exactly when its hit count is zero. -/
theorem frequencyZeroIffW1 {Ω : Type} {J : ℕ} (hJ : 0 < J)
    (E : Ω → Prop) (draws : Fin J → Ω) : frequencyW1 E draws = 0 ↔ hitCountW1 E draws = 0 := by
  simp only [frequencyW1, div_eq_zero_iff, Nat.cast_eq_zero]
  simp [ne_of_gt hJ]
/-- Assemble every mathematical clause of the outcome-specific population claim. The only new proof obligations are the block marginal, the joint cutoff, and the balanced supported simulation. Random-set measurability allows constant masks. -/
theorem T22_assembly (h1 : T22_L1) (h2 : T22_L2) (h3 : T22_L3) : T22WholeStatement := by
  refine ⟨Bridge.T22_correspondence.{0,0,0,0,0}, ?_, ?_, ?_, ?_, h2, ?_, ?_, ?_⟩
  · intro Ω I _ P D J hJ draws i k hp
    have he := AronowAudit.P037.Wave1.exposureMC_zero (Bridge.toProject P)
      (fun z => D z i = k) hp
    simp [frequencyW1, hitCountW1, he]
  · intro Ω I _ P D i
    simp_rw [labelProbabilityW1]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
    exact P.total
  · have hc := Bridge.T21_correspondence
    dsimp [T22StrictW1]
    have hπ (k : Fin 4) : eventProbability cutoffDesignW1 (fun z =>
          cutoffExposureW1 ∅ {0,1,2,3,4,5} {0} z = k.castSucc) = (![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k := by
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
      let draws : Fin 10000 → CutoffAssignmentsW1 := fun j => liftCutoffAssignmentW1 (z j) (hz j)
      have hfreq (k : Fin 4) : estimatedExposureW1 (fun w (_ : Unit) =>
            cutoffExposureW1 ∅ {0,1,2,3,4,5} {0} w) draws () k = (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k := by
        simp only [estimatedExposureW1, draws, cutoffExposureW1, liftCutoffAssignmentW1]
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
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      exact iidBinomialW1 P (fun z => D z i = k.castSucc) 10000 r
    · intro draws
      refine ⟨?_, (AronowAudit.P037.cutoff_integer_rule
        (hitCountW1 (fun z => D z i = k.castSucc) draws) (hitCount_leW1 _ _)).1⟩
      dsimp only [frequencyW1]
      ring
    · intro draws h
      have hk := h k
      rw [estimatedFrequencyW1] at hk ⊢
      exact (AronowAudit.P037.cutoff_integer_rule
        (hitCountW1 (fun z => D z i = k.castSucc) draws) (hitCount_leW1 _ _)).2
          ((AronowAudit.P037.cutoff_integer_rule
            (hitCountW1 (fun z => D z i = k.castSucc) draws) (hitCount_leW1 _ _)).1.mp hk)
  · intro Ω I _ P D estimated outcome baseline screen i
    exact ⟨AronowAudit.P037.code_analysis_seed_exclusion (Bridge.toProject P)
      estimated (fun z i => D z i = 4) outcome baseline screen i, @measurable_from_top Ω (Set I) ⊤ _⟩
  · dsimp [T22DependenceExampleW1]
    refine ⟨?_, ?_⟩
    · change eventProbability cutoffDesignW1
        (fun z => cutoffExposureW1 {2} {0,1} {0} z = 4) = 1/4
      rw [h1]
      exact Bridge.T21_correspondence.1.2.2.2.2.2.1 4
    · obtain ⟨draws, hdraws⟩ := h3
      let a : CutoffAssignmentsW1 := (true, fun _ => ⟨{2,3,4,5,6,7}, by norm_num⟩)
      let b : CutoffAssignmentsW1 := (true, fun _ => ⟨{3,4,5,6,7,8}, by norm_num⟩)
      have hest : estimatedExposureW1 cutoffNetworkW1 draws = (fun (_ : Fin 2) (_ : Fin 4) => (1/4 : ℝ)) := by
        funext i k
        exact hdraws i k
      refine ⟨draws, hdraws, a, b, ?_, ?_, ?_, ?_⟩
      · norm_num [a, cutoffNetworkW1, cutoffExposureW1, localTreatedLabel,
          Finset.disjoint_insert_right]
      · norm_num [b, cutoffNetworkW1, cutoffExposureW1, localTreatedLabel,
          Finset.disjoint_insert_right]
      · rw [hest]
        ext i
        fin_cases i <;>
          norm_num [analysisFinsetW1, analysisPopulation, exposureProbabilityCutoff,
            hdraws, a, cutoffNetworkW1, cutoffExposureW1, localTreatedLabel,
            Finset.disjoint_insert_right]
      · rw [hest]
        ext i
        fin_cases i <;>
          norm_num [analysisFinsetW1, analysisPopulation, exposureProbabilityCutoff,
            hdraws, b, cutoffNetworkW1, cutoffExposureW1, localTreatedLabel,
            Finset.disjoint_insert_right]
  · intro Ω I _ _ P D J hJ draws outcome baseline peerConflict schoolMean z prediction k
    dsimp only
    intro hA
    refine ⟨rfl, Nat.cast_pos.mpr (Finset.card_pos.mpr hA), ?_, rfl⟩
    obtain ⟨i, hi⟩ := hA
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hm := (Finset.mem_filter.mp hi).2
    have hsub : analysisPopulation (estimatedExposureW1 D draws)
        (fun z i => D z i = 4) outcome baseline
        (fun z i => peerConflict = false ∨ passesConflictThreshold (schoolMean z i)) z ⊆
        positiveExposurePopulation (fun i l => eventProbability P (fun w => D w i = l.castSucc)) := by
      have hest : estimatedExposureW1 D draws =
          (fun i (k : Fin 4) => ((Finset.univ.filter
            (fun j => D (draws j) i = k.castSucc)).card : ℝ) / J) := by
        funext i k
        rfl
      rw [hest]
      exact (Bridge.T22_correspondence.{0,0,0,0,0}.1 P D J hJ draws (fun z i => D z i = 4) outcome baseline
          (fun z i => peerConflict = false ∨ passesConflictThreshold (schoolMean z i)) z).2.2.2.2.1
    exact fun l => (hsub hm l).1
/-- Assemble the complete finite witness, with the full independent-draw law. Only the actual two-block selection census is delegated; numerical consequences and probability specializations are proved here. -/
theorem T29_assembly (h1 : T29_L1) : T29WholeStatement := by
  have hc := Bridge.T29_correspondence
  have hb : Fintype.card RareBlockW1 = 252 := by
    rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin 10)).powersetCard 5)
      (by intro s; simp)]
    norm_num [Finset.card_powersetCard, Nat.choose]
  have hs : T29SelectionsW1 := by
    refine ⟨by norm_num [Nat.choose], by norm_num [Nat.choose], hb, ?_, h1⟩
    change Fintype.card (RareBlockW1 × RareBlockW1) = 63504
    rw [Fintype.card_prod, hb]
  have hp1 : eventProbability rareDesignW1 (fun z => rareExposure z = 1) = 1/127008 := by
    rw [labelProbabilityW1]
    exact hc.1.2.1 1
  have hp0 : eventProbability rareDesignW1 (fun z => rareExposure z = 0) = 1/2 := by
    rw [labelProbabilityW1]
    exact hc.1.2.1 0
  have hm1 := iidMomentsW1 rareDesignW1 (fun z => rareExposure z = 1) 10000 (by omega)
  have hm0 := iidMomentsW1 rareDesignW1 (fun z => rareExposure z = 0) 10000 (by omega)
  rw [hp1] at hm1
  rw [hp0] at hm0
  dsimp only [rareDesignW1] at hm1 hm0
  have hv1 : iidVarianceW1 rareAssignmentMass 10000
      (frequencyW1 (fun z => rareExposure z = 1)) = 127007/161310320640000 := by
    convert hm1.2 using 1
    norm_num
  have hv0 : iidVarianceW1 rareAssignmentMass 10000
      (frequencyW1 (fun z => rareExposure z = 0)) = 1/40000 := by
    convert hm0.2 using 1
    norm_num
  refine ⟨hc, hs, ?_, ?_, iidTotalW1 rareDesignW1 10000, ?_, ?_, ?_⟩
  · simp_rw [hc.1.2.1]
    norm_num [Fin.sum_univ_succ]
  · intro z
    norm_num [rareAssignmentMass, Fin.prod_univ_succ]
  · dsimp only
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    intro draws
    let r := hitCountW1 (fun z => rareExposure z = 1) draws
    have hf := hc.2.1 r
    refine ⟨hitCount_leW1 _ _, ?_, ?_, hf.1, ?_⟩
    · intro hr
      rw [hr]
      norm_num
    · intro hr
      have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have hpos : 0 ≤ (r : ℝ)/10000-(1/127008 : ℝ) := by linarith
      rw [abs_of_nonneg hpos]
      constructor <;> linarith
    · convert hf.2 using 1
      norm_num
  · dsimp only
    have hz : iidProbabilityW1 rareAssignmentMass 10000 (fun draws =>
        frequencyW1 (fun z => rareExposure z = 1) draws = 0) =
        (127007/127008 : ℝ)^10000 := by
      have he (draws : Fin 10000 → RareSeedAssignments) :
          (frequencyW1 (fun z => rareExposure z = 1) draws = 0) ↔
            hitCountW1 (fun z => rareExposure z = 1) draws = 0 :=
        frequencyZeroIffW1 (by omega) _ _
      have hzcount := iidBinomialW1 rareDesignW1 (fun z => rareExposure z = 1) 10000 0
      rw [hp1] at hzcount
      dsimp only [rareDesignW1] at hzcount
      have hcomp : 1-(1/127008 : ℝ) = 127007/127008 := by norm_num
      rw [hcomp] at hzcount
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at hzcount
      calc
        _ = iidProbabilityW1 rareAssignmentMass 10000
            (fun draws => hitCountW1 (fun z => rareExposure z = 1) draws = 0) := by
          exact iidProbabilityCongrW1 rareAssignmentMass 10000 _ _ he
        _ = _ := hzcount
    refine ⟨?_, hm1.1, hv1, ?_, ?_, hz, ?_⟩
    · intro r hr
      have hh := iidBinomialW1 rareDesignW1 (fun z => rareExposure z = 1) 10000 r
      rw [hp1] at hh
      dsimp only [rareDesignW1] at hh
      exact hh
    · rw [hv1]
      norm_num
    · rw [hv1]
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1/127008)).mpr
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (7/2)*(1/127008))).mpr
      norm_num
    · rw [hz]
      exact hc.1.2.2.2.2.2.1
  · dsimp only
    refine ⟨hm0.1, hv0, ?_⟩
    rw [hv0]
    have hsq : (1/40000 : ℝ) = (1/200 : ℝ)^2 := by norm_num
    rw [hsq, Real.sqrt_sq_eq_abs]
    norm_num
end SAP.P037b.WH.W1
