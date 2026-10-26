import AronowAudit.P037.P037_Sample
import AronowAudit.P037.P037_Network
import AronowAudit.P037.P037_FiniteDesign

namespace AronowAudit.P037.Wave1
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
noncomputable local instance instDecidableGP037B2 (p : Prop) : Decidable p := Classical.propDecidable p

lemma estimated_cutoff_event_pos {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ z, 0 < p z) (E : Ω → Prop) [DecidablePred E] (he : ∃ z, E z) :
    0 < ∑ z, p z * (if E z then (1:ℝ) else 0) := by
  classical
  obtain ⟨z, hz⟩ := he
  apply Finset.sum_pos'
  · intro w _
    by_cases h : E w
    · simpa [h] using le_of_lt (hp w)
    · simp [h]
  · exact ⟨z, Finset.mem_univ _, by simpa [hz] using hp z⟩

lemma estimated_cutoff_random_bounds {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop)
    (hp : 0<sampleProb P E) (hq : sampleProb P E<1)
    (J t : ℕ) (ht0 : 0<t) (htJ : t≤J) :
    let event := fun z : Fin J → Ω =>
      t≤(Finset.univ.filter (fun j => E (z j))).card
    0<(∑ z, (∏ j, P.mass (z j))*(if event z then (1:ℝ) else 0)) ∧
    (∑ z, (∏ j, P.mass (z j))*(if event z then (1:ℝ) else 0))<1 := by
  classical
  have he : ∃ z, E z := by
    by_contra h
    have hz : sampleProb P E = 0 := by simp [sampleProb, not_exists.mp h]
    linarith
  have hn : ∃ z, ¬E z := by
    by_contra h
    have ha : ∀ z, E z := by simpa using h
    have hz : sampleProb P E = 1 := by simpa [sampleProb, ha] using P.total
    linarith
  dsimp only
  let event := fun z : Fin J → Ω =>
      t≤(Finset.univ.filter (fun j => E (z j))).card
  have hm (z : Fin J → Ω) : 0 < ∏ j, P.mass (z j) :=
    Finset.prod_pos (fun j _ => P.positive (z j))
  have ht : (∑ z : Fin J → Ω, ∏ j, P.mass (z j)) = 1 := by
    rw [finite_product_factorization]
    simp [P.total]
  have hep : 0 < ∑ z : Fin J → Ω,
      (∏ j, P.mass (z j)) * (if event z then (1:ℝ) else 0) := by
    apply estimated_cutoff_event_pos _ hm
    obtain ⟨u, hu⟩ := he
    exact ⟨fun _ => u, by simp [event, hu, htJ]⟩
  refine ⟨hep, ?_⟩
  have hnp : 0 < ∑ z : Fin J → Ω,
      (∏ j, P.mass (z j)) * (if ¬event z then (1:ℝ) else 0) := by
    apply estimated_cutoff_event_pos _ hm
    obtain ⟨v, hv⟩ := hn
    exact ⟨fun _ => v, by simp [event, hv, Nat.not_le.mpr ht0]⟩
  have hsum : (∑ z : Fin J → Ω,
      (∏ j, P.mass (z j)) * (if event z then (1:ℝ) else 0)) +
      (∑ z : Fin J → Ω,
      (∏ j, P.mass (z j)) * (if ¬event z then (1:ℝ) else 0)) = 1 := by
    rw [← Finset.sum_add_distrib]
    conv_rhs => rw [← ht]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : event z <;> simp [h]
  linarith

theorem estimated_cutoff_random_proof {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop)
    (hp : 0<sampleProb P E) (hq : sampleProb P E<1) :
    let event := fun z : Fin 10000 → Ω =>
      101≤(Finset.univ.filter (fun j => E (z j))).card
    0<(∑ z, (∏ j, P.mass (z j))*(if event z then (1:ℝ) else 0)) ∧
    (∑ z, (∏ j, P.mass (z j))*(if event z then (1:ℝ) else 0))<1 := by
  exact estimated_cutoff_random_bounds P E hp hq 10000 101 (by omega) (by omega)

lemma nomination_univ10 : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by
  ext i; fin_cases i <;> simp

lemma nomination_univ20 : (Finset.univ : Finset (Fin 20)) = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19} := by
  ext i; fin_cases i <;> simp

lemma nomination_degrees10 : nominationIndegree nominationWitness10 =
    (![1,2,0,0,0,0,0,0,0,0] : Fin 10 → ℕ) := by
  funext j; fin_cases j <;>
    norm_num [nominationIndegree, nominationWitness10, nomination_univ10, Finset.filter_insert, Finset.filter_singleton]

lemma nomination_percentile10 : indegreeNinety nominationWitness10 = 11/10 := by
  norm_num [indegreeNinety, nomination_degrees10, List.ofFn_succ, List.mergeSort]

lemma nomination_referents10 : networkReferents nominationWitness10 = {1} := by
  ext j; fin_cases j <;>
    norm_num [networkReferents, nomination_percentile10, nomination_degrees10]

lemma nomination_degrees20 : nominationIndegree nominationWitness20 =
    (![1,6,7,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 20 → ℕ) := by
  funext j; fin_cases j <;>
    norm_num [nominationIndegree, nominationWitness20, nomination_univ20, Finset.filter_insert, Finset.filter_singleton]

lemma nomination_percentile20 : indegreeNinety nominationWitness20 = 3/2 := by
  norm_num [indegreeNinety, nomination_degrees20, List.ofFn_succ, List.mergeSort]

lemma nomination_referents20 : networkReferents nominationWitness20 = {1,2} := by
  ext j; fin_cases j <;>
    norm_num [networkReferents, nomination_percentile20, nomination_degrees20]

attribute [-instance] instDecidableGP037B2

/-- Exact census of the twenty three-of-six seed choices. -/
lemma nomination_count_direct (k : Fin 4) :
    (((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) =>
      (rowExposure nominationWitness20 {1,2} (s.image graphEligible20) 0).val+1=k.val)).card) =
      (![0,4,6,10] : Fin 4 → ℕ) k := by
  fin_cases k <;> decide

lemma nomination_count_union (k : Fin 4) :
    (((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) =>
      (rowExposure (eitherDirection nominationWitness20) {1,2} (s.image graphEligible20) 0).val+1=k.val)).card) =
      (![0,1,3,16] : Fin 4 → ℕ) k := by
  fin_cases k <;> decide

attribute [local instance] instDecidableGP037B2

lemma nomination_probabilities :
    (∀ k, graphProbability20 nominationWitness20 k=(![1/2,1/10,3/20,1/4] : Fin 4 → ℝ) k) ∧
    (∀ k, graphProbability20 (eitherDirection nominationWitness20) k=(![1/2,1/40,3/40,2/5] : Fin 4 → ℝ) k) := by
  constructor
  · intro k
    simp only [graphProbability20, nomination_referents20, nomination_count_direct]
    fin_cases k <;> norm_num
  · intro k
    simp only [graphProbability20, nomination_referents20, nomination_count_union]
    fin_cases k <;> norm_num

theorem nomination_union_counterexamples_proof :
    indegreeNinety nominationWitness10=11/10 ∧ networkReferents nominationWitness10={1} ∧
    rowExposure nominationWitness10 (networkReferents nominationWitness10) {1} 0=0 ∧
    rowExposure (eitherDirection nominationWitness10) (networkReferents nominationWitness10) {1} 0=2 ∧
    indegreeNinety nominationWitness20=3/2 ∧ networkReferents nominationWitness20={1,2} ∧
    (∀ k, graphProbability20 nominationWitness20 k=(![1/2,1/10,3/20,1/4] : Fin 4 → ℝ) k) ∧
    (∀ k, graphProbability20 (eitherDirection nominationWitness20) k=(![1/2,1/40,3/40,2/5] : Fin 4 → ℝ) k) ∧
    (∀ k, 0<graphProbability20 nominationWitness20 k ∧ graphProbability20 nominationWitness20 k<1 ∧
      0<graphProbability20 (eitherDirection nominationWitness20) k ∧
      graphProbability20 (eitherDirection nominationWitness20) k<1) := by
  refine ⟨nomination_percentile10, nomination_referents10, ?_, ?_,
    nomination_percentile20, nomination_referents20,
    nomination_probabilities.1, nomination_probabilities.2, ?_⟩
  · norm_num [nomination_referents10, rowExposure, countExposure,
      networkSeedCount, networkReferentCount, nominationWitness10]
  · norm_num [nomination_referents10, rowExposure, countExposure,
      networkSeedCount, networkReferentCount, nominationWitness10, eitherDirection]
  · intro k
    simp only [nomination_probabilities.1, nomination_probabilities.2]
    fin_cases k <;> norm_num

abbrev RareProbabilityDesignBlock := {s : Finset (Fin 10) // s.card=5}

lemma rare_probability_block_card : Fintype.card RareProbabilityDesignBlock = 252 := by
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin 10)).powersetCard 5)
    (by intro s; simp)]
  norm_num [Finset.card_powersetCard, Nat.choose]

lemma rare_probability_block_sum (f : Finset (Fin 10) → ℝ) :
    (∑ s : RareProbabilityDesignBlock, f s.val) = ∑ s ∈ (Finset.univ : Finset (Fin 10)).powersetCard 5, f s := by
  exact (Finset.sum_subtype _ (by intro s; simp) f).symm

noncomputable def rare_probability_block_law : FiniteDesign RareProbabilityDesignBlock where
  weight := fun _ => 1/252
  nonneg := fun _ => by norm_num
  total := by norm_num [rare_probability_block_card, Nat.choose]

noncomputable def rare_probability_blocks_law : FiniteDesign (Fin 4 → RareProbabilityDesignBlock) :=
  productDesign (fun _ => rare_probability_block_law)

lemma rare_design_avoid_mean : designMean rare_probability_block_law
    (fun s => if Disjoint s.val {0,1,2,3,4} then (1:ℝ) else 0) = 1/252 := by
  unfold designMean rare_probability_block_law
  rw [← Finset.mul_sum, rare_probability_block_sum (fun s => if Disjoint s {0,1,2,3,4} then (1:ℝ) else 0)]
  have h := count_avoiding_seeds 10 5 ({0,1,2,3,4} : Finset (Fin 10))
  simp only [seedChoices] at h
  rw [Finset.sum_boole]
  norm_num at h
  simp only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
  rw [h]
  norm_num

lemma rare_design_referent_mean : designMean rare_probability_block_law
    (fun s => if (0:Fin 10) ∈ s.val then (1:ℝ) else 0) = 1/2 := by
  unfold designMean rare_probability_block_law
  rw [← Finset.mul_sum, rare_probability_block_sum (fun s => if (0:Fin 10) ∈ s then (1:ℝ) else 0), Finset.sum_boole]
  have he : ((Finset.univ : Finset (Fin 10)).powersetCard 5).filter (fun s => 0 ∈ s) =
      ((Finset.univ : Finset (Fin 10)).powersetCard 5).filter (fun s => {0} ⊆ s) := by
    ext s; simp
  rw [he, Finset.card_filter_powersetCard_subset _ _ _ (by simp) (by simp)]
  norm_num [Nat.choose]

lemma rare_design_card : Fintype.card RareSeedState = 2*252^4 := by
  calc
    _ = Fintype.card Bool * Fintype.card (Fin 4 → RareProbabilityDesignBlock) := Fintype.card_prod _ _
    _ = 2 * (Fintype.card RareProbabilityDesignBlock)^4 := by rw [Fintype.card_fun]; rfl
    _ = _ := by rw [rare_probability_block_card]

lemma rare_design_total : (∑ z : RareSeedState, rareDesignMass z) = 1 := by
  change (∑ _z : RareSeedState, (1:ℝ)/(2*252^4)) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rare_design_card]
  norm_num

noncomputable def rare_design_law : FiniteDesign RareSeedState where
  weight := rareDesignMass
  nonneg := fun _ => by norm_num [rareDesignMass]
  total := rare_design_total

lemma rare_design_split (f : RareSeedState → ℝ) :
    designMean rare_design_law f =
      (designMean rare_probability_blocks_law (fun w => f (true,w)) +
       designMean rare_probability_blocks_law (fun w => f (false,w)))/2 := by
  simp only [designMean, rare_design_law, rareDesignMass, Fintype.sum_prod_type, Fintype.sum_bool,
    rare_probability_blocks_law, productDesign, rare_probability_block_law,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma rare_design_probability0 : rareDesignProbability 0 = 1/2 := by
  change designMean rare_design_law (fun z => if rareDesignExposure z = 0 then (1:ℝ) else 0) = _
  rw [rare_design_split]
  have ht : (fun w : Fin 4 → RareProbabilityDesignBlock =>
      if rareDesignExposure (true,w) = 0 then (1:ℝ) else 0) = fun _ => 0 := by
    funext w
    simp only [rareDesignExposure, Bool.not_true, Bool.false_eq_true, ite_false]
    split_ifs <;> norm_num at *
  rw [ht]
  simp [rareDesignExposure, designMean_const]

lemma rare_design_probability1 : rareDesignProbability 1 = 1/127008 := by
  change designMean rare_design_law (fun z => if rareDesignExposure z = 1 then (1:ℝ) else 0) = _
  rw [rare_design_split]
  have ht : (fun w : Fin 4 → RareProbabilityDesignBlock =>
      if rareDesignExposure (true,w) = 1 then (1:ℝ) else 0) =
      fun w => (if Disjoint (w 0).val {0,1,2,3,4} then (1:ℝ) else 0) *
        (if Disjoint (w 1).val {0,1,2,3,4} then (1:ℝ) else 0) := by
    funext w
    by_cases h0 : Disjoint (w 0).val {0,1,2,3,4} <;>
      by_cases h1 : Disjoint (w 1).val {0,1,2,3,4} <;>
      by_cases hr : (0:Fin 10) ∈ (w 0).val <;> simp [rareDesignExposure, h0, h1, hr]
  rw [ht, rare_probability_blocks_law,
    product_design_coordinate_pair (fun _ : Fin 4 => rare_probability_block_law)
      0 1 (by norm_num)
      (fun s : RareProbabilityDesignBlock => if Disjoint s.val {0,1,2,3,4} then (1:ℝ) else 0)
      (fun s : RareProbabilityDesignBlock => if Disjoint s.val {0,1,2,3,4} then (1:ℝ) else 0)]
  simp only [rare_design_avoid_mean]
  norm_num [rareDesignExposure, designMean_const]

lemma rare_design_probability3 : rareDesignProbability 3 = 1/4 := by
  change designMean rare_design_law (fun z => if rareDesignExposure z = 3 then (1:ℝ) else 0) = _
  rw [rare_design_split]
  have ht : (fun w : Fin 4 → RareProbabilityDesignBlock =>
      if rareDesignExposure (true,w) = 3 then (1:ℝ) else 0) =
      fun w => if (0:Fin 10) ∈ (w 0).val then (1:ℝ) else 0 := by
    funext w
    by_cases hr : (0:Fin 10) ∈ (w 0).val
    · have hn : ¬Disjoint (w 0).val {0,1,2,3,4} := by
        intro h; exact Finset.disjoint_left.mp h hr (by simp)
      simp [rareDesignExposure, hr, hn]
    · simp only [rareDesignExposure, Bool.not_true, Bool.false_eq_true, ite_false]
      split_ifs <;> simp_all
  rw [ht, rare_probability_blocks_law, product_design_coordinate_mean (fun _ : Fin 4 => rare_probability_block_law) 0
    (fun s : RareProbabilityDesignBlock => if (0:Fin 10) ∈ s.val then (1:ℝ) else 0), rare_design_referent_mean]
  norm_num [rareDesignExposure, designMean_const]

lemma rare_design_probabilities : ∀ k,
    rareDesignProbability k = (![1/2,1/127008,31751/127008,1/4] : Fin 4 → ℝ) k := by
  have hsum : (∑ k : Fin 4, rareDesignProbability k) = 1 := by
    unfold rareDesignProbability
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    simpa using rare_design_total
  intro k; fin_cases k
  · exact rare_design_probability0
  · exact rare_design_probability1
  · rw [Fin.sum_univ_four, rare_design_probability0, rare_design_probability1, rare_design_probability3] at hsum
    change rareDesignProbability 2 = (31751/127008:ℝ)
    linarith
  · exact rare_design_probability3

/-- Moments under actual independent assignment draws, using finite-design variance additivity. -/
lemma rare_design_iid_moments {Ω : Type*} [Fintype Ω] (law : FiniteDesign Ω)
    (E : Ω → Prop) [DecidablePred E] (J : ℕ) (hJ0 : 0<J) (p : ℝ)
    (hp : designMean law (fun z => if E z then (1:ℝ) else 0) = p) :
    let hits := fun w : Fin J → Ω => (Finset.univ.filter (fun j => E (w j))).card
    let mass := fun w : Fin J → Ω => ∏ j, law.weight (w j)
    (∑ w, mass w*(hits w:ℝ))=(J:ℝ)*p ∧
    (∑ w, mass w*(if hits w=0 then (1:ℝ) else 0))=(1-p)^J ∧
    (∑ w, mass w*((hits w:ℝ)/J-p)^2)=p*(1-p)/J := by
  let d := productDesign (fun _ : Fin J => law)
  let X : Ω → ℝ := fun z => if E z then 1 else 0
  have hm : designMean law X = p := hp
  have hJ : (J:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hJ0)
  have hc (w : Fin J → Ω) :
      ((Finset.univ.filter (fun j => E (w j))).card:ℝ) = ∑ j, X (w j) := by
    simp [X, Finset.sum_boole]
  have hmean : designMean d (fun w => ∑ j, X (w j)) = (J:ℝ)*p := by
    rw [designMean_sum]
    simp only [d, product_design_coordinate_mean, hm, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hvar : designVariance d (fun w => ∑ j, X (w j)) =
      J*((p)*(1-p)) := by
    rw [product_design_sum_variance]
    simp only [X, exposure_indicator_moments, hm, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hz (w : Fin J → Ω) :
      (if (Finset.univ.filter (fun j => E (w j))).card=0 then (1:ℝ) else 0) =
        ∏ j, if ¬E (w j) then (1:ℝ) else 0 := by
    rw [Fintype.prod_boole (p := fun j : Fin J => ¬E (w j))]
    congr 1
    simp [Finset.filter_eq_empty_iff]
  have hcomp : designMean law (fun z => if ¬E z then (1:ℝ) else 0) =
      1-p := by
    have heq : (fun z => if ¬E z then (1:ℝ) else 0) = fun z => 1-X z := by
      funext z; dsimp [X]; split_ifs <;> simp_all
    rw [heq, designMean_sub, designMean_const, hm]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hc]
    exact hmean
  · simp_rw [hz]
    change designMean d (fun w => ∏ j, if ¬E (w j) then (1:ℝ) else 0) = _
    rw [product_design_mean_product (fun _ : Fin J => law)
      (fun _ z => if ¬E z then (1:ℝ) else 0)]
    simp only [hcomp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · simp_rw [hc]
    have heq : (fun w : Fin J → Ω => ((∑ j : Fin J, X (w j))/J-p)^2) =
        fun w : Fin J → Ω => (1/(J:ℝ)^2)*((∑ j : Fin J, X (w j))-(J:ℝ)*p)^2 := by
      funext w; field_simp [hJ]
    change designMean d _ = _
    rw [heq, designMean_mul, ← hmean, ← designVariance_centered, hvar]
    field_simp [hJ]

lemma rare_design_simulation_moments :
    let hits := fun draws : Fin 10000 → RareSeedState =>
       (Finset.univ.filter (fun j => rareDesignExposure (draws j)=1)).card
    let mass := fun draws : Fin 10000 → RareSeedState => ∏ j, rareDesignMass (draws j)
    (∑ draws, mass draws*(hits draws:ℝ))=625/7938 ∧
    (∑ draws, mass draws*(if hits draws=0 then (1:ℝ) else 0))=(127007/127008:ℝ)^10000 ∧
    (∑ draws, mass draws*((hits draws:ℝ)/10000-1/127008)^2)=127007/161310320640000 := by
  have h := rare_design_iid_moments rare_design_law (fun z => rareDesignExposure z=1)
    10000 (by omega) (1/127008) rare_design_probability1
  dsimp only at h ⊢
  have hb : (1-(1/127008:ℝ)) = 127007/127008 := by norm_num
  rw [hb] at h
  refine ⟨?_, h.2.1, ?_⟩
  · calc
      _ = (10000:ℝ)*(1/127008) := h.1
      _ = _ := by norm_num
  · calc
      _ = (1/127008:ℝ)*(127007/127008)/10000 := h.2.2
      _ = _ := by norm_num

theorem rare_probability_design_counterexample_proof :
    (∑ z : RareSeedState, rareDesignMass z)=1 ∧
    (∀ k, rareDesignProbability k=(![1/2,1/127008,31751/127008,1/4] : Fin 4 → ℝ) k) ∧
    (∀ k, 0<rareDesignProbability k ∧ rareDesignProbability k<1) ∧
    (∀ r : ℕ, rareDesignProbability 1≤ |(r:ℝ)/10000-rareDesignProbability 1| ∧
      rareDesignProbability 1/2< |(r:ℝ)/10000-rareDesignProbability 1|) ∧
    (let hits := fun draws : Fin 10000 → RareSeedState =>
       (Finset.univ.filter (fun j => rareDesignExposure (draws j)=1)).card
     let mass := fun draws : Fin 10000 → RareSeedState => ∏ j, rareDesignMass (draws j)
     (∑ draws, mass draws*(hits draws:ℝ))=625/7938 ∧
     (∑ draws, mass draws*(if hits draws=0 then (1:ℝ) else 0))=(127007/127008:ℝ)^10000 ∧
     (∑ draws, mass draws*((hits draws:ℝ)/10000-1/127008)^2)=127007/161310320640000) ∧
    (9/10:ℝ)<(127007/127008:ℝ)^10000 ∧ (127007/127008:ℝ)^10000<19/20 := by
  refine ⟨rare_design_total, rare_design_probabilities, ?_, ?_, rare_design_simulation_moments,
    rare_zero_hit_probability⟩
  · intro k; simp only [rare_design_probabilities]
    fin_cases k <;> norm_num
  · intro r
    simp only [rare_design_probabilities]
    change (1/127008:ℝ) ≤ |(r:ℝ)/10000-1/127008| ∧
      (1/127008:ℝ)/2 < |(r:ℝ)/10000-1/127008|
    have hh : (1/127008:ℝ)/2 = 1/254016 := by norm_num
    simpa only [hh] using rare_exposure_frequency_counterexample.1 r

end AronowAudit.P037.Wave1
