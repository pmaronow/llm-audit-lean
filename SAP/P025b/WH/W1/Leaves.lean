import SAP.P025b.WH.W1.Leaves.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Class totals on the disjoint union of the classes are the corresponding finite sums. -/
theorem sigma_class_total {J : ℕ} (m : Fin J → ℕ) {κ : Type*} [Fintype κ]
    (d : FiniteDesign (Σ j : Fin J, Fin (m j)) κ) (j : Fin J) :
    classTotal d Sigma.fst j = ∑ i : Fin (m j), inclusion d ⟨j,i⟩ := by
  classical
  have hf (k : Fin J) :
      (∑ i : Fin (m k), if k = j then inclusion d ⟨k,i⟩ else 0) =
        if k = j then ∑ i : Fin (m k), inclusion d ⟨k,i⟩ else 0 := by
    by_cases h : k = j <;> simp [h]
  simp only [classTotal, Finset.sum_filter, Fintype.sum_sigma]
  simp_rw [hf]
  simp

/-- The finite marginal realization leaf supplies the sampling-design interpretation. -/
theorem class_design_realization (h1 : T15_L1) : ClassDesignRealization := by
  intro J α β hα hab hb mass m
  constructor
  · intro hm
    have hmpos (j : Fin J) : (0 : ℝ) < m j := by exact_mod_cast (hm j).1
    let p : (Σ j : Fin J, Fin (m j)) → ℝ := fun i => mass i.1/(m i.1 : ℝ)
    have hp (i : Σ j : Fin J, Fin (m j)) : α ≤ p i ∧ p i ≤ β := by
      exact ⟨(le_div_iff₀ (hmpos i.1)).mpr (hm i.1).2.1,
        (div_le_iff₀ (hmpos i.1)).mpr (hm i.1).2.2⟩
    obtain ⟨d, _, _, hd⟩ := h1 _ p (fun i =>
      ⟨hα.le.trans (hp i).1, (hp i).2.trans hb⟩)
    refine ⟨fun j => (hm j).1, d, ?_, ?_⟩
    · intro i; rw [hd]; exact hp i
    · intro j
      rw [sigma_class_total]
      simp_rw [hd]
      simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel₀ _ (hmpos j).ne'
  · rintro ⟨hm, d, hd, hmass⟩ j
    have hs := sigma_class_total m d j
    have hlo := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m j))))
      (fun i _ => (hd ⟨j,i⟩).1)
    have hhi := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m j))))
      (fun i _ => (hd ⟨j,i⟩).2)
    rw [← hs, hmass] at hlo hhi
    refine ⟨hm j, ?_, ?_⟩
    · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_comm] using hlo
    · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_comm] using hhi

/-- Four share-only endpoint values obtained by rescaling the existing class-total examples. -/
theorem binary_share_endpoints :
    lowerEndpoint binaryTwo ![1/3,2/3] (1/2) (3/4) = 4/7 ∧
    upperEndpoint binaryTwo ![1/3,2/3] (1/2) (3/4) = 3/4 ∧
    lowerEndpoint binaryTwo ![1/3,2/3] (1/10) (1/5) = 1/2 ∧
    upperEndpoint binaryTwo ![1/3,2/3] (1/10) (1/5) = 4/5 := by
  have heA : (fun j => (2 : ℝ)*(![1/3,2/3] : Fin 2 → ℝ) j) = ![2/3,4/3] := by
    ext j; fin_cases j <;> norm_num
  have heB : (fun j => (150 : ℝ)*(![1/3,2/3] : Fin 2 → ℝ) j) = ![50,100] := by
    ext j; fin_cases j <;> norm_num
  have hA := attainable_scale binaryTwo ![1/3,2/3] (1/2) (3/4) 2 (by norm_num)
  have hB := attainable_scale binaryTwo ![1/3,2/3] (1/10) (1/5) 150 (by norm_num)
  rw [heA] at hA
  rw [heB] at hB
  obtain ⟨hAl, hAh, hBl, hBh⟩ := AronowAudit.P025.sharpness_counterexample_box_extrema
  refine ⟨?_, ?_, ?_, ?_⟩
  · change sInf _ = _; rw [← hA]; exact hAl.csInf_eq
  · change sSup _ = _; rw [← hA]; exact hAh.csSup_eq
  · change sInf _ = _; rw [← hB]; exact hBl.csInf_eq
  · change sSup _ = _; rw [← hB]; exact hBh.csSup_eq

/-- The retained-size counterexample follows from its integer-count leaf. -/
theorem retained_information_failure (h2 : T15_L2) : RetainedInformationFailure := by
  have hs : sharesKnownSizeMeans binaryTwo ![1/3,2/3] (1/2) (3/4) 3 = {(2/3 : ℝ)} := by
    ext v
    constructor
    · rintro ⟨m, hm, hN, hv⟩
      rw [(h2 m hN).mp hm] at hv
      norm_num [classMean, binaryTwo, Fin.sum_univ_two] at hv
      exact hv.symm
    · intro hv
      have hv' : v = (2/3 : ℝ) := hv
      have hN : (∑ j : Fin 2, (![1,2] : Fin 2 → ℕ) j) = 3 := by
        norm_num [Fin.sum_univ_two]
      refine ⟨![1,2], (h2 _ hN).mpr rfl, hN, ?_⟩
      norm_num [classMean, binaryTwo, Fin.sum_univ_two, hv']
  obtain ⟨hl, hh, _, _⟩ := AronowAudit.P025.sharpness_counterexample_box_extrema
  refine ⟨AronowAudit.P025.integrality_mean_set_and_gaps.1, hl.csInf_eq, hh.csSup_eq,
    hs, binary_share_endpoints.1, binary_share_endpoints.2.1, ?_, ?_⟩ <;> norm_num

/-- Whole shares-only sharpness, with no new assumption on its information set. -/
theorem T15_assembly (h1 : T15_L1) (h2 : T15_L2) : T15WholeStatement := by
  refine ⟨retained_T15, compatibility_existence, class_design_realization h1, ?_,
    retained_information_failure h2⟩
  intro J hJ y q hq α β T hα hab hb hT
  have he := attainable_scale y q α β T hT.ne'
  exact ⟨fun W _ => AronowAudit.P025.ratio_scale_masses y q W T hT.ne',
    he, congrArg sInf he, congrArg sSup he⟩

/-- The two absolute-total integer calibrations, with every numeric interval exported. -/
theorem counterexample_count_intervals :
    (∀ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m ↔
      (∀ j, 0 < m j) ∧
      (8/9 : ℝ) ≤ m 0 ∧ (m 0 : ℝ) ≤ 4/3 ∧
      (16/9 : ℝ) ≤ m 1 ∧ (m 1 : ℝ) ≤ 8/3) ∧
    (∀ m : Fin 2 → ℕ, absoluteCompatible (1/10) (1/5) ![50,100] m ↔
      (∀ j, 0 < m j) ∧ 250 ≤ m 0 ∧ m 0 ≤ 500 ∧ 500 ≤ m 1 ∧ m 1 ≤ 1000) := by
  constructor
  · intro m
    constructor
    · intro hm
      have h0 := hm 0; have h1 := hm 1
      norm_num at h0 h1
      exact ⟨fun j => (hm j).1, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨hp, h00, h01, h10, h11⟩ j
      fin_cases j <;> refine ⟨hp _, ?_, ?_⟩ <;> norm_num <;> linarith
  · intro m
    constructor
    · intro hm
      have h0 := hm 0; have h1 := hm 1
      norm_num at h0 h1
      refine ⟨fun j => (hm j).1, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast (show (250 : ℝ) ≤ m 0 by linarith)
      · exact_mod_cast (show (m 0 : ℝ) ≤ 500 by linarith)
      · exact_mod_cast (show (500 : ℝ) ≤ m 1 by linarith)
      · exact_mod_cast (show (m 1 : ℝ) ≤ 1000 by linarith)
    · rintro ⟨hp, h00, h01, h10, h11⟩ j
      have h00' : (250 : ℝ) ≤ m 0 := by exact_mod_cast h00
      have h01' : (m 0 : ℝ) ≤ 500 := by exact_mod_cast h01
      have h10' : (500 : ℝ) ≤ m 1 := by exact_mod_cast h10
      have h11' : (m 1 : ℝ) ≤ 1000 := by exact_mod_cast h11
      fin_cases j <;> refine ⟨hp _, ?_, ?_⟩ <;> norm_num <;> linarith

/-- Uniform quota draws combine to realize every permitted integer k. -/
theorem known_size_quota_realization (h1 : T16_L1) (h2 : T16_L2)
    (k : ℕ) (hklo : 500 ≤ k) (hkhi : k ≤ 750) : KnownSizeQuotaRealization k := by
  obtain ⟨d₀, hs₀, hp₀, hi₀⟩ := h1 (1000-k) 50 (by norm_num) (by omega)
  obtain ⟨d₁, hs₁, hp₁, hi₁⟩ := h1 k 100 (by norm_num) (by omega)
  have hiL (i : Fin (1000-k)) :
      inclusion (sumDesign d₀ d₁) (Sum.inl i) = 50/((1000-k : ℕ) : ℝ) :=
    ((h2 d₀ d₁).1 i).trans (hi₀ i)
  have hiR (i : Fin k) : inclusion (sumDesign d₀ d₁) (Sum.inr i) = 100/(k : ℝ) :=
    ((h2 d₀ d₁).2 i).trans (hi₁ i)
  have hnlo : (250 : ℝ) ≤ ((1000-k : ℕ) : ℝ) := by
    exact_mod_cast (show 250 ≤ 1000-k by omega)
  have hnhi : ((1000-k : ℕ) : ℝ) ≤ 500 := by
    exact_mod_cast (show 1000-k ≤ 500 by omega)
  have hklo' : (500 : ℝ) ≤ k := by exact_mod_cast hklo
  have hkhi' : (k : ℝ) ≤ 750 := by exact_mod_cast hkhi
  have hnpos : (0 : ℝ) < ((1000-k : ℕ) : ℝ) := by linarith
  have hkpos : (0 : ℝ) < k := by linarith
  refine ⟨sumDesign d₀ d₁, ?_, ?_, hiL, hiR, ?_, ?_, ?_, replications_iid _⟩
  · intro ω
    change (d₀.sample ω.1).map _ ∪ (d₁.sample ω.2).map _ = _
    rw [hs₀, hs₁]
  · intro ω
    change d₀.probability ω.1*d₁.probability ω.2 = _
    rw [hp₀, hp₁]
  · intro i
    rcases i with i | i
    · rw [hiL]
      exact ⟨(le_div_iff₀ hnpos).mpr (by linarith),
        (div_le_iff₀ hnpos).mpr (by linarith)⟩
    · rw [hiR]
      exact ⟨(le_div_iff₀ hkpos).mpr (by linarith),
        (div_le_iff₀ hkpos).mpr (by linarith)⟩
  · intro j
    rw [classTotal, Finset.sum_filter, Fintype.sum_sum_type]
    fin_cases j <;> simp [sumClass, hiL, hiR] <;> field_simp [hnpos.ne', hkpos.ne']
  · intro ω
    have hdisj : Disjoint (ω.1.val.map (Function.Embedding.inl :
        Fin (1000-k) ↪ Fin (1000-k) ⊕ Fin k))
        (ω.2.val.map Function.Embedding.inr) := by
      apply Finset.disjoint_left.mpr
      intro i hL hR
      obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hL
      obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hR
      have hxy : (Sum.inl x : Fin (1000-k) ⊕ Fin k) = Sum.inr y := hx.trans hy.symm
      cases hxy
    change ((d₀.sample ω.1).map _ ∪ (d₁.sample ω.2).map _).card = 150
    rw [hs₀, hs₁, Finset.card_union_of_disjoint hdisj, Finset.card_map,
      Finset.card_map, ω.1.property, ω.2.property]

/-- Both examples retain outer bounds and the shares-only sharpness conclusion. -/
theorem counterexample_preservation : CounterexamplePreservation := by
  have hy : StrictMono binaryTwo := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [binaryTwo] at *
  have hq : ∀ j : Fin 2, (0 : ℝ) < (![1/3,2/3] : Fin 2 → ℝ) j := by
    intro j; fin_cases j <;> norm_num
  have hcA : ∃ m : Fin 2 → ℕ, sharesCompatible (1/2) (3/4) ![1/3,2/3] m := by
    refine ⟨![1,2], 2, by norm_num, ?_⟩
    intro j; fin_cases j <;> norm_num
  have hcB : ∃ m : Fin 2 → ℕ, sharesCompatible (1/10) (1/5) ![1/3,2/3] m := by
    refine ⟨![1,2], 3/10, by norm_num, ?_⟩
    intro j; fin_cases j <;> norm_num
  obtain ⟨hlA, hhA⟩ := AronowAudit.P025.shares_sharp_endpoints
    (by norm_num : 0 < 2) binaryTwo ![1/3,2/3] hy hq (1/2) (3/4)
      (by norm_num) (by norm_num) (by norm_num) hcA
  obtain ⟨hlB, hhB⟩ := AronowAudit.P025.shares_sharp_endpoints
    (by norm_num : 0 < 2) binaryTwo ![1/3,2/3] hy hq (1/10) (1/5)
      (by norm_num) (by norm_num) (by norm_num) hcB
  change IsGLB (compatibleMeans binaryTwo ![1/3,2/3] (1/2) (3/4))
    (lowerEndpoint binaryTwo ![1/3,2/3] (1/2) (3/4)) at hlA
  change IsLUB (compatibleMeans binaryTwo ![1/3,2/3] (1/2) (3/4))
    (upperEndpoint binaryTwo ![1/3,2/3] (1/2) (3/4)) at hhA
  change IsGLB (compatibleMeans binaryTwo ![1/3,2/3] (1/10) (1/5))
    (lowerEndpoint binaryTwo ![1/3,2/3] (1/10) (1/5)) at hlB
  change IsLUB (compatibleMeans binaryTwo ![1/3,2/3] (1/10) (1/5))
    (upperEndpoint binaryTwo ![1/3,2/3] (1/10) (1/5)) at hhB
  rw [binary_share_endpoints.1] at hlA
  rw [binary_share_endpoints.2.1] at hhA
  rw [binary_share_endpoints.2.2.1] at hlB
  rw [binary_share_endpoints.2.2.2] at hhB
  obtain ⟨hAl, hAh, hBl, hBh⟩ := AronowAudit.P025.sharpness_counterexample_box_extrema
  have eAl : lowerEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) = 4/7 := hAl.csInf_eq
  have eAh : upperEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) = 3/4 := hAh.csSup_eq
  have eBl : lowerEndpoint binaryTwo ![50,100] (1/10) (1/5) = 1/2 := hBl.csInf_eq
  have eBh : upperEndpoint binaryTwo ![50,100] (1/10) (1/5) = 4/5 := hBh.csSup_eq
  refine ⟨?_, ?_, hlA, hhA, hlB, hhB⟩
  · intro m hm
    have ho := AronowAudit.P025.absolute_outer_bound (by norm_num : 0 < 2)
      binaryTwo ![2/3,4/3] hy (by intro j; fin_cases j <;> norm_num)
      (1/2) (3/4) (by norm_num) (by norm_num) (by norm_num) m hm
    change lowerEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) ≤ classMean binaryTwo m ∧
      classMean binaryTwo m ≤ upperEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) at ho
    simpa only [eAl, eAh] using ho
  · intro m hm
    have ho := AronowAudit.P025.absolute_outer_bound (by norm_num : 0 < 2)
      binaryTwo ![50,100] hy (by intro j; fin_cases j <;> norm_num)
      (1/10) (1/5) (by norm_num) (by norm_num) (by norm_num) m hm
    change lowerEndpoint binaryTwo ![50,100] (1/10) (1/5) ≤ classMean binaryTwo m ∧
      classMean binaryTwo m ≤ upperEndpoint binaryTwo ![50,100] (1/10) (1/5) at ho
    simpa only [eBl, eBh] using ho

/-- The two complete counterexamples, including their explicit sampling laws. -/
theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2) : T16WholeStatement := by
  refine ⟨retained_T16, replications_iid omitOneDesign, ?_, ?_, ?_, ?_, ?_, ?_,
    counterexample_count_intervals.1, counterexample_count_intervals.2,
    known_size_quota_realization h1 h2, ?_, counterexample_preservation⟩
  all_goals norm_num [ratio, binaryTwo, classMean, lowerValue, upperValue,
    lowerWeights, upperWeights, Fin.sum_univ_two]

end
end SAP.P025b.WH.W1
