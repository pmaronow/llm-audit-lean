import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.Topology.Order.Compact
import Mathlib.Probability.Independence.Integration



namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## P006-T2: the finite threshold frontier -/

private lemma T2_sum_threshold {K : ℕ} (p a : Fin K → ℝ) (j : Fin K) (q : ℝ) :
    (∑ i, a i * thresholdRule p j q i) =
      (∑ i, if i < j then a i else 0) +
        a j * ((q - prefixMass p j) / p j) := by
  calc
    (∑ i, a i * thresholdRule p j q i) =
        ∑ i, ((if i < j then a i else 0) +
          (if i = j then a j * ((q - prefixMass p j) / p j) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hij : i < j
      · have hne : i ≠ j := ne_of_lt hij
        simp [thresholdRule, hij, hne]
      · by_cases heq : i = j
        · subst i
          simp [thresholdRule]
        · simp [thresholdRule, hij, heq]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private lemma T2_threshold_data {K : ℕ} (p m : Fin K → ℝ)
    (hp : ∀ i, 0 < p i) (j : Fin K) (q : ℝ)
    (hlo : prefixMass p j ≤ q) (hhi : q ≤ prefixMass p j + p j) :
    thresholdRule p j q ∈ finitePolicies ∧
    finiteMass p (thresholdRule p j q) = q ∧
    finiteA p m (thresholdRule p j q) =
      prefixA p m j + m j * (q - prefixMass p j) := by
  have hr0 : 0 ≤ (q - prefixMass p j) / p j :=
    div_nonneg (sub_nonneg.mpr hlo) (hp j).le
  have hr1 : (q - prefixMass p j) / p j ≤ 1 := by
    apply (div_le_iff₀ (hp j)).mpr
    linarith
  have hc : p j * ((q - prefixMass p j) / p j) = q - prefixMass p j := by
    field_simp [ne_of_gt (hp j)]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [thresholdRule]
    split_ifs <;> first | exact ⟨hr0, hr1⟩ | norm_num
  · unfold finiteMass
    rw [T2_sum_threshold]
    change prefixMass p j + p j * ((q - prefixMass p j) / p j) = q
    rw [hc]
    ring
  · unfold finiteA
    rw [T2_sum_threshold]
    change prefixA p m j + (p j * m j) * ((q - prefixMass p j) / p j) = _
    calc
      _ = prefixA p m j + m j *
          (p j * ((q - prefixMass p j) / p j)) := by ring
      _ = _ := by rw [hc]

private lemma T2_frontier {K : ℕ} (p m : Fin K → ℝ)
    (hp : ∀ i, 0 < p i) (hm : Antitone m) (j : Fin K)
    (π : Fin K → ℝ) (hπ : π ∈ finitePolicies) :
    finiteA p m π ≤ prefixA p m j + m j * (finiteMass p π - prefixMass p j) := by
  have hid : finiteA p m π - m j * finiteMass p π =
      ∑ i, p i * (m i - m j) * π i := by
    unfold finiteA finiteMass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hprefix : prefixA p m j - m j * prefixMass p j =
      ∑ i, if i < j then p i * (m i - m j) else 0 := by
    unfold prefixA prefixMass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : i < j <;> simp [hij] <;> ring
  have hbound : (∑ i, p i * (m i - m j) * π i) ≤
      ∑ i, if i < j then p i * (m i - m j) else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hij : i < j
    · rw [if_pos hij]
      have hcoef : 0 ≤ p i * (m i - m j) :=
        mul_nonneg (hp i).le (sub_nonneg.mpr (hm hij.le))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hπ i).2 hcoef
    · rw [if_neg hij]
      have hcoef : p i * (m i - m j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hp i).le
          (sub_nonpos.mpr (hm (le_of_not_gt hij)))
      exact mul_nonpos_of_nonpos_of_nonneg hcoef (hπ i).1
  rw [← hid, ← hprefix] at hbound
  linarith

private lemma T2_prefix_right {K : ℕ} (p : Fin K → ℝ) (j : Fin K) :
    prefixMass p j + p j = ∑ i, if i ≤ j then p i else 0 := by
  have hsingle : (∑ i : Fin K, if i = j then p j else 0) = p j := by simp
  rw [prefixMass, ← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : i < j
  · simp [hij, hij.le, ne_of_lt hij]
  · by_cases heq : i = j
    · subst i
      simp
    · have hnle : ¬ i ≤ j := by
        intro h
        exact heq (le_antisymm h (le_of_not_gt hij))
      simp [hij, heq, hnle]

private lemma T2_prefix_cover {K : ℕ} (hK : 0 < K) (p : Fin K → ℝ)
    (hsum : ∑ i, p i = 1) (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∃ j, prefixMass p j ≤ q ∧ q ≤ prefixMass p j + p j := by
  let last : Fin K := ⟨K - 1, by omega⟩
  have hlast : prefixMass p last + p last = 1 := by
    rw [T2_prefix_right, ← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i ≤ last := by
      change i.val ≤ K - 1
      omega
    simp only [if_pos hil]
  let s : Finset (Fin K) := Finset.univ.filter (fun j => q ≤ prefixMass p j + p j)
  have hs : s.Nonempty := by
    refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hlast]
    exact hq.2
  let j : Fin K := s.min' hs
  have hjmem : j ∈ s := Finset.min'_mem s hs
  refine ⟨j, ?_, (Finset.mem_filter.mp hjmem).2⟩
  by_cases hj0 : j.val = 0
  · have hpref : prefixMass p j = 0 := by
      unfold prefixMass
      apply Finset.sum_eq_zero
      intro i hi
      have hnlt : ¬ i < j := by change ¬ i.val < j.val; omega
      simp only [if_neg hnlt]
    rw [hpref]
    exact hq.1
  · let k : Fin K := ⟨j.val - 1, by omega⟩
    have hkj : k < j := by change j.val - 1 < j.val; omega
    have hprev : prefixMass p k + p k = prefixMass p j := by
      rw [T2_prefix_right]
      unfold prefixMass
      apply Finset.sum_congr rfl
      intro i hi
      have he : i ≤ k ↔ i < j := by
        change i.val ≤ j.val - 1 ↔ i.val < j.val
        omega
      simp only [he]
    have hknot : ¬ q ≤ prefixMass p k + p k := by
      intro hk
      have hkmem : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      have hjk : j ≤ k := Finset.min'_le s k hkmem
      exact (not_le_of_gt hkj) hjk
    rw [hprev] at hknot
    exact (lt_of_not_ge hknot).le

private lemma T2_mass_bounds {K : ℕ} (p : Fin K → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (π : Fin K → ℝ) (hπ : π ∈ finitePolicies) :
    0 ≤ finiteMass p π ∧ finiteMass p π ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hp i).le (hπ i).1)
  · calc
      finiteMass p π ≤ ∑ i, p i := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hπ i).2 (hp i).le
      _ = 1 := hsum

private lemma T2_threshold_maximum {K : ℕ} (hK : 0 < K) (n : ℕ)
    (p m : Fin K → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hm : Antitone m) :
    ∃ j q, prefixMass p j ≤ q ∧ q ≤ prefixMass p j + p j ∧
      IsBest finitePolicies
        (fun π => emptyFactor n (finiteMass p π) * finiteA p m π)
        (thresholdRule p j q) := by
  have hcompact : IsCompact (finitePolicies : Set (Fin K → ℝ)) := by
    exact isCompact_pi_infinite (s := fun _ : Fin K => Set.Icc (0 : ℝ) 1)
      (fun _ => isCompact_Icc)
  have hne : (finitePolicies : Set (Fin K → ℝ)).Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    intro i
    exact ⟨le_rfl, zero_le_one⟩
  have hmass : Continuous (fun π : Fin K → ℝ => finiteMass p π) := by
    unfold finiteMass
    exact continuous_finsetSum _ (fun i hi => continuous_const.mul (continuous_apply i))
  have hvalue : Continuous (fun π : Fin K → ℝ => finiteA p m π) := by
    unfold finiteA
    exact continuous_finsetSum _ (fun i hi => continuous_const.mul (continuous_apply i))
  have hfactor : Continuous (fun π : Fin K → ℝ => emptyFactor n (finiteMass p π)) := by
    unfold emptyFactor
    exact continuous_finsetSum _ (fun r hr => (continuous_const.sub hmass).pow r)
  obtain ⟨π₀, hπ₀, hmax⟩ := hcompact.exists_isMaxOn hne (hfactor.mul hvalue).continuousOn
  have hq := T2_mass_bounds p hp hsum π₀ hπ₀
  obtain ⟨j, hjlo, hjhi⟩ := T2_prefix_cover hK p hsum (finiteMass p π₀) hq
  obtain ⟨ht, htq, htA⟩ := T2_threshold_data p m hp j (finiteMass p π₀) hjlo hjhi
  have hfactor0 : 0 ≤ emptyFactor n (finiteMass p π₀) := by
    unfold emptyFactor
    apply Finset.sum_nonneg
    intro r hr
    exact pow_nonneg (sub_nonneg.mpr hq.2) r
  have hfront : finiteA p m π₀ ≤ finiteA p m (thresholdRule p j (finiteMass p π₀)) := by
    rw [htA]
    exact T2_frontier p m hp hm j π₀ hπ₀
  refine ⟨j, finiteMass p π₀, hjlo, hjhi, ht, ?_⟩
  intro π hπ
  calc
    emptyFactor n (finiteMass p π) * finiteA p m π ≤
        emptyFactor n (finiteMass p π₀) * finiteA p m π₀ :=
      (isMaxOn_iff.mp hmax) π hπ
    _ ≤ emptyFactor n (finiteMass p (thresholdRule p j (finiteMass p π₀))) *
        finiteA p m (thresholdRule p j (finiteMass p π₀)) := by
      rw [htq]
      exact mul_le_mul_of_nonneg_left hfront hfactor0

theorem T2_finite_threshold_proof {K : ℕ} (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (p m : Fin K → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hm : Antitone m) :
    (∀ j q, prefixMass p j ≤ q → q ≤ prefixMass p j+p j →
      thresholdRule p j q ∈ finitePolicies ∧
      finiteMass p (thresholdRule p j q) = q ∧
      finiteA p m (thresholdRule p j q) = prefixA p m j + m j*(q-prefixMass p j) ∧
      ∀ π ∈ finitePolicies, finiteMass p π = q →
        finiteA p m π ≤ prefixA p m j + m j*(q-prefixMass p j)) ∧
    (∃ j q, prefixMass p j ≤ q ∧ q ≤ prefixMass p j+p j ∧
      IsBest finitePolicies
        (fun π => emptyFactor n (finiteMass p π) * finiteA p m π)
        (thresholdRule p j q)) ∧
    (if 0 < m ⟨0,hK⟩ then
      IsBest finitePolicies (finiteConditionalAverage p m) (printedAverageRule m) ∧
        finiteConditionalAverage p m (printedAverageRule m) = m ⟨0,hK⟩
    else IsBest finitePolicies (finiteConditionalAverage p m) (fun _ => 0)) := by
  refine ⟨?_, T2_threshold_maximum hK n p m hp hsum hm, ?_⟩
  · intro j q hlo hhi
    obtain ⟨ht, hmass, hvalue⟩ := T2_threshold_data p m hp j q hlo hhi
    refine ⟨ht, hmass, hvalue, ?_⟩
    intro π hπ hq
    simpa only [hq] using T2_frontier p m hp hm j π hπ
  · exact T2_population_conditional_rule p m hp ⟨0, hK⟩
      (fun i => hm (show (⟨0, hK⟩ : Fin K) ≤ i from Nat.zero_le i.val))

/-! ## P006-T24: event means and the normalized untreated law -/

private lemma T24_union_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (A1 A0 : Set Ω) (hA0 : MeasurableSet A0) (hdisj : Disjoint A1 A0)
    (ha : 0 < (μ (A1 ∪ A0)).toReal) (ha1 : 0 < (μ A1).toReal)
    (hq : (μ A1).toReal / (μ (A1 ∪ A0)).toReal < 1) :
    eventMean μ (A1 ∪ A0) f =
      ((μ A1).toReal / (μ (A1 ∪ A0)).toReal) * eventMean μ A1 f +
      (1 - (μ A1).toReal / (μ (A1 ∪ A0)).toReal) * eventMean μ A0 f := by
  have hmass : (μ (A1 ∪ A0)).toReal = (μ A1).toReal + (μ A0).toReal := by
    rw [measure_union hdisj hA0,
      ENNReal.toReal_add (measure_ne_top μ A1) (measure_ne_top μ A0)]
  have ha1lt : (μ A1).toReal < (μ (A1 ∪ A0)).toReal := by
    have h := (div_lt_iff₀ ha).mp hq
    simpa only [one_mul] using h
  have ha0 : 0 < (μ A0).toReal := by linarith
  have hcoeff : 1 - (μ A1).toReal / (μ (A1 ∪ A0)).toReal =
      (μ A0).toReal / (μ (A1 ∪ A0)).toReal := by
    rw [← div_self (ne_of_gt ha), ← sub_div]
    congr 1
    linarith
  unfold eventMean
  rw [setIntegral_union hdisj hA0 hf.integrableOn hf.integrableOn, hcoeff]
  field_simp [ne_of_gt ha, ne_of_gt ha1, ne_of_gt ha0] <;> ring

/-- Normalization and successive restriction, with all real denominators positive. -/
private lemma T24_normalized_restriction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A H : Set Ω) (hH : MeasurableSet H)
    (ha : 0 < (μ A).toReal) (hah : 0 < (μ (H ∩ A)).toReal) (f : Ω → ℝ) :
    let ν := (μ A)⁻¹ • μ.restrict A
    IsProbabilityMeasure ν ∧
      (∫ ω, f ω ∂ν) = eventMean μ A f ∧
      (ν H).toReal = (μ (H ∩ A)).toReal / (μ A).toReal ∧
      eventMean ν H f = eventMean μ (H ∩ A) f := by
  let ν := (μ A)⁻¹ • μ.restrict A
  change IsProbabilityMeasure ν ∧
    (∫ ω, f ω ∂ν) = eventMean μ A f ∧
    (ν H).toReal = (μ (H ∩ A)).toReal / (μ A).toReal ∧
    eventMean ν H f = eventMean μ (H ∩ A) f
  have hane : μ A ≠ 0 := ne_of_gt (ENNReal.toReal_pos_iff.mp ha).1
  have hprob : IsProbabilityMeasure ν := by
    constructor
    change ((μ A)⁻¹ • μ.restrict A) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hane (measure_ne_top μ A)
  have hwhole : (∫ ω, f ω ∂ν) = eventMean μ A f := by
    change (∫ ω, f ω ∂((μ A)⁻¹ • μ.restrict A)) = eventMean μ A f
    rw [integral_smul_measure]
    simp only [ENNReal.toReal_inv, smul_eq_mul, eventMean, div_eq_mul_inv, mul_comm]
  have hmass : (ν H).toReal = (μ (H ∩ A)).toReal / (μ A).toReal := by
    change (((μ A)⁻¹ • μ.restrict A) H).toReal =
      (μ (H ∩ A)).toReal / (μ A).toReal
    rw [Measure.smul_apply, Measure.restrict_apply hH, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    ring
  have hrestricted : (∫ ω in H, f ω ∂ν) =
      (μ A).toReal⁻¹ * (∫ ω in H ∩ A, f ω ∂μ) := by
    change (∫ ω, f ω ∂(((μ A)⁻¹ • μ.restrict A).restrict H)) =
      (μ A).toReal⁻¹ * (∫ ω in H ∩ A, f ω ∂μ)
    rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hH]
    simp only [ENNReal.toReal_inv, smul_eq_mul]
  refine ⟨hprob, hwhole, hmass, ?_⟩
  unfold eventMean
  rw [hmass, hrestricted]
  field_simp [ne_of_gt ha, ne_of_gt hah] <;> ring

theorem T24_corrected_identification_proof {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
    (Y0 Y1 : Ω → ℝ) (T R : Ω → Bool)
    (hm : Measurable Y0 ∧ Measurable Y1 ∧ Measurable T ∧ Measurable R)
    (hint : Integrable Y0 μ ∧ Integrable Y1 μ)
    (hI : IndepFun (fun ω => (Y0 ω,Y1 ω)) T μ)
    (hT : 0 < (μ {ω | T ω = false}).toReal)
    (hR : 0 < (μ {ω | T ω = false ∧ R ω = true}).toReal) :
    let A := {ω | T ω = false}
    let A1 := {ω | T ω = false ∧ R ω = true}
    let A0 := {ω | T ω = false ∧ R ω = false}
    let Y := fun ω => if T ω then Y1 ω else Y0 ω
    let q := (μ A1).toReal/(μ A).toReal
    (eventMean μ A1 Y0 = eventMean μ A Y0 →
      (∫ ω, Y0 ω ∂μ) = eventMean μ A1 Y) ∧
    (q < 1 →
      (∫ ω, Y0 ω ∂μ) = q*eventMean μ A1 Y0+(1-q)*eventMean μ A0 Y0 ∧
      (eventMean μ A1 Y0 = (∫ ω, Y0 ω ∂μ) ↔
        eventMean μ A1 Y0 = eventMean μ A0 Y0)) ∧
    (IndepFun Y0 R ((μ A)⁻¹ • μ.restrict A) →
      eventMean μ A1 Y0 = eventMean μ A Y0) := by
  letI : IsProbabilityMeasure μ := hμ
  let A := {ω | T ω = false}
  let A1 := {ω | T ω = false ∧ R ω = true}
  let A0 := {ω | T ω = false ∧ R ω = false}
  let Y := fun ω => if T ω then Y1 ω else Y0 ω
  let q := (μ A1).toReal / (μ A).toReal
  change (eventMean μ A1 Y0 = eventMean μ A Y0 →
      (∫ ω, Y0 ω ∂μ) = eventMean μ A1 Y) ∧
    (q < 1 →
      (∫ ω, Y0 ω ∂μ) = q * eventMean μ A1 Y0 + (1 - q) * eventMean μ A0 Y0 ∧
      (eventMean μ A1 Y0 = (∫ ω, Y0 ω ∂μ) ↔
        eventMean μ A1 Y0 = eventMean μ A0 Y0)) ∧
    (IndepFun Y0 R ((μ A)⁻¹ • μ.restrict A) →
      eventMean μ A1 Y0 = eventMean μ A Y0)
  have hA : MeasurableSet A := measurableSet_eq_fun hm.2.2.1 measurable_const
  have hH : MeasurableSet {ω | R ω = true} :=
    measurableSet_eq_fun hm.2.2.2 measurable_const
  have hA0 : MeasurableSet A0 :=
    hA.inter (measurableSet_eq_fun hm.2.2.2 measurable_const)
  have hpart : A1 ∪ A0 = A := by
    ext ω
    cases hr : R ω <;> simp [A1, A0, A, hr]
  have hdisj : Disjoint A1 A0 := by
    apply Set.disjoint_left.mpr
    intro ω h1 h0
    have hbad : (true : Bool) = false := h1.2.symm.trans h0.2
    cases hbad
  have hI0 : IndepFun Y0 T μ := by
    exact hI.comp measurable_fst measurable_id
  have hbase : eventMean μ A Y0 = (∫ ω, Y0 ω ∂μ) :=
    independent_untreated_mean μ hμ Y0 T hm.1 hm.2.2.1 hint.1 hI0 hT
  have hqpos : 0 < q := div_pos hR hT
  refine ⟨?_, ?_, ?_⟩
  · intro hrep
    exact T24_representative_identification μ hμ Y0 Y1 T R hm hint hI hT hR hrep
  · intro hq
    have hmix : (∫ ω, Y0 ω ∂μ) =
        q * eventMean μ A1 Y0 + (1 - q) * eventMean μ A0 Y0 := by
      have ha : 0 < (μ (A1 ∪ A0)).toReal := by simpa only [hpart] using hT
      have hq' : (μ A1).toReal / (μ (A1 ∪ A0)).toReal < 1 := by
        simpa only [hpart, q] using hq
      have hmix' := T24_union_mixture μ Y0 hint.1 A1 A0 hA0 hdisj ha hR hq'
      rw [hpart] at hmix'
      exact hbase.symm.trans hmix'
    refine ⟨hmix, ?_⟩
    rw [hmix]
    exact T24_mixture_mean_iff q (eventMean μ A1 Y0) (eventMean μ A0 Y0) ⟨hqpos, hq⟩
  · intro hind
    let H := {ω | R ω = true}
    let ν := (μ A)⁻¹ • μ.restrict A
    have hHA : H ∩ A = A1 := by
      ext ω
      simp only [H, A, A1, Set.mem_inter_iff, Set.mem_setOf_eq, and_comm]
    have hah : 0 < (μ (H ∩ A)).toReal := by rw [hHA]; exact hR
    obtain ⟨hνprob, hνint, hνmass, hνevent⟩ :=
      T24_normalized_restriction μ A H hH hT hah Y0
    have hpνH : 0 < (ν H).toReal := by
      rw [hνmass, hHA]
      exact div_pos hR hT
    have hane : μ A ≠ 0 := ne_of_gt (ENNReal.toReal_pos_iff.mp hT).1
    have hYν : Integrable Y0 ν :=
      hint.1.restrict.smul_measure (ENNReal.inv_ne_top.mpr hane)
    have hn : Measurable (fun b : Bool => !b) := measurable_of_finite _
    have hnot : Measurable (fun ω => !(R ω)) := hn.comp hm.2.2.2
    have hindnot : IndepFun Y0 (fun ω => !(R ω)) ν := by
      exact hind.comp measurable_id hn
    have hnotset : {ω | (!(R ω)) = false} = H := by
      ext ω
      cases hr : R ω <;> simp [H, hr]
    have hpnot : 0 < (ν {ω | (!(R ω)) = false}).toReal := by
      rw [hnotset]
      exact hpνH
    have hmean := independent_untreated_mean ν hνprob Y0 (fun ω => !(R ω))
      hm.1 hnot hYν hindnot hpnot
    rw [hnotset, hνevent, hνint, hHA] at hmean
    exact hmean

end

end AronowAudit.P006.Wave1
