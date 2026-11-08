import SAP.P037a.Defs.WholeW2
import AronowAudit.P037.P037_Bootstrap
import AronowAudit.P037.Wave1.Gap.GP037B4b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

theorem measurable_headW2 (m : ℕ) : Measurable (headCoordinatesW2 m) := by
  exact Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem measurable_appendW2 (m : ℕ) : Measurable (appendSimplex m) := by
  apply Measurable.of_eval
  intro i
  unfold appendSimplex
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

theorem measurable_normalizedW2 (n : ℕ) :
    Measurable (@normalizedWeights n) := by
  exact Measurable.of_eval fun i => (measurable_pi_apply i).div
    (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

theorem measurable_forwardW2 (m : ℕ) : Measurable (forwardNormalizationW2 m) := by
  apply Measurable.of_eval
  intro i
  unfold forwardNormalizationW2 Fin.snoc
  split_ifs
  · exact (measurable_pi_apply _).comp
      ((measurable_headW2 m).comp (measurable_normalizedW2 (m+1)))
  · exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

theorem measurable_openSimplexW2 (m : ℕ) : MeasurableSet (openSimplex m) := by
  change MeasurableSet ({p : Fin m → ℝ | ∀ i, 0 < p i} ∩ {p | ∑ i, p i < 1})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_pi_apply i)
  · exact measurableSet_lt (Finset.measurable_sum _
      (fun j _ => measurable_pi_apply j)) measurable_const

@[simp] theorem append_castSuccW2 (m : ℕ) (q : Fin m → ℝ) (i : Fin m) :
    appendSimplex m q i.castSucc = q i := by
  simp [appendSimplex, i.isLt]

@[simp] theorem append_lastW2 (m : ℕ) (q : Fin m → ℝ) :
    appendSimplex m q (Fin.last m) = 1 - ∑ i, q i := by
  simp [appendSimplex]

@[simp] theorem sum_appendW2 (m : ℕ) (q : Fin m → ℝ) :
    ∑ i, appendSimplex m q i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp

theorem positive_appendW2 (m : ℕ) (q : Fin m → ℝ) (hq : q ∈ openSimplex m) :
    ∀ i, 0 < appendSimplex m q i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using sub_pos.mpr hq.2
  · simpa using hq.1 j

theorem positive_totalW2 (m : ℕ) (e : Fin (m+1) → ℝ)
    (he : e ∈ positiveOrthantW2 (m+1)) : 0 < ∑ i, e i :=
  Finset.sum_pos (fun i _ => he i) Finset.univ_nonempty

theorem normalized_sumW2 {n : ℕ} (e : Fin n → ℝ) (he : (∑ i, e i) ≠ 0) :
    ∑ i, normalizedWeights e i = 1 := by
  simp only [normalizedWeights, ← Finset.sum_div]
  exact div_self he

theorem normalized_factsW2 (m : ℕ) (e : Fin (m+1) → ℝ)
    (he : e ∈ positiveOrthantW2 (m+1)) :
    0 < ∑ i, e i ∧ (∀ i, 0 < normalizedWeights e i) ∧
      ∑ i, normalizedWeights e i = 1 := by
  have hs := positive_totalW2 m e he
  exact ⟨hs, fun i => div_pos (he i) hs, normalized_sumW2 e hs.ne'⟩

theorem append_headW2 (m : ℕ) (p : Fin (m+1) → ℝ) (hp : ∑ i, p i = 1) :
    appendSimplex m (headCoordinatesW2 m p) = p := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h := hp
    rw [Fin.sum_univ_castSucc] at h
    simp only [append_lastW2, headCoordinatesW2]
    linarith
  · simp [headCoordinatesW2]

@[simp] theorem head_forwardW2 (m : ℕ) (e : Fin (m+1) → ℝ) :
    headCoordinatesW2 m (forwardNormalizationW2 m e) =
      headCoordinatesW2 m (normalizedWeights e) := by
  funext i
  simp [headCoordinatesW2, forwardNormalizationW2]

@[simp] theorem last_forwardW2 (m : ℕ) (e : Fin (m+1) → ℝ) :
    forwardNormalizationW2 m e (Fin.last m) = ∑ i, e i := by
  simp [forwardNormalizationW2]

theorem geometry_proofW2 : normalizationGeometryW2 := by
  intro m
  constructor
  · intro e he
    have hs := positive_totalW2 m e he
    have hn := normalized_factsW2 m e he
    have ha := append_headW2 m (normalizedWeights e) hn.2.2
    constructor
    · change headCoordinatesW2 m (forwardNormalizationW2 m e) ∈ openSimplex m ∧ _
      rw [head_forwardW2, last_forwardW2]
      refine ⟨⟨fun i => hn.2.1 i.castSucc, ?_⟩, hs⟩
      have hsum := hn.2.2
      rw [Fin.sum_univ_castSucc] at hsum
      have hlast := hn.2.1 (Fin.last m)
      change ∑ i : Fin m, normalizedWeights e i.castSucc < 1
      linarith
    · funext i
      change forwardNormalizationW2 m e (Fin.last m) *
        appendSimplex m (headCoordinatesW2 m (forwardNormalizationW2 m e)) i = e i
      rw [last_forwardW2, head_forwardW2, ha]
      change (∑ j, e j) * (e i / ∑ j, e j) = e i
      field_simp
  · intro z hz
    have ht := hz.2
    have hq := positive_appendW2 m _ hz.1
    have hsum : ∑ i, inverseNormalizationW2 m z i = z (Fin.last m) := by
      simp only [inverseNormalizationW2, ← Finset.mul_sum, sum_appendW2, mul_one]
    constructor
    · exact fun i => mul_pos ht (hq i)
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [last_forwardW2, hsum]
      · simp only [forwardNormalizationW2, Fin.snoc_castSucc, headCoordinatesW2,
          normalizedWeights]
        rw [hsum]
        simp only [inverseNormalizationW2, append_castSuccW2, headCoordinatesW2]
        exact mul_div_cancel_left₀ _ ht.ne'

theorem simplex_certificationW2 (hvol : simplexVolumeFactsW2) : simplexCertificationW2 := by
  intro k
  let ν : Measure (Fin (k+1) → ℝ) :=
    ((k+1).factorial : ℝ≥0∞) • volume.restrict (openSimplex (k+1))
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, (hvol (k+1)).2]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Nat.factorial_ne_zero (k+1))
      (by simp)
  constructor
  · exact (Measure.isProbabilityMeasure_map_iff (measurable_appendW2 (k+1)).aemeasurable).2 hν
  · change ∀ᵐ p ∂Measure.map (appendSimplex (k+1)) ν, _
    apply (ae_map_iff (measurable_appendW2 (k+1)).aemeasurable ?_).2
    · have hq : ∀ᵐ q ∂ν, q ∈ openSimplex (k+1) := by
        change ν (openSimplex (k+1))ᶜ = 0
        simp [ν, Measure.smul_apply, Measure.restrict_apply
          (measurable_openSimplexW2 (k+1)).compl]
      filter_upwards [hq] with q hq
      exact ⟨positive_appendW2 (k+1) q hq, sum_appendW2 (k+1) q⟩
    · have hpos : MeasurableSet {p : Fin (k+2) → ℝ | ∀ i, 0 < p i} := by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i =>
          measurableSet_lt measurable_const (measurable_pi_apply i)
      exact hpos.inter (measurableSet_eq_fun
          (show Measurable (fun p : Fin (k+2) → ℝ => ∑ i, p i) from
            Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

/-- Independence and the marginal laws identify the complete finite product law. -/
theorem joint_inputW2 {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Fin n → Ω → ℝ) (ν : Measure ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hl : ∀ i, Measure.map (X i) μ = ν) :
    Measure.map (fun ω i => X i ω) μ = Measure.pi (fun _ : Fin n => ν) := by
  rw [hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  simp_rw [hl]

theorem uniform_input_positiveW2 (n : ℕ) :
    ∀ᵐ u ∂uniformInputW2 n, u ∈ positiveOrthantW2 n := by
  have : IsProbabilityMeasure uniformDraw := ⟨by
    norm_num [uniformDraw, Real.volume_Ioo]⟩
  have h : ∀ i : Fin n, ∀ᵐ u ∂uniformInputW2 n, 0 < u i := by
    intro i
    apply Measure.tendsto_eval_ae_ae
    exact (ae_restrict_mem measurableSet_Ioo).mono (fun _ hx => hx.1)
  simpa only [positiveOrthantW2, Set.mem_ofPred_eq, ae_all_iff] using h

theorem scaling_proofW2 : weightScaling :=
  AronowAudit.P037.weighted_least_squares_scale

/-- The positive gamma-integral value also excludes the undefined-integral convention. -/
theorem gamma_integrableW2 (m : ℕ) :
    IntegrableOn (fun t : ℝ => t^m * Real.exp (-t)) (Ioi 0) := by
  by_contra h
  have hg := AronowAudit.P037.simplex_gamma_integral m
  rw [integral_undef h] at hg
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  linarith

theorem normalization_refit_proofW2 : normalizationRefit := by
  intro K _ _ n w X y hw hX
  have hs := positive_totalW2 (n+1) w hw
  have h := (scaling_proofW2 w X y 0 hw hX (1 / ∑ i, w i) (one_div_pos.mpr hs)).1
  have heq : normalizedWeights w = fun i => (1 / ∑ j, w j) * w i := by
    funext i
    simp [normalizedWeights, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact h

end SAP.P037a.WH.W2
