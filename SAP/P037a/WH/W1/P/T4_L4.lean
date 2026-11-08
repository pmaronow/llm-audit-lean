import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T4_L4

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

private lemma gamma_lintegral (m : ℕ) :
    ∫⁻ t : ℝ, (Ioi (0 : ℝ)).indicator
      (fun t => ENNReal.ofReal (t^m * Real.exp (-t))) t ∂volume = m.factorial := by
  rw [lintegral_indicator measurableSet_Ioi]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [AronowAudit.P037.simplex_gamma_integral]
    norm_num
  · have hq : (-1 : ℝ) < (m:ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m)
    have hbase : IntegrableOn (fun t : ℝ => t^(m:ℝ) * Real.exp (-t)) (Ioi 0) := by
      simpa [Real.rpow_one, one_mul] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (m:ℝ)) (b := 1)
          hq (by norm_num) (by norm_num))
    apply hbase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.rpow_natCast]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg (le_of_lt ht) _) (le_of_lt (Real.exp_pos _))

theorem marginal_cone_density (n : ℕ) :
    Measure.map (fun x : Fin (n+2) → ℝ => fun i : Fin (n+1) => x i.castSucc)
      (SAP.P037a.exponentialConeDensityLaw n) =
      ((n+1).factorial : ℝ≥0∞) • (volume.restrict (SAP.P037a.openSimplex (n+1))) := by
  classical
  let e : (Fin (n+2) → ℝ) ≃ᵐ ℝ × (Fin (n+1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (Fin.last (n+1))
  let f : ℝ × (Fin (n+1) → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (z.1^(n+1) * Real.exp (-z.1))
  have he (x : Fin (n+2) → ℝ) : e x = (x (Fin.last (n+1)), fun i => x i.castSucc) := by
    ext <;> simp [e, MeasurableEquiv.piFinSuccAbove, Fin.succAbove_last, Fin.init]
  have hset (A : Set (Fin (n+1) → ℝ)) :
      e ⁻¹' (Ioi (0:ℝ) ×ˢ (SAP.P037a.openSimplex (n+1) ∩ A)) =
        SAP.P037a.simplexCone n ∩
          (fun x : Fin (n+2) → ℝ => fun i : Fin (n+1) => x i.castSucc) ⁻¹' A := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioi]
    rw [he]
    simp [SAP.P037a.simplexCone, SAP.P037a.openSimplex]
    tauto
  have hinit : Measurable (fun x : Fin (n+2) → ℝ => fun i : Fin (n+1) => x i.castSucc) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.castSucc
  have hcone : MeasurableSet (SAP.P037a.simplexCone n) := by
    have hopen : MeasurableSet (SAP.P037a.openSimplex (n+1)) := by
      have hpos : MeasurableSet {p : Fin (n+1) → ℝ | ∀ i, 0 < p i} := by
        convert MeasurableSet.iInter (fun i : Fin (n+1) =>
          measurableSet_lt (measurable_const : Measurable fun _ : (Fin (n+1) → ℝ) => (0:ℝ))
            (measurable_pi_apply i)) using 1
        ext p
        simp
      have hsum : MeasurableSet {p : Fin (n+1) → ℝ | ∑ i, p i < 1} :=
        measurableSet_lt (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
          (measurable_const : Measurable fun _ : (Fin (n+1) → ℝ) => (1:ℝ))
      unfold SAP.P037a.openSimplex
      convert hpos.inter hsum using 1 <;> ext p <;> simp
    unfold SAP.P037a.simplexCone
    exact (hopen.preimage hinit).inter (measurableSet_lt
      (measurable_const : Measurable fun _ : (Fin (n+2) → ℝ) => (0:ℝ))
      (measurable_pi_apply (Fin.last (n+1))) )
  have hsimplex : MeasurableSet (SAP.P037a.openSimplex (n+1)) := by
    have hpos : MeasurableSet {p : Fin (n+1) → ℝ | ∀ i, 0 < p i} := by
      convert MeasurableSet.iInter (fun i : Fin (n+1) =>
        measurableSet_lt (measurable_const : Measurable fun _ : (Fin (n+1) → ℝ) => (0:ℝ))
          (measurable_pi_apply i)) using 1
      ext p
      simp
    have hsum : MeasurableSet {p : Fin (n+1) → ℝ | ∑ i, p i < 1} :=
      measurableSet_lt (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
        (measurable_const : Measurable fun _ : (Fin (n+1) → ℝ) => (1:ℝ))
    unfold SAP.P037a.openSimplex
    convert hpos.inter hsum using 1 <;> ext p <;> simp
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hinit hA]
  have hpreA : MeasurableSet ((fun x : Fin (n+2) → ℝ => fun i : Fin (n+1) => x i.castSucc) ⁻¹' A) :=
    hA.preimage hinit
  rw [SAP.P037a.exponentialConeDensityLaw, withDensity_apply _ hpreA]
  have hp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (Fin.last (n+1))
  have hden (x : Fin (n+2) → ℝ) :
      ENNReal.ofReal (x (Fin.last (n+1))^(n+1) * Real.exp (-x (Fin.last (n+1)))) = f (e x) := by
    simp [f, he]
  have hmeasf : Measurable f := by fun_prop
  have hmeasRestrict : AEMeasurable f
      ((volume.prod volume).restrict
        (Ioi (0:ℝ) ×ˢ (SAP.P037a.openSimplex (n+1) ∩ A))) := hmeasf.aemeasurable
  calc
    (∫⁻ x in (fun x : Fin (n+2) → ℝ => fun i : Fin (n+1) => x i.castSucc) ⁻¹' A,
        ENNReal.ofReal (x (Fin.last (n+1))^(n+1) * Real.exp (-x (Fin.last (n+1))))
        ∂volume.restrict (SAP.P037a.simplexCone n))
        = ∫⁻ x in SAP.P037a.simplexCone n ∩
            (fun x : Fin (n+2) → ℝ => fun i : Fin (n+1) => x i.castSucc) ⁻¹' A,
          ENNReal.ofReal (x (Fin.last (n+1))^(n+1) * Real.exp (-x (Fin.last (n+1)))) ∂volume := by
            rw [Measure.restrict_restrict hpreA]
            congr 1
            rw [Set.inter_comm]
    _ = ∫⁻ z in Ioi (0:ℝ) ×ˢ (SAP.P037a.openSimplex (n+1) ∩ A), f z ∂volume.prod volume := by
      simp_rw [hden, ← hset]
      exact hp.setLIntegral_comp_preimage_emb e.measurableEmbedding f
        (Ioi (0:ℝ) ×ˢ (SAP.P037a.openSimplex (n+1) ∩ A))
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ p in SAP.P037a.openSimplex (n+1) ∩ A,
          f (t,p) ∂volume ∂volume := by
      exact setLIntegral_prod _ hmeasRestrict
    _ = ((n+1).factorial : ℝ≥0∞) * volume (SAP.P037a.openSimplex (n+1) ∩ A) := by
      simp only [f, setLIntegral_const]
      rw [lintegral_mul_const (volume (SAP.P037a.openSimplex (n+1) ∩ A)) (by fun_prop)]
      rw [← lintegral_indicator measurableSet_Ioi, gamma_lintegral]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hsimplex]
  rw [Measure.restrict_apply hA, Set.inter_comm]

end SAP.P037a.WH.W1.P.T4_L4

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

theorem SAP.P037a.WH.W1.T4_L4_proof : SAP.P037a.WH.W1.T4_L4 := by
  intro hjoint n
  classical
  let μ : Measure (Fin (n+2) → ℝ) := SAP.P037a.exponentialProduct n
  let q : (Fin (n+2) → ℝ) → (Fin (n+1) → ℝ) :=
    fun x i => x i.castSucc
  let a : (Fin (n+1) → ℝ) → (Fin (n+2) → ℝ) := SAP.P037a.appendSimplex (n+1)
  let w : (Fin (n+2) → ℝ) → (Fin (n+2) → ℝ) := SAP.P037a.normalizedWeights
  have hExpProb : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num : (0:ℝ) < 1)
  letI := hExpProb
  have hμProb : IsProbabilityMeasure μ := by
    dsimp [μ, SAP.P037a.exponentialProduct]
    infer_instance
  have hExpPos : ∀ᵐ x : ℝ ∂ProbabilityTheory.expMeasure 1, 0 < x := by
    haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) := hExpProb
    rw [ae_iff]
    simp only [not_lt]
    change ProbabilityTheory.expMeasure 1 (Iic 0) = 0
    rw [← ProbabilityTheory.ofReal_cdf,
      ProbabilityTheory.cdf_expMeasure_eq (by norm_num : (0:ℝ) < 1)]
    norm_num
  have hpos : ∀ᵐ x ∂μ, ∀ i : Fin (n+2), 0 < x i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
    rw [show Measure.map (fun x : Fin (n+2) → ℝ => x i) μ =
      ProbabilityTheory.expMeasure 1 from by
        dsimp [μ, SAP.P037a.exponentialProduct]
        exact (measurePreserving_eval
          (fun _ : Fin (n+2) => ProbabilityTheory.expMeasure 1) i).map_eq]
    exact hExpPos
  have htotal (x : Fin (n+2) → ℝ) (hx : ∀ i, 0 < x i) : 0 < ∑ i, x i :=
    Finset.sum_pos (fun i _ => hx i) Finset.univ_nonempty
  have hnorm_append (x : Fin (n+2) → ℝ) (hx : ∀ i, 0 < x i) :
      w x = a (fun i : Fin (n+1) =>
        (SAP.P037a.simplexConeInverse n x) i.castSucc) := by
    funext i
    unfold w a SAP.P037a.normalizedWeights SAP.P037a.appendSimplex
    by_cases hi : i.val < n+1
    · let j : Fin (n+1) := ⟨i.val, hi⟩
      have hij : j.castSucc = i := by
        apply Fin.ext
        rfl
      rw [dif_pos hi]
      have hxi : x i = x j.castSucc := congrArg x hij.symm
      change x i / (∑ k, x k) = SAP.P037a.simplexConeInverse n x j.castSucc
      rw [hxi]
      simp [SAP.P037a.simplexConeInverse]
    · have hi' : i = Fin.last (n+1) := by
        apply Fin.ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) (Nat.le_of_not_gt hi)
      subst i
      simp only [Fin.val_last, Nat.lt_irrefl, dite_false, SAP.P037a.simplexConeInverse,
        Fin.snoc_castSucc]
      have ht : (∑ i, x i) ≠ 0 := ne_of_gt (htotal x hx)
      rw [← Finset.sum_div]
      change x (Fin.last (n+1)) / (∑ i : Fin (n+2), x i) =
        1 - (∑ j : Fin (n+1), x j.castSucc) / (∑ i : Fin (n+2), x i)
      field_simp [ht]
      have hs := Fin.sum_univ_castSucc x
      linarith
  have hq : Measurable q := by
    dsimp [q]
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.castSucc
  have ha : Measurable a := by
    dsimp [a]
    apply measurable_pi_lambda
    intro i
    unfold SAP.P037a.appendSimplex
    split_ifs with hi
    · exact measurable_pi_apply (⟨i.val, hi⟩ : Fin (n+1))
    · exact measurable_const.sub
        (Finset.measurable_sum Finset.univ fun j _ => measurable_pi_apply j)
  have hw : Measurable w := by
    dsimp [w, SAP.P037a.normalizedWeights]
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).div
      (Finset.measurable_sum Finset.univ fun j _ => measurable_pi_apply j)
  have hinv : Measurable (SAP.P037a.simplexConeInverse n) := by
    unfold SAP.P037a.simplexConeInverse
    fun_prop
  have hcomp : w =ᵐ[μ] fun x => a (q (SAP.P037a.simplexConeInverse n x)) := by
    filter_upwards [hpos] with x hx
    exact hnorm_append x hx
  have hweight : SAP.P037a.exponentialWeightLaw n =
      Measure.map a (Measure.map q (Measure.map (SAP.P037a.simplexConeInverse n) μ)) := by
    change Measure.map w μ = _
    calc
      Measure.map w μ = Measure.map (fun x => a (q (SAP.P037a.simplexConeInverse n x))) μ :=
        Measure.map_congr hcomp
      _ = Measure.map a (Measure.map q (Measure.map (SAP.P037a.simplexConeInverse n) μ)) := by
        rw [Measure.map_map ha hq, Measure.map_map (ha.comp hq) hinv]
        congr 1
  have hsimplex : SAP.P037a.exponentialWeightLaw n = SAP.P037a.simplexLaw (n+1) := by
    rw [hweight, Measure.map_map ha hq, hjoint n, ← Measure.map_map ha hq,
      SAP.P037a.WH.W1.P.T4_L4.marginal_cone_density]
    rfl
  have hweightProb : IsProbabilityMeasure (SAP.P037a.exponentialWeightLaw n) := by
    change IsProbabilityMeasure (Measure.map w μ)
    exact (Measure.isProbabilityMeasure_map_iff hw.aemeasurable).mpr hμProb
  have hsimplexProb : IsProbabilityMeasure (SAP.P037a.simplexLaw (n+1)) := by
    rw [← hsimplex]
    exact hweightProb
  have hweightSupport : ∀ᵐ x ∂μ,
      (∀ i, 0 < w x i) ∧ (∑ i, w x i = 1) := by
    filter_upwards [hpos] with x hx
    have ht := htotal x hx
    constructor
    · intro i
      dsimp [w, SAP.P037a.normalizedWeights]
      exact div_pos (hx i) ht
    · dsimp [w, SAP.P037a.normalizedWeights]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt ht)
  have hsupportSet : MeasurableSet {p : Fin (n+2) → ℝ |
      (∀ i, 0 < p i) ∧ ∑ i, p i = 1} := by
    have hp : MeasurableSet {p : Fin (n+2) → ℝ | ∀ i, 0 < p i} := by
      convert MeasurableSet.iInter (fun i : Fin (n+2) =>
        measurableSet_lt (measurable_const : Measurable fun _ : (Fin (n+2) → ℝ) => (0:ℝ))
          (measurable_pi_apply i)) using 1
      ext p
      simp
    have hs : MeasurableSet {p : Fin (n+2) → ℝ | ∑ i, p i = 1} :=
      measurableSet_eq_fun
        (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
        measurable_const
    convert hp.inter hs using 1 <;> ext p <;> simp
  have hmapSupport : ∀ᵐ p ∂SAP.P037a.exponentialWeightLaw n,
      (∀ i, 0 < p i) ∧ ∑ i, p i = 1 := by
    rw [SAP.P037a.exponentialWeightLaw]
    exact (ae_map_iff hw.aemeasurable hsupportSet).2 hweightSupport
  refine ⟨hsimplex, hsimplexProb, ?_⟩
  rw [← hsimplex]
  exact hmapSupport
