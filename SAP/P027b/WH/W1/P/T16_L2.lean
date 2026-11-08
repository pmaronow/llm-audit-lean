import SAP.P027b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false


open MeasureTheory ProbabilityTheory

namespace SAP.P027b.WH.W1.P.T16_L2

lemma fairSign_mass_one : SAP.P027b.wholeFairSignLaw {1} = (1 / 2 : ENNReal) := by
  let p : unitInterval := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hp : unitInterval.toNNReal p = (1 / 2 : NNReal) := by
    apply Subtype.ext
    norm_num [unitInterval.toNNReal, p]
  have hh : ProbabilityTheory.bernoulliMeasure (1 : ℝ) (-1) p {1} =
      (1 / 2 : ENNReal) := by
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem
      (p := p) (measurableSet_singleton (1 : ℝ)) (by simp) (by norm_num)]
    rw [hp]
    norm_num
  simpa [SAP.P027b.wholeFairSignLaw, p] using hh

lemma fairSign_mass_neg_one : SAP.P027b.wholeFairSignLaw {-1} = (1 / 2 : ENNReal) := by
  let p : unitInterval := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hp : unitInterval.toNNReal p = (1 / 2 : NNReal) := by
    apply Subtype.ext
    norm_num [unitInterval.toNNReal, p]
  have hpsym : unitInterval.symm p = p := by
    apply Subtype.ext
    norm_num [unitInterval.coe_symm_eq, p]
  have hps : unitInterval.toNNReal (unitInterval.symm p) = (1 / 2 : NNReal) := by
    rw [hpsym, hp]
  have hh : ProbabilityTheory.bernoulliMeasure (1 : ℝ) (-1) p {-1} =
      (1 / 2 : ENNReal) := by
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem
      (p := p) (measurableSet_singleton (-1 : ℝ)) (by norm_num) (by simp)]
    rw [hps]
    norm_num
  simpa [SAP.P027b.wholeFairSignLaw, p] using hh

lemma cond_map_eq_map {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (X₀ : Ω → ℝ) (g : Ω → β) (s : ℝ)
    (hX₀ : Measurable X₀) (hg : Measurable g)
    (hInd : IndepFun g X₀ μ)
    (hpos : (μ {ω | X₀ ω = s}) ≠ 0) (htop : (μ {ω | X₀ ω = s}) ≠ ⊤) :
    (ProbabilityTheory.cond μ {ω | X₀ ω = s}).map g = μ.map g := by
  classical
  let A : Set Ω := {ω | X₀ ω = s}
  have hA : MeasurableSet A := by exact (hX₀ (measurableSet_singleton s))
  have hpre : X₀ ⁻¹' ({s} : Set ℝ) = A := by
    ext ω
    rfl
  have hfac (t : Set β) (ht : MeasurableSet t) :
      μ (A ∩ g ⁻¹' t) = μ (g ⁻¹' t) * μ A := by
    have hh := hInd.measure_inter_preimage_eq_mul t {s} ht (measurableSet_singleton s)
    rw [hpre] at hh
    simpa [Set.inter_comm, mul_comm] using hh
  ext t ht
  rw [Measure.map_apply hg ht, Measure.map_apply hg ht,
    ProbabilityTheory.cond_apply hA μ (g ⁻¹' t)]
  rw [hfac t ht]
  calc
    (μ A)⁻¹ * (μ (g ⁻¹' t) * μ A) = μ (g ⁻¹' t) * ((μ A)⁻¹ * μ A) := by ac_rfl
    _ = μ (g ⁻¹' t) := by rw [ENNReal.inv_mul_cancel hpos htop, mul_one]

end SAP.P027b.WH.W1.P.T16_L2

open SAP.P027b.WH.W1.P.T16_L2

theorem SAP.P027b.WH.W1.T16_L2_proof : SAP.P027b.WH.W1.T16_L2 := by
  classical
  intro Ξ _ μ hμ X hX s hs
  let A : Set Ξ := {ξ | X 0 ξ = s}
  let ν : Measure Ξ := ProbabilityTheory.cond μ A
  have hmass : μ A = (1 / 2 : ENNReal) := by
    have hfair : SAP.P027b.wholeFairSignLaw {s} = (1 / 2 : ENNReal) := by
      rcases hs with h | h
      · rw [h]
        exact fairSign_mass_one
      · rw [h]
        exact fairSign_mass_neg_one
    calc
      μ A = μ.map (X 0) {s} := by
        rw [Measure.map_apply (hX.1 0) (measurableSet_singleton s)]
        congr 1
      _ = SAP.P027b.wholeFairSignLaw {s} := by exact congrArg (fun m => m {s}) hX.2.1
      _ = (1 / 2 : ENNReal) := hfair
  have hpos : μ A ≠ 0 := by rw [hmass]; norm_num
  have htop : μ A ≠ ⊤ := by rw [hmass]; norm_num
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (hX.1 0 (measurableSet_singleton s))
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact ProbabilityTheory.cond_isProbabilityMeasure hpos
  have hI : iIndepFun X μ := hX.2.2.2.2
  have hInd01 : IndepFun (X 1) (X 0) μ := hI.indepFun (by decide)
  have hInd02 : IndepFun (X 2) (X 0) μ := hI.indepFun (by decide)
  have hInd12 : IndepFun (X 1) (X 2) μ := hI.indepFun (by decide)
  have hIndPair0 : IndepFun (fun ξ => (X 1 ξ, X 2 ξ)) (X 0) μ :=
    hI.indepFun_prodMk hX.1 1 2 0 (by decide) (by decide)
  have hmap1μ : ν.map (X 1) = μ.map (X 1) := by
    dsimp [ν]
    exact cond_map_eq_map μ (X 0) (X 1) s (hX.1 0) (hX.1 1) hInd01 hpos htop
  have hmap2μ : ν.map (X 2) = μ.map (X 2) := by
    dsimp [ν]
    exact cond_map_eq_map μ (X 0) (X 2) s (hX.1 0) (hX.1 2) hInd02 hpos htop
  have hmapPair : ν.map (fun ξ => (X 1 ξ, X 2 ξ)) =
      μ.map (fun ξ => (X 1 ξ, X 2 ξ)) := by
    dsimp [ν]
    exact cond_map_eq_map μ (X 0) (fun ξ => (X 1 ξ, X 2 ξ)) s (hX.1 0)
      ((hX.1 1).prodMk (hX.1 2)) hIndPair0 hpos htop
  have hν12 : IndepFun (X 1) (X 2) ν := by
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro B C hB hC
    have hrect : MeasurableSet (B ×ˢ C) := hB.prod hC
    calc
      ν ((X 1) ⁻¹' B ∩ (X 2) ⁻¹' C) = ν ((fun ξ => (X 1 ξ, X 2 ξ)) ⁻¹' (B ×ˢ C)) := by
        congr 1
      _ = (ν.map (fun ξ => (X 1 ξ, X 2 ξ))) (B ×ˢ C) := by
        rw [Measure.map_apply ((hX.1 1).prodMk (hX.1 2)) hrect]
      _ = (μ.map (fun ξ => (X 1 ξ, X 2 ξ))) (B ×ˢ C) := by rw [hmapPair]
      _ = μ ((fun ξ => (X 1 ξ, X 2 ξ)) ⁻¹' (B ×ˢ C)) := by
        rw [Measure.map_apply ((hX.1 1).prodMk (hX.1 2)) hrect]
      _ = μ ((X 1) ⁻¹' B ∩ (X 2) ⁻¹' C) := by
        congr 1
      _ = μ ((X 1) ⁻¹' B) * μ ((X 2) ⁻¹' C) :=
        hInd12.measure_inter_preimage_eq_mul B C hB hC
      _ = ν ((X 1) ⁻¹' B) * ν ((X 2) ⁻¹' C) := by
        have hm1 : ν ((X 1) ⁻¹' B) = μ ((X 1) ⁻¹' B) := by
          rw [← Measure.map_apply (hX.1 1) hB, hmap1μ,
            Measure.map_apply (hX.1 1) hB]
        have hm2 : ν ((X 2) ⁻¹' C) = μ ((X 2) ⁻¹' C) := by
          rw [← Measure.map_apply (hX.1 2) hC, hmap2μ,
            Measure.map_apply (hX.1 2) hC]
        rw [hm1, hm2]
  have hmap1 : ν.map (X 1) = gaussianReal 0 1 := hmap1μ.trans hX.2.2.1
  have hmap2 : ν.map (X 2) = gaussianReal 0 1 := hmap2μ.trans hX.2.2.2.1
  have hGaussLp : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal (μ := 0) (v := 1) 2
  have hLp1 : MemLp (X 1) 2 ν := by
    have hm := (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (hX.1 1).aemeasurable).mp (by rw [hmap1]; exact hGaussLp)
    simpa only [Function.comp_def, id_eq] using hm
  have hLp2 : MemLp (X 2) 2 ν := by
    have hm := (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (hX.1 2).aemeasurable).mp (by rw [hmap2]; exact hGaussLp)
    simpa only [Function.comp_def, id_eq] using hm
  have hX0ae : (X 0) =ᵐ[ν] fun _ => s := by
    filter_upwards [ProbabilityTheory.ae_cond_mem hA] with ξ hξ
    exact hξ
  have hYae : wholePairY X =ᵐ[ν] fun ξ => s / 2 + X 1 ξ := by
    filter_upwards [hX0ae] with ξ hξ
    simp only [wholePairY]
    rw [hξ]
    ring
  have hY'ae : wholePairY' X =ᵐ[ν] fun ξ => s / 2 + X 2 ξ := by
    filter_upwards [hX0ae] with ξ hξ
    simp only [wholePairY']
    rw [hξ]
    ring
  have hBase1 : MemLp (fun ξ => s / 2 + X 1 ξ) 2 ν :=
    (memLp_const (s / 2)).add hLp1
  have hBase2 : MemLp (fun ξ => s / 2 + X 2 ξ) 2 ν :=
    (memLp_const (s / 2)).add hLp2
  have hY : MemLp (wholePairY X) 2 ν := hBase1.ae_eq hYae.symm
  have hY' : MemLp (wholePairY' X) 2 ν := hBase2.ae_eq hY'ae.symm
  have hv1 : ProbabilityTheory.variance (X 1) ν = 1 := by
    rw [← ProbabilityTheory.variance_id_map (hX.1 1).aemeasurable, hmap1]
    simpa using (variance_id_gaussianReal (μ := 0) (v := 1))
  have hv2 : ProbabilityTheory.variance (X 2) ν = 1 := by
    rw [← ProbabilityTheory.variance_id_map (hX.1 2).aemeasurable, hmap2]
    simpa using (variance_id_gaussianReal (μ := 0) (v := 1))
  have hvY : ProbabilityTheory.variance (wholePairY X) ν = 1 := by
    rw [ProbabilityTheory.variance_congr hYae,
      ProbabilityTheory.variance_const_add (hLp1.aestronglyMeasurable) (s / 2), hv1]
  have hvY' : ProbabilityTheory.variance (wholePairY' X) ν = 1 := by
    rw [ProbabilityTheory.variance_congr hY'ae,
      ProbabilityTheory.variance_const_add (hLp2.aestronglyMeasurable) (s / 2), hv2]
  have hcov : ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) ν = 0 := by
    have hcovcongr :
        ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) ν =
          ProbabilityTheory.covariance (fun ξ => s / 2 + X 1 ξ)
            (fun ξ => s / 2 + X 2 ξ) ν := by
      rw [ProbabilityTheory.covariance_eq_sub hY hY',
        ProbabilityTheory.covariance_eq_sub hBase1 hBase2]
      simp only [integral_congr_ae hYae, integral_congr_ae hY'ae,
        integral_congr_ae (hYae.mul hY'ae)]
    calc
      ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) ν =
          ProbabilityTheory.covariance (fun ξ => s / 2 + X 1 ξ)
            (fun ξ => s / 2 + X 2 ξ) ν := hcovcongr
      _ = ProbabilityTheory.covariance (X 1) (X 2) ν := by
        rw [ProbabilityTheory.covariance_const_add_left (hLp1.integrable one_le_two),
          ProbabilityTheory.covariance_const_add_right (hLp2.integrable one_le_two)]
      _ = 0 := hν12.covariance_eq_zero hLp1 hLp2
  refine ⟨by simpa [A] using hmass, ?_⟩
  dsimp [ν]
  exact ⟨hν, hY, hY', hvY, hvY', hcov⟩

