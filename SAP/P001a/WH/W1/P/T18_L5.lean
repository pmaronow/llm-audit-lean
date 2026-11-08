import SAP.P001a.WH.W1.Leaves
import AronowAudit.P001.Wave1.Gap.DecideB
import AronowAudit.P001.Wave1.Gap.GLP0011B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L5

lemma normalVectorLaw_mulVec {p : ℕ} (A S : Matrix (Fin p) (Fin p) ℝ)
    (hS : S.PosSemidef) :
    (SAP.P001a.normalVectorLaw S).map (fun z => A.mulVec z) =
      SAP.P001a.normalVectorLaw (A * S * A.transpose) := by
  let c : EuclideanSpace ℝ (Fin p) → Fin p → ℝ := fun z j => z j
  let f : (Fin p → ℝ) → (Fin p → ℝ) := fun z => A.mulVec z
  have hcomp : f ∘ c = c ∘ Matrix.toEuclideanCLM (𝕜 := ℝ) A := by
    funext z j
    dsimp [f, c]
  unfold SAP.P001a.normalVectorLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [hcomp]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM (A := A) (μ := 0) hS]
  simp [c, Matrix.conjTranspose_eq_transpose_of_trivial]

lemma rankFailure_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℕ} (q : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hm : ∀ n, Measurable (q n))
    (hr : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, IsUnit (q n ω).det) :
    Tendsto (fun n => SAP.P001a.prob μ {ω | ¬ IsUnit (q n ω).det}) atTop (nhds 0) := by
  let B : ℕ → Set Ω := fun n => {ω | ¬ IsUnit (q n ω).det}
  let U : ℕ → Set Ω := fun N => {ω | ∃ n, N ≤ n ∧ ω ∈ B n}
  have hb (n : ℕ) : MeasurableSet (B n) := by
    have hd : Measurable (fun ω => (q n ω).det) :=
      continuous_id.matrix_det.measurable.comp (hm n)
    have heq : B n = {ω | (q n ω).det = 0} := by
      ext ω
      simp [B, isUnit_iff_ne_zero]
    rw [heq]
    exact measurableSet_eq_fun hd measurable_const
  have hu (N : ℕ) : MeasurableSet (U N) := by
    have heq : U N = ⋃ n, if h : N ≤ n then B n else ∅ := by
      ext ω
      simp [U]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    split_ifs <;> simp [hb]
  have hanti : Antitone U := by
    intro N M hNM ω hω
    rcases hω with ⟨n, hn, hbad⟩
    exact ⟨n, le_trans hNM hn, hbad⟩
  have hnull : μ (⋂ N, U N) = 0 := by
    have hae : ∀ᵐ ω ∂μ, ω ∉ ⋂ N, U N := by
      filter_upwards [hr] with ω hω
      intro hall
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hω
      have hUN := Set.mem_iInter.mp hall N
      obtain ⟨n, hnN, hbad⟩ := hUN
      exact hbad (hN n hnN)
    have hz := (MeasureTheory.ae_iff (p := fun ω => ω ∉ ⋂ N, U N)).1 hae
    have hset : {ω : Ω | ¬ ω ∉ ⋂ N, U N} = ⋂ N, U N := by ext ω; simp
    rw [hset] at hz
    exact hz
  have ht : Tendsto (fun N => μ (U N)) atTop (nhds 0) := by
    have ht' := MeasureTheory.tendsto_measure_iInter_atTop
      (fun N => (hu N).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    simpa [hnull, Function.comp_def] using ht'
  have hpr : Tendsto (fun N => SAP.P001a.prob μ (U N)) atTop (nhds 0) := by
    change Tendsto (fun N => (μ (U N)).toReal) atTop (nhds 0)
    exact (ENNReal.tendsto_toReal_zero_iff (fun N => measure_ne_top μ _)).2 ht
  have hle (n : ℕ) : SAP.P001a.prob μ (B n) ≤ SAP.P001a.prob μ (U n) := by
    change μ.real (B n) ≤ μ.real (U n)
    exact measureReal_mono (by
      intro ω hω
      exact ⟨n, le_rfl, hω⟩) (measure_ne_top μ _)
  have hnonneg : ∀ n, 0 ≤ SAP.P001a.prob μ (B n) := by
    intro n
    exact ENNReal.toReal_nonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpr
    (fun n => hnonneg n) hle

lemma sampleGram_eq {Ω : Type*} {p n : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (ω : Ω) (hn : 0 < n) :
    (SAP.P001a.wholeRows Z n ω).transpose * SAP.P001a.wholeRows Z n ω =
      (n : ℝ) • SAP.P001a.wholeEmpiricalQ Z n ω := by
  ext j k
  change (∑ i : Fin n, Z i ω j * Z i ω k) =
    (n : ℝ) * ((∑ i ∈ Finset.range n, Z i ω j * Z i ω k) / (n : ℝ))
  rw [Fin.sum_univ_eq_sum_range (fun i => Z i ω j * Z i ω k) n]
  field_simp

lemma score_transpose_eq {Ω : Type*} {p n : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (ω : Ω) :
    (SAP.P001a.wholeRows Z n ω).transpose.mulVec
      (fun i : Fin n => SAP.P001a.wholeResidual (Z i) (D i) b ω) =
      ∑ i ∈ Finset.range n, SAP.P001a.wholeResidual (Z i) (D i) b ω • Z i ω := by
  ext j
  simp only [SAP.P001a.wholeRows, Matrix.mulVec, Matrix.transpose_apply,
    Pi.smul_apply, Finset.sum_apply, dotProduct]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => Z i ω j * SAP.P001a.wholeResidual (Z i) (D i) b ω) n]
  apply Finset.sum_congr rfl
  intro i hi
  simp [SAP.P001a.wholeResidual, dotProduct]
  ring

lemma gram_unit_of_sample {Ω : Type*} {p n : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (ω : Ω) (hn : 0 < n)
    (hQ : IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det) :
    IsUnit ((SAP.P001a.wholeRows Z n ω).transpose * SAP.P001a.wholeRows Z n ω).det := by
  have hEq := sampleGram_eq Z ω hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hEq, Matrix.det_smul]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hnR) hQ.ne_zero)

lemma inv_sampleGram {Ω : Type*} {p n : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (ω : Ω) (hn : 0 < n)
    (hQ : IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det) :
    ((SAP.P001a.wholeRows Z n ω).transpose * SAP.P001a.wholeRows Z n ω)⁻¹ =
      (n : ℝ)⁻¹ • (SAP.P001a.wholeEmpiricalQ Z n ω)⁻¹ := by
  letI : Invertible (n : ℝ) := invertibleOfNonzero (by exact_mod_cast hn.ne')
  rw [sampleGram_eq Z ω hn,
    Matrix.inv_smul (SAP.P001a.wholeEmpiricalQ Z n ω) (n : ℝ) hQ]
  simp

lemma ols_err {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (b : Fin p → ℝ) (hG : IsUnit (X.transpose * X).det) :
    SAP.P001a.olsCoef X y - b =
      ((X.transpose * X)⁻¹).mulVec (X.transpose.mulVec (y - X.mulVec b)) := by
  let G := X.transpose * X
  have hRight : X.transpose.mulVec (y - X.mulVec b) =
      X.transpose.mulVec y - G.mulVec b := by
    simp [G, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hmul : G⁻¹.mulVec (G.mulVec b) = b := by
    have hmatrix := Matrix.nonsing_inv_mul G hG
    have hvec := congrArg (fun M : Matrix (Fin p) (Fin p) ℝ => M.mulVec b) hmatrix
    simpa only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] using hvec
  change G⁻¹.mulVec (X.transpose.mulVec y) - b =
    G⁻¹.mulVec (X.transpose.mulVec (y - X.mulVec b))
  rw [hRight, Matrix.mulVec_sub, hmul]

lemma rootError_eq_proxy {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω)
    (hn : 0 < n) (hQ : IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det) :
    SAP.P001a.wholeRootError Z D b n ω =
      (SAP.P001a.wholeEmpiricalQ Z n ω)⁻¹.mulVec (SAP.P001a.wholeScoreSum Z D b n ω) := by
  let X := SAP.P001a.wholeRows Z n ω
  let Q := SAP.P001a.wholeEmpiricalQ Z n ω
  have hG : IsUnit (X.transpose * X).det := by
    simpa [X] using gram_unit_of_sample Z ω hn hQ
  have hinv : (X.transpose * X)⁻¹ = (n : ℝ)⁻¹ • Q⁻¹ := by
    simpa [X, Q] using inv_sampleGram Z ω hn hQ
  have hscore : SAP.P001a.wholeScoreSum Z D b n ω =
      (Real.sqrt n)⁻¹ • X.transpose.mulVec
        (fun i : Fin n => SAP.P001a.wholeResidual (Z i) (D i) b ω) := by
    dsimp [SAP.P001a.wholeScoreSum, X]
    rw [← score_transpose_eq Z D b ω]
  have hy : (fun i : Fin n => D i ω) - X.mulVec b =
      (fun i : Fin n => SAP.P001a.wholeResidual (Z i) (D i) b ω) := by
    funext i
    simp [X, SAP.P001a.wholeRows, SAP.P001a.wholeResidual, Matrix.mulVec, dotProduct]
  have hsqrt : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hs0 : Real.sqrt (n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    field_simp [hn0, hs0]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  change Real.sqrt n • (SAP.P001a.olsCoef X (fun i => D i ω) - b) =
    Q⁻¹.mulVec (SAP.P001a.wholeScoreSum Z D b n ω)
  rw [ols_err X (fun i => D i ω) b hG, hy, hinv, hscore,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, hsqrt]

lemma weakLimit_to_tendstoInDistribution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E)
    (ν : Measure E) [IsProbabilityMeasure ν] (hm : ∀ n, Measurable (X n))
    (h : SAP.P001a.WeakLimit μ X ν) :
    TendstoInDistribution X atTop id (fun _ => μ) ν := by
  refine ⟨fun n => (hm n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).2
  intro f
  have hb : ∃ C : ℝ, ∀ x : E, |f x| ≤ C :=
    ⟨‖f‖, fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
  have hl := h f f.continuous hb
  have hmap (n : ℕ) : ∫ x, f x ∂(μ.map (X n)) = ∫ ω, f (X n ω) ∂μ :=
    integral_map (hm n).aemeasurable f.continuous.aestronglyMeasurable
  convert hl using 1
  · funext n
    simpa only [ProbabilityMeasure.coe_mk, SAP.P001a.mean] using hmap n
  · simp only [ProbabilityMeasure.coe_mk, SAP.P001a.mean, Measure.map_id]

lemma tight_of_tendstoInDistribution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [NormedAddCommGroup E] [SecondCountableTopology E]
    [BorelSpace E] [TopologicalSpace.IsCompletelyPseudoMetrizableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E)
    (ν : Measure E) [IsProbabilityMeasure ν] (hT : ∀ n, AEMeasurable (T n) μ)
    (h : TendstoInDistribution T atTop id (fun _ => μ) ν) : SAP.P001a.WholeTight μ T := by
  intro η hη
  have htail : Tendsto (fun r : ℝ => ν {x | r < ‖x‖}) atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using (tendsto_measure_norm_gt_of_isTightMeasureSet
      (isTightMeasureSet_singleton (μ := ν)))
  have hevent : ∀ᶠ r : ℝ in atTop, ν {x | r < ‖x‖} < ENNReal.ofReal η :=
    htail.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨r, hrpos, hrsmall⟩ := (eventually_gt_atTop (0 : ℝ)).and hevent |>.exists
  let C := 2 * r
  have hC : 0 < C := by dsimp [C]; positivity
  let F : Set E := {x | C ≤ ‖x‖}
  have hF : IsClosed F := isClosed_le continuous_const continuous_norm
  have hνF : ν F < ENNReal.ofReal η := by
    apply lt_of_le_of_lt (measure_mono ?_) hrsmall
    intro x hx
    dsimp [F, C] at hx ⊢
    linarith [hx]
  let ms : ℕ → ProbabilityMeasure E := fun n => ⟨μ.map (T n), inferInstance⟩
  have hconv : Tendsto ms atTop (𝓝 ⟨ν, inferInstance⟩) := by
    simpa [ms, Measure.map_id] using h.tendsto
  have hlimsup0 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hF
  have hlimsup : Filter.limsup (fun n => (ms n : Measure E) F) atTop ≤ ν F := by
    simpa using hlimsup0
  have hmevent : ∀ᶠ n in atTop, (ms n : Measure E) F < ENNReal.ofReal η :=
    (Filter.limsup_le_iff (u := fun n => (ms n : Measure E) F) (x := ν F)).mp
      hlimsup (ENNReal.ofReal η) hνF
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmevent] with n hn
  have hmap : (μ.map (T n)) F = μ {ω | C ≤ ‖T n ω‖} := by
    rw [Measure.map_apply_of_aemeasurable (hT n) hF.measurableSet]
    rfl
  have hsub : {ω | C < ‖T n ω‖} ⊆ {ω | C ≤ ‖T n ω‖} := by
    intro ω hω
    change C < ‖T n ω‖ at hω
    exact le_of_lt hω
  have hprob : (μ {ω | C < ‖T n ω‖}).toReal ≤ ((ms n : Measure E) F).toReal := by
    change (μ {ω | C < ‖T n ω‖}).toReal ≤ (μ.map (T n) F).toReal
    rw [hmap]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono hsub
  have htarget : ((ms n : Measure E) F).toReal < η := by
    have hlt : (ms n : Measure E) F < ENNReal.ofReal η := hn
    have ht := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hlt
    simpa [ENNReal.toReal_ofReal (le_of_lt hη)] using ht
  change (μ {ω | C < ‖T n ω‖}).toReal ≤ η
  exact hprob.trans htarget.le

end SAP.P001a.WH.W1.P.T18_L5

theorem SAP.P001a.WH.W1.T18_L5_proof : SAP.P001a.WH.W1.T18_L5 := by
  intro Ω _ μ _ p Z D hiid b h hgram hscore
  let q := SAP.P001a.wholeQ μ (Z 0)
  let om := SAP.P001a.wholeOmega μ (Z 0) (D 0) b
  let V := SAP.P001a.wholeSandwich μ (Z 0) (D 0) b
  letI : IsProbabilityMeasure (SAP.P001a.normalVectorLaw (SAP.P001a.wholeOmega μ (Z 0) (D 0) b)) :=
    AronowAudit.P001.Wave1.DecideB_instProbability_normalVectorLaw _
  letI : IsProbabilityMeasure (SAP.P001a.normalVectorLaw V) :=
    AronowAudit.P001.Wave1.DecideB_instProbability_normalVectorLaw V
  letI : SeminormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) :=
    Matrix.seminormedAddCommGroup
  letI : TopologicalSpace (Matrix (Fin p) (Fin p) ℝ) :=
    (inferInstance : SeminormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : SecondCountableTopology (Matrix (Fin p) (Fin p) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin p → Fin p → ℝ))
  letI : MeasurableSpace (Matrix (Fin p) (Fin p) ℝ) := Matrix.instMeasurableSpace
  letI : BorelSpace (Matrix (Fin p) (Fin p) ℝ) :=
    Matrix.instBorelSpaceOfCountableOfSecondCountableTopology (Fin p) (Fin p) ℝ
  let P : ℕ → Ω → Fin p → ℝ := fun n ω =>
    (SAP.P001a.wholeEmpiricalQ Z n ω)⁻¹.mulVec
      (SAP.P001a.wholeScoreSum Z D b n ω)
  have hmZ (i : ℕ) : Measurable (Z i) := measurable_fst.comp (hiid.1 i)
  have hmD (i : ℕ) : Measurable (D i) := measurable_snd.comp (hiid.1 i)
  have hmScore (n : ℕ) : Measurable (SAP.P001a.wholeScoreSum Z D b n) := by
    apply measurable_pi_lambda
    intro j
    simp only [SAP.P001a.wholeScoreSum, Pi.smul_apply, smul_eq_mul,
      SAP.P001a.wholeResidual, dotProduct]
    fun_prop
  have hscoreDist := SAP.P001a.WH.W1.P.T18_L5.weakLimit_to_tendstoInDistribution
    μ (SAP.P001a.wholeScoreSum Z D b) (SAP.P001a.normalVectorLaw om) hmScore hscore
  have hInvTM : TendstoInMeasure μ
      (fun n ω => (SAP.P001a.wholeEmpiricalQ Z n ω)⁻¹) atTop (fun _ => q⁻¹) := by
    exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mp hgram.inverse
  have hmQn (n : ℕ) : Measurable (SAP.P001a.wholeEmpiricalQ Z n) := by
    apply Measurable.of_eval_matrix
    intro j k
    dsimp [SAP.P001a.wholeEmpiricalQ]
    fun_prop
  have hmInv (n : ℕ) : AEMeasurable
      (fun ω => (SAP.P001a.wholeEmpiricalQ Z n ω)⁻¹) μ := by
    exact (AronowAudit.P001.Wave1.DecideB_matrix_inv_measurable).comp_aemeasurable
      (hmQn n).aemeasurable
  have hSlutsky := hscoreDist.continuous_comp_prodMk_of_tendstoInMeasure_const
    (mE' := Matrix.instMeasurableSpace)
    (g := fun z : (Fin p → ℝ) × Matrix (Fin p) (Fin p) ℝ => z.2.mulVec z.1)
    (by fun_prop) hInvTM hmInv
  have hLaw : (SAP.P001a.normalVectorLaw om).map (fun z => q⁻¹.mulVec z) =
      SAP.P001a.normalVectorLaw V := by
    simpa [q, om, V, SAP.P001a.wholeSandwich] using
      SAP.P001a.WH.W1.P.T18_L5.normalVectorLaw_mulVec q⁻¹ om h.positiveOmega
  have hPdist : TendstoInDistribution P atTop id (fun _ => μ)
      (SAP.P001a.normalVectorLaw V) := by
    exact ⟨hSlutsky.forall_aemeasurable, measurable_id.aemeasurable, by
      simpa [hLaw, Measure.map_id] using hSlutsky.tendsto⟩
  have hRankFail : Tendsto
      (fun n => SAP.P001a.prob μ
        {ω | ¬ IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det}) atTop (nhds 0) :=
    SAP.P001a.WH.W1.P.T18_L5.rankFailure_tendsto μ (SAP.P001a.wholeEmpiricalQ Z)
      (by intro n; fun_prop) hgram.eventualRank
  have hdiffCP : SAP.P001a.CP μ
      (fun n ω => SAP.P001a.wholeRootError Z D b n ω - P n ω) 0 := by
    intro ε hε
    change Tendsto (fun n => SAP.P001a.prob μ
      {ω | ε ≤ dist (SAP.P001a.wholeRootError Z D b n ω - P n ω) 0})
      atTop (nhds 0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRankFail
      (fun _ => ENNReal.toReal_nonneg) ?_
    intro n
    have hsub : {ω | ε ≤ dist
        (SAP.P001a.wholeRootError Z D b n ω - P n ω) 0} ⊆
        {ω | ¬ IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det} := by
      intro ω he
      change ¬ IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det
      by_cases hn : 0 < n
      · by_cases hunit : IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det
        · have heq := SAP.P001a.WH.W1.P.T18_L5.rootError_eq_proxy Z D b n ω hn hunit
          have hzero : ε ≤ 0 := by simpa [P, heq] using he
          exact (not_le_of_gt hε hzero).elim
        · exact hunit
      · by_cases hunit : IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det
        · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
          subst n
          have heq : SAP.P001a.wholeRootError Z D b 0 ω = P 0 ω := by
            simp [P, SAP.P001a.wholeRootError, SAP.P001a.wholeScoreSum]
          have hzero : ε ≤ 0 := by simpa [heq] using he
          exact (not_le_of_gt hε hzero).elim
        · exact hunit
    change μ.real {ω | ε ≤ dist
        (SAP.P001a.wholeRootError Z D b n ω - P n ω) 0} ≤
      μ.real {ω | ¬ IsUnit (SAP.P001a.wholeEmpiricalQ Z n ω).det}
    exact measureReal_mono hsub (measure_ne_top μ _)
  have hdiffTM : TendstoInMeasure μ
      (fun n ω => SAP.P001a.wholeRootError Z D b n ω - P n ω) atTop 0 :=
    (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mp hdiffCP
  have hmBeta (n : ℕ) : Measurable (SAP.P001a.wholeBetaHat Z D n) := hgram.measurableBeta n
  have hmRoot (n : ℕ) : Measurable (SAP.P001a.wholeRootError Z D b n) := by
    change Measurable (fun ω => Real.sqrt n • (SAP.P001a.wholeBetaHat Z D n ω - b))
    fun_prop
  have hRootDist : TendstoInDistribution (SAP.P001a.wholeRootError Z D b)
      atTop id (fun _ => μ) (SAP.P001a.normalVectorLaw V) :=
    tendstoInDistribution_of_tendstoInMeasure_sub (X := P)
      (Y := SAP.P001a.wholeRootError Z D b) (Z := id) hPdist hdiffTM
      (fun n => (hmRoot n).aemeasurable)
  have hweak := AronowAudit.P001.Wave1.DecideB_weakLimit_of_tendstoInDistribution
    μ (SAP.P001a.wholeRootError Z D b) (SAP.P001a.normalVectorLaw V) hRootDist
  have htight := SAP.P001a.WH.W1.P.T18_L5.tight_of_tendstoInDistribution μ (SAP.P001a.wholeRootError Z D b)
    (SAP.P001a.normalVectorLaw V) (fun n => (hmRoot n).aemeasurable) hRootDist
  have hweakSAP : SAP.P001a.WeakLimit μ (SAP.P001a.wholeRootError Z D b)
      (SAP.P001a.normalVectorLaw V) := by
    intro f hf hb
    have hh := hweak f hf hb
    simpa only [SAP.P001a.mean, AronowAudit.P001.mean] using hh
  exact ⟨by simpa [V] using hweakSAP, by simpa [V] using htight⟩
