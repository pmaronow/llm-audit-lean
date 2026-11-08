import SAP.P001a.WH.W1.Leaves
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L10

def inverseExtension {L : ℕ} (S A : Matrix (Fin L) (Fin L) ℝ) :
    Matrix (Fin L) (Fin L) ℝ :=
  if 0 < S.det then (max (S.det / 2) A.det)⁻¹ • A.adjugate
  else (min (S.det / 2) A.det)⁻¹ • A.adjugate

def inverseGood {L : ℕ} (S A : Matrix (Fin L) (Fin L) ℝ) : Prop :=
  if 0 < S.det then S.det / 2 < A.det else A.det < S.det / 2

lemma inverseExtension_continuous {L : ℕ} (S : Matrix (Fin L) (Fin L) ℝ)
    (hS : S.det ≠ 0) : Continuous (inverseExtension S) := by
  let d : Matrix (Fin L) (Fin L) ℝ → ℝ := fun A =>
    if 0 < S.det then max (S.det / 2) A.det else min (S.det / 2) A.det
  have hd : Continuous d := by
    by_cases hp : 0 < S.det
    · simpa [d, hp] using (continuous_const.max continuous_id.matrix_det)
    · simpa [d, hp] using (continuous_const.min continuous_id.matrix_det)
  have hd0 : ∀ A, d A ≠ 0 := by
    intro A
    by_cases hp : 0 < S.det
    · have hpos : 0 < max (S.det / 2) A.det :=
        lt_of_lt_of_le (by linarith) (le_max_left _ _)
      simpa [d, hp] using hpos.ne'
    · have hneg : S.det < 0 := lt_of_le_of_ne (le_of_not_gt hp) hS
      have hlt : min (S.det / 2) A.det < 0 :=
        (min_le_left _ _).trans_lt (by linarith)
      simpa [d, hp] using hlt.ne
  have hi : Continuous (fun A => (d A)⁻¹) := hd.inv₀ hd0
  have ha : Continuous (fun A : Matrix (Fin L) (Fin L) ℝ => A.adjugate) :=
    continuous_id.matrix_adjugate
  have hm : Continuous (fun A => (d A)⁻¹ • A.adjugate) := hi.smul ha
  have heq : (inverseExtension S) = (fun A => (d A)⁻¹ • A.adjugate) := by
    funext A
    by_cases hp : 0 < S.det <;> simp [inverseExtension, d, hp]
  rw [heq]
  exact hm

lemma inverseExtension_eq_inv {L : ℕ} (S A : Matrix (Fin L) (Fin L) ℝ)
    (hgood : inverseGood S A) : inverseExtension S A = A⁻¹ := by
  by_cases hp : 0 < S.det
  · have hg : S.det / 2 < A.det := by simpa [inverseGood, hp] using hgood
    have hm : max (S.det / 2) A.det = A.det := max_eq_right (le_of_lt hg)
    simp [inverseExtension, inverseGood, hp, hm, Matrix.inv_def, Ring.inverse_eq_inv]
  · have hg : A.det < S.det / 2 := by simpa [inverseGood, hp] using hgood
    have hm : min (S.det / 2) A.det = A.det := min_eq_right (le_of_lt hg)
    simp [inverseExtension, inverseGood, hp, hm, Matrix.inv_def, Ring.inverse_eq_inv]

lemma weakLimit_to_tendstoInDistribution {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [Nonempty E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E) (ν : Measure E)
    [IsProbabilityMeasure ν] (hX : ∀ n, Measurable (X n))
    (h : SAP.P001a.WeakLimit μ X ν) :
    TendstoInDistribution X atTop (id : E → E) (fun _ : ℕ => μ) ν := by
  have hXm : ∀ n, AEMeasurable (X n) μ := fun n => (hX n).aemeasurable
  have hid : AEMeasurable (id : E → E) ν := measurable_id.aemeasurable
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hXm hid]
  intro f
  rcases f.bounded with ⟨C, hC⟩
  let y : E := Classical.choice ‹Nonempty E›
  have hb : ∃ C' : ℝ, ∀ x, |f x| ≤ C' := by
    refine ⟨C + |f y|, fun x => ?_⟩
    have hx := hC x y
    rw [Real.dist_eq] at hx
    calc
      |f x| = |(f x - f y) + f y| := by congr 1 <;> ring
      _ ≤ |f x - f y| + |f y| := abs_add_le _ _
      _ ≤ C + |f y| := add_le_add hx le_rfl
  exact h f f.continuous hb

lemma cp_to_tendstoInMeasure {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (c : E) (h : SAP.P001a.CP μ X c) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  exact h ε hε

lemma continuousAt_cdf_atomless {ν : Measure ℝ} [IsProbabilityMeasure ν] {x : ℝ}
    (hcont : ContinuousAt (fun t => SAP.P001a.prob ν (Set.Iic t)) x) : ν {x} = 0 := by
  have heq : (fun t : ℝ => ProbabilityTheory.cdf ν t) =
      (fun t => SAP.P001a.prob ν (Set.Iic t)) := by
    funext t
    exact ProbabilityTheory.cdf_eq_real ν t
  have hcdf : ContinuousAt (ProbabilityTheory.cdf ν) x := by
    exact hcont.congr (Eventually.of_forall fun t => (congrFun heq t).symm)
  have hleft : Function.leftLim (ProbabilityTheory.cdf ν) x = ProbabilityTheory.cdf ν x :=
    (ProbabilityTheory.monotone_cdf ν).continuousWithinAt_Iio_iff_leftLim_eq.mp
      hcdf.continuousWithinAt
  have hs : (ProbabilityTheory.cdf ν).measure {x} = 0 := by
    rw [StieltjesFunction.measure_singleton, hleft]
    simp
  calc
    ν {x} = (ProbabilityTheory.cdf ν).measure {x} := by rw [ProbabilityTheory.measure_cdf]
    _ = 0 := hs

lemma tendstoInDistribution_cdf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hX : ∀ n, AEMeasurable (X n) μ)
    (h : TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ : ℕ => μ) ν)
    (x : ℝ) (hcont : ContinuousAt (fun t => SAP.P001a.prob ν (Set.Iic t)) x) :
    Tendsto (fun n => SAP.P001a.prob μ {ω | X n ω ≤ x}) atTop
      (nhds (SAP.P001a.prob ν (Set.Iic x))) := by
  let νp : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  let μp : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μ.map (X n), inferInstance⟩
  have hconv : Tendsto μp atTop (𝓝 νp) := by
    have hh := h.tendsto
    simpa [μp, νp, Measure.map_id] using hh
  have hnull := continuousAt_cdf_atomless hcont
  have hfront : (νp : Measure ℝ) (frontier (Set.Iic x)) = 0 := by
    simpa [νp, frontier_Iic] using hnull
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfront
  have hr := (ENNReal.tendsto_toReal (measure_ne_top ν (Set.Iic x))).comp hp
  simpa only [μp, ProbabilityMeasure.coe_mk,
    Measure.map_apply_of_aemeasurable (hX _) measurableSet_Iic,
    Set.preimage, Set.mem_Iic, SAP.P001a.prob, Function.comp_def] using hr

end SAP.P001a.WH.W1.P.T18_L10

theorem SAP.P001a.WH.W1.T18_L10_proof : SAP.P001a.WH.W1.T18_L10 := by
  intro Ω _ μ hμ p L hL b V hV R hS hnull B C hB hC hCLT hCov hLaw
  have hnormalProb : IsProbabilityMeasure (normalVectorLaw V) := by
    unfold SAP.P001a.normalVectorLaw ProbabilityTheory.multivariateGaussian
    infer_instance
  letI : IsProbabilityMeasure (normalVectorLaw V) := hnormalProb
  have hchiProb : IsProbabilityMeasure (wholeChiSquare L) := by
    unfold wholeChiSquare
    infer_instance
  letI : IsProbabilityMeasure (wholeChiSquare L) := hchiProb
  let root : ℕ → Ω → Fin p → ℝ := fun n ω => Real.sqrt n • (B n ω - b)
  let covn : ℕ → Ω → Fin p → Fin p → ℝ :=
    fun n ω j k => ((n : ℝ) • C n ω) j k
  have hrootMeas : ∀ n, Measurable (root n) := by
    intro n
    have hf : Measurable (fun x : Fin p → ℝ => Real.sqrt n • (x - b)) := by fun_prop
    simpa [root, Function.comp_def] using hf.comp (hB n)
  have hcovMeas : ∀ n, Measurable (covn n) := by
    intro n
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    simpa [covn, Matrix.smul_apply, smul_eq_mul, Pi.mul_def] using
      (measurable_const.mul (Measurable.eval_matrix (hC n) (i := j) (j := k)))
  have hrootWeak : SAP.P001a.WeakLimit μ root (normalVectorLaw V) := by
    simpa [root] using hCLT
  have hrootDist : TendstoInDistribution root atTop (id : (Fin p → ℝ) → (Fin p → ℝ))
      (fun _ : ℕ => μ) (normalVectorLaw V) :=
    SAP.P001a.WH.W1.P.T18_L10.weakLimit_to_tendstoInDistribution μ root
      (normalVectorLaw V) hrootMeas hrootWeak
  have hcovCP : SAP.P001a.CP μ covn V := hCov
  have hcovMeasure : TendstoInMeasure μ covn atTop (fun _ => V) :=
    SAP.P001a.WH.W1.P.T18_L10.cp_to_tendstoInMeasure μ covn V hcovCP
  have hpair : TendstoInDistribution (fun n ω => (root n ω, covn n ω)) atTop
      (fun z => (z, V)) (fun _ : ℕ => μ) (normalVectorLaw V) :=
    TendstoInDistribution.prodMk_of_tendstoInMeasure_const
      (E' := Fin p → Fin p → ℝ) root covn
      (id : (Fin p → ℝ) → (Fin p → ℝ))
      hrootDist hcovMeasure (fun n => (hcovMeas n).aemeasurable)
  let S : Matrix (Fin L) (Fin L) ℝ := R * V * R.transpose
  have hSdet : S.det ≠ 0 := hS.ne_zero
  let Q : Matrix (Fin p) (Fin p) ℝ → Matrix (Fin L) (Fin L) ℝ :=
    fun A => R * A * R.transpose
  have hQ : Continuous Q := by fun_prop
  let invcov : Matrix (Fin p) (Fin p) ℝ → Matrix (Fin L) (Fin L) ℝ :=
    fun A => SAP.P001a.WH.W1.P.T18_L10.inverseExtension S (Q A)
  have hinvcov : Continuous invcov :=
    (SAP.P001a.WH.W1.P.T18_L10.inverseExtension_continuous S hSdet).comp hQ
  let ψ : ((Fin p → ℝ) × Matrix (Fin p) (Fin p) ℝ) → ℝ := fun x =>
    (R.mulVec x.1) ⬝ᵥ (invcov x.2).mulVec (R.mulVec x.1)
  have hψ : Continuous ψ := by fun_prop
  let regW : ℕ → Ω → ℝ := fun n ω => ψ (root n ω, covn n ω)
  have hregDist : TendstoInDistribution regW atTop (fun z => ψ (z, V))
      (fun _ : ℕ => μ) (normalVectorLaw V) :=
    hpair.continuous_comp (g := ψ) hψ
  have hgoodS : SAP.P001a.WH.W1.P.T18_L10.inverseGood S S := by
    unfold SAP.P001a.WH.W1.P.T18_L10.inverseGood
    by_cases hp : 0 < S.det
    · simp [hp]
    · have hn : S.det < 0 := lt_of_le_of_ne (le_of_not_gt hp) hSdet
      simp [hp]
      linarith
  have hinvS := SAP.P001a.WH.W1.P.T18_L10.inverseExtension_eq_inv S S hgoodS
  have hlimitLaw : (normalVectorLaw V).map (fun z => ψ (z, V)) = wholeChiSquare L := by
    rw [← hLaw]
    congr 1
    funext z
    simp [ψ, invcov, Q, S, hinvS]
  have hregDistChi : TendstoInDistribution regW atTop (id : ℝ → ℝ)
      (fun _ : ℕ => μ) (wholeChiSquare L) := by
    refine ⟨hregDist.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa [Measure.map_id, hlimitLaw] using hregDist.tendsto
  have hScont : Continuous (fun A : Matrix (Fin p) (Fin p) ℝ => (Q A).det) :=
    continuous_id.matrix_det.comp hQ
  have hdetS : (Q V).det = S.det := by rfl
  have hgoodRadius : ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin p) (Fin p) ℝ,
      dist A V < δ → SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q A) := by
    by_cases hp : 0 < S.det
    · have hbase : Set.Ioi (S.det / 2) ∈
          𝓝 ((fun A : Matrix (Fin p) (Fin p) ℝ => (Q A).det) V) := by
        rw [hdetS]
        exact Ioi_mem_nhds (by linarith)
      have hevent : {A : Matrix (Fin p) (Fin p) ℝ | S.det / 2 < (Q A).det} ∈ 𝓝 V :=
        hScont.continuousAt.preimage_mem_nhds hbase
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
      refine ⟨δ, hδ, ?_⟩
      intro A hA
      have hmem : A ∈ Metric.ball V δ := by simpa [Metric.mem_ball] using hA
      have hh := hball hmem
      simpa [SAP.P001a.WH.W1.P.T18_L10.inverseGood, hp] using hh
    · have hneg : S.det < 0 := lt_of_le_of_ne (le_of_not_gt hp) hSdet
      have hbase : Set.Iio (S.det / 2) ∈
          𝓝 ((fun A : Matrix (Fin p) (Fin p) ℝ => (Q A).det) V) := by
        rw [hdetS]
        exact Iio_mem_nhds (by linarith)
      have hevent : {A : Matrix (Fin p) (Fin p) ℝ | (Q A).det < S.det / 2} ∈ 𝓝 V :=
        hScont.continuousAt.preimage_mem_nhds hbase
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
      refine ⟨δ, hδ, ?_⟩
      intro A hA
      have hmem : A ∈ Metric.ball V δ := by simpa [Metric.mem_ball] using hA
      have hh := hball hmem
      simpa [SAP.P001a.WH.W1.P.T18_L10.inverseGood, hp] using hh
  obtain ⟨δ, hδ, hgoodBall⟩ := hgoodRadius
  have hbadLim : Tendsto (fun n => SAP.P001a.prob μ
      {ω | ¬ SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q (covn n ω))}) atTop (nhds 0) := by
    have htail := hCov δ hδ
    have hbound : ∀ n, SAP.P001a.prob μ
        {ω | ¬ SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q (covn n ω))} ≤
        SAP.P001a.prob μ {ω | δ ≤ dist (covn n ω) V} := by
      intro n
      apply measureReal_mono (μ := μ) _ (measure_ne_top μ _)
      intro ω hω
      by_contra hdist
      apply hω
      exact hgoodBall (covn n ω) (lt_of_not_ge hdist)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => ENNReal.toReal_nonneg) hbound
  have hrootNorm : ∀ n ω, R.mulVec (root n ω) =
      Real.sqrt n • (R.mulVec (B n ω)) := by
    intro n ω
    simp [root, Matrix.mulVec_smul, Matrix.mulVec_sub, hnull, sub_zero]
  have hcovScale (n : ℕ) (ω : Ω) : Q (covn n ω) =
      (n : ℝ) • (R * C n ω * R.transpose) := by
    change R * ((n : ℝ) • C n ω) * R.transpose =
      (n : ℝ) • (R * C n ω * R.transpose)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hregEq (n : ℕ) (ω : Ω) (hn : 0 < n)
      (hg : SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q (covn n ω))) :
      regW n ω = wholeWald R (B n ω) (C n ω) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hinv := SAP.P001a.WH.W1.P.T18_L10.inverseExtension_eq_inv S
      (Q (covn n ω)) hg
    have hAunit : IsUnit (R * C n ω * R.transpose).det := by
      have hM : IsUnit (Q (covn n ω)) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (by
          have : (Q (covn n ω)).det ≠ 0 := by
            intro hz
            have := hg
            unfold SAP.P001a.WH.W1.P.T18_L10.inverseGood at this
            by_cases hp : 0 < S.det
            · simp [hp, hz] at this
              linarith
            · simp [hp, hz] at this
          exact isUnit_iff_ne_zero.mpr this)
      have hpow : IsUnit ((n : ℝ) ^ L) := isUnit_iff_ne_zero.mpr (pow_ne_zero _ hnR)
      have hMdet : IsUnit (Q (covn n ω)).det := (Matrix.isUnit_iff_isUnit_det _).mp hM
      rw [hcovScale, Matrix.det_smul] at hMdet
      have hdet : IsUnit ((n : ℝ) ^ L * (R * C n ω * R.transpose).det) := by
        simpa using hMdet
      exact (IsUnit.mul_iff.mp hdet).2
    letI : Invertible (n : ℝ) := invertibleOfNonzero (by exact_mod_cast (Nat.ne_of_gt hn))
    have hinvScale : (Q (covn n ω))⁻¹ =
        (n : ℝ)⁻¹ • (R * C n ω * R.transpose)⁻¹ := by
      rw [hcovScale, Matrix.inv_smul (R * C n ω * R.transpose) (n : ℝ) hAunit]
      simp [invOf_eq_inv]
    dsimp [regW, ψ, invcov]
    rw [hinv, hinvScale, hrootNorm]
    simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul]
    simp [wholeWald]
    field_simp [hnR]
    ring_nf
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hdiff : TendstoInMeasure μ
      (fun n ω => wholeWald R (B n ω) (C n ω) - regW n ω) atTop 0 := by
    rw [tendstoInMeasure_iff_measureReal_dist]
    intro ε hε
    have hsub (n : ℕ) (hn : 0 < n) : {ω | ε ≤ dist
        (wholeWald R (B n ω) (C n ω)) (regW n ω)} ⊆
        {ω | ¬ SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q (covn n ω))} := by
      intro ω hω hgood
      change ε ≤ dist (wholeWald R (B n ω) (C n ω)) (regW n ω) at hω
      have heq := hregEq n ω hn hgood
      rw [heq] at hω
      simp at hω
      linarith
    have hbound : ∀ᶠ n in atTop,
        SAP.P001a.prob μ {ω | ε ≤ dist
          (wholeWald R (B n ω) (C n ω) - regW n ω) 0} ≤
        SAP.P001a.prob μ
          {ω | ¬ SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q (covn n ω))} := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      calc
        SAP.P001a.prob μ {ω | ε ≤ dist
            (wholeWald R (B n ω) (C n ω) - regW n ω) 0} =
          SAP.P001a.prob μ {ω | ε ≤ dist
            (wholeWald R (B n ω) (C n ω)) (regW n ω)} := by
              congr 1
              ext ω
              simp [Real.dist_eq]
        _ ≤ SAP.P001a.prob μ
            {ω | ¬ SAP.P001a.WH.W1.P.T18_L10.inverseGood S (Q (covn n ω))} :=
          measureReal_mono (hsub n hn) (measure_ne_top μ _)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbadLim
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
  have hwaldMeas : ∀ n, Measurable (fun ω => wholeWald R (B n ω) (C n ω)) := by
    intro n
    exact SAP.P001a.WH.W1.measurable_wald R (B n) (C n) (hB n) (hC n)
  have hactualDist : TendstoInDistribution (fun n ω => wholeWald R (B n ω) (C n ω))
      atTop (id : ℝ → ℝ) (fun _ : ℕ => μ) (wholeChiSquare L) :=
    tendstoInDistribution_of_tendstoInMeasure_sub
      (fun n ω => wholeWald R (B n ω) (C n ω)) (id : ℝ → ℝ)
      hregDistChi hdiff (fun n => (hwaldMeas n).aemeasurable)
  intro x hx
  exact SAP.P001a.WH.W1.P.T18_L10.tendstoInDistribution_cdf μ
    (fun n ω => wholeWald R (B n ω) (C n ω)) (wholeChiSquare L)
    (fun n => (hwaldMeas n).aemeasurable) hactualDist x hx
