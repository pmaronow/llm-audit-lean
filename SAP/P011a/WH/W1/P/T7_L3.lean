import SAP.P011a.WH.W1.Leaves
import AronowAudit.P011.P011_ProbabilityCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P011a
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem SAP.P011a.WH.W1.T7_L3_proof : SAP.P011a.WH.W1.T7_L3 := by
  unfold SAP.P011a.WH.W1.T7_L3 WholeCLT
  intro F c1 c2 c3 c4 h t
  classical
  let (k : ℕ) : IsProbabilityMeasure (SAP.P011a.Bridge.model (F.model k)).law :=
    (SAP.P011a.Bridge.model (F.model k)).probability
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    AronowAudit.P011.ProbabilityCompletion.weighted_memLp
      (SAP.P011a.Bridge.model (F.model k)) c1 (h.bounded k) i
  have hdep (k : ℕ) : AronowAudit.P011.Dependency
      (SAP.P011a.Bridge.model (F.model k)) := by
    intro S T hdis hsep
    simpa [AronowAudit.P011.Dependency, SAP.P011a.Dependency,
      AronowAudit.P011.VariableDependency, SAP.P011a.VariableDependency,
      SAP.P011a.Bridge.model] using h.dependency k S T hdis hsep
  let X : ∀ k, Fin (F.size k) → (Fin (F.size k) → ℝ) → ℝ :=
    fun k i y => AronowAudit.P011.weighted (SAP.P011a.Bridge.model (F.model k)) y i -
      AronowAudit.P011.expectation (SAP.P011a.Bridge.model (F.model k))
        (fun z => AronowAudit.P011.weighted (SAP.P011a.Bridge.model (F.model k)) z i)
  let D := fun k => AronowAudit.P011.ProbabilityCompletion.modelDep
    (SAP.P011a.Bridge.model (F.model k)) (hdep k)
  have hdeg (k : ℕ) (i : Fin (F.size k)) : ((D k).nbhd i).card ≤ ⌈c2⌉₊+1 := by
    dsimp [D]
    rw [AronowAudit.P011.ProbabilityCompletion.modelDep_degree]
    have hh : AronowAudit.P011.degree (SAP.P011a.Bridge.model (F.model k)).G i ≤ ⌈c2⌉₊ := by
      exact_mod_cast (h.degrees k i).trans (Nat.le_ceil c2)
    omega
  have hb (k : ℕ) (i : Fin (F.size k)) :
      ∀ᵐ y ∂(SAP.P011a.Bridge.model (F.model k)).law, |X k i y| ≤ 2*c1 :=
    (AronowAudit.P011.ProbabilityCompletion.own_centred_bound
      (SAP.P011a.Bridge.model (F.model k)) c1 (hL2 k) (h.bounded k)).mono
      (fun y hy => hy i)
  have hm (k : ℕ) (i : Fin (F.size k)) :
      ∫ y, X k i y ∂(SAP.P011a.Bridge.model (F.model k)).law = 0 := by
    dsimp [X]
    rw [integral_sub ((hL2 k i).integrable (by norm_num)) (integrable_const _)]
    simp [AronowAudit.P011.expectation]
  let v := fun k => (F.size k:ℝ)^2 *
    AronowAudit.P011.var (SAP.P011a.Bridge.model (F.model k))
      (AronowAudit.P011.betaHat (SAP.P011a.Bridge.model (F.model k)))
  have hv (k : ℕ) :
      ∫ y, (Causalean.Mathlib.Probability.SteinMethod.depSum (X k) y)^2
        ∂(SAP.P011a.Bridge.model (F.model k)).law = v k := by
    simpa [v, X, SAP.P011a.Bridge.model] using
      (AronowAudit.P011.ProbabilityCompletion.sum_variance
        (F.positive k) (SAP.P011a.Bridge.model (F.model k)) (hL2 k))
  have hvc : ∀ᶠ k in atTop,
      (c3/2)*(Fintype.card (Fin (F.size k)):ℝ) ≤ v k := by
    have hev : ∀ᶠ k in atTop,
        c3/2 < (F.size k:ℝ)*var (F.model k) (betaHat (F.model k)) :=
      h.variance_limit.eventually (Ioi_mem_nhds (show c3/2 < c3 by nlinarith [h.c3_pos]))
    filter_upwards [hev] with k hk
    dsimp [v]
    simp only [Fintype.card_fin]
    have hn : 0 < (F.size k:ℝ) := by exact_mod_cast F.positive k
    have hvEq : var (F.model k) (betaHat (F.model k)) =
        AronowAudit.P011.var (SAP.P011a.Bridge.model (F.model k))
          (AronowAudit.P011.betaHat (SAP.P011a.Bridge.model (F.model k))) := rfl
    nlinarith [hvEq]
  have hh := Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt_ae
    (fun k => (SAP.P011a.Bridge.model (F.model k)).law) X D
    (⌈c2⌉₊+1) hdeg (2*c1) hb hm v hv
    (c3/2) (by nlinarith [h.c3_pos]) hvc
    (by simpa only [Fintype.card_fin] using F.grows) t
  have hid (k : ℕ) :
      (fun y => Causalean.Mathlib.Probability.SteinMethod.depSum (X k) y /
          Real.sqrt (v k)) = fun y => AronowAudit.P011.standardized
            (SAP.P011a.Bridge.model (F.model k)) y := by
    funext y
    dsimp [v, X]
    exact AronowAudit.P011.ProbabilityCompletion.depSum_standardized
      (F.positive k) (SAP.P011a.Bridge.model (F.model k)) (hL2 k) y
  simp only [hid] at hh
  have hPhi : (gaussianReal 0 1).real (Set.Iic t) = Phi t :=
    (ProbabilityTheory.cdf_eq_real (gaussianReal 0 1) t).symm
  rw [hPhi] at hh
  convert hh using 1
  funext k
  have hstd : Measurable (AronowAudit.P011.standardized
      (SAP.P011a.Bridge.model (F.model k))) := by
    exact ((AronowAudit.P011.ProbabilityCompletion.betaHat_measurable
      (SAP.P011a.Bridge.model (F.model k))).sub measurable_const).div_const _
  symm
  change (Measure.map (AronowAudit.P011.standardized
      (SAP.P011a.Bridge.model (F.model k)))
      (SAP.P011a.Bridge.model (F.model k)).law).real (Set.Iic t) =
    (SAP.P011a.Bridge.model (F.model k)).law.real
      {y | AronowAudit.P011.standardized
        (SAP.P011a.Bridge.model (F.model k)) y ≤ t}
  exact map_measureReal_apply hstd measurableSet_Iic

