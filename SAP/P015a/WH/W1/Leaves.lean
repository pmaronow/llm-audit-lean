import SAP.P015a.WH.W1.LeafTypes
import SAP.P015a.WH.W1.TaylorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.WH.W1

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Normalization supplies the smoothness needed to linearize κ', through the
analytic cumulant-generating function and an invertible scalar change of variable. -/
private theorem analytic_from_local_mgf (P : Measure ℝ) (κ : ℝ → ℝ) (s η : ℝ)
    (hs : 0 < s)
    (hzero : (0 : ℝ) ∈ interior (integrableExpSet (fun y : ℝ => y) P))
    (hmgf : mgf (fun y : ℝ => y) P =ᶠ[𝓝 0]
      fun t => Real.exp ((κ (η + s * t) - κ η) / s)) : AnalyticAt ℝ κ η := by
  have ht : AnalyticAt ℝ (fun x : ℝ => (x - η) / s) η :=
    (analyticAt_id.sub analyticAt_const).div_const
  have ha : AnalyticAt ℝ (fun x : ℝ => cgf (fun y : ℝ => y) P ((x - η) / s)) η :=
    (analyticAt_cgf hzero).comp_of_eq ht (by simp)
  have hg : AnalyticAt ℝ (fun x : ℝ => κ η + s * cgf (fun y : ℝ => y) P ((x - η) / s)) η :=
    analyticAt_const.add (analyticAt_const.mul ha)
  apply hg.congr
  have hc : Tendsto (fun x : ℝ => (x - η) / s) (𝓝 η) (𝓝 0) := by
    convert (show ContinuousAt (fun x : ℝ => (x - η) / s) η by fun_prop).tendsto using 1
    simp
  filter_upwards [hc.eventually hmgf] with x hx
  change κ η + s * Real.log (mgf (fun y : ℝ => y) P ((x - η) / s)) = κ x
  rw [hx, Real.log_exp]
  have hinv : η + s * ((x - η) / s) = x := by field_simp [hs.ne']; ring
  rw [hinv]
  have hcancel : s * ((κ x - κ η) / s) = κ x - κ η := by field_simp [hs.ne']
  rw [hcancel]
  ring

private theorem mean_from_local_mgf (P : Measure ℝ) (κ : ℝ → ℝ) (s η : ℝ)
    (hs : 0 < s) (hκ : DifferentiableAt ℝ κ η)
    (hzero : (0 : ℝ) ∈ interior (integrableExpSet (fun y : ℝ => y) P))
    (hmgf : mgf (fun y : ℝ => y) P =ᶠ[𝓝 0]
      fun t => Real.exp ((κ (η + s * t) - κ η) / s)) :
    Integrable (fun y : ℝ => y) P ∧ (∫ y : ℝ, y ∂P) = deriv κ η := by
  have hi : Integrable (fun y : ℝ => y) P := by
    simpa using integrable_pow_of_mem_interior_integrableExpSet hzero 1
  have ha : HasDerivAt (fun t : ℝ => η + s * t) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul s).const_add η
  have hk : HasDerivAt (fun t : ℝ => κ (η + s * t)) (deriv κ η * s) 0 := by
    exact hκ.hasDerivAt.comp_of_eq 0 ha (by simp)
  have hd : HasDerivAt (fun t : ℝ => Real.exp ((κ (η + s * t) - κ η) / s))
      (deriv κ η) 0 := by
    convert ((hk.sub_const (κ η)).div_const s).exp using 1
    simp [hs.ne']
  have hd' := hd.congr_of_eventuallyEq hmgf
  exact ⟨hi, (deriv_mgf_zero hzero).symm.trans hd'.deriv⟩

private theorem differential_zero {q : ℕ} (g : Fin q → ℝ)
    (h : scoreDifferential g = 0) : g = 0 := by
  ext j
  have h' := DFunLike.congr_fun h (Pi.single j 1)
  simpa [scoreDifferential, Pi.single_apply] using h'

private theorem bernoulli_score (hchain : T8_L1) : wholeBernoulliScore := by
  intro n K W Y hY hW I hI m hm hp θ hθ
  have hd : ∀ i, HasDerivAt (bernoulliLogLikelihood m 1 (Y i))
      (likelihoodMultiplier m (W.mulVec θ i) * (Y i - m (W.mulVec θ i)))
      (W.mulVec θ i) := by
    intro i
    exact AronowAudit.P015.bernoulli_score_derivative m (Y i) (W.mulVec θ i) _ (hY i)
      (hm.differentiableAt (hI.mem_nhds (hθ i))).hasDerivAt (hp _ (hθ i)).1 (hp _ (hθ i)).2
  have hgrad : W.transpose.mulVec (fun i => likelihoodMultiplier m (W.mulVec θ i) *
      (Y i - m (W.mulVec θ i))) = likelihoodScore W (fun _ => 1) Y m θ := by
    ext j
    simp only [likelihoodScore, Matrix.mulVec, dotProduct, Matrix.transpose_apply, one_mul]
    congr 1
    ext i
    ring
  have hder : HasFDerivAt (logLikelihood W (fun _ => 1) Y m)
      (scoreDifferential (likelihoodScore W (fun _ => 1) Y m θ)) θ := by
    change HasFDerivAt (fun t => ∑ i, bernoulliLogLikelihood m 1 (Y i) (W.mulVec t i))
      (scoreDifferential (likelihoodScore W (fun _ => 1) Y m θ)) θ
    rw [← hgrad]
    exact hchain n (K + 2) W _ _ θ hd
  refine ⟨hder, ?_⟩
  intro hmax
  have hopen : IsOpen (admissibleParameters W I) := by
    have he : admissibleParameters W I = ⋂ i, {t | W.mulVec t i ∈ I} := by
      ext t
      simp [admissibleParameters]
    rw [he]
    apply isOpen_iInter_of_finite
    intro i
    exact hI.preimage (by fun_prop)
  have hloc : IsLocalMax (logLikelihood W (fun _ => 1) Y m) θ := by
    filter_upwards [hopen.mem_nhds hθ] with t ht using hmax t ht
  exact differential_zero _ (hloc.hasFDerivAt_eq_zero hder)

private theorem canonical_score (hchain : T8_L1) : wholeCanonicalScore := by
  intro n K W κ s hs Y carrier θ hκ
  have hd : ∀ i, HasDerivAt (canonicalContribution κ s (Y i) (carrier i))
      ((Y i - deriv κ (W.mulVec θ i)) / s) (W.mulVec θ i) := by
    intro i
    exact AronowAudit.P015.canonical_score_derivative_calculus κ s (Y i) (carrier i)
      (W.mulVec θ i) _ hs (hκ i).hasDerivAt
  have hg : W.transpose.mulVec (fun i => (Y i - deriv κ (W.mulVec θ i)) / s) =
      canonicalGradient W κ s Y θ := by
    ext j
    simp only [canonicalGradient, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨?_, ?_⟩
  · change HasFDerivAt (fun t => ∑ i, canonicalContribution κ s (Y i) (carrier i)
        (W.mulVec t i)) (scoreDifferential (canonicalGradient W κ s Y θ)) θ
    rw [← hg]
    exact hchain n (K + 2) W _ _ θ hd
  · change s⁻¹ • _ = 0 ↔ _ = 0
    exact smul_eq_zero_iff_right (inv_ne_zero hs.ne')

private theorem full_polynomial_zero {q : ℕ} (A B : Matrix (Fin q) (Fin q) ℝ)
    (r δ : Fin q → ℝ) (h f h' : ℝ) (hh : h ≠ 0) :
    (h • r + ((-h * f) • A + h' • B).mulVec δ = 0 ↔
      (f • A - (h' / h) • B).mulVec δ = r) := by
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  constructor
  · intro hz
    ext j
    have hj := congrFun hz j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at *
    apply (mul_left_cancel₀ hh)
    field_simp
    linear_combination -hj
  · intro hz
    ext j
    have hj := congrFun hz j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at *
    field_simp at hj
    linear_combination -hj

private theorem linearization : wholeScoreLinearization := by
  intro n K W Y hY hW I hI m hm hp η₀ p₀ hη hp₀ hu₀ hmean hm₂
  dsimp only
  have hpred : ∀ δ : Fin (K + 2) → ℝ,
      W.mulVec (interceptVector K η₀ + δ) = fun i => η₀ + W.mulVec δ i := by
    intro δ
    rw [Matrix.mulVec_add]
    ext i
    simp [interceptVector, Matrix.mulVec, dotProduct, mul_ite, hW]
  have hpoly : ∀ δ, fullScoreTaylor W Y m η₀ δ =
      likelihoodMultiplier m η₀ • centeredResidual W Y p₀ +
        ((-likelihoodMultiplier m η₀ * deriv m η₀) • (W.transpose * W) +
          deriv (likelihoodMultiplier m) η₀ • residualMoment W Y p₀).mulVec δ := by
    intro δ
    have h := AronowAudit.P015.full_score_firstTaylor n K W Y hY hW I hI m hm hp
      η₀ p₀ hη hp₀ hu₀ hmean hm₂ δ
    change (fun j => ∑ i, W i j * firstTaylorPolynomial
      (fun η => likelihoodMultiplier m η * (Y i - m η)) η₀
        (W.mulVec (interceptVector K η₀ + δ) i)) =
      likelihoodMultiplier m η₀ • centeredResidual W Y p₀ +
        ((-likelihoodMultiplier m η₀ * deriv m η₀) • (W.transpose * W) +
          deriv (likelihoodMultiplier m) η₀ • residualMoment W Y p₀).mulVec δ at h
    rw [hpred δ] at h
    exact h
  refine ⟨hpoly, ?_⟩
  intro hh
  have hf : deriv m η₀ ≠ 0 := by
    intro hf
    apply hh
    simp [likelihoodMultiplier, hf]
  refine ⟨hf, ?_, ?_⟩
  · intro δ
    rw [hpoly δ]
    exact full_polynomial_zero _ _ _ _ _ _ _ hh
  · intro δ hc
    rcases hc with hz | hz
    · simp [hz, Matrix.smul_mulVec]
    · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hz]

private theorem logistic_score : wholeLogisticScore := by
  have hm : ∀ η : ℝ, likelihoodMultiplier inverseLogit η = 1 :=
    AronowAudit.P015.logistic_multiplier
  refine ⟨?_, ?_⟩
  · intro η
    refine ⟨Real.hasDerivAt_sigmoid η, hm η, ?_⟩
    have he : likelihoodMultiplier inverseLogit = fun _ : ℝ => (1 : ℝ) := funext hm
    simp [he]
  · intro n K W Y θ
    ext j
    simp [likelihoodScore, residualEquation, hm]

private theorem canonical_mean (htilt : T8_L2) : wholeCanonicalMean := by
  intro ν κ s carrier I support hfamily hκ η hη
  obtain ⟨hP, hzero, hmgf⟩ := htilt ν κ s carrier I support hfamily η hη
  have hc : Tendsto (fun t : ℝ => η + s * t) (𝓝 0) (𝓝 η) := by
    convert (show ContinuousAt (fun t : ℝ => η + s * t) 0 by fun_prop).tendsto using 1
    simp
  have he : mgf (fun y : ℝ => y) (canonicalResponseLaw ν κ s carrier η) =ᶠ[𝓝 0]
      fun t => Real.exp ((κ (η + s * t) - κ η) / s) := by
    filter_upwards [hc.eventually (hfamily.2.1.mem_nhds hη)] with t ht using (hmgf t ht).2
  have hmean := mean_from_local_mgf _ κ s η hfamily.1
    (hκ.differentiableAt (hfamily.2.1.mem_nhds hη)) hzero he
  have ha := analytic_from_local_mgf _ κ s η hfamily.1 hzero he
  exact ⟨hP, hmean.1, hmean.2, ha, ha.deriv.differentiableAt⟩

private theorem probit_example : T6Statement := by
  apply Bridge.T6_correspondence.mpr
  have h := AronowAudit.P015.ProbitCounterexample_checked
  have hc : AronowAudit.P015.normalCDF AronowAudit.P015.probitA = 3 / 4 := h.1.2.2.2.2.1
  have h0 : AronowAudit.P015.normalCDF 0 = 1 / 2 := h.1.2.2.2.1
  refine ⟨h, ⟨⟨_, hc.ge⟩, ?_⟩, ?_⟩
  · refine ⟨0, ?_⟩
    intro x hx
    by_contra hn
    have hl := AronowAudit.P015.AnalyticCompletion.strictMono_normalCDF (lt_of_not_ge hn)
    rw [h0] at hl
    change 3 / 4 ≤ AronowAudit.P015.normalCDF x at hx
    linarith
  · intro v
    have hd := AronowAudit.P015.likelihood_directional_derivative_calculus
      AronowAudit.P015.probitW (fun _ => 8) AronowAudit.P015.probitSuccess
      AronowAudit.P015.normalCDF ![0, 0, AronowAudit.P015.probitA] v
      (fun _ => (AronowAudit.P015.AnalyticCompletion.hasDerivAt_normalCDF _).differentiableAt)
      (fun _ => (AronowAudit.P015.AnalyticCompletion.normalCDF_bounds _).1)
      (fun _ => (AronowAudit.P015.AnalyticCompletion.normalCDF_bounds _).2)
    simpa only [AronowAudit.P015.AnalyticCompletion.scoreMultiplier_normalCDF] using hd

private theorem probit_score (hbern : wholeBernoulliScore) : wholeProbitScore := by
  have hm : ∀ η : ℝ, likelihoodMultiplier standardNormalCDF η = probitMultiplier η :=
    AronowAudit.P015.AnalyticCompletion.scoreMultiplier_normalCDF
  refine ⟨?_, hm, ?_, AronowAudit.P015.AnalyticCompletion.probitH_nonconstant,
    AronowAudit.P015.probit_multiplier_at_half, probit_example⟩
  · intro n K W Y hY hW θ
    have h := hbern n K W Y hY hW Set.univ isOpen_univ standardNormalCDF
      (fun η _ => (AronowAudit.P015.AnalyticCompletion.hasDerivAt_normalCDF η).differentiableAt.differentiableWithinAt)
      (fun η _ => AronowAudit.P015.AnalyticCompletion.normalCDF_bounds η) θ (by intro i; trivial)
    have he : likelihoodScore W (fun _ => 1) Y standardNormalCDF θ =
        fun j => ∑ i, W i j * probitMultiplier (W.mulVec θ i) *
          (Y i - standardNormalCDF (W.mulVec θ i)) := by
      ext j
      simp only [likelihoodScore, hm, one_mul]
    rw [← he]
    exact h.1
  · intro η
    exact div_pos (AronowAudit.P015.AnalyticCompletion.normalPDF_pos η)
      (mul_pos (AronowAudit.P015.AnalyticCompletion.normalCDF_bounds η).1
        (sub_pos.mpr (AronowAudit.P015.AnalyticCompletion.normalCDF_bounds η).2))

private theorem square_link_example : T7Statement := by
  apply Bridge.T7_correspondence.mpr
  refine ⟨AronowAudit.P015.RootLinkCounterexample_checked, ?_, ?_,
    AronowAudit.P015.RootPotentialCompletion.unit_D_integrable, ?_⟩
  · intro θ
    refine ⟨rfl, ?_⟩
    intro i
    simp [AronowAudit.P015.rootZ, AronowAudit.P015.rootE, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · intro α β γ
    refine ⟨![α + β / 2, β, γ + β / 4], ?_⟩
    ext j
    fin_cases j <;> simp
  · intro a ε
    exact AronowAudit.P015.RootPotentialCompletion.unitY_integrable
      AronowAudit.P015.rootUnitLaw a ε AronowAudit.P015.rootUnitD measurable_fst.snd

/-- Assembly of all clauses; only the four explicitly named mathematical leaves remain. -/
theorem T8_assembly (h1 : T8_L1) (h2 : T8_L2) (h3 : T8_L3) (h4 : T8_L4) :
    T8WholeStatement := by
  have hb := bernoulli_score h1
  refine ⟨hb, logistic_score, canonical_score h1, canonical_mean h2,
    AronowAudit.P015.Wave1.canonical_named_model_means, probit_score hb,
    h3, linearization, square_link_example, h4, ?_⟩
  norm_num [finiteCoxScore, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end
end SAP.P015a.WH.W1
