import SAP.P001a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001
open AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W2.P.T12_L2

theorem cp_equiv_donor {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) :
    SAP.P001a.CP μ Z c ↔ AronowAudit.P001.CP μ Z c := by
  constructor <;> intro h ε hε
  · simpa [SAP.P001a.CP, SAP.P001a.prob, AronowAudit.P001.CP,
      AronowAudit.P001.prob] using h ε hε
  · simpa [SAP.P001a.CP, SAP.P001a.prob, AronowAudit.P001.CP,
      AronowAudit.P001.prob] using h ε hε

theorem cp_of_bad_event_and_control {Ω E F : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → E) (z : E) (bad : ℝ → ℕ → Set Ω)
    (A : ℕ → Ω → F) (a : F)
    (hbad : ∀ β : ℝ, 0 < β →
      Tendsto (fun n => prob μ (bad β n)) atTop (nhds 0))
    (hA : CP μ A a)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ β : ℝ, 0 < β ∧ ∃ α : ℝ, 0 < α ∧
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ω ∉ bad α n → dist (A n ω) a < β → dist (Z n ω) z < ε) :
    CP μ Z z := by
  intro ε hε
  obtain ⟨β, hβ, α, hα, hl⟩ := hlocal ε hε
  have hbound : ∀ᶠ n in atTop,
      prob μ {ω | ε ≤ dist (Z n ω) z} ≤
        prob μ (bad α n) + prob μ {ω | β ≤ dist (A n ω) a} := by
    filter_upwards [hl] with n hn
    calc
      _ ≤ prob μ (bad α n ∪ {ω | β ≤ dist (A n ω) a}) := by
        apply ENNReal.toReal_mono (measure_ne_top μ _)
        apply measure_mono_ae
        filter_upwards [hn] with ω hω
        intro hz
        by_contra h
        have hgood : ω ∉ bad α n := by
          intro hb
          exact h (Or.inl hb)
        have hsmall : dist (A n ω) a < β := by
          exact lt_of_not_ge (fun hh => h (Or.inr hh))
        exact (not_lt_of_ge hz) (hω hgood hsmall)
      _ ≤ _ := measureReal_union_le _ _
  exact squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hbound
    (by simpa only [zero_add] using (hbad α hα).add (hA β hβ))

theorem scoreMatrix_cp_of_hessianUniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hdiff : ∀ᵐ ω ∂μ, ∀ i, ContDiffOn ℝ 2
      (fun t => Real.log (g (Y i ω) (X i ω) t)) (Metric.ball θ δ))
    (I : Matrix (Fin τ) (Fin τ) ℝ)
    (hHinfo : populationHessian μ (X 0) (Y 0) g θ = -I)
    (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) g) θ)
    (hHuniform : W2HessianCP μ X Y g (Metric.ball θ δ))
    (that : ℕ → Ω → Fin τ → ℝ) (hconsistent : CP μ that θ)
    (hzero : ∀ n, ∀ᵐ ω ∂μ, that n ω ∈ Metric.ball θ δ →
      DecideB_sampleScore X Y g n ω (that n ω) = 0) :
    CP μ (fun n ω => DecideB_scoreMatrix I
      (DecideB_sampleScore X Y g n ω θ) (that n ω - θ)) I := by
  let bad (b : ℝ) (n : ℕ) : Set Ω :=
    {ω | ∃ tjk : (Fin τ → ℝ) × Fin τ × Fin τ,
      tjk.1 ∈ Metric.ball θ δ ∧
        b ≤ |sampleHessian X Y g n ω tjk.1 tjk.2.1 tjk.2.2 -
          populationHessian μ (X 0) (Y 0) g tjk.1 tjk.2.1 tjk.2.2|}
  apply cp_of_bad_event_and_control μ _ I bad that θ
  · intro b hb
    simpa [bad, W2HessianCP, W2UniformCP] using hHuniform b hb
  · exact hconsistent
  · intro ε hε
    let b : ℝ := ε / (4 * ((τ : ℝ) + 1))
    have hb : 0 < b := by dsimp [b]; positivity
    obtain ⟨r, hr, hc⟩ := Metric.continuousAt_iff.mp hHcont b hb
    let ρ : ℝ := min r δ
    have hρ : 0 < ρ := lt_min hr hδ
    refine ⟨ρ, hρ, b, hb, Eventually.of_forall (fun n => ?_)⟩
    filter_upwards [hdiff, hzero n] with ω hω hz
    intro hbadω ht
    have hsmall : that n ω ∈ Metric.ball θ ρ := ht
    have hsub : Metric.ball θ ρ ⊆ Metric.ball θ δ :=
      Metric.ball_subset_ball (min_le_right r δ)
    have hs : DecideB_sampleScore X Y g n ω (that n ω) = 0 := hz (hsub hsmall)
    have hdiff' (i : ℕ) : ContDiffOn ℝ 2
        (fun t => Real.log (g (Y i ω) (X i ω) t)) (Metric.ball θ ρ) :=
      (hω i).mono hsub
    have hJ (t : Fin τ → ℝ) (htt : t ∈ Metric.ball θ ρ) (j k : Fin τ) :
        |fderiv ℝ (fun u => DecideB_sampleScore X Y g n ω u j) t (Pi.single k 1) -
          (-I) j k| ≤ 2 * b := by
      rw [← DecideB_sampleHessian_eq_fderiv X Y g n ω (Metric.ball θ ρ)
        Metric.isOpen_ball hdiff' t htt j k]
      have hpop :
          |populationHessian μ (X 0) (Y 0) g t j k - (-I) j k| < b := by
        have hc' := hc (lt_of_lt_of_le htt (min_le_left r δ))
        rw [hHinfo, dist_eq_norm] at hc'
        exact lt_of_le_of_lt
          ((norm_le_pi_norm ((populationHessian μ (X 0) (Y 0) g t - -I) j) k).trans
            (norm_le_pi_norm (populationHessian μ (X 0) (Y 0) g t - -I) j)) hc'
      have hsample :
          |sampleHessian X Y g n ω t j k -
            populationHessian μ (X 0) (Y 0) g t j k| < b := by
        apply lt_of_not_ge
        intro hge
        apply hbadω
        exact ⟨(t, j, k), hsub htt, hge⟩
      calc
        _ ≤ |sampleHessian X Y g n ω t j k -
              populationHessian μ (X 0) (Y 0) g t j k| +
            |populationHessian μ (X 0) (Y 0) g t j k - (-I) j k| := abs_sub_le _ _ _
        _ ≤ b + b := add_le_add hsample.le hpop.le
        _ = 2 * b := by ring
    have hrem := DecideB_gradient_remainder_bound (DecideB_sampleScore X Y g n ω) (-I)
      (Metric.ball θ ρ) (convex_ball θ ρ) θ (that n ω) (Metric.mem_ball_self hρ) hsmall
      (fun t htt j => ((DecideB_sampleScore_contDiffOn X Y g n ω _
        Metric.isOpen_ball hdiff' j).differentiableOn (by norm_num)).differentiableAt
          (Metric.isOpen_ball.mem_nhds htt))
      (2 * b) (by positivity) hJ
    have hrem' :
        ‖DecideB_sampleScore X Y g n ω θ - I *ᵥ (that n ω - θ)‖ ≤
          ((τ : ℝ) * (2 * b)) * ‖that n ω - θ‖ := by
      rw [hs, zero_sub, Matrix.neg_mulVec, sub_neg_eq_add] at hrem
      convert hrem using 1
      rw [← norm_neg]
      congr 1
      abel
    have hcorr := DecideB_scoreMatrix_bound I
      (DecideB_sampleScore X Y g n ω θ) (that n ω - θ)
      ((τ : ℝ) * (2 * b)) (by positivity) hrem'
    rw [dist_eq_norm]
    have hnorm :
        ‖DecideB_scoreMatrix I (DecideB_sampleScore X Y g n ω θ)
          (that n ω - θ) - I‖ ≤ (τ : ℝ) * (2 * b) := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro j
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro k
      exact hcorr j k
    apply lt_of_le_of_lt hnorm
    dsimp [b]
    have htau : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
    field_simp
    nlinarith

theorem local_score_normal_limit_uniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hg : ∀ t ∈ Metric.ball θ δ,
      Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
    (hfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) S = 1)
    (hdiff : ∀ xy ∈ S, ContDiffOn ℝ 2
      (fun t => Real.log (g xy.2 xy.1 t)) (Metric.ball θ δ))
    (hs2 : ∀ j, MemLp (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) 2 μ)
    (hs0 : ∀ j, mean μ (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) = 0)
    (hinfo : (informationMatrix μ (X 0) (Y 0) g θ).PosDef)
    (hHinfo : populationHessian μ (X 0) (Y 0) g θ =
      -informationMatrix μ (X 0) (Y 0) g θ)
    (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) g) θ)
    (hHuniform : W2HessianCP μ X Y g (Metric.ball θ δ))
    (that : ℕ → Ω → Fin τ → ℝ)
    (hmeas : ∀ n, Measurable (that n)) (hconsistent : CP μ that θ)
    (hzero : ∀ n, ∀ᵐ ω ∂μ, that n ω ∈ Metric.ball θ δ →
      DecideB_sampleScore X Y g n ω (that n ω) = 0) :
    WeakLimit μ (fun n ω => Real.sqrt n • (that n ω - θ))
      (normalVectorLaw (informationMatrix μ (X 0) (Y 0) g θ)⁻¹) := by
  let I := informationMatrix μ (X 0) (Y 0) g θ
  let s : ℕ → Ω → Fin τ → ℝ :=
    fun i ω => DecideB_scoreVersion g S θ (X i ω, Y i ω)
  have hm : Measurable (DecideB_scoreVersion g S θ) :=
    DecideB_scoreVersion_measurable g S hS (Metric.ball θ δ) Metric.isOpen_ball θ
      (Metric.mem_ball_self hδ) hg hdiff
  obtain ⟨hsiid, heq⟩ := DecideB_scoreVersion_iid μ X Y hiid g S hS hfull θ hm
  have hs (j : Fin τ) : (fun ω => s 0 ω j) =ᵐ[μ]
      (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) := by
    filter_upwards [heq] with ω hω
    exact congrFun (hω 0) j
  have h2 (j : Fin τ) : MemLp (fun ω => s 0 ω j) 2 μ :=
    (memLp_congr_ae (hs j)).mpr (hs2 j)
  have h0 (j : Fin τ) : mean μ (fun ω => s 0 ω j) = 0 :=
    (integral_congr_ae (hs j)).trans (hs0 j)
  have hcov (j k : Fin τ) : I j k = mean μ (fun ω => s 0 ω j * s 0 ω k) := by
    apply integral_congr_ae
    filter_upwards [hs j, hs k] with ω hj hk
    rw [hj, hk]
  let q : ℕ → Ω → Fin τ → ℝ := fun n ω => DecideB_sampleScore X Y g n ω θ
  let v : ℕ → Ω → Fin τ → ℝ := fun n ω => that n ω - θ
  let B : ℕ → Ω → Matrix (Fin τ) (Fin τ) ℝ := fun n ω =>
    DecideB_scoreMatrix I (q n ω) (v n ω)
  have hqm (n : ℕ) : AEMeasurable (q n) μ := by
    have hm' : Measurable (fun ω => fun j =>
        (∑ i ∈ Finset.range n, s i ω j) / (n : ℝ)) := by
      apply measurable_pi_lambda
      intro j
      exact (Finset.measurable_sum _ (fun i _ =>
        (measurable_pi_apply j).comp (hsiid.1 i))).div_const _
    apply hm'.aemeasurable.congr
    filter_upwards [heq] with ω hω
    ext j
    change (∑ i ∈ Finset.range n, s i ω j) / (n : ℝ) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hω i) j
  have hvm (n : ℕ) : AEMeasurable (v n) μ :=
    (hmeas n).aemeasurable.sub_const θ
  have hBm (n : ℕ) : AEMeasurable (B n) μ :=
    (DecideB_scoreMatrix_measurable I).comp_aemeasurable ((hqm n).prodMk (hvm n))
  have hconsistentA : AronowAudit.P001.CP μ that θ :=
    (cp_equiv_donor μ that θ).mp hconsistent
  have hvA : AronowAudit.P001.CP μ v 0 := by
    simpa only [v, sub_self] using probability_convergence_continuous_at μ that θ
      (fun t => t - θ) hconsistentA (continuous_id.sub continuous_const).continuousAt
  have hv : SAP.P001a.CP μ v 0 := (cp_equiv_donor μ v 0).mpr hvA
  have hdiffae : ∀ᵐ ω ∂μ, ∀ i, ContDiffOn ℝ 2
      (fun t => Real.log (g (Y i ω) (X i ω) t)) (Metric.ball θ δ) := by
    filter_upwards [DecideB_ae_all_mem μ _ hiid S hS hfull] with ω hω
    exact fun i => hdiff _ (hω i)
  have hB : CP μ B I := scoreMatrix_cp_of_hessianUniform μ X Y g θ δ hδ
    hdiffae I hHinfo hHcont hHuniform that hconsistent hzero
  have hBd : AronowAudit.P001.CP μ B I := (cp_equiv_donor μ B I).mp hB
  have hlinear (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖v n ω‖ < δ → B n ω *ᵥ v n ω = q n ω := by
    filter_upwards [hzero n] with ω hω
    intro hvδ
    by_cases hv0 : v n ω = 0
    · have ht : that n ω = θ := sub_eq_zero.mp hv0
      have hq0 : q n ω = 0 := by
        have hz := hω (by simpa only [ht] using Metric.mem_ball_self hδ)
        simpa only [q, ht] using hz
      simp only [hv0, Matrix.mulVec_zero, hq0]
    · exact DecideB_scoreMatrix_mulVec I (q n ω) (v n ω) hv0
  apply DecideB_linearized_normal_limit μ v q hvm hvA I hinfo B hBm hBd δ hδ hlinear
  have hclt := DecideB_inverse_information_clt μ s hsiid h2 h0 I hinfo hcov
  apply hclt.congr _ (Filter.EventuallyEq.refl _ _)
  intro n
  filter_upwards [heq] with ω hω
  congr 1
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, q, DecideB_sampleScore]
  have he : (∑ i ∈ Finset.range n, s i ω j) =
      ∑ i ∈ Finset.range n, AronowAudit.P001.modelScore g
        (Y i ω) (X i ω) θ j := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hω i) j
  rw [he]
  calc
    _ = (Real.sqrt n / n) *
        (∑ i ∈ Finset.range n, AronowAudit.P001.modelScore g
          (Y i ω) (X i ω) θ j) := by
      rw [DecideB_sqrt_div_nat]
    _ = _ := by ring

end SAP.P001a.WH.W2.P.T12_L2

theorem SAP.P001a.WH.W2.T12_L2_proof : SAP.P001a.WH.W2.T12_L2 := by
  intro Ω hΩ μ hμ K τ X Y hiid g θ B R hconsistent
  have hzero : ∀ n, ∀ᵐ ω ∂μ,
      B.estimate n ω ∈ Metric.ball θ R.radius →
        DecideB_sampleScore X Y g n ω (B.estimate n ω) = 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      filter_upwards [] with ω
      intro _
      ext j
      simp [DecideB_sampleScore]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      filter_upwards [
        DecideB_ae_all_mem μ (fun i ω => (X i ω, Y i ω)) hiid
          R.regularSet R.measurable_set R.full,
        B.values n hnpos,
        B.maximizes n hnpos] with ω hω hv hm
      intro ht
      have hgood : W2LogGood X Y g B.parameterSet n ω := by
        intro t htΘ i hi
        exact R.positive (X i ω, Y i ω) (hω i) t htΘ
      exact DecideB_log_maximizer_score_zero X Y g n ω B.parameterSet
        (Metric.ball θ R.radius) Metric.isOpen_ball R.interior
        (fun i => R.smooth _ (hω i)) (B.estimate n ω) ht
        (fun t htΘ => hm hgood t htΘ)
  apply SAP.P001a.WH.W2.P.T12_L2.local_score_normal_limit_uniform
    μ X Y hiid g θ R.radius R.radius_pos
    (fun t ht => R.sections t (R.interior ht))
    R.regularSet R.measurable_set R.full R.smooth R.score_l2 R.score_centered
    R.information_positive R.information_identity R.hessian_continuous
    R.hessian_uniform B.estimate B.measurable hconsistent hzero

