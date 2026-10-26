import AronowAudit.P046.P046_Audit

namespace AronowAudit.P046.Wave1

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

lemma population_criterion_borel_version (M : Study) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable (fun o => g (W o)) M.law) :
    ∃ g0 : ℝ → ℝ, Measurable g0 ∧
      (fun o => g (W o)) =ᵐ[M.law] (fun o => g0 (W o)) := by
  classical
  let H := hg.aemeasurable.mk (fun o => g (W o))
  have mH : Measurable H := hg.aemeasurable.measurable_mk
  let N := toMeasurable M.law {o | g (W o) ≠ H o}
  have mN : MeasurableSet N := measurableSet_toMeasurable _ _
  have zN : M.law N = 0 := by
    rw [measure_toMeasurable]
    have heq : (fun o => g (W o)) =ᵐ[M.law] H := hg.aemeasurable.ae_eq_mk
    simpa only [Filter.EventuallyEq, ae_iff] using heq
  let D : ℝ → ℝ := fun w => ∑ b : Bool × (Bool × Bool), if (w, b) ∈ N then 0 else 1
  let A : ℝ → ℝ := fun w => ∑ b : Bool × (Bool × Bool), if (w, b) ∈ N then 0 else H (w, b)
  have mD : Measurable D := by
    apply Finset.measurable_sum
    intro b hb
    exact Measurable.ite (mN.preimage (measurable_id.prodMk measurable_const))
      measurable_const measurable_const
  have mA : Measurable A := by
    apply Finset.measurable_sum
    intro b hb
    exact Measurable.ite (mN.preimage (measurable_id.prodMk measurable_const))
      measurable_const (mH.comp (measurable_id.prodMk measurable_const))
  refine ⟨fun w => A w / D w, mA.div mD, ?_⟩
  filter_upwards [show ∀ᵐ o ∂M.law, o ∉ N from by simpa [ae_iff] using zN] with o ho
  have hD : 0 < D (W o) := by
    apply Finset.sum_pos'
    · intro b hb
      split_ifs <;> norm_num
    · exact ⟨o.2, Finset.mem_univ _, by simpa [W, ho]⟩
  have hA : A (W o) = g (W o) * D (W o) := by
    dsimp [A, D]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : (W o, b) ∈ N
    · simp [h]
    · have he : g (W o) = H (W o, b) := by
        by_contra hn
        exact h (subset_toMeasurable M.law _ hn)
      simp [h, he]
  rw [hA, mul_div_cancel_right₀ _ hD.ne']

lemma risk_expansion_q_bounds (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, 0 ≤ q M (W o) ∧ q M (W o) ≤ M.delta⁻¹ := by
  filter_upwards [hM.positivity] with o ho
  have hp : 0 < M.pi (W o) := lt_trans hM.delta_pos ho.1
  have hp1 : M.pi (W o) < 1 := by linarith [hM.delta_pos]
  refine ⟨div_nonneg (by linarith) hp.le, ?_⟩
  calc
    q M (W o) ≤ (M.pi (W o))⁻¹ := by
      dsimp [q]
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hp.le
    _ ≤ M.delta⁻¹ := (inv_le_inv₀ hp hM.delta_pos).2 ho.1.le

lemma risk_expansion_q_measurable (M : Study) (hM : ValidStudy M) :
    Measurable (fun o => q M (W o)) :=
  (measurable_const.sub (hM.measurable_pi.comp measurable_fst)).div
    (hM.measurable_pi.comp measurable_fst)

lemma risk_expansion_y_memLp (M : Study) (hM : ValidStudy M) : MemLp Y1 2 M.law := by
  letI := hM.probability
  apply MemLp.of_bound ((measurable_of_countable bit).comp
    measurable_snd.snd.snd).aestronglyMeasurable 1
  exact ae_of_all _ (fun o => by cases h : o.2.2.2 <;> simp [Y1, bit, h])

lemma risk_expansion_weighted_integrable (M : Study) (hM : ValidStudy M)
    {f : Unit → ℝ} (hf : Integrable f M.law) :
    Integrable (fun o => q M (W o) * f o) M.law := by
  apply hf.bdd_mul (risk_expansion_q_measurable M hM).aestronglyMeasurable
  filter_upwards [risk_expansion_q_bounds M hM] with o ho
  simpa only [Real.norm_eq_abs, abs_of_nonneg ho.1] using ho.2

lemma risk_expansion_sqrt_memLp (M : Study) (hM : ValidStudy M)
    {f : Unit → ℝ} (hf : MemLp f 2 M.law) :
    MemLp (fun o => Real.sqrt (q M (W o)) * f o) 2 M.law := by
  apply (memLp_two_iff_integrable_sq
    (((risk_expansion_q_measurable M hM).sqrt.aestronglyMeasurable).mul
      hf.aestronglyMeasurable)).2
  apply (risk_expansion_weighted_integrable M hM hf.integrable_sq).congr
  filter_upwards [risk_expansion_q_bounds M hM] with o ho
  simp [mul_pow, Real.sq_sqrt ho.1]

lemma risk_expansion_integral_cauchy {α : Type*} [MeasurableSpace α] (P : Measure α)
    (f h : α → ℝ) (hf : MemLp f 2 P) (hh : MemLp h 2 P) :
    |∫ o, f o * h o ∂P| ≤ Real.sqrt ((∫ o, (f o)^2 ∂P) * (∫ o, (h o)^2 ∂P)) := by
  have heq (u v : α → ℝ) (hu : MemLp u 2 P) (hv : MemLp v 2 P) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ o, u o * v o ∂P := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with o ho ho'
    simp [ho, ho', mul_comm]
  have hc := real_inner_mul_inner_self_le (hf.toLp f) (hh.toLp h)
  rw [heq f h hf hh, heq f f hf hf, heq h h hh hh] at hc
  simp only [← sq] at hc
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using hc

lemma population_criterion_integral_transfer (M : Study) (hM : ValidStudy M)
    (f b c : Unit → ℝ) (mf : StronglyMeasurable[covariateSigma] f)
    (hf : Integrable f M.law) (mb : Measurable b) (mc : Measurable c)
    (bb : ∀ᵐ o ∂M.law, ‖b o‖ ≤ 1) (bc : ∀ᵐ o ∂M.law, ‖c o‖ ≤ 1)
    (hbc : condExp covariateSigma M.law b =ᵐ[M.law]
      condExp covariateSigma M.law c) :
    (∫ o, f o * b o ∂M.law) = ∫ o, f o * c o ∂M.law := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have hb : Integrable b M.law :=
    memLp_one_iff_integrable.1 (MemLp.of_bound mb.aestronglyMeasurable 1 bb)
  have hc : Integrable c M.law :=
    memLp_one_iff_integrable.1 (MemLp.of_bound mc.aestronglyMeasurable 1 bc)
  have hfb : Integrable (f * b) M.law := hf.mul_bdd mb.aestronglyMeasurable bb
  have hfc : Integrable (f * c) M.law := hf.mul_bdd mc.aestronglyMeasurable bc
  calc
    _ = ∫ o, condExp covariateSigma M.law (f * b) o ∂M.law := (integral_condExp hm).symm
    _ = ∫ o, f o * condExp covariateSigma M.law b o ∂M.law :=
      integral_congr_ae (condExp_mul_of_stronglyMeasurable_left mf hfb hb)
    _ = ∫ o, f o * condExp covariateSigma M.law c o ∂M.law :=
      integral_congr_ae (hbc.mono (fun o ho => by dsimp only; rw [ho]))
    _ = ∫ o, condExp covariateSigma M.law (f * c) o ∂M.law :=
      (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left mf hfc hc)).symm
    _ = _ := integral_condExp hm

lemma population_criterion_transfer (M : Study) (hM : ValidStudy M)
    (f : ℝ → ℝ) (mf : Measurable f) (hf : Integrable (fun o => f (W o)) M.law) :
    (∫ o, f (W o) * X o ∂M.law) = (∫ o, f (W o) * M.pi (W o) ∂M.law) ∧
    (∫ o, f (W o) * (X o * Y1 o) ∂M.law) =
      ∫ o, f (W o) * (M.pi (W o) * Y1 o) ∂M.law := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have mx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  have my : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  have mp : Measurable (fun o => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have sp : StronglyMeasurable[covariateSigma] (fun o => M.pi (W o)) :=
    (hM.measurable_pi.comp (comap_measurable W)).stronglyMeasurable
  have sf : StronglyMeasurable[covariateSigma] (fun o => f (W o)) :=
    (mf.comp (comap_measurable W)).stronglyMeasurable
  have bx : ∀ᵐ o ∂M.law, ‖X o‖ ≤ 1 := ae_of_all _ (fun o => by
    cases h : o.2.1 <;> simp [X, bit, h])
  have by1 : ∀ᵐ o ∂M.law, ‖Y1 o‖ ≤ 1 := ae_of_all _ (fun o => by
    cases h : o.2.2.2 <;> simp [Y1, bit, h])
  have bp : ∀ᵐ o ∂M.law, ‖M.pi (W o)‖ ≤ 1 := by
    filter_upwards [hM.positivity] with o ho
    rw [Real.norm_eq_abs, abs_of_pos (lt_trans hM.delta_pos ho.1)]
    linarith [hM.delta_pos]
  have bxy : ∀ᵐ o ∂M.law, ‖X o * Y1 o‖ ≤ 1 := by
    filter_upwards [bx, by1] with o hx hy
    simpa using mul_le_mul hx hy (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have bpy : ∀ᵐ o ∂M.law, ‖M.pi (W o) * Y1 o‖ ≤ 1 := by
    filter_upwards [bp, by1] with o hp hy
    simpa using mul_le_mul hp hy (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hy : Integrable Y1 M.law :=
    memLp_one_iff_integrable.1 (MemLp.of_bound my.aestronglyMeasurable 1 by1)
  have hpy : Integrable ((fun o => M.pi (W o)) * Y1) M.law :=
    hy.bdd_mul mp.aestronglyMeasurable bp
  have hce : condExp covariateSigma M.law (fun o => X o * Y1 o) =ᵐ[M.law]
      condExp covariateSigma M.law (fun o => M.pi (W o) * Y1 o) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left sp hpy hy
    filter_upwards [conditional_xy_factorization M hM, hpull, hM.regression] with o hx hp hy
    change condExp covariateSigma M.law (fun o => M.pi (W o) * Y1 o) o =
      M.pi (W o) * condExp covariateSigma M.law Y1 o at hp
    rw [hy] at hp
    exact hx.trans hp.symm
  constructor
  · apply population_criterion_integral_transfer M hM _ _ _ sf hf mx mp bx bp
    rw [condExp_of_stronglyMeasurable hm sp
      (memLp_one_iff_integrable.1 (MemLp.of_bound mp.aestronglyMeasurable 1 bp))]
    exact hM.propensity
  · exact population_criterion_integral_transfer M hM _ _ _ sf hf (mx.mul my)
      (mp.mul my) bxy bpy hce

lemma population_criterion_k_bound (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, ‖(1 - M.pi (W o)) / (M.pi (W o))^2‖ ≤ M.delta⁻¹^2 := by
  filter_upwards [hM.positivity, risk_expansion_q_bounds M hM] with o ho hq
  have hp : 0 < M.pi (W o) := lt_trans hM.delta_pos ho.1
  have he : (1 - M.pi (W o)) / (M.pi (W o))^2 = q M (W o) * (M.pi (W o))⁻¹ := by
    dsimp [q]; ring
  rw [he, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq.1 (inv_nonneg.2 hp.le))]
  simpa only [sq] using mul_le_mul hq.2 ((inv_le_inv₀ hp hM.delta_pos).2 ho.1.le)
    (inv_nonneg.2 hp.le) (inv_nonneg.2 hM.delta_pos.le)

lemma population_criterion_reduce (M : Study) (hM : ValidStudy M)
    (f : ℝ → ℝ) (mf : Measurable f) (hf : Integrable (fun o => f (W o)) M.law) :
    (∫ o, ((1 - M.pi (W o)) / (M.pi (W o))^2 * f (W o)) * X o ∂M.law) =
      (∫ o, q M (W o) * f (W o) ∂M.law) ∧
    (∫ o, ((1 - M.pi (W o)) / (M.pi (W o))^2 * f (W o)) * (X o * Y1 o) ∂M.law) =
      ∫ o, q M (W o) * f (W o) * Y1 o ∂M.law := by
  have mk : Measurable (fun w => (1 - M.pi w) / (M.pi w)^2) :=
    (measurable_const.sub hM.measurable_pi).div (hM.measurable_pi.pow_const 2)
  have hi : Integrable (fun o => (1 - M.pi (W o)) / (M.pi (W o))^2 * f (W o)) M.law :=
    hf.bdd_mul (mk.comp measurable_fst).aestronglyMeasurable (population_criterion_k_bound M hM)
  have ht := population_criterion_transfer M hM _ (mk.mul mf) hi
  have heq : ∀ᵐ o ∂M.law,
      ((1 - M.pi (W o)) / (M.pi (W o))^2 * f (W o)) * M.pi (W o) =
        q M (W o) * f (W o) := by
    filter_upwards [hM.positivity] with o ho
    have hp : M.pi (W o) ≠ 0 := ne_of_gt (lt_trans hM.delta_pos ho.1)
    dsimp [q]
    field_simp
  refine ⟨ht.1.trans (integral_congr_ae heq), ht.2.trans (integral_congr_ae ?_)⟩
  filter_upwards [heq] with o ho
  simpa only [Pi.mul_apply, mul_assoc] using congrArg (fun z => z * Y1 o) ho

lemma population_criterion_borel (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    (∫ o, X o * (1 - M.pi (W o)) / (M.pi (W o))^2 * (Y o - g (W o))^2 ∂M.law) =
      risk M g := by
  letI := hM.probability
  let k : ℝ → ℝ := fun w => (1 - M.pi w) / (M.pi w)^2
  have mk : Measurable k :=
    (measurable_const.sub hM.measurable_pi).div (hM.measurable_pi.pow_const 2)
  have ik {f : Unit → ℝ} (hf : Integrable f M.law) :
      Integrable (fun o => k (W o) * f o) M.law :=
    hf.bdd_mul (mk.comp measurable_fst).aestronglyMeasurable (population_criterion_k_bound M hM)
  have mx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  have my : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  have bm {f : Unit → ℝ} (hf : Integrable f M.law) :
      Integrable (fun o => f o * X o) M.law ∧ Integrable (fun o => f o * (X o * Y1 o)) M.law := by
    constructor
    · apply hf.mul_bdd (c := 1) mx.aestronglyMeasurable
      exact ae_of_all _ (fun o => by cases h : o.2.1 <;> simp [X, bit, h])
    · apply hf.mul_bdd (c := 1) (mx.mul my).aestronglyMeasurable
      exact ae_of_all _ (fun o => by
        cases hx : o.2.1 <;> cases hy : o.2.2.2 <;> simp [X, Y1, bit, hx, hy])
  have ig := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hg
  have i0 : Integrable (fun o => k (W o)) M.law := by simpa using ik (integrable_const (1 : ℝ))
  have iA := (bm i0).2
  have iB := (bm (ik ig)).2
  have iC := (bm (ik hg.integrable_sq)).1
  have hy := risk_expansion_y_memLp M hM
  have iA' := risk_expansion_weighted_integrable M hM hy.integrable_sq
  have iB' : Integrable (fun o => q M (W o) * g (W o) * Y1 o) M.law := by
    simpa only [Pi.mul_apply, mul_assoc] using
      risk_expansion_weighted_integrable M hM (hg.integrable_mul hy)
  have iC' := risk_expansion_weighted_integrable M hM hg.integrable_sq
  have iAB : Integrable (fun o => k (W o) * (X o * Y1 o) -
      2 * ((k (W o) * g (W o)) * (X o * Y1 o))) M.law := by
    exact iA.sub' (iB.const_mul 2)
  have iAB' : Integrable (fun o => q M (W o) * (Y1 o)^2 -
      2 * (q M (W o) * g (W o) * Y1 o)) M.law := by
    exact iA'.sub' (iB'.const_mul 2)
  have h0 := (population_criterion_reduce M hM (fun _ => 1) measurable_const (integrable_const 1)).2
  simp only [mul_one] at h0
  have h1 := (population_criterion_reduce M hM g mg ig).2
  have h2 := (population_criterion_reduce M hM (fun w => (g w)^2) (mg.pow_const 2) hg.integrable_sq).1
  have hy2 : (fun o => q M (W o) * Y1 o) = (fun o => q M (W o) * (Y1 o)^2) := by
    funext o
    cases h : o.2.2.2 <;> simp [Y1, bit, h]
  rw [hy2] at h0
  have hl : (fun o => X o * (1 - M.pi (W o)) / (M.pi (W o))^2 * (Y o - g (W o))^2) =
      (fun o => k (W o) * (X o * Y1 o) -
        2 * ((k (W o) * g (W o)) * (X o * Y1 o)) + (k (W o) * (g (W o))^2) * X o) := by
    funext o
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> cases y1 <;> simp [k, X, Y, Y0, Y1, bit, div_eq_mul_inv] <;> ring
  have hr : (fun o => q M (W o) * (Y1 o - g (W o))^2) =
      (fun o => q M (W o) * (Y1 o)^2 - 2 * (q M (W o) * g (W o) * Y1 o) +
        q M (W o) * (g (W o))^2) := by funext o; ring
  unfold risk
  rw [hl, hr, integral_add iAB iC, integral_sub iA (iB.const_mul 2), integral_const_mul,
    integral_add iAB' iC', integral_sub iA' (iB'.const_mul 2), integral_const_mul]
  change _ - 2 * _ + _ = _ - 2 * _ + _
  rw [h0, h1, h2]

/-- The treated-case population criterion equals the weighted population risk. -/
theorem population_weighted_criterion_proof (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    (∫ o, X o * (1 - M.pi (W o)) / (M.pi (W o))^2 * (Y o - g (W o))^2 ∂M.law) =
      risk M g := by
  obtain ⟨g0, mg0, heq⟩ := population_criterion_borel_version M g hg.aestronglyMeasurable
  have hg0 : MemLp (fun o => g0 (W o)) 2 M.law := hg.ae_eq heq
  calc
    _ = ∫ o, X o * (1 - M.pi (W o)) / (M.pi (W o))^2 * (Y o - g0 (W o))^2 ∂M.law := by
      apply integral_congr_ae
      filter_upwards [heq] with o ho
      rw [ho]
    _ = risk M g0 := population_criterion_borel M hM g0 mg0 hg0
    _ = risk M g := by
      apply integral_congr_ae
      filter_upwards [heq] with o ho
      rw [ho]

/-- Weighted risk expansion and Cauchy--Schwarz with finite second moments. -/
theorem risk_expansion_cauchy_proof (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    risk M g - risk M (fun _ => 0) =
      -2 * (∫ o, q M (W o) * Y1 o * g (W o) ∂M.law) + weightedNormSq M g ∧
    |∫ o, q M (W o) * Y1 o * g (W o) ∂M.law| ≤
      Real.sqrt ((∫ o, q M (W o) * (Y1 o)^2 ∂M.law) * weightedNormSq M g) := by
  have hy := risk_expansion_y_memLp M hM
  have iy := risk_expansion_weighted_integrable M hM hy.integrable_sq
  have ig := risk_expansion_weighted_integrable M hM hg.integrable_sq
  have ic : Integrable (fun o => q M (W o) * Y1 o * g (W o)) M.law := by
    simpa only [mul_assoc, Pi.mul_apply] using
      risk_expansion_weighted_integrable M hM (hy.integrable_mul hg)
  constructor
  · have heq : (fun o => q M (W o) * (Y1 o - g (W o))^2) =
        (fun o => q M (W o) * (Y1 o)^2 - 2 * (q M (W o) * Y1 o * g (W o)) +
          q M (W o) * (g (W o))^2) := by funext o; ring
    unfold risk weightedNormSq
    simp only [sub_zero]
    have isub : Integrable (fun o => q M (W o) * (Y1 o)^2 -
        2 * (q M (W o) * Y1 o * g (W o))) M.law := by
      exact iy.sub' (ic.const_mul 2)
    rw [heq, integral_add isub ig, integral_sub iy (ic.const_mul 2), integral_const_mul]
    ring
  · have hc := risk_expansion_integral_cauchy M.law
      (fun o => Real.sqrt (q M (W o)) * Y1 o)
      (fun o => Real.sqrt (q M (W o)) * g (W o))
      (risk_expansion_sqrt_memLp M hM hy) (risk_expansion_sqrt_memLp M hM hg)
    have hprod : (fun o => (Real.sqrt (q M (W o)) * Y1 o) *
        (Real.sqrt (q M (W o)) * g (W o))) =ᵐ[M.law]
        (fun o => q M (W o) * Y1 o * g (W o)) := by
      filter_upwards [risk_expansion_q_bounds M hM] with o ho
      calc
        _ = (Real.sqrt (q M (W o)))^2 * (Y1 o * g (W o)) := by ring
        _ = _ := by rw [Real.sq_sqrt ho.1]; ring
    have hsq (f : Unit → ℝ) : (fun o => (Real.sqrt (q M (W o)) * f o)^2) =ᵐ[M.law]
        (fun o => q M (W o) * (f o)^2) := by
      filter_upwards [risk_expansion_q_bounds M hM] with o ho
      rw [mul_pow, Real.sq_sqrt ho.1]
    rw [integral_congr_ae hprod, integral_congr_ae (hsq Y1),
      integral_congr_ae (hsq (fun o => g (W o)))] at hc
    exact hc

end
end AronowAudit.P046.Wave1
