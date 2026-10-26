import AronowAudit.P046.P046_Audit

namespace AronowAudit.P046.Wave1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

set_option maxHeartbeats 500000
set_option linter.style.haveILetI false

/-- Two populations coupled by the same covariate and assignment uniforms. -/
def proposition1_generate (p : ℝ) (b : Bool) (z : ℝ × ℝ) : Unit :=
  (z.1, (decide (z.2 ≤ p), (false, b)))

def proposition1_study (p : ℝ) (b : Bool) : Study :=
  ⟨(unitUniform.prod unitUniform).map (proposition1_generate p b),
    fun _ => p, fun _ => bit b, p / 2⟩

lemma proposition1_measurable_generate (p : ℝ) (b : Bool) :
    Measurable (proposition1_generate p b) :=
  measurable_fst.prodMk ((measurable_threshold Prod.snd (fun _ => p)
    measurable_snd measurable_const).prodMk (measurable_const.prodMk measurable_const))

lemma proposition1_valid (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (b : Bool) :
    ValidStudy (proposition1_study p b) ∧ mu (proposition1_study p b) = bit b := by
  let M := proposition1_study p b
  have mg := proposition1_measurable_generate p b
  have hprob : IsProbabilityMeasure M.law := by
    dsimp [M, proposition1_study]
    infer_instance
  letI := hprob
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have mw : Measurable W := measurable_fst
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := mw.comap_le
  have hw : M.law.map W = unitUniform := by
    dsimp [M, proposition1_study]
    rw [Measure.map_map mw mg]
    change (unitUniform.prod unitUniform).map Prod.fst = unitUniform
    simp
  have hy0 : Y0 =ᵐ[M.law] fun _ => (0 : ℝ) := by
    apply (ae_map_iff mg.aemeasurable (measurableSet_eq_fun my0 measurable_const)).2
    exact ae_of_all _ (fun _ => by simp [proposition1_generate, Y0, bit])
  have hy1 : Y1 =ᵐ[M.law] fun _ => bit b := by
    apply (ae_map_iff mg.aemeasurable (measurableSet_eq_fun my1 measurable_const)).2
    exact ae_of_all _ (fun _ => rfl)
  have hmu : mu M = bit b := by
    unfold mu
    rw [integral_congr_ae hy1, integral_const]
    simp
  refine ⟨?_, hmu⟩
  refine ⟨hprob, atomless_of_uniform_marginal M.law hw,
    measurable_const, measurable_const, by dsimp [M, proposition1_study]; positivity,
    ae_of_all _ (fun _ => ?_), ?_, ?_, ?_, ?_, ?_⟩
  · change p / 2 < p ∧ p < 1 - p / 2
    constructor <;> linarith
  · have mt := measurable_threshold id (fun _ : ℝ => p) measurable_id measurable_const
    have hi : IndepFun X W M.law := by
      apply (indepFun_map_iff (unitUniform.prod unitUniform) (proposition1_generate p b)
        X W mg mx mw).2
      simpa only [Function.comp_def, proposition1_generate, X, W, id_eq] using
        (indepFun_prod (μ := unitUniform) (ν := unitUniform)
          measurable_id (mb.comp mt)).symm
    have hxmean : (∫ o, X o ∂M.law) = p := by
      change (∫ o, X o ∂(unitUniform.prod unitUniform).map (proposition1_generate p b)) = p
      rw [integral_map mg.aemeasurable mx.aestronglyMeasurable]
      change (∫ z : ℝ × ℝ, bit (decide (z.2 ≤ p)) ∂unitUniform.prod unitUniform) = p
      rw [integral_fun_snd (fun u : ℝ => bit (decide (u ≤ p))),
        unitUniform_bernE p hp.le (by linarith) bit]
      simp [bernE, bit]
    have hind : Indep (MeasurableSpace.comap X inferInstance) covariateSigma M.law := hi
    have hc := condExp_indep_eq mx.comap_le hle (comap_measurable X).stronglyMeasurable hind
    change condExp covariateSigma M.law X =ᵐ[M.law] (fun _ => p)
    simpa only [hxmean] using hc
  · exact (condExp_congr_ae hy1).trans (by
      rw [condExp_const hle]
      rfl)
  · exact ae_of_all _ (fun _ => by cases b <;> norm_num [M, proposition1_study, bit])
  · exact condIndepFun_congr_left covariateSigma M.law hle Y0 (fun _ => 0) X
      my0 measurable_const mx hy0 (condIndepFun_const_left 0 X)
  · exact condIndepFun_congr_left covariateSigma M.law hle Y1 (fun _ => bit b) X
      my1 measurable_const mx hy1 (condIndepFun_const_left (bit b) X)

lemma proposition1_observe_measurable : Measurable observe := by
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  exact measurable_fst.prodMk ((((measurable_const.sub mx).mul my0).add (mx.mul my1)).prodMk mx)

/-- P046: impossibility of uniform consistency with unknown propensity.
The varying positivity constant allows treatment to become rare as the
adversarial sample size grows. -/
theorem proposition1_proof (est : ObservationalEstimator) (hmeas : ∀ n, Measurable (est n)) :
    ∃ eps > 0, ∃ c > 0, ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧ ∃ M : Study,
      ValidStudy M ∧ (sampleLaw M n
        {a | eps < |est n (fun i => observe (a i)) - mu M|}).toReal ≥ c := by
  classical
  refine ⟨1/4, by norm_num, 1/4, by norm_num, ?_⟩
  intro N
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) (le_max_right N 1)
  let p : ℝ := 1 / (4 * ((n : ℝ) + 1))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1/2 := by
    dsimp [p]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  let Q : Measure (Fin n → ℝ × ℝ) := Measure.pi (fun _ => unitUniform.prod unitUniform)
  have hQ : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  letI := hQ
  let g (b : Bool) (z : Fin n → ℝ × ℝ) : Sample n :=
    fun i => proposition1_generate p b (z i)
  have mg (b : Bool) : Measurable (g b) :=
    measurable_pi_lambda (fun i => (proposition1_measurable_generate p b).comp (measurable_pi_apply i))
  have hg (b : Bool) : Q.map (g b) = sampleLaw (proposition1_study p b) n := by
    exact Measure.pi_map_pi (fun _ => (proposition1_measurable_generate p b).aemeasurable)
  let E : Bool → Set (Fin n → ℝ × ℝ) := fun b =>
    {z | (1/4 : ℝ) < |est n (fun i => observe (g b z i)) - bit b|}
  have mE (b : Bool) : MeasurableSet (E b) := by
    exact measurableSet_lt measurable_const
      (((hmeas n).comp (measurable_pi_lambda (fun i =>
        proposition1_observe_measurable.comp ((measurable_pi_apply i).comp (mg b))))).sub_const (bit b)).abs
  let B : Set (Fin n → ℝ × ℝ) := ⋃ i : Fin n, {z | (z i).2 ≤ p}
  have mB : MeasurableSet B := MeasurableSet.iUnion (fun i =>
    measurableSet_le (measurable_snd.comp (measurable_pi_apply i)) measurable_const)
  have hBi (i : Fin n) : Q.real {z | (z i).2 ≤ p} = p := by
    have me : MeasurableSet {z : ℝ × ℝ | z.2 ≤ p} := measurableSet_le measurable_snd measurable_const
    have he := (measurePreserving_eval (fun _ : Fin n => unitUniform.prod unitUniform) i).map_eq
    have hv : Q {z | (z i).2 ≤ p} = (unitUniform.prod unitUniform) {z | z.2 ≤ p} := by
      rw [← he, Measure.map_apply (measurable_pi_apply i) me]
      rfl
    change (Q {z | (z i).2 ≤ p}).toReal = p
    rw [hv]
    have ht : (unitUniform.prod unitUniform) {z : ℝ × ℝ | z.2 ≤ p} = ENNReal.ofReal p := by
      change (unitUniform.prod unitUniform) (Prod.snd ⁻¹' Set.Iic p) = _
      rw [← Set.univ_prod, Measure.prod_prod, unitUniform_Iic p hp.le (by linarith)]
      simp
    rw [ht, ENNReal.toReal_ofReal hp.le]
  have hB : Q.real B ≤ 1/4 := by
    calc
      Q.real B ≤ ∑ i : Fin n, Q.real {z | (z i).2 ≤ p} := measureReal_iUnion_fintype_le _
      _ = n * p := by simp [hBi]
      _ ≤ 1/4 := by
        dsimp [p]
        rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]
        linarith
  have hcover : Bᶜ ⊆ E false ∪ E true := by
    intro z hz
    have hnone (i : Fin n) : ¬ (z i).2 ≤ p := by
      intro hi
      exact hz (Set.mem_iUnion.2 ⟨i, hi⟩)
    have ho : (fun i => observe (g false z i)) = fun i => observe (g true z i) := by
      funext i
      simp [g, proposition1_generate, observe, W, Y, X, Y0, Y1, bit, hnone i]
    change (1/4 : ℝ) < |est n (fun i => observe (g false z i)) - bit false| ∨
      (1/4 : ℝ) < |est n (fun i => observe (g true z i)) - bit true|
    rw [ho]
    simp only [bit, Bool.false_eq_true, if_false, if_true, sub_zero]
    by_contra hc
    push_neg at hc
    have h0 := (abs_le.1 hc.1).2
    have h1 := (abs_le.1 hc.2).1
    linarith
  have hsum : 3/4 ≤ Q.real (E false) + Q.real (E true) := by
    have hu := measureReal_union_le (μ := Q) (E false) (E true)
    have hm := measureReal_mono (μ := Q) hcover
    rw [measureReal_compl mB, probReal_univ] at hm
    linarith
  have hchoose : ∃ b : Bool, 1/4 ≤ Q.real (E b) := by
    by_cases hf : 1/4 ≤ Q.real (E false)
    · exact ⟨false, hf⟩
    · exact ⟨true, by linarith⟩
  obtain ⟨b, hb⟩ := hchoose
  obtain ⟨hvalid, hmu⟩ := proposition1_valid p hp hp1 b
  refine ⟨n, le_max_left N 1, hn, proposition1_study p b, hvalid, ?_⟩
  rw [hmu]
  have me : MeasurableSet {a : Sample n | (1/4 : ℝ) < |est n (fun i => observe (a i)) - bit b|} :=
    measurableSet_lt measurable_const (((hmeas n).comp
      (measurable_pi_lambda (fun i => proposition1_observe_measurable.comp
        (measurable_pi_apply i)))).sub_const (bit b)).abs
  rw [← hg b, Measure.map_apply (mg b) me]
  exact hb

lemma htcentre_unit (M : Study) (hM : ValidStudy M) :
    condExp covariateSigma M.law (fun o => htTerm (M.pi (W o)) (X o) (Y o))
      =ᵐ[M.law] fun o => M.m (W o) := by
  letI := hM.probability
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have bg : ∀ᵐ o ∂M.law, X o * Y1 o ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_of_all _ (fun ⟨w,x,y0,y1⟩ => by
      cases x <;> cases y1 <;> norm_num [X, Y1, bit])
  have ig : Integrable (fun o => X o * Y1 o) M.law :=
    memLp_one_iff_integrable.1 (memLp_of_bounded bg (mx.mul my).aestronglyMeasurable 1)
  have hfun : (fun o => (M.pi (W o))⁻¹ * (X o * Y1 o)) =
      (fun o => htTerm (M.pi (W o)) (X o) (Y o)) := by
    funext o
    simp only [htTerm, consistency_treated, div_eq_mul_inv]
    ring
  have mip : StronglyMeasurable[covariateSigma] (fun o => (M.pi (W o))⁻¹) :=
    (hM.measurable_pi.comp (comap_measurable W)).inv.stronglyMeasurable
  have hprod : Integrable ((fun o => (M.pi (W o))⁻¹) * (fun o => X o * Y1 o)) M.law := by
    change Integrable (fun o => (M.pi (W o))⁻¹ * (X o * Y1 o)) M.law
    rw [hfun]
    exact (ht_unit_facts M hM).1
  have hpull := condExp_mul_of_stronglyMeasurable_left mip hprod ig
  change condExp covariateSigma M.law (fun o => (M.pi (W o))⁻¹ * (X o * Y1 o)) =ᵐ[M.law]
    (fun o => (M.pi (W o))⁻¹ * condExp covariateSigma M.law (fun o => X o * Y1 o) o) at hpull
  rw [hfun] at hpull
  filter_upwards [hpull, conditional_xy_factorization M hM, hM.positivity] with o h1 h2 ho
  rw [h1, h2]
  have hp : M.pi (W o) ≠ 0 := ne_of_gt (lt_trans hM.delta_pos ho.1)
  field_simp

/-- Fubini for a coordinate function restricted to a product rectangle. -/
lemma htcentre_rectangle (M : Study) (hM : ValidStudy M) (n : ℕ) (i : Fin n)
    (S : Fin n → Set Unit) (f : Unit → ℝ) (mf : Measurable f) :
    (∫ a in Set.univ.pi S, f (a i) ∂sampleLaw M n) =
      (∏ j ∈ Finset.univ.erase i, M.law.restrict (S j) Set.univ).toReal *
        ∫ o in S i, f o ∂M.law := by
  classical
  letI := hM.probability
  unfold sampleLaw
  rw [Measure.restrict_pi_pi]
  rw [← integral_map (measurable_pi_apply i).aemeasurable mf.aestronglyMeasurable]
  rw [Measure.pi_map_eval, integral_smul_measure]
  rfl

lemma htcentre_coordinate (M : Study) (hM : ValidStudy M) (n : ℕ) (i : Fin n) :
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (fun a => htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) =ᵐ[sampleLaw M n]
        fun a => M.m (W (a i)) := by
  classical
  letI := hM.probability
  have hcovle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hcovle) := isFiniteMeasure_trim hcovle
  let H : Unit → ℝ := fun o => htTerm (M.pi (W o)) (X o) (Y o)
  let R : Unit → ℝ := fun o => M.m (W o)
  have mH : Measurable H := by
    have mb : Measurable bit := measurable_of_countable _
    have mx : Measurable X := mb.comp measurable_snd.fst
    have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
    have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
    exact (mx.mul (((measurable_const.sub mx).mul my0).add (mx.mul my1))).div
      (hM.measurable_pi.comp measurable_fst)
  have mR : Measurable R := hM.measurable_m.comp measurable_fst
  have hH : Integrable H M.law := (ht_unit_facts M hM).1
  have hR : Integrable R M.law := integrable_condExp.congr hM.regression
  have hiH : Integrable (fun a : Sample n => H (a i)) (sampleLaw M n) :=
    (measurePreserving_eval (fun _ => M.law) i).integrable_comp_of_integrable hH
  have hiR : Integrable (fun a : Sample n => R (a i)) (sampleLaw M n) :=
    (measurePreserving_eval (fun _ => M.law) i).integrable_comp_of_integrable hR
  have mc : Measurable (covariates (n := n)) :=
    measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := mc.comap_le
  have hu : (∫ a : Sample n, R (a i) ∂sampleLaw M n) =
      ∫ a : Sample n, H (a i) ∂sampleLaw M n := by
    simp only [sampleLaw]
    rw [integral_comp_eval (i := i) mR.aestronglyMeasurable,
      integral_comp_eval (i := i) mH.aestronglyMeasurable]
    exact (regression_mean M hM).trans (ht_unit_facts M hM).2.symm
  have hsets : ∀ t : Set (Fin n → ℝ), MeasurableSet t →
      (∫ a in covariates ⁻¹' t, R (a i) ∂sampleLaw M n) =
        ∫ a in covariates ⁻¹' t, H (a i) ∂sampleLaw M n := by
    intro t mt
    induction t, mt using MeasurableSpace.induction_on_inter
        (generateFrom_pi (α := fun _ : Fin n => ℝ)).symm
        (IsPiSystem.pi (fun _ : Fin n => MeasurableSpace.isPiSystem_measurableSet)) with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, rfl⟩ := ht
      have mS (j : Fin n) : MeasurableSet (S j) := hS j (Set.mem_univ j)
      have he : covariates ⁻¹' (Set.univ.pi S) = Set.univ.pi (fun j => W ⁻¹' S j) := by
        ext a
        simp [covariates, Set.mem_pi]
      rw [he, htcentre_rectangle M hM n i _ R mR, htcentre_rectangle M hM n i _ H mH]
      congr 1
      have hs : MeasurableSet[covariateSigma] (W ⁻¹' S i) := (comap_measurable W) (mS i)
      calc
        _ = ∫ o in W ⁻¹' S i, condExp covariateSigma M.law H o ∂M.law :=
          setIntegral_congr_ae (measurable_fst (mS i)) ((htcentre_unit M hM).symm.mono (fun _ h _ => h))
        _ = _ := setIntegral_condExp measurable_fst.comap_le hH hs
    | compl t mt iht =>
      simp only [Set.preimage_compl]
      rw [setIntegral_compl (mc mt) hiR, setIntegral_compl (mc mt) hiH, hu, iht]
    | iUnion f hd mf ih =>
      simp only [Set.preimage_iUnion]
      rw [integral_iUnion (fun k => mc (mf k)) (hd.mono fun _ _ h => h.preimage _) hiR.integrableOn,
        integral_iUnion (fun k => mc (mf k)) (hd.mono fun _ _ h => h.preimage _) hiH.integrableOn]
      exact tsum_congr ih
  apply (ae_eq_condExp_of_forall_setIntegral_eq hle hiH
    (fun _ _ _ => hiR.integrableOn) ?_ ?_).symm
  · rintro s ⟨t, mt, rfl⟩ _
    exact hsets t mt
  · exact ((hM.measurable_m.comp (measurable_pi_apply i)).comp
      (comap_measurable (covariates (n := n)))).stronglyMeasurable.aestronglyMeasurable

theorem ht_conditional_centre_proof (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n) :
    condExp (sampleCovariateSigma n) (sampleLaw M n) (ht M) =ᵐ[sampleLaw M n] muW M := by
  letI := hM.probability
  have hi (i : Fin n) : Integrable
      (fun a : Sample n => htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) (sampleLaw M n) :=
    (measurePreserving_eval (fun _ => M.law) i).integrable_comp_of_integrable (ht_unit_facts M hM).1
  have hs := condExp_finsetSum (μ := sampleLaw M n) (m := sampleCovariateSigma n)
    (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_fn] at hs
  have hc := condExp_smul (μ := sampleLaw M n) ((n : ℝ)⁻¹)
    (fun a : Sample n => ∑ i, htTerm (M.pi (W (a i))) (X (a i)) (Y (a i)))
    (sampleCovariateSigma n)
  have heq : ht M (n := n) = (n : ℝ)⁻¹ •
      (fun a : Sample n => ∑ i, htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) := by
    funext a
    simp only [ht, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  have hall := ae_all_iff.2 (fun i => htcentre_coordinate M hM n i)
  filter_upwards [hs, hc, hall] with a ha hb hh
  simpa only [muW, div_eq_mul_inv, smul_eq_mul, Pi.smul_apply, Finset.sum_apply, hh, mul_comm] using hb.trans (congrArg (fun x : ℝ => (n : ℝ)⁻¹ * x) ha)

lemma p3_product_conditional (M : Study) (hM : ValidStudy M) (n : ℕ)
    (f : Fin n → Unit → ℝ) (k : Fin n → ℝ → ℝ)
    (mf : ∀ i, Measurable (f i)) (mk : ∀ i, Measurable (k i))
    (hf : ∀ i, Integrable (f i) M.law)
    (hc : ∀ i, condExp covariateSigma M.law (f i) =ᵐ[M.law] fun o => k i (W o)) :
    condExp (sampleCovariateSigma n) (sampleLaw M n) (fun a => ∏ i, f i (a i))
      =ᵐ[sampleLaw M n] fun a => ∏ i, k i (W (a i)) := by
  classical
  letI := hM.probability
  have hcovle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hcovle) := isFiniteMeasure_trim hcovle
  have hk (i) : Integrable (fun o => k i (W o)) M.law := integrable_condExp.congr (hc i)
  have hiF : Integrable (fun a : Sample n => ∏ i, f i (a i)) (sampleLaw M n) :=
    Integrable.fintype_prod hf
  have hiK : Integrable (fun a : Sample n => ∏ i, k i (W (a i))) (sampleLaw M n) :=
    Integrable.fintype_prod hk
  have mc : Measurable (covariates (n := n)) :=
    measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := mc.comap_le
  have hset (i : Fin n) (S : Set ℝ) (mS : MeasurableSet S) :
      (∫ o in W ⁻¹' S, k i (W o) ∂M.law) = ∫ o in W ⁻¹' S, f i o ∂M.law := by
    calc
      _ = ∫ o in W ⁻¹' S, condExp covariateSigma M.law (f i) o ∂M.law :=
        setIntegral_congr_ae (measurable_fst mS) ((hc i).symm.mono (fun _ h _ => h))
      _ = _ := setIntegral_condExp measurable_fst.comap_le (hf i) ((comap_measurable W) mS)
  have hu : (∫ a : Sample n, ∏ i, k i (W (a i)) ∂sampleLaw M n) =
      ∫ a : Sample n, ∏ i, f i (a i) ∂sampleLaw M n := by
    simp only [sampleLaw]
    rw [integral_fintype_prod_eq_prod (fun i o => k i (W o)),
      integral_fintype_prod_eq_prod f]
    apply Finset.prod_congr rfl
    intro i _
    exact (integral_congr_ae (hc i).symm).trans (integral_condExp measurable_fst.comap_le)
  have hsets : ∀ t : Set (Fin n → ℝ), MeasurableSet t →
      (∫ a in covariates ⁻¹' t, ∏ i, k i (W (a i)) ∂sampleLaw M n) =
        ∫ a in covariates ⁻¹' t, ∏ i, f i (a i) ∂sampleLaw M n := by
    intro t mt
    induction t, mt using MeasurableSpace.induction_on_inter
        (generateFrom_pi (α := fun _ : Fin n => ℝ)).symm
        (IsPiSystem.pi (fun _ : Fin n => MeasurableSpace.isPiSystem_measurableSet)) with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, rfl⟩ := ht
      have mS (j : Fin n) : MeasurableSet (S j) := hS j (Set.mem_univ j)
      have he : covariates ⁻¹' (Set.univ.pi S) = Set.univ.pi (fun j => W ⁻¹' S j) := by
        ext a
        simp [covariates, Set.mem_pi]
      rw [he]
      change (∫ a, ∏ i, k i (W (a i)) ∂(Measure.pi (fun _ : Fin n => M.law)).restrict _) =
        ∫ a, ∏ i, f i (a i) ∂(Measure.pi (fun _ : Fin n => M.law)).restrict _
      simp only [Measure.restrict_pi_pi]
      rw [integral_fintype_prod_eq_prod (fun i o => k i (W o)),
        integral_fintype_prod_eq_prod f]
      exact Finset.prod_congr rfl (fun i _ => hset i (S i) (mS i))
    | compl t mt iht =>
      simp only [Set.preimage_compl]
      rw [setIntegral_compl (mc mt) hiK, setIntegral_compl (mc mt) hiF, hu, iht]
    | iUnion f hd mf ih =>
      simp only [Set.preimage_iUnion]
      rw [integral_iUnion (fun j => mc (mf j)) (hd.mono fun _ _ h => h.preimage _) hiK.integrableOn,
        integral_iUnion (fun j => mc (mf j)) (hd.mono fun _ _ h => h.preimage _) hiF.integrableOn]
      exact tsum_congr ih
  apply (ae_eq_condExp_of_forall_setIntegral_eq hle hiF
    (fun _ _ _ => hiK.integrableOn) ?_ ?_).symm
  · rintro s ⟨t, mt, rfl⟩ _
    exact hsets t mt
  · exact ((Finset.measurable_prod Finset.univ (fun i _ =>
      (mk i).comp (measurable_pi_apply i))).comp (comap_measurable covariates)).stronglyMeasurable.aestronglyMeasurable


def p3_indicator (b : Bool) (o : Unit) : ℝ :=
  if (o.2.1 && o.2.2.2) = b then 1 else 0

def p3_weight (M : Study) (b : Bool) (w : ℝ) : ℝ :=
  if b then M.pi w * M.m w else 1 - M.pi w * M.m w

lemma p3_indicator_measurable (b : Bool) : Measurable (p3_indicator b) := by
  have md : Measurable (fun o : Unit => o.2.1 && o.2.2.2) :=
    (measurable_of_countable (fun z : Bool × Bool => z.1 && z.2)).comp
      (measurable_snd.fst.prodMk measurable_snd.snd.snd)
  exact measurable_const.ite (measurableSet_eq_fun md measurable_const) measurable_const

lemma p3_indicator_integrable (M : Study) (hM : ValidStudy M) (b : Bool) :
    Integrable (p3_indicator b) M.law := by
  letI := hM.probability
  apply memLp_one_iff_integrable.1 (memLp_of_bounded (a := 0) (b := 1) _
    (p3_indicator_measurable b).aestronglyMeasurable 1)
  exact ae_of_all _ (fun o => by unfold p3_indicator; split <;> norm_num)

lemma p3_single_conditional (M : Study) (hM : ValidStudy M) (b : Bool) :
    condExp covariateSigma M.law (p3_indicator b) =ᵐ[M.law]
      fun o => p3_weight M b (W o) := by
  letI := hM.probability
  have ht : p3_indicator true = fun o => X o * Y1 o := by
    funext ⟨w,x,y0,y1⟩
    cases x <;> cases y1 <;> simp [p3_indicator, X, Y1, bit]
  have hf : p3_indicator false = (fun _ => (1 : ℝ)) - p3_indicator true := by
    funext ⟨w,x,y0,y1⟩
    cases x <;> cases y1 <;> simp [p3_indicator]
  cases b with
  | true => simpa only [ht, p3_weight, if_true] using conditional_xy_factorization M hM
  | false =>
    rw [hf]
    have hs := condExp_sub (integrable_const (1 : ℝ)) (p3_indicator_integrable M hM true) covariateSigma
    have hc := conditional_xy_factorization M hM
    rw [← ht] at hc
    have hconst : condExp covariateSigma M.law (fun _ => (1 : ℝ)) = fun _ => 1 :=
      condExp_const measurable_fst.comap_le 1
    filter_upwards [hs, hc] with o hs hc
    rw [hs]
    simp only [Pi.sub_apply, hconst, hc, p3_weight, Bool.false_eq_true, if_false]

lemma p3_product_indicator (n : ℕ) (b : Fin n → Bool) (a : Sample n) :
    (∏ i, p3_indicator (b i) (a i)) =
      if (fun i => (a i).2.1 && (a i).2.2.2) = b then (1 : ℝ) else 0 := by
  classical
  simp [p3_indicator, Fintype.prod_boole, funext_iff]

/-- Two-sided Hoeffding on a fixed covariate vector. -/
lemma p3_bernoulli_tail (n : ℕ) (hn : 0 < n) (p m : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hr : ∀ i, 0 ≤ p i * m i ∧ p i * m i ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    let r : Fin n → Set.Icc (0 : ℝ) 1 := fun i => ⟨p i * m i, hr i⟩
    let Q := Measure.pi (fun i => bernoulliMeasure true false (r i))
    Q.real {b | t ≤ |(∑ i, bit (b i) / p i) / n - (∑ i, m i) / n|} ≤
      2 * Real.exp (-2 * n * t^2 / ((∑ i, (p i)⁻¹^2) / n)) := by
  classical
  intro r Q
  let c : Fin n → NNReal := fun i => (‖(p i)⁻¹ - 0‖₊ / 2)^2
  have hm (i) : (∫ b, bit b / p i ∂bernoulliMeasure true false (r i)) = m i := by
    rw [integral_bernoulliMeasure]
    simp only [bit, if_true, Bool.false_eq_true, if_false, zero_div, smul_eq_mul, mul_zero, add_zero]
    change (p i * m i) * (1 / p i) = m i
    field_simp [ne_of_gt (hp i)]
  have hs (i : Fin n) : HasSubgaussianMGF (fun b : Fin n → Bool => bit (b i) / p i - m i) (c i) Q := by
    have h : HasSubgaussianMGF
        (fun b : Bool => bit b / p i - ∫ b, bit b / p i ∂bernoulliMeasure true false (r i))
        (c i) (bernoulliMeasure true false (r i)) := by
      apply hasSubgaussianMGF_of_mem_Icc (a := 0) (b := (p i)⁻¹)
        (X := fun b : Bool => bit b / p i) (measurable_of_countable _).aemeasurable
      exact ae_of_all _ (fun b => by cases b <;> simp [bit, one_div, (inv_pos.mpr (hp i)).le])
    rw [hm i] at h
    have hmap := (measurePreserving_eval (fun i => bernoulliMeasure true false (r i)) i).map_eq
    rw [← hmap] at h
    exact HasSubgaussianMGF.of_map (μ := Q) (Y := fun b : Fin n → Bool => b i)
      (measurable_pi_apply i).aemeasurable h
  have hind : iIndepFun (fun (i : Fin n) (b : Fin n → Bool) => bit (b i) / p i - m i) Q :=
    iIndepFun_pi (fun i => (measurable_of_countable (fun b : Bool => bit b / p i - m i)).aemeasurable)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => hs i)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hu := hsum.measure_ge_le (mul_nonneg hnR.le ht)
  have hl := hsum.neg.measure_ge_le (mul_nonneg hnR.le ht)
  have hc : ((∑ i, c i : NNReal) : ℝ) = (∑ i, (p i)⁻¹^2) / 4 := by
    simp [c, Real.norm_eq_abs, div_pow, ← Finset.sum_div] <;> norm_num
  have hd : -(n*t)^2 / (2 * ((∑ i, c i : NNReal) : ℝ)) =
      -2*n*t^2 / ((∑ i, (p i)⁻¹^2) / n) := by
    rw [hc]
    field_simp
    <;> ring
  rw [hd] at hu hl
  simp only [Pi.neg_apply] at hl
  have hcenter (b : Fin n → Bool) :
      (∑ i, (bit (b i) / p i - m i)) =
        (n : ℝ) * ((∑ i, bit (b i) / p i) / n - (∑ i, m i) / n) := by
    rw [Finset.sum_sub_distrib]
    field_simp [ne_of_gt hnR]
  have hsub : {b : Fin n → Bool | t ≤ |(∑ i, bit (b i) / p i) / n - (∑ i, m i) / n|} ⊆
      {b | (n : ℝ)*t ≤ ∑ i, (bit (b i) / p i - m i)} ∪
        {b | (n : ℝ)*t ≤ -(∑ i, (bit (b i) / p i - m i))} := by
    intro b hb
    simp only [Set.mem_setOf_eq, Set.mem_union] at hb ⊢
    by_cases hpos : 0 ≤ (∑ i, bit (b i) / p i) / n - (∑ i, m i) / n
    · left
      rw [abs_of_nonneg hpos] at hb
      rw [hcenter]
      exact mul_le_mul_of_nonneg_left hb hnR.le
    · right
      rw [abs_of_neg (lt_of_not_ge hpos)] at hb
      rw [hcenter, ← mul_neg]
      exact mul_le_mul_of_nonneg_left hb hnR.le
  have hle := measureReal_mono (μ := Q) hsub
  have hun := measureReal_union_le (μ := Q)
    {b | (n : ℝ)*t ≤ ∑ i, (bit (b i) / p i - m i)}
    {b | (n : ℝ)*t ≤ -(∑ i, (bit (b i) / p i - m i))}
  linarith


lemma p3_ht_bits (M : Study) {n : ℕ} (a : Sample n) :
    ht M a = (∑ i, bit ((a i).2.1 && (a i).2.2.2) / M.pi (W (a i))) / n := by
  unfold ht
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [htTerm, consistency_treated]
  rcases a i with ⟨w,x,y0,y1⟩
  cases x <;> cases y1 <;> simp [X, Y1, bit]

lemma p3_random_tail (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    (sampleLaw M n).real {a | Real.sqrt (xi M a) * t ≤ |AronowAudit.P046.ht M a - muW M a|} ≤
      2 * Real.exp (-2 * n * t^2) := by
  classical
  letI := hM.probability
  let P := sampleLaw M n
  let C (b : Fin n → Bool) (a : Sample n) : ℝ :=
    if Real.sqrt (xi M a) * t ≤
      |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a| then 1 else 0
  let J (b : Fin n → Bool) (a : Sample n) : ℝ := ∏ i, p3_indicator (b i) (a i)
  let f (a : Sample n) : ℝ :=
    if Real.sqrt (xi M a) * t ≤ |AronowAudit.P046.ht M a - muW M a| then 1 else 0
  have mc : Measurable (covariates (n := n)) :=
    measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := mc.comap_le
  have mC (b) : Measurable[sampleCovariateSigma n] (C b) := by
    letI instP3CovariateMeasurable : MeasurableSpace (Sample n) := sampleCovariateSigma n
    have mp (i : Fin n) : Measurable[sampleCovariateSigma n] (fun a : Sample n => M.pi (W (a i))) :=
      ((hM.measurable_pi.comp (show Measurable (fun w : Fin n → ℝ => w i) from measurable_pi_apply i)).comp
        (comap_measurable (covariates (n := n))))
    have mm (i : Fin n) : Measurable[sampleCovariateSigma n] (fun a : Sample n => M.m (W (a i))) :=
      ((hM.measurable_m.comp (show Measurable (fun w : Fin n → ℝ => w i) from measurable_pi_apply i)).comp
        (comap_measurable (covariates (n := n))))
    have mx : Measurable[sampleCovariateSigma n] (xi M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => (mp i).inv.pow_const 2)).div_const n
    have mr : Measurable[sampleCovariateSigma n] (muW M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => mm i)).div_const n
    have mh : Measurable[sampleCovariateSigma n]
        (fun a : Sample n => (∑ i, bit (b i) / M.pi (W (a i))) / n) :=
      (Finset.measurable_sum Finset.univ (fun i _ => measurable_const.div (mp i))).div_const n
    exact measurable_const.ite (measurableSet_le (mx.sqrt.mul_const t) (mh.sub mr).abs) measurable_const
  have mJ (b) : Measurable (J b) :=
    Finset.measurable_prod Finset.univ (fun i _ => (p3_indicator_measurable (b i)).comp (measurable_pi_apply i))
  have iCJ (b) : Integrable (fun a => C b a * J b a) P := by
    apply memLp_one_iff_integrable.1 (memLp_of_bounded (a := 0) (b := 1) _
      (((mC b).mono hle le_rfl).mul (mJ b)).aestronglyMeasurable 1)
    exact ae_of_all _ (fun a => by
      dsimp [J]
      rw [p3_product_indicator]
      dsimp [C]
      split <;> split <;> norm_num)
  have hJ (b) : condExp (sampleCovariateSigma n) P (J b) =ᵐ[P]
      fun a => ∏ i, p3_weight M (b i) (W (a i)) := by
    apply p3_product_conditional M hM n (fun i => p3_indicator (b i))
      (fun i => p3_weight M (b i)) (fun i => p3_indicator_measurable (b i))
    · intro i
      cases b i
      · change Measurable (fun w : ℝ => 1 - M.pi w * M.m w)
        exact measurable_const.sub (hM.measurable_pi.mul hM.measurable_m)
      · change Measurable (fun w : ℝ => M.pi w * M.m w)
        exact hM.measurable_pi.mul hM.measurable_m
    · exact fun i => p3_indicator_integrable M hM (b i)
    · exact fun i => p3_single_conditional M hM (b i)
  have heq : f = fun a => ∑ b : Fin n → Bool, C b a * J b a := by
    funext a
    rw [Finset.sum_eq_single (fun i => (a i).2.1 && (a i).2.2.2)]
    · simp only [J, p3_product_indicator, if_true, mul_one]
      simp only [f, C, p3_ht_bits]
    · intro b _ hb
      simp only [J, p3_product_indicator, if_neg (Ne.symm hb), mul_zero]
    · simp
  have hpull (b) : condExp (sampleCovariateSigma n) P (fun a => C b a * J b a) =ᵐ[P]
      fun a => C b a * ∏ i, p3_weight M (b i) (W (a i)) := by
    have iJ : Integrable (J b) P := Integrable.fintype_prod (fun i => p3_indicator_integrable M hM (b i))
    have h := condExp_mul_of_stronglyMeasurable_left (mC b).stronglyMeasurable (iCJ b) iJ
    exact h.trans ((hJ b).mono (fun a ha => congrArg (fun x => C b a * x) ha))
  have hs := condExp_finsetSum (μ := P) (fun b (_ : b ∈ (Finset.univ : Finset (Fin n → Bool))) => iCJ b)
    (sampleCovariateSigma n)
  simp only [Finset.sum_fn] at hs
  have hc : condExp (sampleCovariateSigma n) P f =ᵐ[P]
      fun a => ∑ b : Fin n → Bool, C b a * ∏ i, p3_weight M (b i) (W (a i)) := by
    have ha := ae_all_iff.2 hpull
    filter_upwards [hs, ha] with a hs ha
    rw [heq]
    exact hs.trans (Finset.sum_congr rfl (fun b _ => ha b))
  have hgood : ∀ᵐ a ∂P, ∀ i : Fin n,
      M.delta < M.pi (W (a i)) ∧ M.pi (W (a i)) < 1 - M.delta ∧
        0 ≤ M.m (W (a i)) ∧ M.m (W (a i)) ≤ 1 := by
    apply ae_all_iff.2
    intro i
    have hu : ∀ᵐ o ∂M.law, M.delta < M.pi (W o) ∧ M.pi (W o) < 1 - M.delta ∧
        0 ≤ M.m (W o) ∧ M.m (W o) ≤ 1 := by
      filter_upwards [hM.positivity, hM.regression_range] with o hp hm
      exact ⟨hp.1, hp.2, hm⟩
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => M.law) (i := i)).eventually hu
  have hbound : ∀ᵐ a ∂P, condExp (sampleCovariateSigma n) P f a ≤ 2 * Real.exp (-2 * n * t^2) := by
    filter_upwards [hc, hgood] with a hc hg
    have hp (i) : 0 < M.pi (W (a i)) := lt_trans hM.delta_pos (hg i).1
    have hr (i) : 0 ≤ M.pi (W (a i)) * M.m (W (a i)) ∧
        M.pi (W (a i)) * M.m (W (a i)) ≤ 1 := by
      refine ⟨mul_nonneg (hp i).le (hg i).2.2.1, ?_⟩
      calc
        _ ≤ M.pi (W (a i)) * 1 := mul_le_mul_of_nonneg_left (hg i).2.2.2 (hp i).le
        _ ≤ 1 := by simp only [mul_one]; linarith [(hg i).2.1, hM.delta_pos]
    let r : Fin n → Set.Icc (0 : ℝ) 1 := fun i => ⟨M.pi (W (a i)) * M.m (W (a i)), hr i⟩
    let Q := Measure.pi (fun i => bernoulliMeasure true false (r i))
    have hQ : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
    letI := hQ
    have hxi : 0 < xi M a := by
      apply div_pos _ (Nat.cast_pos.mpr hn)
      exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr (hp i)))
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hh := p3_bernoulli_tail n hn (fun i => M.pi (W (a i))) (fun i => M.m (W (a i)))
      hp hr (Real.sqrt (xi M a) * t) (mul_nonneg (Real.sqrt_nonneg _) ht)
    change Q.real _ ≤ _ at hh
    have hex : -2 * (n : ℝ) * (Real.sqrt (xi M a) * t)^2 / xi M a = -2 * n * t^2 := by
      rw [mul_pow, Real.sq_sqrt hxi.le]
      field_simp
    change Q.real _ ≤ 2 * Real.exp (-2 * (n : ℝ) * (Real.sqrt (xi M a) * t)^2 / xi M a) at hh
    rw [hex] at hh
    rw [hc]
    convert hh using 1
    let A : Set (Fin n → Bool) := {b | Real.sqrt (xi M a) * t ≤
      |(∑ i, bit (b i) / M.pi (W (a i))) / n - (∑ i, M.m (W (a i))) / n|}
    have mA : MeasurableSet A := Set.toFinite A |>.measurableSet
    rw [← integral_indicator_one mA, integral_fintype Integrable.of_finite]
    apply Finset.sum_congr rfl
    intro b _
    have hb : Q.real {b} = ∏ i, p3_weight M (b i) (W (a i)) := by
      have hs : ({b} : Set (Fin n → Bool)) = Set.univ.pi (fun i => {b i}) := by
        ext d
        simp [funext_iff, Set.mem_pi]
      change (Q {b}).toReal = _
      dsimp only [Q]
      rw [hs, Measure.pi_pi, ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro i _
      change (bernoulliMeasure true false (r i)).real {b i} = _
      cases hbi : b i <;> simp [bernoulliMeasure_real_apply, p3_weight, r, hbi]
    rw [hb]
    simp [C, A, muW, Set.indicator, mul_comm]
  have hleint := integral_mono_ae (integrable_condExp (f := f))
    (integrable_const (2 * Real.exp (-2 * n * t^2))) hbound
  have mF : MeasurableSet {a : Sample n | Real.sqrt (xi M a) * t ≤ |AronowAudit.P046.ht M a - muW M a|} := by
    have mb : Measurable bit := measurable_of_countable _
    have mx : Measurable X := mb.comp measurable_snd.fst
    have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
    have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
    have my : Measurable Y := ((measurable_const.sub mx).mul my0).add (mx.mul my1)
    have mp (i : Fin n) : Measurable (fun a : Sample n => M.pi (W (a i))) :=
      hM.measurable_pi.comp (measurable_fst.comp (measurable_pi_apply i))
    have mh : Measurable (AronowAudit.P046.ht M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ =>
        ((mx.comp (measurable_pi_apply i)).mul (my.comp (measurable_pi_apply i))).div (mp i))).div_const n
    have mr : Measurable (muW M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ =>
        hM.measurable_m.comp (measurable_fst.comp (measurable_pi_apply i)))).div_const n
    have mxi : Measurable (xi M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => (mp i).inv.pow_const 2)).div_const n
    exact measurableSet_le (mxi.sqrt.mul_const t) (mh.sub mr).abs
  have hf : (∫ a, f a ∂P) = P.real {a | Real.sqrt (xi M a) * t ≤ |AronowAudit.P046.ht M a - muW M a|} := by
    exact integral_indicator_one mF
  rw [integral_condExp hle, hf] at hleint
  simpa using hleint


theorem proposition3_corrected_proof (M : Study) (hM : ValidStudy M)
    (n : ℕ) (hn : 0 < n) (alpha : ℝ) (ha : 0 < alpha ∧ alpha < 1) :
    tailProb M (ht M) (correctedRadius M alpha (n := n)) ≤ alpha := by
  letI := hM.probability
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log (4 / alpha) := Real.log_pos (by
    apply (lt_div_iff₀ ha.1).2
    linarith [ha.2])
  let t := Real.sqrt (Real.log (4 / alpha) / (2 * n))
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have he : 2 * Real.exp (-2 * (n : ℝ) * t^2) = alpha / 2 := by
    have hx : -2 * (n : ℝ) * t^2 = -Real.log (4 / alpha) := by
      dsimp [t]
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    rw [hx, Real.exp_neg, Real.exp_log (div_pos (by norm_num) ha.1)]
    field_simp
    <;> ring
  have h1 := p3_random_tail M hM n hn t ht
  have h2 := covariate_hoeffding M hM n hn t ht
  rw [he] at h1 h2
  have h := two_error_union_bound (sampleLaw M n) (AronowAudit.P046.ht M) (muW M) (mu M)
    (fun a => Real.sqrt (xi M a) * t) (fun _ => t) alpha h1 h2
  convert h using 1
  unfold tailProb
  congr 2
  ext a
  dsimp [correctedRadius, t]
  rw [add_mul, one_mul]

end
end AronowAudit.P046.Wave1
