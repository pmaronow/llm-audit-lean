import AronowAudit.P046.P046_Audit
import AronowAudit.P061.P061_Foundations

/-!
Cross-fitting remainder bounds and the normal limit.
The remainder bound is proved by splitting the finite product into training and
validation coordinates. The normal limit uses that bound and a direct calculation
of the true-regression summand's variance.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology
namespace AronowAudit.P046.Wave1
set_option maxHeartbeats 2000000

/- A measurable predictor version, scalar multiplier moments, and product tails. -/
lemma rcheb_finite_fiber_version {B : Type*} [Fintype B] [MeasurableSpace B]
    (P : Measure (ℝ × B)) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable (fun o : ℝ × B => g o.1) P) :
    ∃ g₀ : ℝ → ℝ, Measurable g₀ ∧ (fun o : ℝ × B => g₀ o.1) =ᵐ[P] fun o => g o.1 := by
  classical
  obtain ⟨N, hNsub, hNm, hN⟩ := exists_measurable_superset_of_null
    (show P {o | g o.1 ≠ hg.mk (fun o : ℝ × B => g o.1) o} = 0 from
      ae_iff.1 hg.ae_eq_mk)
  have hs (s : Finset B) : ∃ f : ℝ → ℝ, Measurable f ∧
      ∀ w, (∃ b ∈ s, (w, b) ∉ N) → f w = g w := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, measurable_const, by simp⟩
    | @insert b s hb ih =>
      obtain ⟨f, hf, he⟩ := ih
      refine ⟨fun w => if (w, b) ∉ N then hg.mk _ (w,b) else f w,
        (hg.stronglyMeasurable_mk.measurable.comp
          (measurable_id.prodMk measurable_const)).ite
          ((hNm.preimage (measurable_id.prodMk measurable_const)).compl) hf, ?_⟩
      intro w hw
      by_cases hwN : (w, b) ∉ N
      · simp only [if_pos hwN]
        exact (not_not.1 (mt (fun h => hNsub h) hwN)).symm
      · simp only [if_neg hwN]
        apply he
        obtain ⟨c, hc, hcN⟩ := hw
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact False.elim (hwN hcN)
        · exact ⟨c, hc, hcN⟩
  obtain ⟨f, hf, he⟩ := hs Finset.univ
  refine ⟨f, hf, ?_⟩
  filter_upwards [show ∀ᵐ o ∂P, o ∉ N from ae_iff.2 (by simpa only [not_not, Set.setOf_mem_eq] using hN)] with o ho
  exact he o.1 ⟨o.2, Finset.mem_univ _, ho⟩

lemma rcheb_pi_bounds (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, 0 < M.pi (W o) ∧ M.pi (W o) < 1 ∧
      |(M.pi (W o))⁻¹| ≤ M.delta⁻¹ ∧
      |1 - X o / M.pi (W o)| ≤ 1 + M.delta⁻¹ ∧
      0 ≤ q M (W o) ∧ q M (W o) ≤ M.delta⁻¹ := by
  filter_upwards [hM.positivity] with o ho
  have hp : 0 < M.pi (W o) := hM.delta_pos.trans ho.1
  have hp1 : M.pi (W o) < 1 := by linarith [hM.delta_pos]
  have hip : (M.pi (W o))⁻¹ ≤ M.delta⁻¹ :=
    (inv_le_inv₀ hp hM.delta_pos).2 ho.1.le
  have hx : |X o| ≤ 1 := by cases hx : o.2.1 <;> norm_num [X, bit, hx]
  refine ⟨hp, hp1, by simpa [abs_of_pos (inv_pos.2 hp)] using hip, ?_,
    div_nonneg (sub_nonneg.2 hp1.le) hp.le, ?_⟩
  · calc
      |1 - X o / M.pi (W o)| ≤ |(1 : ℝ)| + |X o / M.pi (W o)| := abs_sub _ _
      _ ≤ 1 + M.delta⁻¹ := by
        simp only [abs_one, abs_div, abs_of_pos hp]
        gcongr
        calc
          |X o| / M.pi (W o) ≤ 1 / M.pi (W o) := div_le_div_of_nonneg_right hx hp.le
          _ ≤ M.delta⁻¹ := by simpa only [one_div] using hip
  · calc
      q M (W o) ≤ 1 / M.pi (W o) := by unfold q; gcongr; linarith
      _ ≤ M.delta⁻¹ := by simpa only [one_div] using hip

lemma p4d_regression_L2 (M : Study) (hM : ValidStudy M) :
    MemLp (fun o => M.m (W o)) 2 M.law := by
  letI := hM.probability
  exact memLp_of_bounded hM.regression_range
    (hM.measurable_m.comp measurable_fst).aestronglyMeasurable 2

lemma rcheb_measurable_X : Measurable X :=
  (measurable_of_countable bit).comp measurable_snd.fst

lemma rcheb_X_bound (o : Unit) : |X o| ≤ 1 := by
  cases hx : o.2.1 <;> norm_num [X, bit, hx]

lemma rcheb_propensity_integral (M : Study) (hM : ValidStudy M)
    (h : ℝ → ℝ) (hm : Measurable h) (hi : Integrable (fun o => h (W o)) M.law) :
    (∫ o, h (W o) * X o ∂M.law) = ∫ o, h (W o) * M.pi (W o) ∂M.law := by
  letI := hM.probability
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hle) := isFiniteMeasure_trim hle
  have ix : Integrable X M.law := (memLp_of_bounded
    (show ∀ᵐ o ∂M.law, X o ∈ Set.Icc (0 : ℝ) 1 from
      ae_of_all _ (fun o => by cases hx : o.2.1 <;> norm_num [X, bit, hx]))
      rcheb_measurable_X.aestronglyMeasurable 1).integrable (by simp)
  have ihx := hi.mul_bdd rcheb_measurable_X.aestronglyMeasurable
    (ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o))
  have he := condExp_mul_of_stronglyMeasurable_left
    (hm.comp (comap_measurable W)).stronglyMeasurable ihx ix
  calc
    (∫ o, h (W o) * X o ∂M.law) =
        ∫ o, condExp covariateSigma M.law (fun o => h (W o) * X o) o ∂M.law :=
      (integral_condExp hle).symm
    _ = ∫ o, h (W o) * M.pi (W o) ∂M.law := by
      apply integral_congr_ae
      filter_upwards [he, hM.propensity] with o ho hp
      exact ho.trans (congrArg (h (W o) * ·) hp)

lemma rcheb_multiplier_L2 (M : Study) (hM : ValidStudy M)
    (h : ℝ → ℝ) (hm : Measurable h) (hL : MemLp (fun o => h (W o)) 2 M.law) :
    MemLp (fun o => (1 - X o / M.pi (W o)) * h (W o)) 2 M.law := by
  apply hL.of_le_mul
    (((measurable_const.sub (rcheb_measurable_X.div
      (hM.measurable_pi.comp measurable_fst))).mul (hm.comp measurable_fst)).aestronglyMeasurable)
  filter_upwards [rcheb_pi_bounds M hM] with o ho
  simpa only [W, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right ho.2.2.2.1 (abs_nonneg (h (W o)))

lemma rcheb_multiplier_mean (M : Study) (hM : ValidStudy M)
    (h : ℝ → ℝ) (hm : Measurable h) (hi : Integrable (fun o => h (W o)) M.law) :
    (∫ o, (1 - X o / M.pi (W o)) * h (W o) ∂M.law) = 0 := by
  have mp : Measurable (fun o : Unit => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have hip : Integrable (fun o => h (W o) / M.pi (W o)) M.law := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hi.mul_bdd mp.inv.aestronglyMeasurable
      ((rcheb_pi_bounds M hM).mono (fun o ho => by simpa only [Real.norm_eq_abs, Pi.inv_apply] using ho.2.2.1))
  have hipx := hip.mul_bdd rcheb_measurable_X.aestronglyMeasurable
    (ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o))
  calc
    (∫ o, (1 - X o / M.pi (W o)) * h (W o) ∂M.law) =
      (∫ o, h (W o) - h (W o) / M.pi (W o) * X o ∂M.law) := by
        congr 1; funext o; ring
    _ = (∫ o, h (W o) ∂M.law) - ∫ o, h (W o) / M.pi (W o) * X o ∂M.law :=
      integral_sub hi hipx
    _ = (∫ o, h (W o) ∂M.law) - ∫ o, h (W o) / M.pi (W o) * M.pi (W o) ∂M.law := by
      rw [rcheb_propensity_integral M hM (fun w => h w / M.pi w) (hm.div hM.measurable_pi) hip]
    _ = 0 := by
      have he : (∫ o, h (W o) / M.pi (W o) * M.pi (W o) ∂M.law) = ∫ o, h (W o) ∂M.law := by
        apply integral_congr_ae
        filter_upwards [rcheb_pi_bounds M hM] with o ho
        exact div_mul_cancel₀ _ ho.1.ne'
      rw [he, sub_self]

lemma rcheb_multiplier_second (M : Study) (hM : ValidStudy M)
    (h : ℝ → ℝ) (hm : Measurable h) (hL : MemLp (fun o => h (W o)) 2 M.law) :
    (∫ o, ((1 - X o / M.pi (W o)) * h (W o))^2 ∂M.law) ≤
      l2Sq M h / M.delta := by
  let k : ℝ → ℝ := fun w => (-2 * (M.pi w)⁻¹ + (M.pi w)⁻¹^2) * h w ^ 2
  have mp : Measurable (fun o : Unit => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have mk : Measurable k := ((measurable_const.mul hM.measurable_pi.inv).add
    (hM.measurable_pi.inv.pow_const 2)).mul (hm.pow_const 2)
  have ik : Integrable (fun o => k (W o)) M.law := by
    apply hL.integrable_sq.bdd_mul
      (((measurable_const.mul mp.inv).add (mp.inv.pow_const 2)).aestronglyMeasurable)
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    simp only [Real.norm_eq_abs]
    calc
      |-2 * (M.pi (W o))⁻¹ + (M.pi (W o))⁻¹^2| ≤
          |-2 * (M.pi (W o))⁻¹| + |(M.pi (W o))⁻¹^2| := abs_add_le _ _
      _ ≤ 2 * M.delta⁻¹ + M.delta⁻¹^2 := by
        rw [abs_mul, abs_pow]
        norm_num only [abs_neg, Nat.abs_ofNat]
        exact add_le_add (mul_le_mul_of_nonneg_left ho.2.2.1 (by norm_num))
          (pow_le_pow_left₀ (abs_nonneg _) ho.2.2.1 2)
  have ikx := ik.mul_bdd rcheb_measurable_X.aestronglyMeasurable
    (ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o))
  have he : (fun o => ((1 - X o / M.pi (W o)) * h (W o))^2) =
      (fun o => h (W o)^2 + k (W o) * X o) := by
    funext o
    cases hx : o.2.1 <;> simp [X, bit, hx, k, div_eq_mul_inv] <;> ring
  rw [he, integral_add hL.integrable_sq ikx,
    rcheb_propensity_integral M hM k mk ik]
  have ikp : Integrable (fun o => k (W o) * M.pi (W o)) M.law := by
    apply ik.mul_bdd mp.aestronglyMeasurable
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    simpa only [Real.norm_eq_abs, abs_of_pos ho.1] using ho.2.1.le
  rw [← integral_add hL.integrable_sq ikp]
  calc
    (∫ o, h (W o)^2 + k (W o) * M.pi (W o) ∂M.law) =
        ∫ o, q M (W o) * h (W o)^2 ∂M.law := by
      apply integral_congr_ae
      filter_upwards [rcheb_pi_bounds M hM] with o ho
      dsimp [k, q]
      field_simp [ho.1.ne']
      <;> ring
    _ ≤ ∫ o, M.delta⁻¹ * h (W o)^2 ∂M.law := by
      apply integral_mono_of_nonneg
      · exact (rcheb_pi_bounds M hM).mono (fun o ho => mul_nonneg ho.2.2.2.2.1 (sq_nonneg _))
      · exact hL.integrable_sq.const_mul _
      · filter_upwards [rcheb_pi_bounds M hM] with o ho
        exact mul_le_mul_of_nonneg_right ho.2.2.2.2.2 (sq_nonneg _)
    _ = l2Sq M h / M.delta := by rw [integral_const_mul]; unfold l2Sq; ring

lemma rcheb_scaled_iid_tail {I : Type*} [Fintype I]
    (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card I ≤ n) (h : ℝ → ℝ) (hm : Measurable h)
    (hL : MemLp (fun o => h (W o)) 2 M.law) (eps : ℝ) (heps : 0 < eps) :
    ((Measure.pi (fun _ : I => M.law))
      {a | eps < |Real.sqrt n / n *
        ∑ i : I, (1 - X (a i) / M.pi (W (a i))) * h (W (a i))|}).toReal ≤
      l2Sq M h / (M.delta * eps^2) := by
  letI := hM.probability
  let f : Unit → ℝ := fun o => (1 - X o / M.pi (W o)) * h (W o)
  let P : Measure (I → Unit) := Measure.pi (fun _ => M.law)
  let S : (I → Unit) → ℝ := fun a => ∑ i, f (a i)
  let c : ℝ := Real.sqrt n / n
  have hf : MemLp f 2 M.law := rcheb_multiplier_L2 M hM h hm hL
  have hfm : (∫ o, f o ∂M.law) = 0 := rcheb_multiplier_mean M hM h hm
    (hL.integrable (by norm_num))
  have hcoord (i : I) : MemLp (fun a : I → Unit => f (a i)) 2 P :=
    hf.comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp S 2 P := memLp_finsetSum _ (fun i _ => hcoord i)
  have hSm : (∫ a, S a ∂P) = 0 := by
    have he := integral_finsetSum Finset.univ (fun i _ => (hcoord i).integrable (by norm_num))
    rw [show (∫ a, S a ∂P) = ∑ i : I, ∫ a, f (a i) ∂P by
      simpa only [S, Finset.sum_fn] using he]
    apply Finset.sum_eq_zero
    intro i hi
    change (∫ a, f (a i) ∂Measure.pi (fun _ : I => M.law)) = 0
    have hp := measurePreserving_eval (fun _ : I => M.law) i
    have hmap : AEStronglyMeasurable f (Measure.map (Function.eval i) (Measure.pi (fun _ : I => M.law))) := by
      rw [hp.map_eq]; exact hf.aestronglyMeasurable
    calc
      _ = ∫ o, f o ∂Measure.map (Function.eval i) (Measure.pi (fun _ : I => M.law)) :=
        (integral_map hp.measurable.aemeasurable hmap).symm
      _ = 0 := by rw [hp.map_eq]; exact hfm
  have hvar : variance S P = (Fintype.card I : ℝ) * variance f M.law := by
    simpa only [S, P, Finset.sum_fn, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      using (variance_sum_pi (fun _ : I => hf))
  have hcvar : variance (fun a => c * S a) P ≤ l2Sq M h / M.delta := by
    rw [variance_const_mul, hvar]
    have hfvar : variance f M.law ≤ l2Sq M h / M.delta := by
      rw [variance_of_integral_eq_zero hf.aestronglyMeasurable.aemeasurable hfm]
      exact rcheb_multiplier_second M hM h hm hL
    have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hc : 0 ≤ c^2 * (Fintype.card I : ℝ) := by positivity
    have hc1 : c^2 * (Fintype.card I : ℝ) ≤ 1 := by
      have hs := Real.sq_sqrt hnR.le
      have hcardR : (Fintype.card I : ℝ) ≤ n := by exact_mod_cast hcard
      dsimp [c]
      rw [div_pow, hs]
      rw [div_mul_eq_mul_div]
      apply (div_le_one (sq_pos_of_pos hnR)).2
      nlinarith
    calc
      c ^ 2 * ((Fintype.card I : ℝ) * variance f M.law) =
        (c^2 * (Fintype.card I : ℝ)) * variance f M.law := by ring
      _ ≤ variance f M.law := mul_le_of_le_one_left (variance_nonneg _ _) hc1
      _ ≤ _ := hfvar
  have hZ : MemLp (fun a => c * S a) 2 P := hS.const_mul _
  have hZm : (∫ a, c * S a ∂P) = 0 := by rw [integral_const_mul, hSm, mul_zero]
  have htail := meas_ge_le_variance_div_sq hZ heps
  rw [hZm] at htail
  simp only [sub_zero] at htail
  have htail' : P {a | eps < |c * S a|} ≤
      ENNReal.ofReal (variance (fun a => c * S a) P / eps^2) :=
    (measure_mono (by intro a ha; exact (show eps < |c * S a| from ha).le)).trans htail
  change (P {a | eps < |c * S a|}).toReal ≤ _
  calc
    _ ≤ variance (fun a => c * S a) P / eps^2 := by
      simpa only [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))]
        using ENNReal.toReal_mono ENNReal.ofReal_ne_top htail'
    _ ≤ (l2Sq M h / M.delta) / eps^2 := div_le_div_of_nonneg_right hcvar (sq_nonneg _)
    _ = _ := by ring

lemma rcheb_product_tail {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    (P : Measure T) (Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : T × E → ℝ) (hZ : Measurable Z) (e : T → ℝ) (he : Measurable e)
    (d eps eta : ℝ) (hd : 0 < d) (heps : 0 < eps) (heta : 0 < eta)
    (hbound : ∀ᵐ t ∂P, (Q {b | eps < |Z (t,b)|}).toReal ≤ e t / (d * eps^2)) :
    ((P.prod Q) {z | eps < |Z z|}).toReal ≤
      (P {t | eta < e t}).toReal + eta / (d * eps^2) := by
  let H : T × E → ℝ := fun z => if eps < |Z z| then 1 else 0
  let J : T → ℝ := fun t => if eta < e t then 1 else 0
  have mA : MeasurableSet {z | eps < |Z z|} := measurableSet_lt measurable_const hZ.abs
  have mB : MeasurableSet {t | eta < e t} := measurableSet_lt measurable_const he
  have mH : Measurable H := Measurable.ite mA measurable_const measurable_const
  have mJ : Measurable J := Measurable.ite mB measurable_const measurable_const
  have iH : Integrable H (P.prod Q) := Integrable.of_bound mH.aestronglyMeasurable 1
    (ae_of_all _ (fun z => by dsimp [H]; split_ifs <;> norm_num))
  have iJ : Integrable J P := Integrable.of_bound mJ.aestronglyMeasurable 1
    (ae_of_all _ (fun t => by dsimp [J]; split_ifs <;> norm_num))
  have hH : (∫ z, H z ∂P.prod Q) = ((P.prod Q) {z | eps < |Z z|}).toReal := by
    simpa [H, Set.indicator, Measure.real] using
      (integral_indicator_one (μ := P.prod Q) mA)
  have hJ : (∫ t, J t ∂P) = (P {t | eta < e t}).toReal := by
    simpa [J, Set.indicator, Measure.real] using (integral_indicator_one (μ := P) mB)
  have hsec (t : T) : (∫ b, H (t,b) ∂Q) = (Q {b | eps < |Z (t,b)|}).toReal := by
    simpa [H, Set.indicator, Measure.real] using
      (integral_indicator_one (μ := Q) (mA.preimage (measurable_const.prodMk measurable_id)))
  have hc : (∫ _ : T, eta / (d * eps^2) ∂P) = eta / (d * eps^2) := by simp
  rw [← hH, integral_prod H iH, ← hJ, ← hc, ← integral_add iJ (integrable_const _)]
  apply integral_mono_ae iH.integral_prod_left (iJ.add (integrable_const _))
  filter_upwards [hbound] with t ht
  rw [hsec]
  change (Q {b | eps < |Z (t,b)|}).toReal ≤ J t + eta / (d * eps^2)
  by_cases ht' : eta < e t
  · simp only [J, if_pos ht']
    have hQ : (Q {b | eps < |Z (t,b)|}).toReal ≤ 1 := by
      exact measureReal_le_one
    linarith [div_pos heta (mul_pos hd (sq_pos_of_pos heps))]
  · simp only [J, if_neg ht', zero_add]
    exact ht.trans (div_le_div_of_nonneg_right (le_of_not_gt ht') (by positivity))

lemma rcheb_measurable_predictor (M : Study) (hM : ValidStudy M)
    (n : ℕ) (hn : 0 < n) (F : CrossFit n) (j : Bool) (g : ℝ → ℝ)
    (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hfits : ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law)
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    (sampleLaw M n {a | eps < |Real.sqrt n * foldRemainder M F j g a|}).toReal ≤
      (sampleLaw M n {a | eta < l2Sq M (fun w => F.g j a w - g w)}).toReal +
        eta / (M.delta * eps^2) := by
  classical
  letI := hM.probability
  let p : Fin n → Prop := fun i => F.fold i ≠ j
  let T := {i : Fin n // p i} → Unit
  let E := {i : Fin n // ¬p i} → Unit
  let P : Measure T := Measure.pi (fun _ => M.law)
  let Q : Measure E := Measure.pi (fun _ => M.law)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Unit) p
  have hp : MeasurePreserving e (sampleLaw M n) (P.prod Q) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => M.law) p
  have hp' : MeasurePreserving e.symm (P.prod Q) (sampleLaw M n) :=
    MeasurePreserving.symm e hp
  let b₀ : E := fun _ => (0, (false, (false, false)))
  let base : T → Sample n := fun t => e.symm (t,b₀)
  let h : T → ℝ → ℝ := fun t w => F.g j (base t) w - g w
  have mbase : Measurable base := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have mh : Measurable (fun z : T × ℝ => h z.1 z.2) :=
    ((F.measurable_g j).comp ((mbase.comp measurable_fst).prodMk measurable_snd)).sub
      (mg.comp measurable_snd)
  have hfreeze (t : T) (b : E) : F.g j (e.symm (t,b)) = F.g j (base t) := by
    apply F.opposite_fold
    intro i hi
    have hpi : p i := hi
    congr 1
    simp [e, base, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hpi]
  let err : T → ℝ := fun t => l2Sq M (h t)
  have merr : Measurable err := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    exact ((mh.comp (measurable_fst.prodMk measurable_snd.fst)).pow_const 2).stronglyMeasurable
  let Z : T × E → ℝ := fun z => Real.sqrt n / n *
    ∑ i : {i : Fin n // ¬p i},
      (1 - X (z.2 i) / M.pi (W (z.2 i))) * h z.1 (W (z.2 i))
  have mZ : Measurable Z := by
    have mx := rcheb_measurable_X
    have mp := hM.measurable_pi
    dsimp [Z]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_const.sub ((mx.comp ((measurable_pi_apply i).comp measurable_snd)).div
      (mp.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))))).mul
      (mh.comp (measurable_fst.prodMk (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)))))
  have hZ (t : T) (b : E) :
      Real.sqrt n * foldRemainder M F j g (e.symm (t,b)) = Z (t,b) := by
    dsimp [foldRemainder, Z]
    rw [hfreeze]
    have hsum : (∑ i : Fin n, if F.fold i = j then
        (1 - X (e.symm (t,b) i) / M.pi (W (e.symm (t,b) i))) *
          (F.g j (base t) (W (e.symm (t,b) i)) - g (W (e.symm (t,b) i))) else 0) =
      ∑ i : {i : Fin n // ¬p i},
        (1 - X (b i) / M.pi (W (b i))) * h t (W (b i)) := by
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      rw [Finset.subtype_univ]
      let ee : {i : Fin n // F.fold i = j} ≃ {i : Fin n // ¬p i} :=
        Equiv.subtypeEquivRight (fun i => by dsimp [p]; tauto)
      refine Fintype.sum_equiv ee _ _ ?_
      intro i
      have hpi : ¬p i.1 := by dsimp [p]; exact not_not.2 i.2
      simp [e, h, ee, Equiv.subtypeEquivRight_apply, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hpi]
    rw [hsum]
    ring
  have hL : ∀ᵐ t ∂P, MemLp (fun o => h t (W o)) 2 M.law := by
    have hh := Measure.ae_ae_of_ae_prod (hp'.quasiMeasurePreserving.ae hfits)
    filter_upwards [hh] with t ht
    change ∀ᵐ b ∂Q, MemLp (fun o => F.g j (e.symm (t,b)) (W o)) 2 M.law at ht
    obtain ⟨b, hb⟩ := ht.exists
    have hh' : MemLp (fun o => F.g j (base t) (W o)) 2 M.law := by
      rw [hfreeze] at hb
      exact hb
    exact hh'.sub hg
  have hcard : Fintype.card {i : Fin n // ¬p i} ≤ n :=
    (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
  have hb : ∀ᵐ t ∂P, (Q {b | eps < |Z (t,b)|}).toReal ≤ err t / (M.delta * eps^2) := by
    filter_upwards [hL] with t ht
    exact rcheb_scaled_iid_tail M hM n hn hcard (h t)
      (mh.comp (measurable_const.prodMk measurable_id)) ht eps heps
  have htail := rcheb_product_tail P Q Z mZ err merr M.delta eps eta hM.delta_pos heps heta hb
  have hleft : (sampleLaw M n {a | eps < |Real.sqrt n * foldRemainder M F j g a|}) =
      (P.prod Q) {z | eps < |Z z|} := by
    rw [← hp'.measure_preimage_equiv]
    congr 1
    ext z
    exact Iff.of_eq (congrArg (fun x => eps < |x|) (hZ z.1 z.2))
  have hright : (sampleLaw M n {a | eta < l2Sq M (fun w => F.g j a w - g w)}) =
      P {t | eta < err t} := by
    rw [← hp'.measure_preimage_equiv]
    have hevent : e.symm ⁻¹' {a | eta < l2Sq M (fun w => F.g j a w - g w)} =
        {t | eta < err t} ×ˢ Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
      rw [hfreeze]
    rw [hevent, Measure.prod_prod]
    simp
  rw [hleft, hright]
  exact htail

/- The true-regression variance and normal limit. -/
lemma p4d_xy_integral (M : Study) (hM : ValidStudy M)
    (h : ℝ → ℝ) (hm : Measurable h) (hi : Integrable (fun o => h (W o)) M.law) :
    (∫ o, h (W o) * (X o * Y1 o) ∂M.law) =
      ∫ o, h (W o) * (M.pi (W o) * M.m (W o)) ∂M.law := by
  letI := hM.probability
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hle) := isFiniteMeasure_trim hle
  have mxy : Measurable (fun o => X o * Y1 o) := rcheb_measurable_X.mul
    ((measurable_of_countable bit).comp measurable_snd.snd.snd)
  have bxy : ∀ᵐ o ∂M.law, X o * Y1 o ∈ Set.Icc (0 : ℝ) 1 := by
    apply ae_of_all
    intro o
    cases hx : o.2.1 <;> cases hy : o.2.2.2 <;> norm_num [X, Y1, bit, hx, hy]
  have ixy : Integrable (fun o => X o * Y1 o) M.law :=
    (memLp_of_bounded bxy mxy.aestronglyMeasurable 1).integrable (by simp)
  have ihxy := hi.mul_bdd mxy.aestronglyMeasurable
    (bxy.mono (fun o ho => by simpa only [Real.norm_eq_abs, abs_of_nonneg ho.1] using ho.2))
  have he := condExp_mul_of_stronglyMeasurable_left
    (hm.comp (comap_measurable W)).stronglyMeasurable ihxy ixy
  calc
    (∫ o, h (W o) * (X o * Y1 o) ∂M.law) =
        ∫ o, condExp covariateSigma M.law (fun o => h (W o) * (X o * Y1 o)) o ∂M.law :=
      (integral_condExp hle).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [he, conditional_xy_factorization M hM] with o ho hp
      exact ho.trans (congrArg (h (W o) * ·) hp)

lemma p4d_summand_facts (M : Study) (hM : ValidStudy M) :
    let f := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (M.m (W o))
    MemLp f 2 M.law ∧ (∫ o, f o ∂M.law) = mu M ∧ variance f M.law = hahnBound M := by
  letI := hM.probability
  let f : Unit → ℝ := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (M.m (W o))
  have mf : Measurable f := by
    have mx := rcheb_measurable_X
    have my : Measurable Y := by
      unfold Y Y0 Y1
      exact (measurable_const.sub mx).mul ((measurable_of_countable bit).comp measurable_snd.snd.fst) |>.add
        (mx.mul ((measurable_of_countable bit).comp measurable_snd.snd.snd))
    exact ((mx.mul (my.sub (hM.measurable_m.comp measurable_fst))).div
      (hM.measurable_pi.comp measurable_fst)).add (hM.measurable_m.comp measurable_fst)
  have feq : f = fun o => htTerm (M.pi (W o)) (X o) (Y o) +
      (1 - X o / M.pi (W o)) * M.m (W o) := by
    funext o; dsimp [f, adjustedTerm, htTerm]; ring
  have hf : MemLp f 2 M.law := by
    rw [feq]
    exact (ht_unit_memLp M hM).add (rcheb_multiplier_L2 M hM M.m hM.measurable_m (p4d_regression_L2 M hM))
  have hmean : (∫ o, f o ∂M.law) = mu M := by
    rw [feq, integral_add (ht_unit_facts M hM).1
      ((rcheb_multiplier_L2 M hM M.m hM.measurable_m (p4d_regression_L2 M hM)).integrable (by norm_num)),
      (ht_unit_facts M hM).2,
      rcheb_multiplier_mean M hM M.m hM.measurable_m
        ((p4d_regression_L2 M hM).integrable (by norm_num)), add_zero]
  refine ⟨hf, hmean, ?_⟩
  have mp : Measurable (fun o : Unit => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have mm : Measurable (fun o : Unit => M.m (W o)) := hM.measurable_m.comp measurable_fst
  have hi : MemLp (fun o => (M.pi (W o))⁻¹) ⊤ M.law :=
    memLp_top_of_bound mp.inv.aestronglyMeasurable M.delta⁻¹
      ((rcheb_pi_bounds M hM).mono (fun o ho => by simpa only [Real.norm_eq_abs] using ho.2.2.1))
  have hm : MemLp (fun o => M.m (W o)) ⊤ M.law :=
    memLp_of_bounded hM.regression_range mm.aestronglyMeasurable ⊤
  have hi2 : MemLp (fun o => (M.pi (W o))⁻¹^2) ⊤ M.law := by
    simpa only [pow_two] using hi.fun_mul hi
  have hm2 : MemLp (fun o => M.m (W o)^2) ⊤ M.law := by
    simpa only [pow_two] using hm.fun_mul hm
  let a : ℝ → ℝ := fun w => (M.pi w)⁻¹^2 + 2 * M.m w * (M.pi w)⁻¹ -
    2 * M.m w * (M.pi w)⁻¹^2
  let b : ℝ → ℝ := fun w => M.m w^2 * (M.pi w)⁻¹^2 - 2 * M.m w^2 * (M.pi w)⁻¹
  have mpi0 := hM.measurable_pi
  have mm0 := hM.measurable_m
  have ma : Measurable a := by dsimp [a]; fun_prop
  have mb : Measurable b := by dsimp [b]; fun_prop
  have ha : MemLp (fun o => a (W o)) ⊤ M.law :=
    (hi2.add ((hm.const_mul 2).fun_mul hi)).sub ((hm.const_mul 2).fun_mul hi2)
  have hb : MemLp (fun o => b (W o)) ⊤ M.law :=
    (hm2.fun_mul hi2).sub ((hm2.const_mul 2).fun_mul hi)
  have ia := ha.integrable (by simp)
  have ib := hb.integrable (by simp)
  have im2 := hm2.integrable (by simp)
  have ixa := ia.mul_bdd (c := (1 : ℝ))
    (rcheb_measurable_X.mul ((measurable_of_countable bit).comp measurable_snd.snd.snd)).aestronglyMeasurable
    (ae_of_all _ (fun o => by
      cases hx : o.2.1 <;> cases hy : o.2.2.2 <;> norm_num [X, Y1, bit, hx, hy]))
  change Integrable (fun o => a (W o) * (X o * Y1 o)) M.law at ixa
  have ixb := ib.mul_bdd rcheb_measurable_X.aestronglyMeasurable
    (ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o))
  have hsq : (fun o => f o ^ 2) = fun o => M.m (W o)^2 + a (W o) * (X o * Y1 o) + b (W o) * X o := by
    funext o
    rw [feq]
    simp only [htTerm, consistency_treated]
    cases hx : o.2.1 <;> cases hy : o.2.2.2 <;>
      simp [X, Y1, bit, hx, hy, a, b, div_eq_mul_inv] <;> ring
  have hsecond : (∫ o, f o^2 ∂M.law) =
      (∫ o, M.m (W o)^2 ∂M.law) +
      ∫ o, M.m (W o) * (1 - M.m (W o)) / M.pi (W o) ∂M.law := by
    rw [hsq]
    have iadd : Integrable (fun o => M.m (W o)^2 + a (W o) * (X o * Y1 o)) M.law := im2.add ixa
    rw [integral_add iadd ixb, integral_add im2 ixa,
      p4d_xy_integral M hM a ma ia, rcheb_propensity_integral M hM b mb ib, add_assoc]
    congr 1
    have ip : MemLp (fun o => M.pi (W o)) ⊤ M.law :=
      memLp_of_bounded ((rcheb_pi_bounds M hM).mono (fun o ho => ⟨ho.1.le, ho.2.1.le⟩))
        mp.aestronglyMeasurable ⊤
    have hapi : MemLp (fun o => a (W o) * (M.pi (W o) * M.m (W o))) ⊤ M.law :=
      ha.fun_mul (ip.fun_mul (r := ⊤) hm)
    have hbpi : MemLp (fun o => b (W o) * M.pi (W o)) ⊤ M.law := hb.fun_mul ip
    rw [← integral_add (hapi.integrable (by simp)) (hbpi.integrable (by simp))]
    apply integral_congr_ae
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    dsimp [a, b]
    field_simp [ho.1.ne']
    <;> ring
  rw [variance_eq_sub hf]
  simp only [Pi.pow_apply]
  rw [hsecond, hmean]
  unfold hahnBound
  rw [variance_eq_sub (p4d_regression_L2 M hM), regression_mean M hM]
  simp only [Pi.pow_apply]
  ring

lemma p4d_remainder_negligible (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (hconv : ∀ j, L2InProbability M F j M.m)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law)
    (j : Bool) (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun n => (sampleLaw M n {a | eps <
      |Real.sqrt n * foldRemainder M (F n) j M.m a|}).toReal) atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le ENNReal.toReal_nonneg)
  · intro b hb
    let eta : ℝ := b * (M.delta * eps^2) / 2
    have hd : 0 < M.delta * eps^2 := by positivity [hM.delta_pos]
    have heta : 0 < eta := div_pos (mul_pos hb hd) (by norm_num)
    have hsmall := (tendsto_order.1 (hconv j eta heta)).2 (b/2) (by linarith)
    filter_upwards [hsmall, eventually_ge_atTop 1] with n hnerr hn
    have hbound := rcheb_measurable_predictor M hM n (by omega) (F n) j M.m
      hM.measurable_m (p4d_regression_L2 M hM) (hfitsL2 n j) eps eta heps heta
    have heta' : eta / (M.delta * eps^2) = b/2 := by dsimp [eta]; field_simp [hM.delta_pos.ne', heps.ne']
    rw [heta'] at hbound
    linarith

lemma p4d_measurable_Y : Measurable Y := by
  unfold Y Y0 Y1
  have mx := rcheb_measurable_X
  exact (measurable_const.sub mx).mul ((measurable_of_countable bit).comp measurable_snd.snd.fst) |>.add
    (mx.mul ((measurable_of_countable bit).comp measurable_snd.snd.snd))

lemma p4d_measurable_adjusted (M : Study) (hM : ValidStudy M) {n : ℕ} (F : CrossFit n) :
    Measurable (adjusted M F) := by
  unfold adjusted
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  have mev : Measurable (fun a : Sample n => a i) := measurable_pi_apply i
  have mw : Measurable (fun a : Sample n => W (a i)) := measurable_fst.comp mev
  have mg := (F.measurable_g (F.fold i)).comp (measurable_id.prodMk mw)
  exact (((rcheb_measurable_X.comp mev).mul ((p4d_measurable_Y.comp mev).sub mg)).div
    (hM.measurable_pi.comp mw)).add mg

lemma p4d_normal_limit (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (hconv : ∀ j, L2InProbability M F j M.m)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) :
    NormalLimit M (fun n => adjusted M (F n)) (hahnBound M) := by
  letI := hM.probability
  let f : Unit → ℝ := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (M.m (W o))
  have mf : Measurable f :=
    ((rcheb_measurable_X.mul (p4d_measurable_Y.sub (hM.measurable_m.comp measurable_fst))).div
      (hM.measurable_pi.comp measurable_fst)).add (hM.measurable_m.comp measurable_fst)
  have hf := p4d_summand_facts M hM
  have hm : (∫ o, f o ∂M.law) = mu M := hf.2.1
  have hv : variance f M.law = hahnBound M := hf.2.2
  let A : ∀ n, Sample n → ℝ := fun n a => Real.sqrt n * (fixedAdjusted M M.m a - mu M)
  let B : ∀ n, Sample n → ℝ := fun n a => Real.sqrt n * (adjusted M (F n) a - mu M)
  have hA : TendstoInDistribution A atTop (fun z : ℝ => z) (fun n => sampleLaw M n)
      (gaussianReal 0 (hahnBound M).toNNReal) := by
    simpa only [hm, hv, A, f, fixedAdjusted, sampleLaw] using iid_mean_normal M.law f mf hf.1
  have mB (n : ℕ) : AEMeasurable (B n) (sampleLaw M n) :=
    ((p4d_measurable_adjusted M hM (F n)).sub measurable_const).const_mul _ |>.aemeasurable
  have hdist : ∀ eps > 0, Tendsto (fun n => (sampleLaw M n).real
      {a | eps ≤ dist (A n a) (B n a)}) atTop (nhds 0) := by
    intro eps heps
    have hr0 := p4d_remainder_negligible M hM F hconv hfitsL2 false (eps/3) (by linarith)
    have hr1 := p4d_remainder_negligible M hM F hconv hfitsL2 true (eps/3) (by linarith)
    have hsum := hr0.add hr1
    simp only [zero_add] at hsum
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
    intro n
    have hs : {a : Sample n | eps ≤ dist (A n a) (B n a)} ⊆
        {a | eps/3 < |Real.sqrt n * foldRemainder M (F n) false M.m a|} ∪
        {a | eps/3 < |Real.sqrt n * foldRemainder M (F n) true M.m a|} := by
      intro a ha
      by_contra hnot
      have hn0 : |Real.sqrt n * foldRemainder M (F n) false M.m a| ≤ eps/3 := by
        exact le_of_not_gt (fun h => hnot (Or.inl h))
      have hn1 : |Real.sqrt n * foldRemainder M (F n) true M.m a| ≤ eps/3 := by
        exact le_of_not_gt (fun h => hnot (Or.inr h))
      have he := crossfit_decomposition M (F n) (fun _ => M.m) a
      have hlead : leading M (F n) (fun _ => M.m) a = fixedAdjusted M M.m a := rfl
      rw [hlead] at he
      have hd : dist (A n a) (B n a) ≤
          |Real.sqrt n * foldRemainder M (F n) false M.m a| +
          |Real.sqrt n * foldRemainder M (F n) true M.m a| := by
        rw [Real.dist_eq]
        have hid : A n a - B n a = -(Real.sqrt n * foldRemainder M (F n) false M.m a +
            Real.sqrt n * foldRemainder M (F n) true M.m a) := by dsimp [A, B]; rw [he]; ring
        rw [hid, abs_neg]
        exact abs_add_le _ _
      change eps ≤ dist (A n a) (B n a) at ha
      linarith
    exact (measureReal_mono hs).trans (measureReal_union_le _ _)
  have hweakA : AronowAudit.P061.Analytic.WeakConvergesLaw
      (fun n => (sampleLaw M n).map (A n)) (gaussianReal 0 (hahnBound M).toNNReal) := by
    have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hA.tendsto
    intro test
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id'] using hh test
  have hweakB := AronowAudit.P061.Analytic.weakConvergesLaw_slutsky_dist
    hA.forall_aemeasurable mB hweakA hdist
  refine ⟨hM.probability, mB, measurable_id.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro test
  simpa only [ProbabilityMeasure.coe_mk, B, Measure.map_id'] using hweakB test

theorem proposition4d_proof (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (hbal : Balanced F) (hconv : ∀ j, L2InProbability M F j M.m)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) :
    NormalLimit M (fun n => adjusted M (F n)) (hahnBound M) := by
  exact p4d_normal_limit M hM F hconv hfitsL2

/- Transfer from a Borel version to an arbitrary L2 predictor. -/
theorem remainder_chebyshev_proof (M : Study) (hM : ValidStudy M)
    (n : ℕ) (hn : 0 < n) (F : CrossFit n) (j : Bool) (g : ℝ → ℝ)
    (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hfits : ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law)
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    (sampleLaw M n {a | eps < |Real.sqrt n * foldRemainder M F j g a|}).toReal ≤
      (sampleLaw M n {a | eta < l2Sq M (fun w => F.g j a w - g w)}).toReal +
        eta / (M.delta * eps^2) := by
  letI := hM.probability
  obtain ⟨g₀, mg₀, heq⟩ := rcheb_finite_fiber_version M.law g hg.aestronglyMeasurable
  have hg₀ : MemLp (fun o => g₀ (W o)) 2 M.law := (memLp_congr_ae heq).2 hg
  have herr (a : Sample n) : l2Sq M (fun w => F.g j a w - g w) =
      l2Sq M (fun w => F.g j a w - g₀ w) := by
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [show g₀ (W o) = g (W o) from ho]
  have hcoord : ∀ᵐ a ∂sampleLaw M n, ∀ i : Fin n, g₀ (W (a i)) = g (W (a i)) := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => M.law) i).quasiMeasurePreserving.ae heq
  have hR : foldRemainder M F j g =ᵐ[sampleLaw M n] foldRemainder M F j g₀ := by
    filter_upwards [hcoord] with a ha
    unfold foldRemainder
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ha i]
  have htail : (sampleLaw M n {a | eps < |Real.sqrt n * foldRemainder M F j g a|}) =
      (sampleLaw M n {a | eps < |Real.sqrt n * foldRemainder M F j g₀ a|}) := by
    apply measure_congr
    filter_upwards [hR] with a ha
    simp only [Set.mem_setOf_eq, ha]
  have hevent : {a | eta < l2Sq M (fun w => F.g j a w - g w)} =
      {a | eta < l2Sq M (fun w => F.g j a w - g₀ w)} := by
    ext a
    change (eta < l2Sq M (fun w => F.g j a w - g w)) ↔
      (eta < l2Sq M (fun w => F.g j a w - g₀ w))
    rw [herr]
  rw [htail, hevent]
  exact rcheb_measurable_predictor M hM n hn F j g₀ mg₀ hg₀ hfits eps eta heps heta

end AronowAudit.P046.Wave1
