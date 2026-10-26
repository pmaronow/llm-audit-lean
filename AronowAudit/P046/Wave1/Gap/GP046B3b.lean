import AronowAudit.P046.Wave1.Gap.RepairT4
import AronowAudit.P046.Wave1.Gap.GP046B3
import AronowAudit.P046.Wave1.Gap.GP046B4
import AronowAudit.P046.Wave1.Gap.GP046B5

namespace AronowAudit.P046.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open RegressionExample in
theorem crossfit_counterexample_proof : ValidStudy study ∧ mu study = 1/20 ∧
    Balanced fits ∧ (∀ j, L2InProbability study fits j (prediction 0)) ∧
    (∀ n j, ∀ᵐ a ∂sampleLaw study n, ∀ theta,
      empiricalRisk study (Finset.univ.filter (fun i => (fits n).fold i ≠ j)) a (prediction 0) ≤
      empiricalRisk study (Finset.univ.filter (fun i => (fits n).fold i ≠ j)) a (prediction theta)) ∧
    (∀ n : ℕ, 0 < n →
      (∫ a, ht study a ∂sampleLaw study n) = mu study ∧
      (∫ a, adjusted study (fits n) a ∂sampleLaw study n) = mu study ∧
      variance (ht study (n := n)) (sampleLaw study n) = 79/(400*n) ∧
      variance (adjusted study (fits n)) (sampleLaw study n) = 169/(400*n)) ∧
    NormalLimit study (fun _ => ht study) (79/400) ∧
    NormalLimit study (fun n => adjusted study (fits n)) (169/400) ∧
    (79/400 : ℝ) < 169/400 ∧
    (∀ theta, weightedNormSq study (prediction theta) = 3/8 + theta^2/6) ∧
    risk study (fun _ => 0) = 3/20 ∧ risk study (prediction 0) = 3/8 := by
  exact regression_counterexample_proof


lemma GP046B3b_summand_facts (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    let f := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))
    MemLp f 2 M.law ∧ (∫ o, f o ∂M.law) = mu M ∧ variance f M.law = V M g := by
  letI := hM.probability
  let f : Unit → ℝ := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))
  have feq : f = fun o => htTerm (M.pi (W o)) (X o) (Y o) +
      (1 - X o / M.pi (W o)) * g (W o) := by
    funext o; dsimp [f, adjustedTerm, htTerm]; ring
  have hf : MemLp f 2 M.law := by
    rw [feq]
    exact (ht_unit_memLp M hM).add (rcheb_multiplier_L2 M hM g mg hg)
  have hmean : (∫ o, f o ∂M.law) = mu M := by
    rw [feq, integral_add (ht_unit_facts M hM).1
      ((rcheb_multiplier_L2 M hM g mg hg).integrable (by norm_num)),
      (ht_unit_facts M hM).2,
      rcheb_multiplier_mean M hM g mg (hg.integrable (by norm_num)), add_zero]
  refine ⟨hf, hmean, ?_⟩
  have mp : Measurable (fun o : Unit => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have hy := risk_expansion_y_memLp M hM
  have hi : Integrable (fun o : Unit => (M.pi (W o))⁻¹) M.law := by
    apply Integrable.of_bound mp.inv.aestronglyMeasurable M.delta⁻¹
    exact (rcheb_pi_bounds M hM).mono (fun o ho => by simpa only [Real.norm_eq_abs, Pi.inv_apply] using ho.2.2.1)
  have hgip : Integrable (fun o => (g (W o))^2 / M.pi (W o)) M.law := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hg.integrable_sq.mul_bdd mp.inv.aestronglyMeasurable
      ((rcheb_pi_bounds M hM).mono (fun o ho => by simpa only [Real.norm_eq_abs, Pi.inv_apply] using ho.2.2.1))
  have hxg := hgip.mul_bdd rcheb_measurable_X.aestronglyMeasurable
    (ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o))
  have mxy : Measurable (fun o => X o * Y1 o) := rcheb_measurable_X.mul
    ((measurable_of_countable bit).comp measurable_snd.snd.snd)
  have hxy := hi.mul_bdd (c := (1 : ℝ)) mxy.aestronglyMeasurable
    (ae_of_all _ (fun o => by
      cases hx : o.2.1 <;> cases ht : o.2.2.2 <;> norm_num [X, Y1, bit, hx, ht]))
  have hT : (∫ o, (M.pi (W o))⁻¹ * (X o * Y1 o) ∂M.law) = mu M := by
    rw [(population_criterion_transfer M hM (fun w => (M.pi w)⁻¹) hM.measurable_pi.inv hi).2]
    apply integral_congr_ae
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    field_simp [ho.1.ne']
  have hG : (∫ o, ((g (W o))^2 / M.pi (W o)) * X o ∂M.law) =
      ∫ o, (g (W o))^2 ∂M.law := by
    rw [(population_criterion_transfer M hM (fun w => (g w)^2 / M.pi w)
      ((mg.pow_const 2).div hM.measurable_pi) hgip).1]
    apply integral_congr_ae
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    exact div_mul_cancel₀ _ ho.1.ne'
  let H : Unit → ℝ := fun o => X o * (1 - M.pi (W o)) / (M.pi (W o))^2 *
    (Y o - g (W o))^2
  have iH : Integrable H M.law := by
    have iH' : Integrable (fun o => (1 - M.pi (W o)) / (M.pi (W o))^2 *
        (Y1 o - g (W o))^2) M.law :=
      (hy.sub hg).integrable_sq.bdd_mul
        (((measurable_const.sub mp).div (mp.pow_const 2)).aestronglyMeasurable)
        (population_criterion_k_bound M hM)
    have h := iH'.mul_bdd rcheb_measurable_X.aestronglyMeasurable
      (ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o))
    apply h.congr
    apply ae_of_all
    intro o
    cases hx : o.2.1 <;> simp [H, X, Y, bit, hx] <;> ring
  have hs : (fun o => f o^2) =ᵐ[M.law] fun o =>
      H o + (g (W o))^2 + (M.pi (W o))⁻¹ * (X o * Y1 o) -
        ((g (W o))^2 / M.pi (W o)) * X o := by
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    cases hx : o.2.1 <;> cases ht : o.2.2.2 <;>
      simp [f, H, adjustedTerm, X, Y, Y0, Y1, bit, hx, ht] <;>
      field_simp [ho.1.ne'] <;> ring
  have hsecond : (∫ o, f o^2 ∂M.law) = risk M g + mu M := by
    have iHg : Integrable (fun o => H o + (g (W o))^2) M.law := iH.add hg.integrable_sq
    have iS : Integrable (fun o => H o + (g (W o))^2 +
        (M.pi (W o))⁻¹ * (X o * Y1 o)) M.law := iHg.add hxy
    rw [integral_congr_ae hs, integral_sub iS hxg,
      integral_add iHg hxy, integral_add iH hg.integrable_sq,
      hT, hG]
    have hh : (∫ o, H o ∂M.law) = risk M g := population_weighted_criterion_proof M hM g hg
    rw [hh]; ring
  rw [variance_eq_sub hf]
  simp only [Pi.pow_apply]
  rw [hsecond, hmean]
  unfold V
  rw [variance_eq_sub hy]
  have hy2 : (fun o => Y1 o ^ 2) = Y1 := by
    funext o; cases ht : o.2.2.2 <;> simp [Y1, bit, ht]
  simp only [Pi.pow_apply, hy2]
  unfold mu
  ring

lemma GP046B3b_remainder_negligible (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (g : ℝ → ℝ) (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hconv : ∀ j, L2InProbability M F j g)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law)
    (j : Bool) (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun n => (sampleLaw M n {a | eps <
      |Real.sqrt n * foldRemainder M (F n) j g a|}).toReal) atTop (nhds 0) := by
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
    have hbound := remainder_chebyshev_proof M hM n (by omega) (F n) j g
      hg (hfitsL2 n j) eps eta heps heta
    have heta' : eta / (M.delta * eps^2) = b/2 := by dsimp [eta]; field_simp [hM.delta_pos.ne', heps.ne']
    rw [heta'] at hbound
    linarith


lemma GP046B3b_normal_limit_borel (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hconv : ∀ j, L2InProbability M F j g)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) :
    NormalLimit M (fun n => adjusted M (F n)) (V M g) := by
  letI := hM.probability
  let f : Unit → ℝ := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))
  have mf : Measurable f :=
    ((rcheb_measurable_X.mul (p4d_measurable_Y.sub (mg.comp measurable_fst))).div
      (hM.measurable_pi.comp measurable_fst)).add (mg.comp measurable_fst)
  have hf := GP046B3b_summand_facts M hM g mg hg
  have hm : (∫ o, f o ∂M.law) = mu M := hf.2.1
  have hv : variance f M.law = V M g := hf.2.2
  let A : ∀ n, Sample n → ℝ := fun n a => Real.sqrt n * (fixedAdjusted M g a - mu M)
  let B : ∀ n, Sample n → ℝ := fun n a => Real.sqrt n * (adjusted M (F n) a - mu M)
  have hA : TendstoInDistribution A atTop (fun z : ℝ => z) (fun n => sampleLaw M n)
      (gaussianReal 0 (V M g).toNNReal) := by
    simpa only [hm, hv, A, f, fixedAdjusted, sampleLaw] using iid_mean_normal M.law f mf hf.1
  have mB (n : ℕ) : AEMeasurable (B n) (sampleLaw M n) :=
    ((p4d_measurable_adjusted M hM (F n)).sub measurable_const).const_mul _ |>.aemeasurable
  have hdist : ∀ eps > 0, Tendsto (fun n => (sampleLaw M n).real
      {a | eps ≤ dist (A n a) (B n a)}) atTop (nhds 0) := by
    intro eps heps
    have hr0 := GP046B3b_remainder_negligible M hM F g hg hconv hfitsL2 false (eps/3) (by linarith)
    have hr1 := GP046B3b_remainder_negligible M hM F g hg hconv hfitsL2 true (eps/3) (by linarith)
    have hsum := hr0.add hr1
    simp only [zero_add] at hsum
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
    intro n
    have hs : {a : Sample n | eps ≤ dist (A n a) (B n a)} ⊆
        {a | eps/3 < |Real.sqrt n * foldRemainder M (F n) false g a|} ∪
        {a | eps/3 < |Real.sqrt n * foldRemainder M (F n) true g a|} := by
      intro a ha
      by_contra hnot
      have hn0 : |Real.sqrt n * foldRemainder M (F n) false g a| ≤ eps/3 := by
        exact le_of_not_gt (fun h => hnot (Or.inl h))
      have hn1 : |Real.sqrt n * foldRemainder M (F n) true g a| ≤ eps/3 := by
        exact le_of_not_gt (fun h => hnot (Or.inr h))
      have he := crossfit_decomposition M (F n) (fun _ => g) a
      have hlead : leading M (F n) (fun _ => g) a = fixedAdjusted M g a := rfl
      rw [hlead] at he
      have hd : dist (A n a) (B n a) ≤
          |Real.sqrt n * foldRemainder M (F n) false g a| +
          |Real.sqrt n * foldRemainder M (F n) true g a| := by
        rw [Real.dist_eq]
        have hid : A n a - B n a = -(Real.sqrt n * foldRemainder M (F n) false g a +
            Real.sqrt n * foldRemainder M (F n) true g a) := by dsimp [A, B]; rw [he]; ring
        rw [hid, abs_neg]
        exact abs_add_le _ _
      change eps ≤ dist (A n a) (B n a) at ha
      linarith
    exact (measureReal_mono hs).trans (measureReal_union_le _ _)
  have hweakA : AronowAudit.P061.Analytic.WeakConvergesLaw
      (fun n => (sampleLaw M n).map (A n)) (gaussianReal 0 (V M g).toNNReal) := by
    have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hA.tendsto
    intro test
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id'] using hh test
  have hweakB := AronowAudit.P061.Analytic.weakConvergesLaw_slutsky_dist
    hA.forall_aemeasurable mB hweakA hdist
  refine ⟨hM.probability, mB, measurable_id.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro test
  simpa only [ProbabilityMeasure.coe_mk, B, Measure.map_id'] using hweakB test


lemma GP046B3b_normal_limit (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (g : ℝ → ℝ) (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hconv : ∀ j, L2InProbability M F j g)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) :
    NormalLimit M (fun n => adjusted M (F n)) (V M g) := by
  obtain ⟨g₀, mg₀, heq⟩ := rcheb_finite_fiber_version M.law g hg.aestronglyMeasurable
  have hg₀ : MemLp (fun o => g₀ (W o)) 2 M.law := (memLp_congr_ae heq).2 hg
  have hc : ∀ j, L2InProbability M F j g₀ := by
    intro j eps heps
    have herr (n : ℕ) (a : Sample n) : l2Sq M (fun w => (F n).g j a w - g₀ w) =
        l2Sq M (fun w => (F n).g j a w - g w) := by
      apply integral_congr_ae
      filter_upwards [heq] with o ho
      rw [show g₀ (W o) = g (W o) from ho]
    simpa only [herr] using hconv j eps heps
  have hv : V M g₀ = V M g := by
    unfold V risk
    congr 1
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [show g₀ (W o) = g (W o) from ho]
  rw [← hv]
  exact GP046B3b_normal_limit_borel M hM F g₀ mg₀ hg₀ hc hfitsL2

theorem proposition4c_direct_proof (M : Study) (hM : ValidStudy M)
    (F : ∀ n, CrossFit n) (hbal : Balanced F) (gstar : ℝ → ℝ)
    (hg : MemLp (fun o => gstar (W o)) 2 M.law)
    (hconv : ∀ j, L2InProbability M F j gstar)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law)
    (hbetter : risk M gstar ≤ risk M (fun _ => 0)) :
    NormalLimit M (fun n => adjusted M (F n)) (V M gstar) ∧
    NormalLimit M (fun _ => ht M) (V M (fun _ => 0)) ∧ V M gstar ≤ V M (fun _ => 0) := by
  refine ⟨GP046B3b_normal_limit M hM F gstar hg hconv hfitsL2, ?_, ?_⟩
  · let Z : ∀ n, CrossFit n := fun n =>
      { fold := (F n).fold
        g := fun _ _ _ => 0
        measurable_g := fun _ => measurable_const
        opposite_fold := fun _ _ _ _ => rfl }
    have hz : MemLp (fun _ : Unit => (0 : ℝ)) 2 M.law := MemLp.zero
    have hc : ∀ j, L2InProbability M Z j (fun _ => 0) := by
      intro j eps heps
      simp only [L2InProbability, Z, l2Sq, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, integral_zero, gt_iff_lt] at *
      simpa [not_lt_of_ge heps.le] using tendsto_const_nhds (x := (0 : ℝ))
    have hfits : ∀ n j, ∀ᵐ a ∂sampleLaw M n,
        MemLp (fun o => (Z n).g j a (W o)) 2 M.law := fun _ _ => ae_of_all _ (fun _ => hz)
    have hn := GP046B3b_normal_limit M hM Z (fun _ => 0) hz hc hfits
    have he : (fun n => adjusted M (Z n)) = (fun _ => ht M) := by
      funext n a
      simp [adjusted, Z, adjustedTerm, ht, htTerm]
    rw [he] at hn
    exact hn
  · exact add_le_add_right hbetter _

theorem proposition4c_corrected_proof (M : Study) (hM : ValidStudy M)
    (d : ℕ) (family : (Fin d → ℝ) → ℝ → ℝ) (F : ∀ n, CrossFit n) (hbal : Balanced F)
    (hG : ∀ theta, MemLp (fun o => family theta (W o)) 2 M.law)
    (hzero : ZeroBenchmark M (Set.range family))
    (hfit : ∀ n j, ∀ᵐ a ∂sampleLaw M n, ∃ theta,
      (F n).g j a = family theta ∧ ∀ eta,
      empiricalRisk M (Finset.univ.filter (fun i => (F n).fold i ≠ j)) a (family theta) ≤
      empiricalRisk M (Finset.univ.filter (fun i => (F n).fold i ≠ j)) a (family eta))
    (gstar : ℝ → ℝ) (hstar : gstar ∈ Set.range family)
    (hmin : ∀ theta, risk M gstar ≤ risk M (family theta))
    (hconv : ∀ j, L2InProbability M F j gstar)
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) :
    NormalLimit M (fun n => adjusted M (F n)) (V M gstar) ∧
    NormalLimit M (fun _ => ht M) (V M (fun _ => 0)) ∧ V M gstar ≤ V M (fun _ => 0) := by
  have hGL2 : ∀ g ∈ Set.range family, MemLp (fun o => g (W o)) 2 M.law := by
    rintro g ⟨theta, rfl⟩
    exact hG theta
  have hbetter : risk M gstar ≤ risk M (fun _ => 0) :=
    zero_benchmark_risk_proof M hM (Set.range family) hGL2 hzero gstar hstar
      (by rintro g ⟨theta, rfl⟩; exact hmin theta)
  exact proposition4c_direct_proof M hM F hbal gstar (hGL2 _ hstar) hconv hfitsL2 hbetter

end
end AronowAudit.P046.Wave1
