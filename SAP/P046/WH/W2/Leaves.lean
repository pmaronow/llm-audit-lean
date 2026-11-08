import SAP.P046.Defs.WholeW2
import SAP.P046.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- A common covariate-only localization for all evaluated predictions.
For each covariate vector, sum the absolute predictions over all indices and
all binary full-data label vectors with these covariates. This is a finite,
measurable envelope. Its sublevel indicators tend pointwise to one and bound
every localized prediction. Integrability then follows from finite measure.
This uses finiteness of the binary labels, not integrability of the original fits. -/
def T8_L1 : Prop := ∀ (M : Study), ValidStudy M → ∀ (n : ℕ) (F : CrossFit n),
  ∃ c : ℕ → Sample n → ℝ,
    (∀ k, Measurable (c k)) ∧
    (∀ k a, 0 ≤ c k a ∧ c k a ≤ 1) ∧
    (∀ k a b, covariates a = covariates b → c k a = c k b) ∧
    (∀ a, Tendsto (fun k => c k a) atTop (nhds 1)) ∧
    ∀ k i, Integrable (fun a => c k a * wholePrediction F i a) (sampleLaw M n)

/-- Leave-one-out cancellation for an integrable prediction that may depend on
all other units and on its own covariate, but not on its own binary labels.
Split off coordinate i with measurePreserving_piFinSuccAbove. Freeze the other
coordinates, use the stated invariance to obtain a measurable function of W_i,
and apply proposition4a_multiplier_cancel. Fubini is legitimate because H is
integrable and the multiplier is bounded by positivity. Adapt
proposition4a_augmentation; no fitted-value moment assumption is hidden here. -/
def T8_L2 : Prop := ∀ (M : Study), ValidStudy M → ∀ (n : ℕ) (i : Fin n)
    (H : Sample n → ℝ), Measurable H → Integrable H (sampleLaw M n) →
    (∀ a b, (∀ k, k ≠ i → a k = b k) → W (a i) = W (b i) → H a = H b) →
    (∫ a, (1 - X (a i) / M.pi (W (a i))) * H a ∂sampleLaw M n) = 0

/-- Opposite-fold conditional independence. Split off observation i, noting
that its fitted function is unchanged when that observation is replaced.
Test with bounded Borel indicators and condition on W_i. The remaining
coordinates have their original product law and are independent of unit i.
No fitted-value moment condition is needed. One can alternatively test
leave-one-out cancellation against covariate and prediction indicators. -/
def T8_L3 : Prop := ∀ (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (i : Fin n), wholeFitIndependent M hM.probability F i

/-- The guarded printed fitted-term expectation chain. Given conditional
independence, use the binary treatment indicator and L1 approximation of the
prediction to obtain conditional factorization. Pull out 1/pi(W_i), use the
tower property, and cancel E[X_i|W_i]=pi(W_i); the latter follows by transporting
the stored single-unit propensity along the product-coordinate projection.
Positivity bounds the treatment multiplier and ensures all guarded quantities
are integrable. Do not assume that the fitted regression is correctly specified. -/
def T8_L4 : Prop := ∀ (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (i : Fin n), wholeFitIndependent M hM.probability F i →
    wholeFitMoments M F i

/-- The technical interface supplied by localization. The real squared errors
are used only after square integrability has been established. -/
def LocalizedSequence (M : Study) (F G : ∀ n, CrossFit n)
    (g : Bool → ℝ → ℝ) : Prop :=
  (∀ n, WholeLocalization M (F n) (G n) g) ∧
  (∀ n j a, MemLp (fun o => (G n).g j a (W o)) 2 M.law) ∧
  (∀ n j a, 0 ≤ l2Sq M (fun w => (G n).g j a w - g j w) ∧
    l2Sq M (fun w => (G n).g j a w - g j w) ≤ 1) ∧
  (∀ n j a, ENNReal.ofReal (l2Sq M (fun w => (G n).g j a w - g j w)) =
    if wholeL2Error M (F n) j (g j) a ≤ 1
    then wholeL2Error M (F n) j (g j) a else 0)

/-- Construct localized CrossFits and their finite-error interface.
The extended error is measurable by Measurable.lintegral_prod_right' and depends
only on the training fold. Thus its sublevel event gives a measurable valid
CrossFit with unchanged folds. On that event the error is L2 by
hasFiniteIntegral_iff_ofReal and memLp_two_iff_integrable_sq; add the reference
L2 function. Off the event the error is zero. Use
ofReal_integral_eq_lintegral_ofReal only on the finite-error event.
This is one localization construction, including its analytic specification. -/
def T9_L1 : Prop := ∀ (M : Study), ValidStudy M → ∀ (F : ∀ n, CrossFit n)
    (g : Bool → ℝ → ℝ), (∀ j, Measurable (g j)) →
    (∀ j, MemLp (fun o => g j (W o)) 2 M.law) →
    ∃ G : ∀ n, CrossFit n, LocalizedSequence M F G g

/-- Extended mean-square convergence implies extended-error convergence in
probability. Apply the nonnegative Markov bound before taking limits.
An extended expectation may be infinite at initial sample sizes; convergence
to zero gives eventual finite upper bounds and suffices for the argument. -/
def T9_L2 : Prop := ∀ (M : Study), ValidStudy M → ∀ (F : ∀ n, CrossFit n)
    (j : Bool) (g : ℝ → ℝ), Measurable g →
    WholeL2InMeanSquare M F j g → WholeL2InProbability_W2 M F j g

/-- Localization converts extended-error consistency in probability into both
of the existing real-error convergence predicates. The localized real error
lies in [0,1], and its tail is bounded by the original extended-error tail.
For 0<eta<1 split its expectation at eta to get E[D_local] <= eta+P(D>eta).
The bound also proves integrability for every n, as required by the old donor.
This is a bounded-expectation argument across changing sample spaces, not a
pointwise dominated-convergence assertion on those different spaces. -/
def T9_L3 : Prop := ∀ (M : Study), ValidStudy M →
    ∀ (F G : ∀ n, CrossFit n) (g : Bool → ℝ → ℝ),
    (∀ j, Measurable (g j)) → LocalizedSequence M F G g →
    (∀ j, WholeL2InProbability_W2 M F j (g j)) →
    ∀ j, L2InMeanSquare M G j (g j) ∧ L2InProbability M G j (g j)

/-- Transfer the numerical Gaussian limit through asymptotic equality.
CrossFit measurability makes both adjusted statistics measurable. The distance
between their root-n transforms exceeds any positive threshold only on the
disagreement event. Use weakConvergesLaw_slutsky_dist and translate its bounded
continuous test formulation back to TendstoInDistribution. Preserve v>=0 and
the point-mass convention at v=0. No moments of the original fits are needed. -/
def T9_L4 : Prop := ∀ (M : Study), ValidStudy M →
    ∀ (F G : ∀ n, CrossFit n) (v : ℝ),
    WholeAsymptoticAgreement M (fun n => adjusted M (F n))
      (fun n => adjusted M (G n)) →
    NormalLimit M (fun n => adjusted M (G n)) v →
    NormalLimit M (fun n => adjusted M (F n)) v

private theorem ht_chain (M : Study) (hM : ValidStudy M) : wholeHTChain M := by
  have hx := AronowAudit.P046.conditional_xy_factorization (Bridge.toStudy M) (Bridge.valid_to hM)
  have hreg := AronowAudit.P046.regression_mean (Bridge.toStudy M) (Bridge.valid_to hM)
  have hf : Integrable (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law ∧
      (∫ o, htTerm (M.pi (W o)) (X o) (Y o) ∂M.law) = mu M :=
    AronowAudit.P046.ht_unit_facts (Bridge.toStudy M) (Bridge.valid_to hM)
  have hs (o : Unit) : X o * Y o = X o * Y1 o :=
    AronowAudit.P046.consistency_treated o
  have hi : Integrable (fun o => X o * Y1 o / M.pi (W o)) M.law := by
    simpa only [htTerm, hs] using hf.1
  have hm : (∫ o, X o * Y1 o / M.pi (W o) ∂M.law) = mu M := by
    simpa only [htTerm, hs] using hf.2
  have hleft : (∫ o, condExp covariateSigma M.law (fun u => X u * Y1 u) o /
      M.pi (W o) ∂M.law) = mu M := by
    calc
      _ = ∫ o, M.m (W o) ∂M.law := by
        apply integral_congr_ae
        filter_upwards [hx, hM.positivity] with o ho hp
        change condExp covariateSigma M.law (fun u => X u * Y1 u) o =
          M.pi (W o) * M.m (W o) at ho
        rw [ho, mul_div_cancel_left₀ _ (hM.delta_pos.trans hp.1).ne']
      _ = mu M := hreg
  have hright : (∫ o, condExp covariateSigma M.law X o *
      condExp covariateSigma M.law Y1 o / M.pi (W o) ∂M.law) = mu M := by
    calc
      _ = ∫ o, M.m (W o) ∂M.law := by
        apply integral_congr_ae
        filter_upwards [hM.propensity, hM.regression, hM.positivity] with o hp hr hb
        rw [hp, hr, mul_div_cancel_left₀ _ (hM.delta_pos.trans hb.1).ne']
      _ = mu M := hreg
  exact ⟨hi, hm.trans hleft.symm, hleft.trans hright.symm, hright⟩

private theorem prediction_measurable {n : ℕ} (F : CrossFit n) (i : Fin n) :
    Measurable (wholePrediction F i) :=
  (F.measurable_g _).comp (measurable_id.prodMk
    (measurable_fst.comp (measurable_pi_apply i)))

private theorem localized_unbiased (h1 : T8_L1) (h2 : T8_L2)
    (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n) (F : CrossFit n)
    (hint : Integrable (adjusted M F) (sampleLaw M n)) :
    (∫ a, adjusted M F a ∂sampleLaw M n) = mu M := by
  let _ := hM.probability
  obtain ⟨c, hcm, hcb, hcw, hct, hci⟩ := h1 M hM n F
  have hlp : MemLp (ht M (n := n)) 2 (sampleLaw M n) :=
    AronowAudit.P046.ht_sample_memLp (Bridge.toStudy M) (Bridge.valid_to hM) n
  have hiht := hlp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hR := hint.sub hiht
  have hpoint (a : Sample n) : adjusted M F a - ht M a =
      (∑ i, (1 - X (a i) / M.pi (W (a i))) * wholePrediction F i a) / n := by
    have hd (p x y g : ℝ) : adjustedTerm p x y g = htTerm p x y + (1 - x / p) * g :=
      AronowAudit.P046.adjusted_decomposition p x y g
    simp only [adjusted, hd,
      Finset.sum_add_distrib, add_div, ht, wholePrediction]
    ring
  have hsum (k : ℕ) :
      (fun a => c k a * (adjusted M F a - ht M a)) =
      (fun a => (∑ i, (1 - X (a i) / M.pi (W (a i))) *
        (c k a * wholePrediction F i a)) / n) := by
    funext a
    rw [hpoint, ← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hz (k : ℕ) (i : Fin n) :
      (∫ a, (1 - X (a i) / M.pi (W (a i))) *
        (c k a * wholePrediction F i a) ∂sampleLaw M n) = 0 := by
    apply h2 M hM n i _ ((hcm k).mul (prediction_measurable F i)) (hci k i)
    intro a b hab hw
    have hwab : covariates a = covariates b := by
      funext l
      by_cases hl : l = i
      · subst l; exact hw
      · exact congrArg W (hab l hl)
    have hg : F.g (F.fold i) a = F.g (F.fold i) b := by
      apply F.opposite_fold
      intro l hl
      exact congrArg observe (hab l (by rintro rfl; exact hl rfl))
    change c k a * wholePrediction F i a = c k b * wholePrediction F i b
    simp only [wholePrediction, hcw k a b hwab, hg, hw]
  have hia (k : ℕ) (i : Fin n) : Integrable
      (fun a => (1 - X (a i) / M.pi (W (a i))) *
        (c k a * wholePrediction F i a)) (sampleLaw M n) := by
    apply (hci k i).bdd_mul
    · exact (AronowAudit.P046.Wave1.proposition4a_multiplier_measurable
        (Bridge.toStudy M) (Bridge.valid_to hM)).aestronglyMeasurable.comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin n => M.law) i)
    · exact (measurePreserving_eval (fun _ : Fin n => M.law) i).quasiMeasurePreserving.ae
        (AronowAudit.P046.Wave1.proposition4a_multiplier_bound
          (Bridge.toStudy M) (Bridge.valid_to hM))
  have hzR (k : ℕ) : (∫ a, c k a * (adjusted M F a - ht M a) ∂sampleLaw M n) = 0 := by
    rw [hsum, integral_div, integral_finsetSum _ (fun i _ => hia k i)]
    simp only [hz, Finset.sum_const_zero, zero_div]
  have hlim : Tendsto (fun k => ∫ a, c k a * (adjusted M F a - ht M a) ∂sampleLaw M n)
      atTop (nhds (∫ a, adjusted M F a - ht M a ∂sampleLaw M n)) := by
    apply tendsto_integral_of_dominated_convergence (fun a => ‖adjusted M F a - ht M a‖)
    · intro k
      exact (hcm k).aestronglyMeasurable.mul hR.aestronglyMeasurable
    · exact hR.norm
    · intro k
      exact Filter.Eventually.of_forall fun a => by
        rw [norm_mul, Real.norm_eq_abs (c k a), abs_of_nonneg (hcb k a).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (hcb k a).2
    · exact Filter.Eventually.of_forall fun a => by
        simpa only [one_mul] using (hct a).mul_const (adjusted M F a - ht M a)
  have hzero : (∫ a, adjusted M F a - ht M a ∂sampleLaw M n) = 0 := by
    apply tendsto_nhds_unique hlim
    simpa only [hzR] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hu : (∫ a, ht M a ∂sampleLaw M n) = mu M :=
    AronowAudit.P046.ht_unbiased (Bridge.toStudy M) (Bridge.valid_to hM) n hn
  rw [integral_sub hint hiht, hu] at hzero
  exact sub_eq_zero.mp hzero

/-- The new work is localization, leave-one-out cancellation, and the conditional
fitted-term chain. Algebra, HT chains, and the dominated limit are proved here. -/
theorem T8_assembly (h1 : T8_L1) (h2 : T8_L2) (h3 : T8_L3) (h4 : T8_L4) :
    T8WholeStatement := by
  classical
  intro M hM n hn F
  let _ := hM.probability
  have hht := ht_chain M hM
  have hchain (i : Fin n) : wholeFitChain M hM.probability F i :=
    ⟨h3 M hM n F i, h4 M hM n F i (h3 M hM n F i)⟩
  have heval (i : Fin n) :
      (∫ a, X (a i) * Y1 (a i) / M.pi (W (a i)) ∂sampleLaw M n) = mu M := by
    have hp : MeasurePreserving (fun a : Sample n => a i) (sampleLaw M n) M.law :=
      measurePreserving_eval (fun _ : Fin n => M.law) i
    have hi : AEStronglyMeasurable (fun o => X o * Y1 o / M.pi (W o))
        (Measure.map (fun a : Sample n => a i) (sampleLaw M n)) := by
      rw [hp.map_eq]
      exact hht.1.aestronglyMeasurable
    have he := integral_map hp.measurable.aemeasurable hi
    rw [hp.map_eq] at he
    exact he.symm.trans ((hht.2.1.trans hht.2.2.1).trans hht.2.2.2)
  refine ⟨localized_unbiased h1 h2 M hM n hn F, ?_, hht, heval, hchain, ?_⟩
  · intro a
    refine ⟨fun i => AronowAudit.P046.consistency_treated (a i), ?_⟩
    have hterm (i : Fin n) :
        adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i)) (wholePrediction F i a) =
        X (a i) * Y1 (a i) / M.pi (W (a i)) -
          wholeWeightedPrediction M F i a + wholePrediction F i a := by
      unfold adjustedTerm wholeWeightedPrediction
      have hs : X (a i) * Y (a i) = X (a i) * Y1 (a i) :=
        AronowAudit.P046.consistency_treated (a i)
      rw [mul_sub, sub_div, hs]
    change (∑ i, adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i))
      (wholePrediction F i a)) / n = _
    simp only [hterm, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, add_div, sub_div]
  · intro hint
    have hj (i : Fin n) := ((hchain i).2 (hint i)).1
    have hc (i : Fin n) : (∫ a, wholeWeightedPrediction M F i a ∂sampleLaw M n) =
        ∫ a, wholePrediction F i a ∂sampleLaw M n :=
      (((hchain i).2 (hint i)).2.2.1).trans
        (((hchain i).2 (hint i)).2.2.2)
    have hcount : (∑ _i : Fin n, mu M) / n = mu M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')
    refine ⟨?_, ?_, hcount⟩
    · rw [integral_div, integral_div,
        integral_finsetSum _ (fun i _ => hj i), integral_finsetSum _ (fun i _ => hint i)]
      simp only [hc]
    · rw [hcount]
      exact Bridge.target8 M hM n hn F hint

private theorem balanced_localized (M : Study) (F G : ∀ n, CrossFit n)
    (g : Bool → ℝ → ℝ) (h : ∀ n, WholeLocalization M (F n) (G n) g)
    (hbal : Balanced F) : Balanced G := by
  intro j
  simpa only [(h _).1] using hbal j

private theorem agreement_localized (M : Study) (hM : ValidStudy M)
    (F G : ∀ n, CrossFit n) (g : Bool → ℝ → ℝ)
    (hl : ∀ n, WholeLocalization M (F n) (G n) g)
    (hp : ∀ j, WholeL2InProbability_W2 M F j (g j)) :
    WholeAsymptoticAgreement M (fun n => adjusted M (F n))
      (fun n => adjusted M (G n)) := by
  let _ := hM.probability
  let E (n : ℕ) (j : Bool) : Set (Sample n) :=
    {a | (1 : ℝ≥0∞) < wholeL2Error M (F n) j (g j) a}
  have hsub (n : ℕ) : {a | adjusted M (F n) a ≠ adjusted M (G n) a} ⊆
      E n false ∪ E n true := by
    intro a ha
    by_contra hbad
    have hgood (j : Bool) : wholeL2Error M (F n) j (g j) a ≤ 1 := by
      apply le_of_not_gt
      intro h
      cases j
      · exact hbad (Or.inl h)
      · exact hbad (Or.inr h)
    have heq : adjusted M (G n) a = adjusted M (F n) a := by
      unfold adjusted
      rw [(hl n).1]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [(hl n).2]
      simp only [wholeLocalPrediction, hgood _, ite_true]
    exact ha heq.symm
  have hlim : Tendsto (fun n => (sampleLaw M n (E n false)).toReal +
      (sampleLaw M n (E n true)).toReal) atTop (nhds 0) := by
    simpa only [E, ENNReal.ofReal_one, add_zero] using
      (hp false 1 (by norm_num)).add (hp true 1 (by norm_num))
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hlim
  intro n
  exact (measureReal_mono (hsub n)).trans (measureReal_union_le _ _)

private theorem rootN_of_agreement (M : Study) (hM : ValidStudy M)
    (A B : ∀ n, Sample n → ℝ) (ha : WholeAsymptoticAgreement M A B)
    (hr : RootN M B) : RootN M A := by
  let _ := hM.probability
  intro eps heps
  obtain ⟨C, hC, N, hN⟩ := hr (eps / 2) (by positivity)
  have hsmall : ∀ᶠ n in atTop,
      (sampleLaw M n {a | A n a ≠ B n a}).toReal < eps / 2 :=
    (tendsto_order.1 ha).2 _ (by positivity)
  obtain ⟨N', hN'⟩ := eventually_atTop.1 hsmall
  refine ⟨C, hC, max N N', ?_⟩
  intro n hn
  have hsub : {a | C < Real.sqrt n * |A n a - mu M|} ⊆
      {a | C < Real.sqrt n * |B n a - mu M|} ∪ {a | A n a ≠ B n a} := by
    intro a ha
    by_cases heq : A n a = B n a
    · apply Or.inl
      change C < Real.sqrt n * |A n a - mu M| at ha
      change C < Real.sqrt n * |B n a - mu M|
      rwa [heq] at ha
    · exact Or.inr heq
  have hbound := (measureReal_mono (μ := sampleLaw M n) hsub).trans
    (measureReal_union_le _ _)
  have hb := hN n ((le_max_left _ _).trans hn)
  have hd := (hN' n ((le_max_right _ _).trans hn)).le
  simp only [Measure.real] at hbound
  linarith

/-- Apply the existing theorems to localized fits, then transfer the results to
the original fits using agreement with probability tending to one. -/
theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) (h3 : T9_L3)
    (h4 : T9_L4) : T9WholeStatement := by
  constructor
  · intro M hM F hbal g hgm hg hconv
    obtain ⟨G, hG⟩ := h1 M hM F g hgm hg
    have hp : ∀ j, WholeL2InProbability_W2 M F j (g j) :=
      fun j => h2 M hM F j (g j) (hgm j) (hconv j)
    have hlocal := h3 M hM F G g hgm hG hp
    have hroot : RootN M (fun n => adjusted M (G n)) :=
      Bridge.target9.1 M hM G (balanced_localized M F G g hG.1 hbal) g hg
        (fun j => (hlocal j).1)
        (fun n j => Filter.Eventually.of_forall (hG.2.1 n j))
    exact rootN_of_agreement M hM _ _ (agreement_localized M hM F G g hG.1 hp) hroot
  · intro M hM F hbal hconv
    let g : Bool → ℝ → ℝ := fun _ => M.m
    have hgm : ∀ j, Measurable (g j) := fun _ => hM.measurable_m
    have hg : ∀ j, MemLp (fun o => g j (W o)) 2 M.law := fun _ =>
      AronowAudit.P046.Wave1.p4d_regression_L2 (Bridge.toStudy M) (Bridge.valid_to hM)
    obtain ⟨G, hG⟩ := h1 M hM F g hgm hg
    have hlocal := h3 M hM F G g hgm hG hconv
    have hnormal : NormalLimit M (fun n => adjusted M (G n)) (hahnBound M) :=
      Bridge.target9.2 M hM G (balanced_localized M F G g hG.1 hbal)
        (fun j => (hlocal j).2)
        (fun n j => Filter.Eventually.of_forall (hG.2.1 n j))
    exact h4 M hM F G (hahnBound M) (agreement_localized M hM F G g hG.1 hconv) hnormal

end
end SAP.P046.WH.W2
