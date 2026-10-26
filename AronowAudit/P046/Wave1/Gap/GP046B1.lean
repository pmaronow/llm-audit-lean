import AronowAudit.P046.P046_Audit

namespace AronowAudit.P046.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

/-- Bounded finite-table functions have actual finite Bochner integrals. -/
private theorem rr_laws_valid_int {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsFiniteMeasure ν] (f : A → ℝ) (hf : Measurable f)
    (hr : ∀ a, 0 ≤ f a ∧ f a ≤ 1) : Integrable f ν := by
  exact memLp_one_iff_integrable.1
    (memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ hr) hf.aestronglyMeasurable 1)

private theorem rr_laws_valid_bern_range (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (f : Bool → ℝ) (hf : ∀ b, 0 ≤ f b ∧ f b ≤ 1) :
    0 ≤ bernE p f ∧ bernE p f ≤ 1 := by
  dsimp [bernE]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) (hf false).1) (mul_nonneg hp.1 (hf true).1)
  · nlinarith [(mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr (hf false).2)),
      mul_nonneg hp.1 (sub_nonneg.mpr (hf true).2)]

private theorem rr_laws_valid_gen_meas (p m : ℝ → ℝ) (hp : Measurable p) (hm : Measurable m) :
    Measurable (RobinsRitov.generate p m) := by
  exact measurable_fst.fst.prodMk
    ((measurable_threshold _ _ measurable_fst.snd (hp.comp measurable_fst.fst)).prodMk
      (measurable_const.prodMk
        (measurable_threshold _ _ measurable_snd (hm.comp measurable_fst.fst))))

private def rr_laws_valid_study (p m : ℝ → ℝ) : Study :=
  ⟨Measure.map (RobinsRitov.generate p m) ((unitUniform.prod unitUniform).prod unitUniform),
    p, m, 1/8⟩

/-- Conditional table for the actual independent-uniform generator. -/
private theorem rr_laws_valid_table (p m : ℝ → ℝ) (hp : Measurable p) (hm : Measurable m)
    (hpr : ∀ w, 0 ≤ p w ∧ p w ≤ 1) (hmr : ∀ w, 0 ≤ m w ∧ m w ≤ 1)
    (f : Bool → Bool → ℝ) (hf : ∀ x y, 0 ≤ f x y ∧ f x y ≤ 1) :
    condExp covariateSigma (rr_laws_valid_study p m).law (fun o => f o.2.1 o.2.2.2) =ᵐ[(rr_laws_valid_study p m).law]
      fun o => bernE (p (W o)) (fun x => bernE (m (W o)) (f x)) := by
  let gen := RobinsRitov.generate p m
  let ν := (unitUniform.prod unitUniform).prod unitUniform
  let M := rr_laws_valid_study p m
  have mg : Measurable gen := rr_laws_valid_gen_meas p m hp hm
  have mp : IsProbabilityMeasure M.law := by dsimp [M, rr_laws_valid_study]; infer_instance
  letI := mp
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hle) := isFiniteMeasure_trim hle
  let F : Unit → ℝ := fun o => f o.2.1 o.2.2.2
  let G : ℝ → ℝ := fun w => bernE (p w) (fun x => bernE (m w) (f x))
  have mF : Measurable F :=
    (measurable_of_countable (Function.uncurry f)).comp (measurable_snd.fst.prodMk measurable_snd.snd.snd)
  have mG : Measurable G := by dsimp [G, bernE]; fun_prop
  have rG : ∀ w, 0 ≤ G w ∧ G w ≤ 1 := fun w =>
    rr_laws_valid_bern_range _ (hpr w) _ (fun x => rr_laws_valid_bern_range _ (hmr w) _ (hf x))
  have mGW : Measurable[covariateSigma] (fun o => G (W o)) := mG.comp (comap_measurable W)
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle (rr_laws_valid_int M.law F mF (fun o => hf _ _))
    (fun s _ _ => (rr_laws_valid_int M.law _ (mG.comp measurable_fst) (fun o => rG _)).integrableOn)
    _ mGW.aestronglyMeasurable
  intro s hs _
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← integral_indicator (ht.preimage (show Measurable W from measurable_fst)),
    ← integral_indicator (ht.preimage (show Measurable W from measurable_fst))]
  change (∫ o, (W ⁻¹' t).indicator (fun o => G (W o)) o ∂Measure.map gen ν) =
    ∫ o, (W ⁻¹' t).indicator F o ∂Measure.map gen ν
  erw [integral_map mg.aemeasurable ((mG.comp measurable_fst).indicator
    (ht.preimage measurable_fst)).aestronglyMeasurable,
    integral_map mg.aemeasurable (mF.indicator (ht.preimage measurable_fst)).aestronglyMeasurable]
  have hleft : (fun z => (W ⁻¹' t).indicator (fun o => G (W o)) (gen z)) =
      (fun z : (ℝ × ℝ) × ℝ => t.indicator G z.1.1) := rfl
  erw [hleft]
  change (∫ z : (ℝ × ℝ) × ℝ, t.indicator G z.1.1
    ∂((unitUniform.prod unitUniform).prod unitUniform)) = _
  rw [integral_fun_fst (fun z : ℝ × ℝ => t.indicator G z.1),
    integral_fun_fst (t.indicator G)]
  simp only [probReal_univ, one_smul]
  change (∫ w, t.indicator G w ∂unitUniform) =
    ∫ z, (W ⁻¹' t).indicator F (gen z) ∂ν
  have mH : Measurable (fun z => (W ⁻¹' t).indicator F (gen z)) :=
    (mF.indicator (ht.preimage measurable_fst)).comp mg
  have rH : ∀ z, 0 ≤ (W ⁻¹' t).indicator F (gen z) ∧
      (W ⁻¹' t).indicator F (gen z) ≤ 1 := by
    intro z
    by_cases h : W (gen z) ∈ t <;> simp [Set.indicator, h, F, hf]
  rw [integral_prod _ (rr_laws_valid_int ν _ mH rH)]
  rw [integral_prod _ (rr_laws_valid_int ν _ mH rH).integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change t.indicator G w = ∫ u, ∫ v,
    (W ⁻¹' t).indicator F (gen ((w,u),v)) ∂unitUniform ∂unitUniform
  by_cases hw : w ∈ t
  · simp only [Set.indicator_of_mem hw]
    have he (u v : ℝ) : (W ⁻¹' t).indicator F (gen ((w,u),v)) =
        f (decide (u ≤ p w)) (decide (v ≤ m w)) := by
      have hz : gen ((w,u),v) ∈ W ⁻¹' t := hw
      exact Set.indicator_of_mem hz F
    simp_rw [he, unitUniform_bernE _ (hmr w).1 (hmr w).2]
    rw [unitUniform_bernE (p w) (hpr w).1 (hpr w).2 (fun x => bernE (m w) (f x))]
  · simp only [Set.indicator_of_notMem hw]
    have he (u v : ℝ) : (W ⁻¹' t).indicator F (gen ((w,u),v)) = 0 := by
      have hz : gen ((w,u),v) ∉ W ⁻¹' t := hw
      exact Set.indicator_of_notMem hz F
    simp_rw [he, integral_zero]


private theorem rr_laws_valid_valid (p m : ℝ → ℝ) (hp : Measurable p) (hm : Measurable m)
    (δ : ℝ) (hδ : 0 < δ) (hpr : ∀ w, δ < p w ∧ p w < 1-δ) (hmr : ∀ w, 0 ≤ m w ∧ m w ≤ 1) :
    ValidStudy {rr_laws_valid_study p m with delta := δ} := by
  let M := {rr_laws_valid_study p m with delta := δ}
  have hpr' : ∀ w, 0 ≤ p w ∧ p w ≤ 1 := fun w => ⟨by linarith [(hpr w).1], by linarith [(hpr w).2]⟩
  have mg := rr_laws_valid_gen_meas p m hp hm
  have prob : IsProbabilityMeasure M.law := by dsimp [M, rr_laws_valid_study]; infer_instance
  letI := prob
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  have hW : Measure.map W M.law = unitUniform := by
    change Measure.map W (Measure.map _ _) = _
    rw [Measure.map_map (show Measurable W from measurable_fst) mg]
    change Measure.map (Prod.fst ∘ Prod.fst) ((unitUniform.prod unitUniform).prod unitUniform) = _
    rw [← Measure.map_map measurable_fst measurable_fst]
    simp
  have hzero : Y0 =ᵐ[M.law] fun _ => (0 : ℝ) := by
    apply (ae_map_iff mg.aemeasurable (measurableSet_eq_fun my0 measurable_const)).2
    exact ae_of_all _ (fun _ => by simp [RobinsRitov.generate, Y0, bit])
  refine ⟨prob, atomless_of_uniform_marginal _ hW, hp, hm, hδ,
    ae_of_all _ (fun o => hpr (W o)), ?_, ?_, ae_of_all _ (fun o => hmr (W o)),
    ?_, ?_⟩
  · have h := rr_laws_valid_table p m hp hm hpr' hmr (fun x _ => bit x)
      (fun x _ => by cases x <;> norm_num [bit])
    have he : (fun o : Unit => bernE (p (W o)) (fun x => bernE (m (W o)) (fun _ => bit x))) =
        (fun o => p (W o)) := by funext o; simp [bernE, bit] <;> ring
    rw [he] at h
    exact h
  · have h := rr_laws_valid_table p m hp hm hpr' hmr (fun _ y => bit y)
      (fun _ y => by cases y <;> norm_num [bit])
    have he : (fun o : Unit => bernE (p (W o)) (fun _ => bernE (m (W o)) bit)) =
        (fun o => m (W o)) := by funext o; simp [bernE, bit] <;> ring
    rw [he] at h
    exact h
  · exact condIndepFun_congr_left covariateSigma M.law hle Y0 (fun _ => 0) X
      my0 measurable_const mx hzero (condIndepFun_const_left 0 X)
  · classical
    change CondIndepFun covariateSigma hle Y1 X M.law
    apply (condIndepFun_iff_condExp_inter_preimage_eq_mul my1 mx).mpr
    intro s t hs ht
    let f1 : Bool → Bool → ℝ := fun _ y => if bit y ∈ s then 1 else 0
    let f2 : Bool → Bool → ℝ := fun x _ => if bit x ∈ t then 1 else 0
    let f : Bool → Bool → ℝ := fun x y => f1 x y * f2 x y
    have h := rr_laws_valid_table p m hp hm hpr' hmr f
      (fun x y => by dsimp [f, f1, f2]; split_ifs <;> norm_num)
    have h1 := rr_laws_valid_table p m hp hm hpr' hmr f1 (fun x y => by dsimp [f1]; split <;> norm_num)
    have h2 := rr_laws_valid_table p m hp hm hpr' hmr f2 (fun x y => by dsimp [f2]; split <;> norm_num)
    have he : (Y1 ⁻¹' s ∩ X ⁻¹' t).indicator (fun _ => (1 : ℝ)) =
        (fun o : Unit => f o.2.1 o.2.2.2) := by
      funext o
      by_cases hs' : bit o.2.2.2 ∈ s <;> by_cases ht' : bit o.2.1 ∈ t <;>
        simp [Set.indicator, Y1, X, f, f1, f2, hs', ht']
    have he1 : (Y1 ⁻¹' s).indicator (fun _ => (1 : ℝ)) =
        (fun o : Unit => f1 o.2.1 o.2.2.2) := by
      funext o
      simp only [Set.indicator, Set.mem_preimage, Y1, f1]
    have he2 : (X ⁻¹' t).indicator (fun _ => (1 : ℝ)) =
        (fun o : Unit => f2 o.2.1 o.2.2.2) := by
      funext o
      simp only [Set.indicator, Set.mem_preimage, X, f2]
    rw [he, he1, he2]
    filter_upwards [h, h1, h2] with o ho ho1 ho2
    rw [ho, ho1, ho2]
    dsimp [f, f1, f2, bernE]
    ring

private theorem rr_laws_valid_mean (p m : ℝ → ℝ) (hp : Measurable p) (hm : Measurable m)
    (hpr : ∀ w, 0 ≤ p w ∧ p w ≤ 1) (hmr : ∀ w, 0 ≤ m w ∧ m w ≤ 1) :
    mu (rr_laws_valid_study p m) = ∫ w, m w ∂unitUniform := by
  have mg := rr_laws_valid_gen_meas p m hp hm
  have mb : Measurable bit := measurable_of_countable _
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  unfold mu rr_laws_valid_study
  rw [integral_map mg.aemeasurable my1.aestronglyMeasurable]
  have mi : Measurable (fun z => Y1 (RobinsRitov.generate p m z)) := my1.comp mg
  have hi := rr_laws_valid_int ((unitUniform.prod unitUniform).prod unitUniform) _ mi
    (fun z => by dsimp [Y1, bit]; split <;> norm_num)
  rw [integral_prod _ hi]
  simp_rw [show ∀ z : ℝ × ℝ, (∫ v, Y1 (RobinsRitov.generate p m (z,v)) ∂unitUniform) = m z.1 by
    intro z
    change (∫ v, bit (decide (v ≤ m z.1)) ∂unitUniform) = m z.1
    rw [unitUniform_bernE _ (hmr z.1).1 (hmr z.1).2]
    simp [bernE, bit]]
  rw [integral_fun_fst]
  simp


private def exact_noncoverage_lower {n : ℕ} (c : Fin n → Fin 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i ≠ 2)
private def exact_noncoverage_success {n : ℕ} (c : Fin n → Fin 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = 0)
private def exact_noncoverage_pattern {n : ℕ} (T A : Finset (Fin n)) (i : Fin n) : Fin 3 :=
  if i ∈ T then if i ∈ A then 0 else 1 else 2

private theorem exact_noncoverage_pattern_lower {n : ℕ} (T A : Finset (Fin n)) :
    exact_noncoverage_lower (exact_noncoverage_pattern T A) = T := by
  ext i
  by_cases ht : i ∈ T <;> by_cases ha : i ∈ A <;> simp [exact_noncoverage_lower, exact_noncoverage_pattern, ht, ha]

private theorem exact_noncoverage_pattern_success {n : ℕ} (T A : Finset (Fin n)) (hAT : A ⊆ T) :
    exact_noncoverage_success (exact_noncoverage_pattern T A) = A := by
  ext i
  simp only [exact_noncoverage_success, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : i ∈ A
  · simp [exact_noncoverage_pattern, hA, hAT hA]
  · by_cases ht : i ∈ T <;> simp [exact_noncoverage_pattern, hA, ht]

private theorem exact_noncoverage_restore {n : ℕ} (c : Fin n → Fin 3) :
    exact_noncoverage_pattern (exact_noncoverage_lower c) (exact_noncoverage_success c) = c := by
  funext i
  have hi : c i = 0 ∨ c i = 1 ∨ c i = 2 := by omega
  rcases hi with h | h | h <;> simp [exact_noncoverage_pattern, exact_noncoverage_lower, exact_noncoverage_success, h]

private theorem exact_noncoverage_sum_patterns {n : ℕ} (F : (Fin n → Fin 3) → ℝ) :
    (∑ c, F c) = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∑ A ∈ T.powerset, F (exact_noncoverage_pattern T A) := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun c _ => ⟨exact_noncoverage_lower c, exact_noncoverage_success c⟩)
  · intro c _
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.subset_univ, true_and]
    intro i hi
    simp only [exact_noncoverage_success, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [exact_noncoverage_lower, hi]
  · intro c _ d _ h
    have ht : exact_noncoverage_lower c = exact_noncoverage_lower d := congrArg Sigma.fst h
    have ha : exact_noncoverage_success c = exact_noncoverage_success d := by simpa using congrArg (fun z => z.2) h
    rw [← exact_noncoverage_restore c, ← exact_noncoverage_restore d, ht, ha]
  · intro b hb
    rcases b with ⟨T,A⟩
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hb
    exact ⟨exact_noncoverage_pattern T A, Finset.mem_univ _, by
      simp [exact_noncoverage_pattern_lower, exact_noncoverage_pattern_success T A hb.2]⟩
  · intro c _
    rw [exact_noncoverage_restore]

private theorem exact_noncoverage_prod_pattern {n : ℕ} (T A : Finset (Fin n)) (hAT : A ⊆ T)
    (a b d : ℝ) :
    (∏ i : Fin n, if exact_noncoverage_pattern T A i = 0 then a else if exact_noncoverage_pattern T A i = 1 then b else d) =
      a^A.card * b^(T.card-A.card) * d^(n-T.card) := by
  classical
  have hf : (fun i : Fin n => if exact_noncoverage_pattern T A i = 0 then a else
      if exact_noncoverage_pattern T A i = 1 then b else d) =
      (fun i => if i ∈ T then if i ∈ A then a else b else d) := by
    funext i
    by_cases ht : i ∈ T <;> by_cases ha : i ∈ A <;> simp [exact_noncoverage_pattern, ht, ha]
  rw [hf, Finset.prod_ite, Finset.prod_ite]
  have hT : Finset.univ.filter (fun i : Fin n => i ∈ T) = T := by ext i; simp
  have hTA : T.filter (fun i => i ∈ A) = A := by
    ext i; simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hAT h,h⟩⟩
  have hTnA : T.filter (fun i => i ∉ A) = T \ A := by ext i; simp
  have hnT : (Finset.univ.filter (fun i : Fin n => i ∉ T)).card = n-T.card := by
    rw [show Finset.univ.filter (fun i : Fin n => i ∉ T) = Finset.univ \ T by ext i; simp,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [hT, hTA, hTnA]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset hAT, hnT]

/-- Enumerate category vectors by a lower-bin subset and its success subset. -/
private theorem exact_noncoverage_multinomial {n : ℕ} (F : ℕ → ℕ → ℝ) (a b d : ℝ) :
    (∑ c : Fin n → Fin 3, F (exact_noncoverage_lower c).card (exact_noncoverage_success c).card *
      ∏ i, if c i = 0 then a else if c i = 1 then b else d) =
    ∑ k ∈ Finset.range (n+1), ∑ s ∈ Finset.range (k+1),
      (n.choose k : ℝ) * (k.choose s : ℝ) * F k s * a^s * b^(k-s) * d^(n-k) := by
  classical
  rw [exact_noncoverage_sum_patterns, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k hk
  have hinner (T : Finset (Fin n)) (hT : T ∈ Finset.univ.powersetCard k) :
      (∑ A ∈ T.powerset,
        F (exact_noncoverage_lower (exact_noncoverage_pattern T A)).card (exact_noncoverage_success (exact_noncoverage_pattern T A)).card *
          ∏ i, if exact_noncoverage_pattern T A i = 0 then a else if exact_noncoverage_pattern T A i = 1 then b else d) =
      ∑ s ∈ Finset.range (k+1), (k.choose s : ℝ) * F k s * a^s * b^(k-s) * d^(n-k) := by
    have hcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
    simp_rw [exact_noncoverage_pattern_lower]
    calc
      _ = ∑ A ∈ T.powerset, F k A.card * (a^A.card * b^(k-A.card) * d^(n-k)) := by
        apply Finset.sum_congr rfl
        intro A hA
        have hs := Finset.mem_powerset.mp hA
        rw [exact_noncoverage_pattern_success T A hs, exact_noncoverage_prod_pattern T A hs, hcard]
      _ = _ := by
        rw [Finset.sum_powerset, hcard]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_powersetCard s T (fun r => F k r * (a^r * b^(k-r) * d^(n-k)))]
        simp only [hcard, nsmul_eq_mul]
        ring
  calc
    _ = ∑ _T ∈ Finset.univ.powersetCard k,
        ∑ s ∈ Finset.range (k+1), (k.choose s : ℝ) * F k s * a^s * b^(k-s) * d^(n-k) :=
      Finset.sum_congr rfl hinner
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring


private def exact_noncoverage_cat (o : Unit) : Fin 3 :=
  if W o ≤ 3/5 then if o.2.1 then 0 else 1 else 2

private theorem exact_noncoverage_cat_meas : Measurable exact_noncoverage_cat := by
  unfold exact_noncoverage_cat
  exact (measurable_const.ite (measurable_snd.fst (measurableSet_singleton true))
    measurable_const).ite (measurableSet_le measurable_fst measurable_const) measurable_const

private theorem exact_noncoverage_cat_mass (j : Fin 3) :
    (Measure.map exact_noncoverage_cat IntervalExample.study.law).real {j} =
      if j = 0 then 39/100 else if j = 1 then 21/100 else 40/100 := by
  have mc := exact_noncoverage_cat_meas
  have mg := IntervalExample.measurable_generate
  change (Measure.map exact_noncoverage_cat (Measure.map IntervalExample.generate (unitUniform.prod unitUniform))).real {j} = _
  rw [Measure.map_map mc mg, Measure.real, Measure.map_apply (mc.comp mg) (measurableSet_singleton j)]
  have hc (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : unitUniform ((Set.Iic p)ᶜ) = ENNReal.ofReal (1-p) := by
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, unitUniform_Iic p h0 h1]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 h0]
  fin_cases j
  · change ((unitUniform.prod unitUniform) ((exact_noncoverage_cat ∘ IntervalExample.generate) ⁻¹' {(0 : Fin 3)})).toReal = (39/100 : ℝ)
    have he : (exact_noncoverage_cat ∘ IntervalExample.generate) ⁻¹' {(0 : Fin 3)} =
        Set.Iic (3/5 : ℝ) ×ˢ Set.Iic (13/20 : ℝ) := by
      ext z
      by_cases hw : z.1 ≤ (3/5 : ℝ) <;> by_cases hu : z.2 ≤ (13/20 : ℝ) <;>
        simp [Function.comp_def, exact_noncoverage_cat, IntervalExample.generate, W, IntervalExample.score, hw, hu, Prod.le_def] <;> linarith
    rw [he, Measure.prod_prod, unitUniform_Iic _ (by norm_num) (by norm_num),
      unitUniform_Iic _ (by norm_num) (by norm_num), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  · change ((unitUniform.prod unitUniform) ((exact_noncoverage_cat ∘ IntervalExample.generate) ⁻¹' {(1 : Fin 3)})).toReal = (21/100 : ℝ)
    have he : (exact_noncoverage_cat ∘ IntervalExample.generate) ⁻¹' {(1 : Fin 3)} =
        Set.Iic (3/5 : ℝ) ×ˢ (Set.Iic (13/20 : ℝ))ᶜ := by
      ext z
      by_cases hw : z.1 ≤ (3/5 : ℝ) <;> by_cases hu : z.2 ≤ (13/20 : ℝ) <;>
        simp [Function.comp_def, exact_noncoverage_cat, IntervalExample.generate, W, IntervalExample.score, hw, hu, Prod.le_def] <;> linarith
    rw [he, Measure.prod_prod, unitUniform_Iic _ (by norm_num) (by norm_num),
      hc _ (by norm_num) (by norm_num), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  · change ((unitUniform.prod unitUniform) ((exact_noncoverage_cat ∘ IntervalExample.generate) ⁻¹' {(2 : Fin 3)})).toReal = (40/100 : ℝ)
    have he : (exact_noncoverage_cat ∘ IntervalExample.generate) ⁻¹' {(2 : Fin 3)} =
        (Set.Iic (3/5 : ℝ))ᶜ ×ˢ Set.univ := by
      ext z
      by_cases hw : z.1 ≤ (3/5 : ℝ) <;> by_cases hu : z.2 ≤ (13/20 : ℝ) <;>
        simp [Function.comp_def, exact_noncoverage_cat, IntervalExample.generate, W, IntervalExample.score, hw, hu, Prod.le_def] <;> linarith
    rw [he, Measure.prod_prod, hc _ (by norm_num) (by norm_num), measure_univ, mul_one,
      ENNReal.toReal_ofReal (by norm_num)]
    norm_num

private theorem exact_noncoverage_statistics (a : Sample 100)
    (ha : ∀ i, Y0 (a i) = 0 ∧ Y1 (a i) = if W (a i) ≤ 3/5 then 1 else 0) :
    ht IntervalExample.study a = ((exact_noncoverage_success (fun i => exact_noncoverage_cat (a i))).card : ℝ)/65 ∧
    xi IntervalExample.study a = IntervalExample.xiK (exact_noncoverage_lower (fun i => exact_noncoverage_cat (a i))).card := by
  classical
  let c := fun i => exact_noncoverage_cat (a i)
  have hterm (i : Fin 100) : htTerm (IntervalExample.score (W (a i))) (X (a i)) (Y (a i)) =
      if c i = 0 then (20/13 : ℝ) else 0 := by
    dsimp [htTerm, Y]
    rw [(ha i).1, (ha i).2]
    dsimp [c, exact_noncoverage_cat, IntervalExample.score]
    by_cases hw : W (a i) ≤ (3/5 : ℝ) <;> by_cases hx : (a i).2.1 = true <;> norm_num [hw, X, bit, hx]
  have hxi (i : Fin 100) : (IntervalExample.score (W (a i)))⁻¹^2 =
      if c i ≠ 2 then (400/169 : ℝ) else 10000/9801 := by
    dsimp [c, exact_noncoverage_cat, IntervalExample.score]
    by_cases hw : W (a i) ≤ (3/5 : ℝ) <;> by_cases hx : (a i).2.1 = true <;> norm_num [hw, hx]
  constructor
  · change (∑ i, htTerm (IntervalExample.score (W (a i))) (X (a i)) (Y (a i)))/(100 : ℝ) = _
    simp_rw [hterm]
    rw [Finset.sum_ite]
    simp [exact_noncoverage_success, c] <;> ring
  · change (∑ i, (IntervalExample.score (W (a i)))⁻¹^2)/(100 : ℝ) = _
    simp_rw [hxi]
    rw [Finset.sum_ite]
    have hcard : (Finset.univ.filter (fun i : Fin 100 => c i = 2)).card =
        100-(exact_noncoverage_lower c).card := by
      rw [show Finset.univ.filter (fun i : Fin 100 => c i = 2) = Finset.univ \ exact_noncoverage_lower c by
        ext i; simp [exact_noncoverage_lower], Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    simp only [not_not, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, Nat.cast_sub (show (exact_noncoverage_lower c).card ≤ 100 from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))]
    dsimp [IntervalExample.xiK, exact_noncoverage_lower, c]
    ring


private theorem exact_noncoverage_exclusion (a : Sample 100)
    (ha : ∀ i, Y0 (a i) = 0 ∧ Y1 (a i) = if W (a i) ≤ 3/5 then 1 else 0) :
    printedRadius IntervalExample.study (1/10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study| ↔
      IntervalExample.certifiedCut (exact_noncoverage_lower (fun i => exact_noncoverage_cat (a i))).card
        (exact_noncoverage_success (fun i => exact_noncoverage_cat (a i))).card = true := by
  let c := fun i => exact_noncoverage_cat (a i)
  let k := (exact_noncoverage_lower c).card
  let s := (exact_noncoverage_success c).card
  have hk : k ≤ 100 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hs : s ≤ k := by
    apply Finset.card_le_card
    intro i hi
    simp only [exact_noncoverage_success, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [exact_noncoverage_lower, hi]
  obtain ⟨hht,hxi⟩ := exact_noncoverage_statistics a ha
  have hxi0 : 0 ≤ IntervalExample.xiK k := by
    have hkR : (k : ℝ) ≤ 100 := by exact_mod_cast hk
    dsimp [IntervalExample.xiK]
    positivity
  have hlog : 0 ≤ Real.log (20000000 : ℝ) := Real.log_nonneg (by norm_num)
  unfold printedRadius
  rw [hxi, hht, IntervalExample.probability_continuity_mean.2.2]
  change Real.sqrt (IntervalExample.xiK k * Real.log (2/(1/10000000 : ℝ))/(2*100)) <
      |(s : ℝ)/65-3/5| ↔ IntervalExample.certifiedCut k s = true
  norm_num only [show (2/(1/10000000 : ℝ)) = 20000000 by norm_num,
    show (2*100 : ℝ) = 200 by norm_num]
  rw [Real.sqrt_lt (by positivity) (abs_nonneg _), sq_abs,
    show ((s : ℝ)/65-3/5)^2 = ((s : ℝ)-39)^2/65^2 by ring]
  exact (IntervalExample.certified_cut_iff_exclusion k s hk hs).symm

/-- Transport the sample law and sum the certified strict-exclusion states. -/
private theorem exact_noncoverage_exact_mass :
    (sampleLaw IntervalExample.study 100 {a | printedRadius IntervalExample.study (1/10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|}).toReal =
      (IntervalExample.certifiedNumerator : ℝ)/(100 : ℝ)^100 := by
  classical
  letI := IntervalExample.probability_continuity_mean.1
  let ν := Measure.map exact_noncoverage_cat IntervalExample.study.law
  let P : Measure (Fin 100 → Fin 3) := Measure.pi (fun _ => ν)
  let D : Set (Fin 100 → Fin 3) := {c | IntervalExample.certifiedCut (exact_noncoverage_lower c).card (exact_noncoverage_success c).card = true}
  have mD : MeasurableSet D := Set.to_countable D |>.measurableSet
  have mc : Measurable (fun a : Sample 100 => fun i => exact_noncoverage_cat (a i)) :=
    measurable_pi_iff.mpr (fun i => exact_noncoverage_cat_meas.comp (measurable_pi_apply i))
  have hgood : ∀ᵐ o ∂IntervalExample.study.law,
      Y0 o = 0 ∧ Y1 o = if W o ≤ 3/5 then 1 else 0 := by
    have mb : Measurable bit := measurable_of_countable _
    have mm : Measurable (fun o : Unit => if W o ≤ 3/5 then (1 : ℝ) else 0) :=
      measurable_const.ite (measurableSet_le measurable_fst measurable_const) measurable_const
    apply (ae_map_iff IntervalExample.measurable_generate.aemeasurable
      ((measurableSet_eq_fun (mb.comp measurable_snd.snd.fst) measurable_const).inter
        (measurableSet_eq_fun (mb.comp measurable_snd.snd.snd) mm))).mpr
    apply ae_of_all
    intro z
    change (0 : ℝ) = 0 ∧ bit (decide (z.1 ≤ (3/5 : ℝ))) = if z.1 ≤ 3/5 then 1 else 0
    by_cases h : z.1 ≤ (3/5 : ℝ) <;> simp [bit, h]
  have hsample : ∀ᵐ a ∂sampleLaw IntervalExample.study 100, ∀ i,
      Y0 (a i) = 0 ∧ Y1 (a i) = if W (a i) ≤ 3/5 then 1 else 0 :=
    ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin 100 => IntervalExample.study.law) (i := i)).eventually hgood)
  have hevent : {a : Sample 100 | printedRadius IntervalExample.study (1/10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|} =ᵐ[sampleLaw IntervalExample.study 100]
      (fun a : Sample 100 => fun i => exact_noncoverage_cat (a i)) ⁻¹' D := by
    filter_upwards [hsample] with a ha
    exact propext (exact_noncoverage_exclusion a ha)
  have hmap : Measure.map (fun a : Sample 100 => fun i => exact_noncoverage_cat (a i))
      (sampleLaw IntervalExample.study 100) = P := Measure.pi_map_pi (fun _ => exact_noncoverage_cat_meas.aemeasurable)
  have hprob : (sampleLaw IntervalExample.study 100 {a | printedRadius IntervalExample.study (1/10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|}).toReal = P.real D := by
    rw [measure_congr hevent, ← Measure.map_apply mc mD, hmap]
    rfl
  rw [hprob]
  have hi : Integrable (D.indicator (fun _ => (1 : ℝ))) P := (integrable_const 1).indicator mD
  have hm (c : Fin 100 → Fin 3) : P.real {c} =
      ∏ i, if c i = 0 then (39/100 : ℝ) else if c i = 1 then 21/100 else 40/100 := by
    simp only [P, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl (fun i _ => exact_noncoverage_cat_mass (c i))
  calc
    P.real D = ∫ c, D.indicator (fun _ => (1 : ℝ)) c ∂P := by
      rw [integral_indicator mD, setIntegral_const]; simp
    _ = ∑ c : Fin 100 → Fin 3,
        (if IntervalExample.certifiedCut (exact_noncoverage_lower c).card (exact_noncoverage_success c).card then (1 : ℝ) else 0) *
          ∏ i, if c i = 0 then (39/100 : ℝ) else if c i = 1 then 21/100 else 40/100 := by
      rw [integral_fintype hi]
      apply Finset.sum_congr rfl
      intro c _
      rw [hm]
      simp [Set.indicator, D, mul_comm]
    _ = ∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
        (Nat.choose 100 k : ℝ) * (k.choose s : ℝ) *
          (if IntervalExample.certifiedCut k s then (1 : ℝ) else 0) *
            (39/100)^s * (21/100)^(k-s) * (40/100)^(100-k) :=
      exact_noncoverage_multinomial (n := 100) (fun k s => if IntervalExample.certifiedCut k s then (1 : ℝ) else 0)
        (39/100) (21/100) (40/100)
    _ = (IntervalExample.certifiedNumerator : ℝ)/(100 : ℝ)^100 := by
      simp only [IntervalExample.certifiedNumerator, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro s hs
      have hk' : k ≤ 100 := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hs' : s ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      by_cases hc : IntervalExample.certifiedCut k s = true
      · simp only [hc, ite_true, mul_one, IntervalExample.massNumerator, Nat.cast_mul, Nat.cast_pow,
          div_pow]
        have hn : s+(k-s)+(100-k) = 100 := by omega
        have he : (100 : ℝ)^s * 100^(k-s) * 100^(100-k) = 100^100 := by
          rw [← pow_add, ← pow_add, hn]
        rw [← he]
        field_simp <;> ring
      · simp [hc]


private theorem counterexample_valid : ValidStudy IntervalExample.study := by
  let p := IntervalExample.score
  let m : ℝ → ℝ := fun w => if w ≤ 3/5 then 1 else 0
  have hp : Measurable p := measurable_const.ite measurableSet_Iic measurable_const
  have hm : Measurable m := measurable_const.ite measurableSet_Iic measurable_const
  have hv : ∀ᵐ v ∂unitUniform, 0 < v ∧ v ≤ 1 := by
    have hmem : ∀ᵐ v ∂unitUniform, v ∈ Set.Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    have hn : ∀ᵐ v ∂unitUniform, v ≠ (0 : ℝ) := by rw [ae_iff]; simpa using unitUniform_singleton 0
    filter_upwards [hmem, hn] with v h hn
    exact ⟨lt_of_le_of_ne h.1 (Ne.symm hn), h.2⟩
  have hvs : ∀ᵐ z ∂((unitUniform.prod unitUniform).prod unitUniform), 0 < z.2 ∧ z.2 ≤ 1 :=
    (measurePreserving_snd (μ := unitUniform.prod unitUniform) (ν := unitUniform)).quasiMeasurePreserving.ae hv
  have he : RobinsRitov.generate p m =ᵐ[((unitUniform.prod unitUniform).prod unitUniform)]
      (IntervalExample.generate ∘ Prod.fst) := by
    filter_upwards [hvs] with z hz
    by_cases hw : z.1.1 ≤ (3/5 : ℝ)
    · simp [RobinsRitov.generate, IntervalExample.generate, p, m, hw, hz.2, Function.comp_def]
    · have hz0 : ¬z.2 ≤ 0 := not_le.mpr hz.1
      simp [RobinsRitov.generate, IntervalExample.generate, p, m, hw, hz0, Function.comp_def]
  have hl : (rr_laws_valid_study p m).law = IntervalExample.study.law := by
    change Measure.map _ _ = _
    rw [Measure.map_congr he, ← Measure.map_map IntervalExample.measurable_generate measurable_fst]
    simp [IntervalExample.study]
  have hstudy : {rr_laws_valid_study p m with delta := (1/200 : ℝ)} = IntervalExample.study := by
    exact congrArg (fun law => Study.mk law p m (1/200)) hl
  rw [← hstudy]
  exact rr_laws_valid_valid p m hp hm (1/200) (by norm_num) IntervalExample.score_positivity
    (fun w => by dsimp [m]; split <;> norm_num)

open IntervalExample in
theorem counterexample_proof : ValidStudy study ∧ mu study = 3/5 ∧
    (sampleLaw study 100 {a | printedRadius study (1/10000000) a < |ht study a - mu study|}).toReal =
      (certifiedNumerator : ℝ) / (100 : ℝ)^100 ∧
    (119/1000000000 : ℝ) <
      (sampleLaw study 100 {a | printedRadius study (1/10000000) a < |ht study a - mu study|}).toReal ∧
    (1/10000000 : ℝ) <
      (sampleLaw study 100 {a | printedRadius study (1/10000000) a < |ht study a - mu study|}).toReal ∧
    (∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
      if xiK k * Real.log 20000000 / 200 < ((s : ℝ)-39)^2 / 65^2 then (1 : ℕ) else 0) =
        1946 := by
  have hgt : (119/1000000000 : ℝ) <
      (sampleLaw study 100 {a | printedRadius study (1/10000000) a < |ht study a - mu study|}).toReal := by
    rw [exact_noncoverage_exact_mass]
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 1000000000) (by positivity : (0 : ℝ) < 100^100)).mpr
    have hN : (119 : ℝ) * 100^100 < 10^9 * (certifiedNumerator : ℝ) := by
      exact_mod_cast certified_mass_gt
    nlinarith
  exact ⟨counterexample_valid, probability_continuity_mean.2.2, exact_noncoverage_exact_mass, hgt,
    lt_trans (by norm_num : (1/10000000 : ℝ) < 119/1000000000) hgt,
    exact_failure_state_count⟩

open IntervalExample in
theorem exact_noncoverage_proof :
    (sampleLaw study 100 {a | printedRadius study (1/10000000) a < |ht study a - mu study|}).toReal =
      (certifiedNumerator : ℝ) / (100 : ℝ)^100 := by
  exact exact_noncoverage_exact_mass

private theorem rr_laws_valid_bin_meas (K : ℕ) (hK : 0 < K) : Measurable (RobinsRitov.bin K hK) := by
  exact (measurable_of_countable (fun n : ℕ => (⟨n % K, Nat.mod_lt n hK⟩ : Fin K))).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

private theorem rr_laws_valid_bin_fiber (K : ℕ) (hK : 0 < K) (j : Fin K) (w : ℝ)
    (hw : w ∈ Set.Ico (0 : ℝ) 1) :
    RobinsRitov.bin K hK w = j ↔ w ∈ Set.Ico ((j : ℝ)/K) (((j : ℝ)+1)/K) := by
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hkw : 0 ≤ (K : ℝ)*w := mul_nonneg hk.le hw.1
  have hfl : ⌊(K : ℝ)*w⌋₊ < K := (Nat.floor_lt hkw).mpr (by nlinarith [hw.2])
  rw [Fin.ext_iff]
  change ⌊(K : ℝ)*w⌋₊ % K = j.val ↔ _
  rw [Nat.mod_eq_of_lt hfl, Nat.floor_eq_iff hkw]
  simp only [Set.mem_Ico, div_le_iff₀ hk, lt_div_iff₀ hk]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

private theorem rr_laws_valid_bin_mass (K : ℕ) (hK : 0 < K) (j : Fin K) :
    unitUniform.real {w | RobinsRitov.bin K hK w = j} = 1/(K : ℝ) := by
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hj : (j : ℝ)+1 ≤ K := by exact_mod_cast j.isLt
  have ha : (0 : ℝ) ≤ (j : ℝ)/K := by positivity
  have hb : ((j : ℝ)+1)/K ≤ 1 := (div_le_one hk).mpr hj
  have hm : ∀ᵐ w ∂unitUniform, w ∈ Set.Ico (0 : ℝ) 1 := by
    have hmem : ∀ᵐ w ∂unitUniform, w ∈ Set.Icc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Icc
    have hne : ∀ᵐ w ∂unitUniform, w ≠ (1 : ℝ) := by
      rw [ae_iff]
      simpa using unitUniform_singleton 1
    filter_upwards [hmem, hne] with w hw hn
    exact ⟨hw.1, lt_of_le_of_ne hw.2 hn⟩
  have he : {w | RobinsRitov.bin K hK w = j} =ᵐ[unitUniform]
      Set.Ico ((j : ℝ)/K) (((j : ℝ)+1)/K) := by
    filter_upwards [hm] with w hw
    exact propext (rr_laws_valid_bin_fiber K hK j w hw)
  rw [Measure.real, measure_congr he, unitUniform, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (show Set.Ico ((j : ℝ)/K) (((j : ℝ)+1)/K) ⊆ Set.Icc 0 1 from
      fun w hw => ⟨ha.trans hw.1, hw.2.le.trans hb⟩), Real.volume_Ico,
    show ((j : ℝ)+1)/K - (j : ℝ)/K = 1/(K : ℝ) by ring,
    ENNReal.toReal_ofReal (by positivity)]

private theorem rr_laws_valid_bin_integral (K : ℕ) (hK : 0 < K) (f : Fin K → ℝ)
    (hr : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
    (∫ w, f (RobinsRitov.bin K hK w) ∂unitUniform) = (∑ j, f j)/(K : ℝ) := by
  have mb := rr_laws_valid_bin_meas K hK
  let ν := Measure.map (RobinsRitov.bin K hK) unitUniform
  have mf : Measurable f := measurable_of_countable _
  have hi : Integrable f ν := rr_laws_valid_int ν f mf hr
  rw [← integral_map mb.aemeasurable mf.aestronglyMeasurable, integral_fintype hi]
  have hm (j : Fin K) : ν.real {j} = 1/(K : ℝ) := by
    rw [Measure.real, Measure.map_apply mb (measurableSet_singleton j)]
    exact rr_laws_valid_bin_mass K hK j
  simp_rw [hm, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

open RobinsRitov in
 theorem rr_laws_valid_proof (K : ℕ) (hK : 0 < K) :
    ValidStudy lawA ∧ mu lawA = 1/2 ∧
    ∀ tau : Fin K → Bool, ValidStudy (lawB hK tau) ∧
      mu (lawB hK tau) = (∑ j : Fin K, if tau j then (1 : ℝ) else 1/3) / K := by
  have hA : ValidStudy lawA := rr_laws_valid_valid _ _ measurable_const measurable_const (1/8) (by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
  refine ⟨hA, ?_, ?_⟩
  · change mu (rr_laws_valid_study (fun _ => 1/2) (fun _ => 1/2)) = _
    rw [rr_laws_valid_mean _ _ measurable_const measurable_const (fun _ => by norm_num) (fun _ => by norm_num)]
    simp
  · intro tau
    have mb := rr_laws_valid_bin_meas K hK
    have mp : Measurable (piB hK tau) :=
      (measurable_of_countable (fun j : Fin K => if tau j then (1/4 : ℝ) else 3/4)).comp mb
    have mm : Measurable (mB hK tau) :=
      (measurable_of_countable (fun j : Fin K => if tau j then (1 : ℝ) else 1/3)).comp mb
    have hp : ∀ w, 1/8 < piB hK tau w ∧ piB hK tau w < 1-1/8 := by
      intro w; dsimp [piB]; split <;> norm_num
    have hm : ∀ w, 0 ≤ mB hK tau w ∧ mB hK tau w ≤ 1 := by
      intro w; dsimp [mB]; split <;> norm_num
    refine ⟨rr_laws_valid_valid _ _ mp mm (1/8) (by norm_num) hp hm, ?_⟩
    change mu (rr_laws_valid_study (piB hK tau) (mB hK tau)) = _
    rw [rr_laws_valid_mean _ _ mp mm (fun w => ⟨by linarith [(hp w).1], by linarith [(hp w).2]⟩) hm]
    exact rr_laws_valid_bin_integral K hK (fun j => if tau j then (1 : ℝ) else 1/3)
      (fun j => by split <;> norm_num)

end
end AronowAudit.P046.Wave1
