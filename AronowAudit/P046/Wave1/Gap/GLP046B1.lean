import AronowAudit.P046.Wave1.Gap.GP046B1

/-!
The interval count-mass bound and the Robins–Ritov observed-sample
indistinguishability theorem. The interval bound uses the continuous-law
exact noncoverage calculation. The second proof transports the uniform
generators, averages the three observed marks over independent bin types,
and bounds event differences by collision mass.
-/

namespace AronowAudit.P046.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open IntervalExample in
private theorem count_mass_bridge_cut (k s : ℕ) (hc : cut17 k s = true) :
    certifiedCut k s = true := by
  simp only [cut17, certifiedCut, decide_eq_true_eq] at hc ⊢
  omega

open IntervalExample in
private theorem count_mass_bridge_numerator : lowerNumerator ≤ certifiedNumerator := by
  unfold lowerNumerator certifiedNumerator
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro s hs
  by_cases hc : cut17 k s = true
  · simp only [hc, count_mass_bridge_cut k s hc, ↓reduceIte, le_refl]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact Nat.zero_le _

open IntervalExample in
theorem count_mass_bridge_proof :
    (lowerNumerator : ℝ) / (100 : ℝ)^100 ≤
      (sampleLaw study 100 {a | printedRadius study (1/10000000) a < |ht study a - mu study|}).toReal := by
  rw [exact_noncoverage_proof]
  exact div_le_div_of_nonneg_right (by exact_mod_cast count_mass_bridge_numerator) (by positivity)

private def rr_indist_mark (p m : ℝ) (z : ℝ × ℝ) : Fin 3 :=
  if z.1 ≤ p then (if z.2 ≤ m then 0 else 1) else 2

private theorem rr_indist_mark_meas (p m : ℝ) : Measurable (rr_indist_mark p m) := by
  unfold rr_indist_mark
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (Measurable.ite (measurableSet_le measurable_snd measurable_const)
      measurable_const measurable_const) measurable_const

private def rr_indist_markLaw (p m : ℝ) : Measure (Fin 3) :=
  Measure.map (rr_indist_mark p m) (unitUniform.prod unitUniform)

private instance rr_indist_markLaw_prob (p m : ℝ) :
    IsProbabilityMeasure (rr_indist_markLaw p m) := by
  unfold rr_indist_markLaw
  infer_instance

private theorem rr_indist_mark_mass (p m : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hm : 0 ≤ m ∧ m ≤ 1) (j : Fin 3) :
    rr_indist_markLaw p m {j} =
      if j = 0 then ENNReal.ofReal p * ENNReal.ofReal m
      else if j = 1 then ENNReal.ofReal p * (1 - ENNReal.ofReal m)
      else 1 - ENNReal.ofReal p := by
  rw [rr_indist_markLaw, Measure.map_apply (rr_indist_mark_meas p m)
    (measurableSet_singleton j)]
  have hc (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
      unitUniform (Set.Ioi x) = 1 - ENNReal.ofReal x := by
    rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
      measure_univ, unitUniform_Iic x hx.1 hx.2]
  fin_cases j <;> simp only [Fin.isValue]
  · change (unitUniform.prod unitUniform) (rr_indist_mark p m ⁻¹' {(0 : Fin 3)}) =
      ENNReal.ofReal p * ENNReal.ofReal m
    have he : rr_indist_mark p m ⁻¹' {0} = Set.Iic p ×ˢ Set.Iic m := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, rr_indist_mark,
        Set.mem_prod, Set.mem_Iic]
      split_ifs <;> simp_all
    rw [he, Measure.prod_prod, unitUniform_Iic p hp.1 hp.2,
      unitUniform_Iic m hm.1 hm.2]
  · change (unitUniform.prod unitUniform) (rr_indist_mark p m ⁻¹' {(1 : Fin 3)}) =
      ENNReal.ofReal p * (1 - ENNReal.ofReal m)
    have he : rr_indist_mark p m ⁻¹' {1} = Set.Iic p ×ˢ Set.Ioi m := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, rr_indist_mark,
        Set.mem_prod, Set.mem_Iic, Set.mem_Ioi]
      split_ifs <;> simp_all
    rw [he, Measure.prod_prod, unitUniform_Iic p hp.1 hp.2, hc m hm]
  · change (unitUniform.prod unitUniform) (rr_indist_mark p m ⁻¹' {(2 : Fin 3)}) =
      1 - ENNReal.ofReal p
    have he : rr_indist_mark p m ⁻¹' {2} = Set.Ioi p ×ˢ Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, rr_indist_mark,
        Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
      split_ifs <;> simp_all
    rw [he, Measure.prod_prod, hc p hp, measure_univ, mul_one]

/-- The fair mixture of the two observed-mark tables is the A table. -/
private theorem rr_indist_table :
    (1/2 : ℝ≥0∞) • rr_indist_markLaw (1/4) 1 +
      (1/2 : ℝ≥0∞) • rr_indist_markLaw (3/4) (1/3) =
        rr_indist_markLaw (1/2) (1/2) := by
  apply Measure.ext_of_singleton
  intro j
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    rr_indist_mark_mass (1/4) 1 (by norm_num) (by norm_num),
    rr_indist_mark_mass (3/4) (1/3) (by norm_num) (by norm_num),
    rr_indist_mark_mass (1/2) (1/2) (by norm_num) (by norm_num)]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  fin_cases j <;> norm_num [ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le (by norm_num : (ENNReal.ofReal (1/3 : ℝ)) ≤ 1),
    ENNReal.toReal_sub_of_le (by norm_num : (ENNReal.ofReal (1/4 : ℝ)) ≤ 1),
    ENNReal.toReal_sub_of_le (by norm_num : (ENNReal.ofReal (3/4 : ℝ)) ≤ 1),
    ENNReal.toReal_sub_of_le (by norm_num : (ENNReal.ofReal (1/2 : ℝ)) ≤ 1),
    ENNReal.toReal_ofReal]


private def rr_indist_embed (w : ℝ) (j : Fin 3) : Observed :=
  (w, (if j = 0 then 1 else 0, if j = 2 then 0 else 1))

private theorem rr_indist_obs (p m : ℝ → ℝ) (w : ℝ) (z : ℝ × ℝ) :
    observe (RobinsRitov.generate p m ((w,z.1),z.2)) =
      rr_indist_embed w (rr_indist_mark (p w) (m w) z) := by
  by_cases hx : z.1 ≤ p w <;> by_cases hy : z.2 ≤ m w <;>
    norm_num [RobinsRitov.generate, observe, W, Y, X, Y0, Y1, bit,
      rr_indist_embed, rr_indist_mark, hx, hy]

private theorem rr_indist_gen_meas (p m : ℝ → ℝ) (hp : Measurable p) (hm : Measurable m) :
    Measurable (RobinsRitov.generate p m) := by
  exact measurable_fst.fst.prodMk
    ((measurable_threshold _ _ measurable_fst.snd (hp.comp measurable_fst.fst)).prodMk
      (measurable_const.prodMk
        (measurable_threshold _ _ measurable_snd (hm.comp measurable_fst.fst))))

private theorem rr_indist_observe_meas : Measurable observe := by
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  exact measurable_fst.prodMk
    (((measurable_const.sub mx).mul my0 |>.add (mx.mul my1)).prodMk mx)

private def rr_indist_study (p m : ℝ → ℝ) : Study :=
  ⟨Measure.map (RobinsRitov.generate p m)
    ((unitUniform.prod unitUniform).prod unitUniform), p, m, 1/8⟩

private def rr_indist_cond {n : ℕ} (p m : ℝ → ℝ) (w : Fin n → ℝ) :
    Measure (Fin n → Observed) :=
  Measure.map (fun c : Fin n → Fin 3 => fun i => rr_indist_embed (w i) (c i))
    (Measure.pi (fun i => rr_indist_markLaw (p (w i)) (m (w i))))

private theorem rr_indist_cond_eq {n : ℕ} (p m : ℝ → ℝ) (w : Fin n → ℝ) :
    rr_indist_cond p m w =
      Measure.map (fun z : Fin n → ℝ × ℝ => fun i =>
        observe (RobinsRitov.generate p m ((w i,(z i).1),(z i).2)))
        (Measure.pi (fun _ => unitUniform.prod unitUniform)) := by
  unfold rr_indist_cond rr_indist_markLaw
  have mm : Measurable (fun z : Fin n → ℝ × ℝ => fun i =>
      rr_indist_mark (p (w i)) (m (w i)) (z i)) := by
    exact measurable_pi_iff.mpr (fun i =>
      (rr_indist_mark_meas (p (w i)) (m (w i))).comp (measurable_pi_apply i))
  rw [← Measure.pi_map_pi (fun i => (rr_indist_mark_meas (p (w i)) (m (w i))).aemeasurable),
    Measure.map_map (measurable_of_countable _) mm]
  congr 1
  funext z i
  exact (rr_indist_obs p m (w i) (z i)).symm

private theorem rr_indist_cond_meas {n : ℕ} (p m : ℝ → ℝ)
    (hp : Measurable p) (hm : Measurable m)
    (S : Set (Fin n → Observed)) (hS : MeasurableSet S) :
    Measurable (fun w : Fin n → ℝ => rr_indist_cond p m w S) := by
  have mj : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ × ℝ) => fun i =>
      observe (RobinsRitov.generate p m ((z.1 i,(z.2 i).1),(z.2 i).2))) := by
    apply measurable_pi_iff.mpr
    intro i
    apply rr_indist_observe_meas.comp
    apply (rr_indist_gen_meas p m hp hm).comp
    exact ((measurable_pi_apply i |>.comp measurable_fst).prodMk
      ((measurable_pi_apply i |>.comp measurable_snd).fst)).prodMk
        ((measurable_pi_apply i |>.comp measurable_snd).snd)
  have he (w : Fin n → ℝ) : rr_indist_cond p m w S =
      (Measure.pi (fun _ : Fin n => unitUniform.prod unitUniform))
        ((fun z : Fin n → ℝ × ℝ => fun i =>
          observe (RobinsRitov.generate p m ((w i,(z i).1),(z i).2))) ⁻¹' S) := by
    rw [rr_indist_cond_eq]
    apply Measure.map_apply _ hS
    exact mj.comp (measurable_const.prodMk measurable_id)
  simp_rw [he]
  exact measurable_measure_prodMk_left (hS.preimage mj)

/-- Split the actual product generator into covariates and assignment/outcome noise. -/
private theorem rr_indist_sample_apply (n : ℕ) (p m : ℝ → ℝ)
    (hp : Measurable p) (hm : Measurable m)
    (S : Set (Fin n → Observed)) (hS : MeasurableSet S) :
    (Measure.map (fun a : Sample n => fun i => observe (a i))
      (sampleLaw (rr_indist_study p m) n)) S =
        ∫⁻ w : Fin n → ℝ, rr_indist_cond p m w S
          ∂Measure.pi (fun _ => unitUniform) := by
  let f : ℝ × (ℝ × ℝ) → Unit := fun z =>
    RobinsRitov.generate p m ((z.1,z.2.1),z.2.2)
  have mf : Measurable f := (rr_indist_gen_meas p m hp hm).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have hlaw : (rr_indist_study p m).law =
      Measure.map f (unitUniform.prod (unitUniform.prod unitUniform)) := by
    rw [← Measure.prodAssoc_prod, Measure.map_map mf MeasurableEquiv.prodAssoc.measurable]
    rfl
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ (ℝ × ℝ) (Fin n)
    (fun _ => unitUniform) (fun _ => unitUniform.prod unitUniform)).symm
  have mobs : Measurable (fun a : Sample n => fun i => observe (a i)) :=
    measurable_pi_iff.mpr (fun i => rr_indist_observe_meas.comp (measurable_pi_apply i))
  have mg : Measurable (fun z : Fin n → ℝ × (ℝ × ℝ) => fun i => observe (f (z i))) :=
    measurable_pi_iff.mpr (fun i => (rr_indist_observe_meas.comp mf).comp (measurable_pi_apply i))
  change (Measure.map _ (Measure.pi (fun _ => (rr_indist_study p m).law))) S = _
  have mpf : Measurable (fun z : Fin n → ℝ × (ℝ × ℝ) => fun i => f (z i)) :=
    measurable_pi_iff.mpr (fun i => mf.comp (measurable_pi_apply i))
  rw [hlaw, ← Measure.pi_map_pi (fun _ => mf.aemeasurable), Measure.map_map mobs mpf]
  change (Measure.map (fun z : Fin n → ℝ × (ℝ × ℝ) => fun i => observe (f (z i))) _) S = _
  rw [← he.map_eq, Measure.map_map mg he.measurable, Measure.map_apply (mg.comp he.measurable) hS,
    Measure.prod_apply (hS.preimage (mg.comp he.measurable))]
  apply lintegral_congr
  intro w
  rw [rr_indist_cond_eq, Measure.map_apply]
  · rfl
  · apply measurable_pi_iff.mpr
    intro i
    exact (rr_indist_observe_meas.comp (rr_indist_gen_meas p m hp hm)).comp
      ((measurable_const.prodMk (measurable_pi_apply i).fst).prodMk (measurable_pi_apply i).snd)
  · exact hS

/-- Independent prior bits at distinct bins average each observed-mark factor. -/
private theorem rr_indist_prior_marks (K n : ℕ) (b : Fin n → Fin K)
    (hb : Function.Injective b) :
    (RobinsRitov.prior K).bind (fun tau => Measure.pi (fun i : Fin n =>
      if tau (b i) then rr_indist_markLaw (1/4) 1 else rr_indist_markLaw (3/4) (1/3))) =
        Measure.pi (fun _ : Fin n => rr_indist_markLaw (1/2) (1/2)) := by
  classical
  let ν : Measure Bool := uniformOn Set.univ
  letI : IsProbabilityMeasure (RobinsRitov.prior K) := by
    unfold RobinsRitov.prior
    infer_instance
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs)
    (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.pi_pi]
  let F : Fin n → Bool → ℝ≥0∞ := fun i t =>
    if t then rr_indist_markLaw (1/4) 1 (s i) else rr_indist_markLaw (3/4) (1/3) (s i)
  have hind : iIndepFun (fun i : Fin n => fun tau : Fin K → Bool => tau (b i))
      (RobinsRitov.prior K) :=
    (iIndepFun_pi (fun _ : Fin K => (measurable_id : Measurable (id : Bool → Bool)).aemeasurable)).precomp hb
  have hF : iIndepFun (fun i : Fin n => fun tau : Fin K → Bool => F i (tau (b i)))
      (RobinsRitov.prior K) :=
    hind.comp F (fun _ => measurable_of_countable _)
  have hval (t : Bool) (i : Fin n) :
      (if t then rr_indist_markLaw (1/4) 1 else rr_indist_markLaw (3/4) (1/3)) (s i) = F i t := by
    cases t <;> rfl
  simp_rw [hval]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hF
    (fun _ => measurable_of_countable _)]
  apply Finset.prod_congr rfl
  intro i hi
  have he := (measurePreserving_eval (fun _ : Fin K => ν) (b i)).lintegral_comp
    (measurable_of_countable (F i))
  change (∫⁻ tau : Fin K → Bool, F i (tau (b i)) ∂(RobinsRitov.prior K)) =
    ∫⁻ t : Bool, F i t ∂ν at he
  rw [he, lintegral_fintype]
  have ht := congrArg (fun μ : Measure (Fin 3) => μ (s i)) rr_indist_table
  have hν (t : Bool) : ν {t} = (1/2 : ℝ≥0∞) := by
    dsimp [ν]
    rw [uniformOn_univ]
    norm_num
  simpa [hν, F, mul_comm, add_comm] using ht

private theorem rr_indist_bin_meas (K : ℕ) (hK : 0 < K) :
    Measurable (RobinsRitov.bin K hK) := by
  exact (measurable_of_countable (fun n : ℕ => (⟨n % K, Nat.mod_lt n hK⟩ : Fin K))).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

private theorem rr_indist_piB_meas (K : ℕ) (hK : 0 < K) (tau : Fin K → Bool) :
    Measurable (RobinsRitov.piB hK tau) :=
  (measurable_of_countable (fun j : Fin K => if tau j then (1/4 : ℝ) else 3/4)).comp
    (rr_indist_bin_meas K hK)

private theorem rr_indist_mB_meas (K : ℕ) (hK : 0 < K) (tau : Fin K → Bool) :
    Measurable (RobinsRitov.mB hK tau) :=
  (measurable_of_countable (fun j : Fin K => if tau j then (1 : ℝ) else 1/3)).comp
    (rr_indist_bin_meas K hK)

private theorem rr_indist_cond_mixture (K n : ℕ) (hK : 0 < K) (w : Fin n → ℝ)
    (hw : Function.Injective (fun i => RobinsRitov.bin K hK (w i)))
    (S : Set (Fin n → Observed)) (hS : MeasurableSet S) :
    (∫⁻ tau, rr_indist_cond (RobinsRitov.piB hK tau) (RobinsRitov.mB hK tau) w S
      ∂(RobinsRitov.prior K)) = rr_indist_cond (fun _ => 1/2) (fun _ => 1/2) w S := by
  classical
  let E := fun c : Fin n → Fin 3 => fun i => rr_indist_embed (w i) (c i)
  have hE : Measurable E := measurable_of_countable _
  dsimp [E] at hE
  have hmark (tau : Fin K → Bool) :
      (fun i : Fin n => rr_indist_markLaw (RobinsRitov.piB hK tau (w i))
        (RobinsRitov.mB hK tau (w i))) =
      (fun i : Fin n => if tau (RobinsRitov.bin K hK (w i)) then
        rr_indist_markLaw (1/4) 1 else rr_indist_markLaw (3/4) (1/3)) := by
    funext i
    dsimp [RobinsRitov.piB, RobinsRitov.mB]
    split <;> rfl
  simp only [rr_indist_cond, Measure.map_apply hE hS, hmark]
  rw [← Measure.bind_apply (hS.preimage hE) (measurable_of_countable _).aemeasurable,
    rr_indist_prior_marks K n _ hw]

private def rr_indist_D (K n : ℕ) (hK : 0 < K) : Set (Fin n → Observed) :=
  {a | Function.Injective (fun i => RobinsRitov.bin K hK (a i).1)}

private theorem rr_indist_D_meas (K n : ℕ) (hK : 0 < K) :
    MeasurableSet (rr_indist_D K n hK) := by
  have he : rr_indist_D K n hK = ⋂ i : Fin n, ⋂ j : Fin n,
      {a : Fin n → Observed | RobinsRitov.bin K hK (a i).1 ≠ RobinsRitov.bin K hK (a j).1 ∨ i = j} := by
    ext a
    simp [rr_indist_D, Function.Injective, imp_iff_not_or]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.union
  · exact (measurableSet_eq_fun
      ((rr_indist_bin_meas K hK).comp (measurable_pi_apply i).fst)
      ((rr_indist_bin_meas K hK).comp (measurable_pi_apply j).fst)).compl
  · exact MeasurableSet.const (i = j)

private theorem rr_indist_mixture_apply (K n : ℕ) (hK : 0 < K)
    (S : Set (Fin n → Observed)) (hS : MeasurableSet S) :
    (Measure.map (fun a : Sample n => fun i => observe (a i))
      (RobinsRitov.mixture hK n)) S =
    ∫⁻ w : Fin n → ℝ, ∫⁻ tau,
      rr_indist_cond (RobinsRitov.piB hK tau) (RobinsRitov.mB hK tau) w S
        ∂(RobinsRitov.prior K) ∂Measure.pi (fun _ => unitUniform) := by
  have mo : Measurable (fun a : Sample n => fun i => observe (a i)) :=
    measurable_pi_iff.mpr (fun i => rr_indist_observe_meas.comp (measurable_pi_apply i))
  rw [Measure.map_apply mo hS, RobinsRitov.mixture,
    Measure.bind_apply (hS.preimage mo) (measurable_of_countable _).aemeasurable]
  have he (tau : Fin K → Bool) :
      sampleLaw (RobinsRitov.lawB hK tau) n ((fun a : Sample n => fun i => observe (a i)) ⁻¹' S) =
      ∫⁻ w : Fin n → ℝ, rr_indist_cond (RobinsRitov.piB hK tau) (RobinsRitov.mB hK tau) w S
        ∂Measure.pi (fun _ => unitUniform) := by
    rw [← Measure.map_apply mo hS]
    exact rr_indist_sample_apply n _ _ (rr_indist_piB_meas K hK tau) (rr_indist_mB_meas K hK tau) S hS
  simp_rw [he]
  apply lintegral_lintegral_swap
  apply Measurable.aemeasurable
  apply measurable_from_prod_countable_right
  intro tau
  exact rr_indist_cond_meas _ _ (rr_indist_piB_meas K hK tau) (rr_indist_mB_meas K hK tau) S hS

private theorem rr_indist_cond_inter (K n : ℕ) (hK : 0 < K)
    (p m : ℝ → ℝ) (w : Fin n → ℝ)
    (S : Set (Fin n → Observed)) (hS : MeasurableSet S) :
    rr_indist_cond p m w (S ∩ rr_indist_D K n hK) =
      if Function.Injective (fun i => RobinsRitov.bin K hK (w i)) then
        rr_indist_cond p m w S else 0 := by
  classical
  unfold rr_indist_cond
  rw [Measure.map_apply (measurable_of_countable _) (hS.inter (rr_indist_D_meas K n hK))]
  split_ifs with hw
  · rw [Measure.map_apply (measurable_of_countable _) hS]
    congr 1
    ext c
    simp [rr_indist_D, rr_indist_embed, hw]
  · have he : (fun c : Fin n → Fin 3 => fun i => rr_indist_embed (w i) (c i)) ⁻¹'
        (S ∩ rr_indist_D K n hK) = ∅ := by
      ext c
      simp [rr_indist_D, rr_indist_embed, hw]
    rw [he, measure_empty]

private theorem rr_indist_restrict_eq (K n : ℕ) (hK : 0 < K) :
    (Measure.map (fun a : Sample n => fun i => observe (a i))
      (sampleLaw RobinsRitov.lawA n)).restrict (rr_indist_D K n hK) =
    (Measure.map (fun a : Sample n => fun i => observe (a i))
      (RobinsRitov.mixture hK n)).restrict (rr_indist_D K n hK) := by
  classical
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  rw [show RobinsRitov.lawA = rr_indist_study (fun _ => 1/2) (fun _ => 1/2) from rfl,
    rr_indist_sample_apply n (fun _ => 1/2) (fun _ => 1/2) measurable_const measurable_const _
      (hS.inter (rr_indist_D_meas K n hK)),
    rr_indist_mixture_apply K n hK _ (hS.inter (rr_indist_D_meas K n hK))]
  apply lintegral_congr
  intro w
  simp_rw [rr_indist_cond_inter K n hK _ _ w S hS]
  split_ifs with hw
  · exact (rr_indist_cond_mixture K n hK w hw S hS).symm
  · simp

-- Interval-fiber calculation for the count-state noncoverage bound.
private theorem rr_indist_bin_fiber (K : ℕ) (hK : 0 < K) (j : Fin K) (w : ℝ)
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

private theorem rr_indist_bin_mass (K : ℕ) (hK : 0 < K) (j : Fin K) :
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
    exact propext (rr_indist_bin_fiber K hK j w hw)
  rw [Measure.real, measure_congr he, unitUniform, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (show Set.Ico ((j : ℝ)/K) (((j : ℝ)+1)/K) ⊆ Set.Icc 0 1 from
      fun w hw => ⟨ha.trans hw.1, hw.2.le.trans hb⟩), Real.volume_Ico,
    show ((j : ℝ)+1)/K - (j : ℝ)/K = 1/(K : ℝ) by ring,
    ENNReal.toReal_ofReal (by positivity)]

private theorem rr_indist_bin_map (K : ℕ) (hK : 0 < K) :
    Measure.map (RobinsRitov.bin K hK) unitUniform =
      uniformOn (Set.univ : Set (Fin K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  apply Measure.ext_of_singleton
  intro j
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [Measure.map_apply (rr_indist_bin_meas K hK) (measurableSet_singleton j)]
  change unitUniform.real {w | RobinsRitov.bin K hK w = j} = _
  rw [rr_indist_bin_mass]
  simp [uniformOn_univ, ENNReal.toReal_inv]

private theorem rr_indist_bin_vector (K n : ℕ) (hK : 0 < K) :
    Measure.map (fun w : Fin n → ℝ => fun i => RobinsRitov.bin K hK (w i))
      (Measure.pi (fun _ => unitUniform)) = binLaw K n := by
  rw [Measure.pi_map_pi (fun _ => (rr_indist_bin_meas K hK).aemeasurable)]
  simp only [rr_indist_bin_map K hK, binLaw]

private theorem rr_indist_cond_compl (K n : ℕ) (hK : 0 < K)
    (p m : ℝ → ℝ) (w : Fin n → ℝ) :
    rr_indist_cond p m w (rr_indist_D K n hK)ᶜ =
      if Function.Injective (fun i => RobinsRitov.bin K hK (w i)) then 0 else 1 := by
  classical
  unfold rr_indist_cond
  rw [Measure.map_apply (measurable_of_countable _) (rr_indist_D_meas K n hK).compl]
  split_ifs with hw
  · have he : (fun c : Fin n → Fin 3 => fun i => rr_indist_embed (w i) (c i)) ⁻¹'
        (rr_indist_D K n hK)ᶜ = ∅ := by
      ext c
      simp [rr_indist_D, rr_indist_embed, hw]
    rw [he, measure_empty]
  · have he : (fun c : Fin n → Fin 3 => fun i => rr_indist_embed (w i) (c i)) ⁻¹'
        (rr_indist_D K n hK)ᶜ = Set.univ := by
      ext c
      simp [rr_indist_D, rr_indist_embed, hw]
    rw [he, measure_univ]

private theorem rr_indist_collision_mass (K n : ℕ) (hK : 0 < K) :
    (Measure.map (fun a : Sample n => fun i => observe (a i))
      (sampleLaw RobinsRitov.lawA n)) (rr_indist_D K n hK)ᶜ =
      binLaw K n {b | ∃ i j, i ≠ j ∧ b i = b j} := by
  classical
  rw [show RobinsRitov.lawA = rr_indist_study (fun _ => 1/2) (fun _ => 1/2) from rfl,
    rr_indist_sample_apply n (fun _ => 1/2) (fun _ => 1/2)
    measurable_const measurable_const _ (rr_indist_D_meas K n hK).compl]
  simp_rw [rr_indist_cond_compl]
  let C : Set (Fin n → ℝ) := {w | ¬ Function.Injective (fun i => RobinsRitov.bin K hK (w i))}
  have hC : MeasurableSet C := by
    have hm : Measurable (fun w : Fin n → ℝ => fun i => (w i, ((0 : ℝ), (0 : ℝ)))) :=
      measurable_pi_iff.mpr (fun i => (measurable_pi_apply i).prodMk measurable_const)
    exact (rr_indist_D_meas K n hK).compl.preimage hm
  have he : (fun w : Fin n → ℝ =>
      if Function.Injective (fun i => RobinsRitov.bin K hK (w i)) then (0 : ℝ≥0∞) else 1) =
      C.indicator (fun _ => 1) := by
    funext w
    by_cases hw : Function.Injective (fun i => RobinsRitov.bin K hK (w i)) <;>
      simp [C, hw]
  rw [he, lintegral_indicator hC]
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
  have hb : Measurable (fun w : Fin n → ℝ => fun i => RobinsRitov.bin K hK (w i)) :=
    measurable_pi_iff.mpr (fun i => (rr_indist_bin_meas K hK).comp (measurable_pi_apply i))
  rw [← rr_indist_bin_vector K n hK, Measure.map_apply hb (Set.to_countable _).measurableSet]
  congr 1
  ext w
  simp only [C, Set.mem_setOf_eq, Set.mem_preimage, Function.Injective]
  push Not
  constructor
  · rintro ⟨i, j, heq, hne⟩
    exact ⟨i, j, hne, heq⟩
  · rintro ⟨i, j, hne, heq⟩
    exact ⟨i, j, heq, hne⟩

private theorem rr_indist_mixture_prob (K n : ℕ) (hK : 0 < K) :
    IsProbabilityMeasure (RobinsRitov.mixture hK n) := by
  letI : IsProbabilityMeasure (RobinsRitov.prior K) := by
    unfold RobinsRitov.prior
    infer_instance
  have hb (tau : Fin K → Bool) : sampleLaw (RobinsRitov.lawB hK tau) n Set.univ = 1 := by
    letI := ((rr_laws_valid_proof K hK).2.2 tau).1.probability
    exact measure_univ
  constructor
  rw [RobinsRitov.mixture, Measure.bind_apply MeasurableSet.univ
    (measurable_of_countable _).aemeasurable]
  simp_rw [hb]
  simp

/-- Equality on D leaves at most the common complement mass in any event difference. -/
private theorem rr_indist_event_bound {A : Type*} [MeasurableSpace A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (D : Set A) (hD : MeasurableSet D) (hr : μ.restrict D = ν.restrict D)
    (S : Set A) (hS : MeasurableSet S) :
    |μ.real S - ν.real S| ≤ μ.real Dᶜ := by
  have hs : μ.real (S ∩ D) = ν.real (S ∩ D) := by
    rw [← measureReal_restrict_apply hS, hr, measureReal_restrict_apply hS]
  have hd : μ.real D = ν.real D := by
    simpa only [measureReal_restrict_apply_univ] using
      congrArg (fun ρ : Measure A => ρ.real Set.univ) hr
  have hc : μ.real Dᶜ = ν.real Dᶜ := by
    rw [probReal_compl_eq_one_sub hD, probReal_compl_eq_one_sub hD, hd]
  have hm := measureReal_inter_add_sdiff (μ := μ) (s := S) hD
  have hn := measureReal_inter_add_sdiff (μ := ν) (s := S) hD
  have hmu : μ.real (S \ D) ≤ μ.real Dᶜ :=
    measureReal_mono (fun _ hx => hx.2)
  have hnu : ν.real (S \ D) ≤ ν.real Dᶜ :=
    measureReal_mono (fun _ hx => hx.2)
  have h0m : 0 ≤ μ.real (S \ D) := measureReal_nonneg
  have h0n : 0 ≤ ν.real (S \ D) := measureReal_nonneg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

open RobinsRitov in
theorem rr_indistinguishability_proof (K n : ℕ) (hK : 0 < K) :
    let obs := fun a : Sample n => fun i => observe (a i)
    let D : Set (Fin n → Observed) := {a | Function.Injective (fun i => bin K hK (a i).1)}
    (Measure.map obs (sampleLaw lawA n)).restrict D =
      (Measure.map obs (mixture hK n)).restrict D ∧
    ∀ S : Set (Fin n → Observed), MeasurableSet S →
      |(Measure.map obs (sampleLaw lawA n)).real S -
        (Measure.map obs (mixture hK n)).real S| ≤ (n : ℝ)*(n-1)/(2*K) := by
  letI := (rr_laws_valid_proof K hK).1.probability
  letI := rr_indist_mixture_prob K n hK
  dsimp only
  refine ⟨rr_indist_restrict_eq K n hK, ?_⟩
  intro S hS
  calc
    _ ≤ (Measure.map (fun a : Sample n => fun i => observe (a i))
          (sampleLaw lawA n)).real (rr_indist_D K n hK)ᶜ :=
      rr_indist_event_bound _ _ _ (rr_indist_D_meas K n hK)
        (rr_indist_restrict_eq K n hK) S hS
    _ = (binLaw K n {b | ∃ i j, i ≠ j ∧ b i = b j}).toReal :=
      congrArg ENNReal.toReal (rr_indist_collision_mass K n hK)
    _ ≤ (n : ℝ)*(n-1)/(2*K) := robins_ritov_collision K n hK

end
end AronowAudit.P046.Wave1
