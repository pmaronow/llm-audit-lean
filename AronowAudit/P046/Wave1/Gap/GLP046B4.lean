import AronowAudit.P046.Wave1.Gap.GP046B4
import AronowAudit.P046.Wave1.Gap.GP046B5

/-!
Conditional moments of the actual cross-fitting remainder, conditioning on the
observed training fold. No unconditional fitted second moment is required.
-/
namespace AronowAudit.P046.Wave1

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Upgrade setwise almost-everywhere identities to an identity of probability
measures, using a countable determining class after a Borel embedding into ℝ. -/
lemma rcm_ae_measure_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] (P : Measure A) (ν ρ : A → Measure B)
    [∀ a, IsProbabilityMeasure (ν a)] [∀ a, IsProbabilityMeasure (ρ a)]
    (h : ∀ s, MeasurableSet s → ∀ᵐ a ∂P, ν a s = ρ a s) :
    ∀ᵐ a ∂P, ν a = ρ a := by
  let f := embeddingReal B
  have hf := measurableEmbedding_embeddingReal B
  have hrat : ∀ᵐ a ∂P, ∀ q : ℚ,
      (ν a).map f (Set.Iic (q : ℝ)) = (ρ a).map f (Set.Iic (q : ℝ)) := by
    apply ae_all_iff.2
    intro q
    filter_upwards [h (f ⁻¹' Set.Iic (q : ℝ)) (hf.measurable measurableSet_Iic)] with a ha
    rw [Measure.map_apply hf.measurable measurableSet_Iic,
      Measure.map_apply hf.measurable measurableSet_Iic]
    exact ha
  filter_upwards [hrat] with a ha
  apply hf.map_injective
  apply ext_of_generate_finite (⋃ q : ℚ, {Set.Iic (q : ℝ)})
    Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
  · simpa only [Set.iUnion_singleton_eq_range, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff] using ha
  · simp [Measure.map_apply hf.measurable MeasurableSet.univ]

/-- The condDistrib/condExpKernel bridge as an equality of measures. -/
lemma rcm_kernel_map {A B C : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]
    (P : Measure A) [IsProbabilityMeasure P] (X : A → B) (Y : A → C)
    (hX : Measurable X) (hY : Measurable Y) :
    ∀ᵐ a ∂P, (condExpKernel P (MeasurableSpace.comap Y inferInstance) a).map X =
      condDistrib X Y P (Y a) := by
  letI (a : A) : IsProbabilityMeasure
      ((condExpKernel P (MeasurableSpace.comap Y inferInstance) a).map X) :=
    inferInstance
  apply rcm_ae_measure_eq
  intro s hs
  filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map (μ := P) hX hY hs] with a ha
  rw [Measure.map_apply hX hs]
  simpa only [Kernel.map_apply _ hX, Measure.map_apply hX hs] using ha.symm

/-- The observed vector generating the training σ-algebra. -/
def rcm_training {n : ℕ} (F : CrossFit n) (j : Bool) (a : Sample n) : Fin n → Observed :=
  fun i => if F.fold i ≠ j then observe (a i) else (0, (0, 0))

/-- The full-data evaluation tuple; training information is not included. -/
def rcm_eval {n : ℕ} (F : CrossFit n) (j : Bool) (a : Sample n) :
    {i : Fin n // F.fold i = j} → Unit := fun i => a i.1

lemma rcm_observe_measurable : Measurable observe :=
  measurable_fst.prodMk (p4d_measurable_Y.prodMk rcheb_measurable_X)

lemma rcm_training_measurable {n : ℕ} (F : CrossFit n) (j : Bool) :
    Measurable (rcm_training F j) := by
  classical
  apply measurable_pi_lambda
  intro i
  by_cases hi : F.fold i ≠ j
  · simpa only [rcm_training, if_pos hi, Function.comp_def] using
      rcm_observe_measurable.comp (measurable_pi_apply i)
  · simpa only [rcm_training, if_neg hi] using
      (measurable_const : Measurable (fun _ : Sample n => (0, (0, 0)) : Sample n → Observed))

lemma rcm_eval_measurable {n : ℕ} (F : CrossFit n) (j : Bool) :
    Measurable (rcm_eval F j) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.1

/-- On almost every training kernel, the entire fitted function is fixed. -/
lemma rcm_kernel_freeze (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (j : Bool) :
    letI := hM.probability
    ∀ᵐ a ∂sampleLaw M n, ∀ᵐ b ∂condExpKernel (sampleLaw M n) (trainingSigma F j) a,
      F.g j b = F.g j a := by
  classical
  letI := hM.probability
  have mt := rcm_training_measurable F j
  have hm := rcm_kernel_map (sampleLaw M n) (rcm_training F j) (rcm_training F j) mt mt
  have hs := ae_of_ae_map mt.aemeasurable (condDistrib_self (μ := sampleLaw M n) mt.aemeasurable)
  filter_upwards [hm, hs] with a ha hself
  have hmap : (condExpKernel (sampleLaw M n) (trainingSigma F j) a).map
      (rcm_training F j) = Measure.dirac (rcm_training F j a) := by
    exact ha.trans hself
  have ht : ∀ᵐ b ∂condExpKernel (sampleLaw M n) (trainingSigma F j) a,
      rcm_training F j b = rcm_training F j a := by
    apply ae_of_ae_map (μ := condExpKernel (sampleLaw M n) (trainingSigma F j) a)
      (p := fun t => t = rcm_training F j a) mt.aemeasurable
    rw [hmap]
    simp
  filter_upwards [ht] with b hb
  apply F.opposite_fold
  intro i hi
  have he := congrFun hb i
  simpa only [rcm_training, if_pos hi, Function.comp_def] using he

/-- Evaluation observations retain their independent product law under almost
all observed-training kernels. -/
lemma rcm_kernel_eval (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (j : Bool) :
    letI := hM.probability
    ∀ᵐ a ∂sampleLaw M n,
      (condExpKernel (sampleLaw M n) (trainingSigma F j) a).map (rcm_eval F j) =
        Measure.pi (fun _ : {i : Fin n // F.fold i = j} => M.law) := by
  classical
  letI := hM.probability
  let p : Fin n → Prop := fun i => F.fold i = j
  let E := {i : Fin n // p i} → Unit
  let T := {i : Fin n // ¬p i} → Unit
  let P : Measure E := Measure.pi (fun _ => M.law)
  let Q : Measure T := Measure.pi (fun _ => M.law)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Unit) p
  have hp : MeasurePreserving e (sampleLaw M n) (P.prod Q) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => M.law) p
  let tr : T → Fin n → Observed := fun t i =>
    if hi : F.fold i ≠ j then observe (t ⟨i, hi⟩) else (0, (0, 0))
  have mtr : Measurable tr := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : F.fold i ≠ j
    · simpa only [tr, dif_pos hi, Function.comp_def] using
        rcm_observe_measurable.comp (measurable_pi_apply (⟨i, hi⟩ : {i : Fin n // ¬p i}))
    · simpa only [tr, dif_neg hi] using
        (measurable_const : Measurable (fun _ : T => (0, (0, 0)) : T → Observed))
  have htr (a : Sample n) : rcm_training F j a = tr (e a).2 := by
    funext i
    by_cases hi : F.fold i ≠ j <;>
      simp [rcm_training, tr, hi, e, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd]
  have hev (a : Sample n) : rcm_eval F j a = (e a).1 := rfl
  have hmapTrainProd : (P.prod Q).map (fun z : E × T => tr z.2) = Q.map tr := by
    have hh := Measure.map_map (μ := P.prod Q) mtr (measurable_snd : Measurable (Prod.snd : E × T → T))
    rw [Measure.map_snd_prod] at hh
    simpa only [Function.comp_def, measure_univ, one_smul] using hh.symm
  have hmapT : (sampleLaw M n).map (rcm_training F j) = Q.map tr := by
    have hh := Measure.map_map (μ := sampleLaw M n) (mtr.comp measurable_snd) e.measurable
    rw [hp.map_eq] at hh
    calc
      _ = (sampleLaw M n).map (fun a => tr (e a).2) :=
        congrArg (fun f : Sample n → (Fin n → Observed) => (sampleLaw M n).map f) (funext htr)
      _ = (P.prod Q).map (fun z : E × T => tr z.2) := by
        simpa only [Function.comp_def] using hh.symm
      _ = _ := hmapTrainProd
  have hind : IndepFun (fun z : E × T => tr z.2) Prod.fst (P.prod Q) :=
    (indepFun_prod measurable_id mtr).symm
  have hjoint : (sampleLaw M n).map (fun a => (rcm_training F j a, rcm_eval F j a)) =
      ((sampleLaw M n).map (rcm_training F j)).prod P := by
    calc
      _ = (P.prod Q).map (fun z : E × T => (tr z.2, z.1)) := by
        have hh := Measure.map_map (μ := sampleLaw M n)
          ((mtr.comp measurable_snd).prodMk measurable_fst) e.measurable
        rw [hp.map_eq] at hh
        calc
          _ = (sampleLaw M n).map (fun a => (tr (e a).2, (e a).1)) :=
            congrArg (fun f : Sample n → ((Fin n → Observed) × E) => (sampleLaw M n).map f)
              (funext fun a => Prod.ext (htr a) (hev a))
          _ = _ := by simpa only [Function.comp_def] using hh.symm
      _ = ((P.prod Q).map (fun z : E × T => tr z.2)).prod
          ((P.prod Q).map Prod.fst) :=
        hind.map_prod_eq_prod_map_map (mtr.comp measurable_snd).aemeasurable
          measurable_fst.aemeasurable
      _ = _ := by
        rw [hmapTrainProd, Measure.map_fst_prod, hmapT]
        simp
  have hcond : condDistrib (rcm_eval F j) (rcm_training F j) (sampleLaw M n) =ᵐ[
      (sampleLaw M n).map (rcm_training F j)] Kernel.const (Fin n → Observed) P := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (rcm_training_measurable F j) (rcm_eval_measurable F j)
    rw [Measure.compProd_const]
    exact hjoint
  have hc := ae_of_ae_map (rcm_training_measurable F j).aemeasurable hcond
  have hk := rcm_kernel_map (sampleLaw M n) (rcm_eval F j) (rcm_training F j)
    (rcm_eval_measurable F j) (rcm_training_measurable F j)
  filter_upwards [hc, hk] with a ha hb
  exact hb.trans ha

/-- Exact second moment, before the upper bound in `rcheb_multiplier_second`. -/
lemma rcm_multiplier_second_measurable (M : Study) (hM : ValidStudy M)
    (h : ℝ → ℝ) (hm : Measurable h) (hL : MemLp (fun o => h (W o)) 2 M.law) :
    (∫ o, ((1 - X o / M.pi (W o)) * h (W o))^2 ∂M.law) =
      weightedNormSq M h := by
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
        weightedNormSq M h := by
      apply integral_congr_ae
      filter_upwards [rcheb_pi_bounds M hM] with o ho
      dsimp [k, q]
      field_simp [ho.1.ne']
      <;> ring

/-- Scalar multiplier moments for an L2 predictor, with no global Borel
assumption on that predictor. -/
lemma rcm_multiplier_moments (M : Study) (hM : ValidStudy M) (h : ℝ → ℝ)
    (hL : MemLp (fun o => h (W o)) 2 M.law) :
    MemLp (fun o => (1 - X o / M.pi (W o)) * h (W o)) 2 M.law ∧
    (∫ o, (1 - X o / M.pi (W o)) * h (W o) ∂M.law) = 0 ∧
    (∫ o, ((1 - X o / M.pi (W o)) * h (W o))^2 ∂M.law) = weightedNormSq M h ∧
    weightedNormSq M h ≤ l2Sq M h / M.delta := by
  letI := hM.probability
  obtain ⟨h₀, mh₀, heq⟩ := rcheb_finite_fiber_version M.law h hL.aestronglyMeasurable
  have hL₀ : MemLp (fun o => h₀ (W o)) 2 M.law := (memLp_congr_ae heq).2 hL
  have hU : (fun o => (1 - X o / M.pi (W o)) * h (W o)) =ᵐ[M.law]
      (fun o => (1 - X o / M.pi (W o)) * h₀ (W o)) := by
    filter_upwards [heq] with o ho
    rw [show h₀ (W o) = h (W o) from ho]
  have hsq := integral_congr_ae (hU.fun_comp (fun x : ℝ => x^2))
  have hw : weightedNormSq M h₀ = weightedNormSq M h := by
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [show h₀ (W o) = h (W o) from ho]
  have hl : l2Sq M h₀ = l2Sq M h := by
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [show h₀ (W o) = h (W o) from ho]
  refine ⟨proposition4b_multiplier_L2 M hM h hL, ?_, ?_, ?_⟩
  · exact (integral_congr_ae hU).trans
      (rcheb_multiplier_mean M hM h₀ mh₀ (hL₀.integrable (by norm_num)))
  · exact hsq.trans ((rcm_multiplier_second_measurable M hM h₀ mh₀ hL₀).trans hw)
  · rw [← hw, ← rcm_multiplier_second_measurable M hM h₀ mh₀ hL₀]
    simpa only [hl] using rcheb_multiplier_second M hM h₀ mh₀ hL₀

/-- The two genuine finite product moments, including L2 membership of the
unscaled average. This also covers an empty evaluation fold. -/
lemma rcm_product_moments {I : Type*} [Fintype I]
    (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (h : ℝ → ℝ) (hL : MemLp (fun o => h (W o)) 2 M.law) :
    let R : (I → Unit) → ℝ := fun b =>
      (∑ i, (1 - X (b i) / M.pi (W (b i))) * h (W (b i))) / n
    MemLp R 2 (Measure.pi (fun _ : I => M.law)) ∧
    (∫ b, R b ∂Measure.pi (fun _ : I => M.law)) = 0 ∧
    (∫ b, (Real.sqrt n * R b)^2 ∂Measure.pi (fun _ : I => M.law)) =
      (Fintype.card I : ℝ) / n * weightedNormSq M h := by
  letI := hM.probability
  dsimp only
  let f : Unit → ℝ := fun o => (1 - X o / M.pi (W o)) * h (W o)
  obtain ⟨hf, hz, hv, hb⟩ := rcm_multiplier_moments M hM h hL
  have hcoord (i : I) : MemLp (fun b : I → Unit => f (b i)) 2
      (Measure.pi (fun _ : I => M.law)) :=
    hf.comp_measurePreserving (measurePreserving_eval _ i)
  have hsum : MemLp (fun b : I → Unit => ∑ i, f (b i)) 2
      (Measure.pi (fun _ : I => M.law)) :=
    memLp_finsetSum _ (fun i _ => hcoord i)
  have hmean : (∫ b : I → Unit, ∑ i, f (b i) ∂Measure.pi (fun _ => M.law)) = 0 := by
    have hh := integral_finsetSum Finset.univ (fun i _ => (hcoord i).integrable (by norm_num))
    change (∫ b : I → Unit, ∑ i, f (b i) ∂Measure.pi (fun _ => M.law)) = _ at hh
    rw [hh]
    apply Finset.sum_eq_zero
    intro i hi
    exact (integral_comp_eval (μ := fun _ : I => M.law) (i := i)
      hf.aestronglyMeasurable).trans hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [f, div_eq_mul_inv] using hsum.mul_const (n : ℝ)⁻¹
  · change (∫ b : I → Unit, (∑ i, f (b i)) / n ∂Measure.pi (fun _ => M.law)) = 0
    rw [integral_div, hmean, zero_div]
  · have hs := proposition4b_sum_sq (ι := I) M hM f hf hz
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hc : (Real.sqrt n / n)^2 = (1 : ℝ) / n := by
      rw [div_pow, Real.sq_sqrt hnR.le]
      field_simp
    calc
      _ = ∫ b : I → Unit, (Real.sqrt n / n)^2 * (∑ i, f (b i))^2
          ∂Measure.pi (fun _ => M.law) := by
        congr 1
        funext b
        dsimp only [f]
        ring
      _ = (Real.sqrt n / n)^2 * ((Fintype.card I : ℝ) * ∫ o, (f o)^2 ∂M.law) := by
        rw [integral_const_mul, hs]
      _ = _ := by rw [hc, hv]; ring

/-- The remainder becomes a fixed function of the evaluation tuple on a
training fiber. -/
lemma rcm_remainder_freeze (M : Study) {n : ℕ} (F : CrossFit n) (j : Bool)
    (g : ℝ → ℝ) (a b : Sample n) (hfit : F.g j b = F.g j a) :
    foldRemainder M F j g b =
      (∑ i : {i : Fin n // F.fold i = j},
        (1 - X (b i) / M.pi (W (b i))) * (F.g j a (W (b i)) - g (W (b i)))) / n := by
  classical
  unfold foldRemainder
  rw [hfit]
  congr 1
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]

theorem remainder_conditional_moments_proof (M : Study) (hM : ValidStudy M)
    (n : ℕ) (hn : 0 < n) (F : CrossFit n) (j : Bool) (g : ℝ → ℝ)
    (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hfits : ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law) :
    letI := hM.probability
    ∀ᵐ a ∂sampleLaw M n,
      (∫ b, foldRemainder M F j g b ∂condExpKernel (sampleLaw M n) (trainingSigma F j) a) = 0 ∧
      (∫ b, (Real.sqrt n * foldRemainder M F j g b)^2
        ∂condExpKernel (sampleLaw M n) (trainingSigma F j) a) =
          ((Finset.univ.filter (fun i => F.fold i = j)).card : ℝ) / n *
            weightedNormSq M (fun w => F.g j a w - g w) ∧
      ((Finset.univ.filter (fun i => F.fold i = j)).card : ℝ) / n *
        weightedNormSq M (fun w => F.g j a w - g w) ≤
      ((Finset.univ.filter (fun i => F.fold i = j)).card : ℝ) / (n * M.delta) *
        l2Sq M (fun w => F.g j a w - g w) := by
  classical
  letI := hM.probability
  have hk := rcm_kernel_eval M hM n F j
  have hf := rcm_kernel_freeze M hM n F j
  filter_upwards [hk, hf, hfits] with a ha hfreeze hfit
  let I := {i : Fin n // F.fold i = j}
  let P : Measure (I → Unit) := Measure.pi (fun _ => M.law)
  let K := condExpKernel (sampleLaw M n) (trainingSigma F j) a
  let R : (I → Unit) → ℝ := fun b =>
    (∑ i, (1 - X (b i) / M.pi (W (b i))) *
      (F.g j a (W (b i)) - g (W (b i)))) / n
  have hL : MemLp (fun o => F.g j a (W o) - g (W o)) 2 M.law := hfit.sub hg
  obtain ⟨hR_L2, hmean, hsecond⟩ := rcm_product_moments (I := I) M hM n hn
    (fun w => F.g j a w - g w) hL
  have hR : foldRemainder M F j g =ᵐ[K] fun b => R (rcm_eval F j b) := by
    filter_upwards [hfreeze] with b hb
    exact rcm_remainder_freeze M F j g a b hb
  have hmapR : AEStronglyMeasurable R (K.map (rcm_eval F j)) := by
    rw [ha]
    exact hR_L2.aestronglyMeasurable
  have hmapS : AEStronglyMeasurable (fun b => (Real.sqrt n * R b)^2)
      (K.map (rcm_eval F j)) := by
    rw [ha]
    exact (hR_L2.const_mul (Real.sqrt n)).integrable_sq.aestronglyMeasurable
  have hcard : Fintype.card I = (Finset.univ.filter (fun i => F.fold i = j)).card :=
    Fintype.card_subtype _
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ∫ b, R (rcm_eval F j b) ∂K := integral_congr_ae hR
      _ = ∫ b, R b ∂P := by
        rw [← integral_map (rcm_eval_measurable F j).aemeasurable hmapR, ha]
      _ = 0 := hmean
  · calc
      _ = ∫ b, (Real.sqrt n * R (rcm_eval F j b))^2 ∂K :=
        integral_congr_ae (hR.fun_comp (fun x : ℝ => (Real.sqrt n * x)^2))
      _ = ∫ b, (Real.sqrt n * R b)^2 ∂P := by
        rw [← integral_map (rcm_eval_measurable F j).aemeasurable hmapS, ha]
      _ = _ := by simpa only [hcard] using hsecond
  · have hb := (rcm_multiplier_moments M hM (fun w => F.g j a w - g w) hL).2.2.2
    calc
      _ ≤ ((Finset.univ.filter (fun i => F.fold i = j)).card : ℝ) / n *
          (l2Sq M (fun w => F.g j a w - g w) / M.delta) :=
        mul_le_mul_of_nonneg_left hb (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end
end AronowAudit.P046.Wave1
