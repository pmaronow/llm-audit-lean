import AronowAudit.P001.P001_Foundations
import Mathlib.Probability.Independence.Integration

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0011B2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! P001-T129: the ratio is zero on the zero-density set by
`div_zero`; no equality of the two supports is assumed. -/

lemma t129_normalized_ratio {A : Type*} [MeasurableSpace A]
    (ρ : Measure A) (f q : A → ℝ)
    (hf : Measurable f) (hq : Measurable q)
    (hf0 : ∀ a, 0 ≤ f a) (hq0 : ∀ a, 0 ≤ q a)
    (hq1 : (∫⁻ a, ENNReal.ofReal (q a) ∂ρ) = 1) :
    Integrable (fun a => q a / f a) (ρ.withDensity (fun a => ENNReal.ofReal (f a))) ∧
      (∫ a, q a / f a ∂ρ.withDensity (fun a => ENNReal.ofReal (f a))) ≤ 1 := by
  have hqi : Integrable q ρ :=
    (lintegral_ofReal_ne_top_iff_integrable hq.aestronglyMeasurable
      (ae_of_all _ hq0)).mp (by rw [hq1]; exact ENNReal.one_ne_top)
  have hqint : (∫ a, q a ∂ρ) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hq0)
      hq.aestronglyMeasurable, hq1, ENNReal.toReal_one]
  have hprod0 (a : A) : 0 ≤ f a * (q a / f a) :=
    mul_nonneg (hf0 a) (div_nonneg (hq0 a) (hf0 a))
  have hprodle (a : A) : f a * (q a / f a) ≤ q a := by
    by_cases h : f a = 0
    · simpa [h] using hq0 a
    · rw [mul_comm, div_mul_cancel₀ _ h]
  have hprodi : Integrable (fun a => f a * (q a / f a)) ρ := by
    apply hqi.mono_nonneg (hf.mul (hq.div hf)).aestronglyMeasurable
      (ae_of_all _ hprod0) (ae_of_all _ hprodle)
  have hdtop : ∀ᵐ a ∂ρ, ENNReal.ofReal (f a) < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have htoReal (a : A) : (ENNReal.ofReal (f a)).toReal = f a :=
    ENNReal.toReal_ofReal (hf0 a)
  have hri : Integrable (fun a => q a / f a)
      (ρ.withDensity (fun a => ENNReal.ofReal (f a))) := by
    apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal hdtop).mpr
    simpa only [htoReal, smul_eq_mul] using hprodi
  refine ⟨hri, ?_⟩
  calc
    (∫ a, q a / f a ∂ρ.withDensity (fun a => ENNReal.ofReal (f a))) =
        ∫ a, f a * (q a / f a) ∂ρ := by
      rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal hdtop]
      simp only [htoReal, smul_eq_mul]
    _ ≤ ∫ a, q a ∂ρ := integral_mono_ae hprodi hqi (ae_of_all _ hprodle)
    _ = 1 := hqint

lemma t129_strict_log_slack {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : A → ℝ)
    (hrpos : ∀ᵐ a ∂P, 0 < r a) (hri : Integrable r P)
    (hli : Integrable (fun a => Real.log (r a)) P)
    (hrmean : (∫ a, r a ∂P) ≤ 1) :
    (∫ a, Real.log (r a) ∂P) ≤ 0 ∧
      ((∫ a, Real.log (r a) ∂P) = 0 ↔ r =ᵐ[P] (fun _ => 1)) := by
  let J : A → ℝ := fun a => r a - 1 - Real.log (r a)
  have hJi : Integrable J P := (hri.sub (integrable_const 1)).sub hli
  have hJ0 : ∀ᵐ a ∂P, 0 ≤ J a := by
    filter_upwards [hrpos] with a ha
    exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos ha)
  have hJmean : (∫ a, J a ∂P) =
      (∫ a, r a ∂P) - 1 - ∫ a, Real.log (r a) ∂P := by
    dsimp only [J]
    rw [integral_sub (f := fun a => r a - 1) (g := fun a => Real.log (r a))
      (hri.sub (integrable_const 1)) hli,
      integral_sub (f := r) (g := fun _ : A => (1 : ℝ)) hri (integrable_const 1)]
    simp
  have hJnonneg : 0 ≤ ∫ a, J a ∂P := integral_nonneg_of_ae hJ0
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hJzero : (∫ a, J a ∂P) = 0 := by linarith
    have hJae : J =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hJ0 hJi).mp hJzero
    filter_upwards [hrpos, hJae] with a ha hJa
    by_contra hne
    have hstrict := Real.log_lt_sub_one_of_pos ha hne
    change r a - 1 - Real.log (r a) = 0 at hJa
    linarith
  · intro he
    calc
      (∫ a, Real.log (r a) ∂P) = ∫ _ : A, (0 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [he] with a ha
        simp only [ha, Real.log_one]
      _ = 0 := integral_zero A ℝ

theorem true_model_log_likelihood_lemma_with_zeros_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hgmeas : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hgpos : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hgnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X ω,Y ω))=conditionalModelLaw νX κ g θ)
   (hdom : ∀ t∈Θ,∀ᵐ xy ∂(νX.prod κ),0 < g xy.2 xy.1 θ → 0 < g xy.2 xy.1 t)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y ω) (X ω) t)) μ) :
   ∀ t∈Θ,expectedLogLikelihood μ X Y g t ≤ expectedLogLikelihood μ X Y g θ ∧
     (expectedLogLikelihood μ X Y g t=expectedLogLikelihood μ X Y g θ ↔
       (fun ω => g (Y ω) (X ω) t)=ᵐ[μ](fun ω => g (Y ω) (X ω) θ)) := by
  intro t ht
  let ρ := νX.prod κ
  let f : ((Fin K → ℝ) × ℝ) → ℝ := fun xy => g xy.2 xy.1 θ
  let q : ((Fin K → ℝ) × ℝ) → ℝ := fun xy => g xy.2 xy.1 t
  let Z : Ω → ((Fin K → ℝ) × ℝ) := fun ω => (X ω, Y ω)
  let P := ρ.withDensity (fun xy => ENNReal.ofReal (f xy))
  let R : ((Fin K → ℝ) × ℝ) → ℝ := fun xy => q xy / f xy
  have hf : Measurable f := hgmeas θ hθ
  have hq : Measurable q := hgmeas t ht
  have hZ : Measurable Z := hX.prodMk hY
  have hmap : μ.map Z = P := htrue
  have hf0 (xy : (Fin K → ℝ) × ℝ) : 0 ≤ f xy := hgpos θ hθ xy.2 xy.1
  have hq0 (xy : (Fin K → ℝ) × ℝ) : 0 ≤ q xy := hgpos t ht xy.2 xy.1
  have hq1 : (∫⁻ xy, ENNReal.ofReal (q xy) ∂ρ) = 1 := by
    change (∫⁻ xy, ENNReal.ofReal (g xy.2 xy.1 t) ∂νX.prod κ) = 1
    rw [lintegral_prod _ (hgmeas t ht).ennreal_ofReal.aemeasurable]
    simp [hgnorm t ht]
  obtain ⟨hRi, hRmean⟩ := t129_normalized_ratio ρ f q hf hq hf0 hq0 hq1
  have hfpos : ∀ᵐ xy ∂P, 0 < f xy := by
    apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
    exact ae_of_all _ (fun xy hxy => ENNReal.ofReal_ne_zero_iff.mp hxy)
  have hqpos : ∀ᵐ xy ∂P, 0 < q xy := by
    apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
    filter_upwards [hdom t ht] with xy hxy hd
    exact hxy (ENNReal.ofReal_ne_zero_iff.mp hd)
  have hRmeas : Measurable R := hq.div hf
  have hRi_map : Integrable R (μ.map Z) := by
    rw [hmap]
    exact hRi
  have hrint : Integrable (fun ω => R (Z ω)) μ :=
    hRi_map.comp_measurable hZ
  have hrmean : (∫ ω, R (Z ω) ∂μ) ≤ 1 := by
    rw [← integral_map hZ.aemeasurable hRmeas.aestronglyMeasurable, hmap]
    exact hRmean
  have hf_sample : ∀ᵐ ω ∂μ, 0 < f (Z ω) := by
    apply ae_of_ae_map (μ := μ) (p := fun xy => 0 < f xy) hZ.aemeasurable
    rw [hmap]
    exact hfpos
  have hq_sample : ∀ᵐ ω ∂μ, 0 < q (Z ω) := by
    apply ae_of_ae_map (μ := μ) (p := fun xy => 0 < q xy) hZ.aemeasurable
    rw [hmap]
    exact hqpos
  have hrpos : ∀ᵐ ω ∂μ, 0 < R (Z ω) := by
    filter_upwards [hf_sample, hq_sample] with ω hfω hqω
    exact div_pos hqω hfω
  have hlog_ratio : (fun ω => Real.log (R (Z ω))) =ᵐ[μ]
      (fun ω => Real.log (g (Y ω) (X ω) t) - Real.log (g (Y ω) (X ω) θ)) := by
    filter_upwards [hf_sample, hq_sample] with ω hfω hqω
    exact Real.log_div hqω.ne' hfω.ne'
  have hlint : Integrable (fun ω => Real.log (R (Z ω))) μ :=
    ((hlog t ht).sub (hlog θ hθ)).congr hlog_ratio.symm
  have hlvalue : (∫ ω, Real.log (R (Z ω)) ∂μ) =
      expectedLogLikelihood μ X Y g t - expectedLogLikelihood μ X Y g θ := by
    rw [integral_congr_ae hlog_ratio, integral_sub (hlog t ht) (hlog θ hθ)]
    rfl
  obtain ⟨hle, heq⟩ :=
    t129_strict_log_slack μ (fun ω => R (Z ω)) hrpos hrint hlint hrmean
  constructor
  · rw [hlvalue] at hle
    linarith
  · constructor
    · intro he
      have hlzero : (∫ ω, Real.log (R (Z ω)) ∂μ) = 0 := by
        rw [hlvalue, he, sub_self]
      have hrone := heq.mp hlzero
      filter_upwards [hrone, hf_sample] with ω hω hfω
      change g (Y ω) (X ω) t / g (Y ω) (X ω) θ = 1 at hω
      exact (div_eq_one_iff_eq hfω.ne').mp hω
    · intro he
      unfold expectedLogLikelihood mean
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]

/-! P001-T14: deterministic regrouping comes first, followed
by moments under the finite product of fair sign measures. -/

lemma t14_donor_exists {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (hr : ∃ j, r j = true) (i : Fin n) :
    ∃ j, nearestDonor p r i = some j ∧ r j = true := by
  have hmin : ∃ j, r j = true ∧
      ∀ k, r k = true → |p j - p i| ≤ |p k - p i| := by
    obtain ⟨j, hj, hleast⟩ := Set.exists_min_image {j : Fin n | r j = true}
      (fun j => |p j - p i|) (Set.toFinite _) hr
    exact ⟨j, hj, hleast⟩
  refine ⟨Classical.choose hmin, ?_, (Classical.choose_spec hmin).1⟩
  simp only [nearestDonor, dif_pos hmin]

lemma t14_donor_responds {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (i j : Fin n) (h : nearestDonor p r i = some j) : r j = true := by
  unfold nearestDonor at h
  split_ifs at h with hmin
  · have hj : Classical.choose hmin = j := Option.some.inj h
    simpa only [hj] using (Classical.choose_spec hmin).1

lemma t14_weight_regrouping {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (r : Fin n → Bool) (e : Fin n → Bool) :
    hotDeck (fun j => (p j,r j,e j)) - 50 =
      (∑ j, donorReuseWeight p r j * noise (e j)) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases hr : ∃ j, r j = true
  · let a : Fin n → ℝ := fun i => if r i then noise (e i) else
      match nearestDonor p r i with
      | some j => noise (e j)
      | none => 0
    have hai (i : Fin n) : a i =
        (if r i then noise (e i) else 0) +
        ∑ j, if r i = false ∧ nearestDonor p r i = some j then noise (e j) else 0 := by
      obtain ⟨j, hd, _⟩ := t14_donor_exists p r hr i
      cases hi : r i
      · simp only [a, hi, Bool.false_eq_true, ite_false, hd, Option.some.injEq, true_and]
        simp [eq_comm]
      · simp [a, hi]
    have hcoeff (j : Fin n) :
        (if r j then noise (e j) else 0) +
          (∑ i, if r i = false ∧ nearestDonor p r i = some j then noise (e j) else 0) =
        donorReuseWeight p r j * noise (e j) := by
      have hcount : (∑ i, if r i = false ∧ nearestDonor p r i = some j
          then noise (e j) else 0) =
          ((Finset.univ.filter (fun i => r i = false ∧
            nearestDonor p r i = some j)).card : ℝ) * noise (e j) := by
        rw [← Finset.sum_filter]
        simp [nsmul_eq_mul]
      cases hj : r j
      · have hnone (i : Fin n) : ¬ (r i = false ∧ nearestDonor p r i = some j) := by
          intro hi
          have := t14_donor_responds p r i j hi.2
          simp only [hj, Bool.false_eq_true] at this
        simp [donorReuseWeight, hj, hnone]
      · rw [hcount]
        simp only [donorReuseWeight, hj, Bool.coe_true, if_true]
        ring
    have hsum : (∑ i, a i) = ∑ j, donorReuseWeight p r j * noise (e j) := by
      simp_rw [hai]
      rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => hcoeff j)
    have hunit (i : Fin n) :
        (if r i then 50 + noise (e i) else
          match nearestDonor p r i with
          | some j => 50 + noise (e j)
          | none => 50) = 50 + a i := by
      cases hi : r i <;> simp only [hi, Bool.false_eq_true, Bool.coe_true,
        if_false, if_true, a]
      cases nearestDonor p r i <;> simp
    have hformula : hotDeck (fun j => (p j,r j,e j)) =
        50 + (∑ i, a i) / (n : ℝ) := by
      unfold hotDeck
      dsimp only
      rw [if_pos hr]
      calc
        _ = (∑ i : Fin n, (50 + a i)) / (n : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact hunit i
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hn0] <;> ring
    rw [hformula, hsum]
    ring
  · have hrfalse (j : Fin n) : r j = false := by
      cases hj : r j
      · rfl
      · exact False.elim (hr ⟨j, hj⟩)
    simp [hotDeck, hr, donorReuseWeight, hrfalse]

/-- One-coordinate fair sign law, definitionally the factor in signProductLaw. -/
def t14_signLaw : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac true + (1/2 : ℝ≥0∞) • Measure.dirac false

lemma t14_signLaw_probability : IsProbabilityMeasure t14_signLaw := by
  constructor
  norm_num [t14_signLaw, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

lemma t14_product_probability (n : ℕ) : IsProbabilityMeasure (signProductLaw n) := by
  letI : IsProbabilityMeasure t14_signLaw := t14_signLaw_probability
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => t14_signLaw))
  infer_instance

lemma t14_finite_integrable {A : Type*} [MeasurableSpace A]
    [DiscreteMeasurableSpace A] [Finite A] (P : Measure A) [IsFiniteMeasure P]
    (f : A → ℝ) : Integrable f P :=
  memLp_one_iff_integrable.mp MemLp.of_discrete

lemma t14_one_sign_mean : (∫ b, noise b ∂t14_signLaw) = 0 := by
  letI : IsProbabilityMeasure t14_signLaw := t14_signLaw_probability
  rw [integral_fintype (t14_finite_integrable t14_signLaw noise), Fintype.sum_bool]
  norm_num [t14_signLaw, measureReal_def, Measure.add_apply, Measure.smul_apply, noise]

lemma t14_noise_square (b : Bool) : noise b * noise b = 1 := by
  cases b <;> norm_num [noise]

lemma t14_sign_mean (n : ℕ) (j : Fin n) :
    (∫ e, noise (e j) ∂signProductLaw n) = 0 := by
  letI : IsProbabilityMeasure t14_signLaw := t14_signLaw_probability
  change (∫ e : Fin n → Bool, noise (e j)
    ∂Measure.pi (fun _ : Fin n => t14_signLaw)) = 0
  rw [integral_comp_eval (show AEStronglyMeasurable noise t14_signLaw from .of_discrete)]
  exact t14_one_sign_mean

lemma t14_sign_cross (n : ℕ) (j k : Fin n) :
    (∫ e, noise (e j) * noise (e k) ∂signProductLaw n) = if j = k then 1 else 0 := by
  letI : IsProbabilityMeasure t14_signLaw := t14_signLaw_probability
  letI : IsProbabilityMeasure (signProductLaw n) := t14_product_probability n
  by_cases hjk : j = k
  · subst k
    simp only [t14_noise_square, integral_const, probReal_univ,
      smul_eq_mul, one_mul, ite_true]
  · have hind : iIndepFun (fun j (e : Fin n → Bool) => noise (e j)) (signProductLaw n) := by
      exact iIndepFun_pi (μ := fun _ : Fin n => t14_signLaw)
        (X := fun _ : Fin n => noise) (fun _ => Measurable.aemeasurable (by fun_prop))
    rw [(hind.indepFun hjk).integral_fun_mul_eq_mul_integral
      (show AEStronglyMeasurable (fun e : Fin n → Bool => noise (e j))
        (signProductLaw n) from .of_discrete)
      (show AEStronglyMeasurable (fun e : Fin n → Bool => noise (e k))
        (signProductLaw n) from .of_discrete), t14_sign_mean, t14_sign_mean, if_neg hjk]
    ring

lemma t14_weighted_mean (n : ℕ) (c : Fin n → ℝ) :
    (∫ e, (∑ j, c j * noise (e j)) ∂signProductLaw n) = 0 := by
  letI : IsProbabilityMeasure (signProductLaw n) := t14_product_probability n
  rw [integral_finsetSum _ (fun j _ => t14_finite_integrable _ _)]
  simp only [integral_const_mul, t14_sign_mean, mul_zero, Finset.sum_const_zero]

lemma t14_weighted_second (n : ℕ) (c : Fin n → ℝ) :
    (∫ e, (∑ j, c j * noise (e j)) ^ 2 ∂signProductLaw n) = ∑ j, (c j) ^ 2 := by
  letI : IsProbabilityMeasure (signProductLaw n) := t14_product_probability n
  have hexpand (e : Fin n → Bool) :
      (∑ j, c j * noise (e j)) ^ 2 =
        ∑ j, ∑ k, (c j * c k) * (noise (e j) * noise (e k)) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun j _ => t14_finite_integrable _ _)]
  simp_rw [integral_finsetSum _ (fun k _ => t14_finite_integrable _ _),
    integral_const_mul, t14_sign_cross]
  simp [pow_two]

theorem hot_deck_conditional_reuse_variance_proof {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (r : Fin n → Bool) :
   (∀ e : Fin n → Bool,hotDeck (fun j => (p j,r j,e j))-50=
     (∑ j,donorReuseWeight p r j*noise (e j))/(n : ℝ)) ∧
   IsProbabilityMeasure (signProductLaw n) ∧
   mean (signProductLaw n) (fun e => hotDeck (fun j => (p j,r j,e j)))=50 ∧
   var (signProductLaw n) (fun e => hotDeck (fun j => (p j,r j,e j)))=
     (∑ j,(donorReuseWeight p r j)^2)/(n : ℝ)^2 := by
  letI : IsProbabilityMeasure (signProductLaw n) := t14_product_probability n
  let T : (Fin n → Bool) → ℝ := fun e => hotDeck (fun j => (p j,r j,e j))
  let S : (Fin n → Bool) → ℝ := fun e => ∑ j, donorReuseWeight p r j * noise (e j)
  have hid (e : Fin n → Bool) : T e - 50 = S e / (n : ℝ) :=
    t14_weight_regrouping hn p r e
  have hT (e : Fin n → Bool) : T e = 50 + S e / (n : ℝ) := by
    linarith [hid e]
  have hSmean : (∫ e, S e ∂signProductLaw n) = 0 :=
    t14_weighted_mean n (donorReuseWeight p r)
  have hTmean : (∫ e, T e ∂signProductLaw n) = 50 := by
    simp_rw [hT]
    rw [integral_add (integrable_const 50) (t14_finite_integrable _ _),
      integral_div, hSmean]
    simp
  refine ⟨hid, inferInstance, hTmean, ?_⟩
  change ProbabilityTheory.variance T (signProductLaw n) = _
  rw [variance_eq_integral (show AEMeasurable T (signProductLaw n) from
    Measurable.aemeasurable (by fun_prop)), hTmean]
  simp_rw [hid, div_pow]
  rw [integral_div, t14_weighted_second]

end
end AronowAudit.P001.Wave1
