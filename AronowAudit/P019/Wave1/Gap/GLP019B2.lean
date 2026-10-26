import AronowAudit.P019.P019_Audit
import AronowAudit.P015.P015_ConvergenceCompletion
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The ordinary discrete probability measure associated with the finite law. -/
def t19_measure (P : FiniteLaw Ω) : Measure Ω :=
  Measure.sum (fun ω => ENNReal.ofReal (P.mass ω) • Measure.dirac ω)

lemma t19_measure_apply (P : FiniteLaw Ω) (D : Set Ω) :
    t19_measure P D = ENNReal.ofReal (P.prob (fun ω => ω ∈ D)) := by
  rw [t19_measure, Measure.sum_apply _ (Set.toFinite D).measurableSet, tsum_fintype]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [FiniteLaw.prob, FiniteLaw.mean, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ D <;> simp [h, Measure.dirac_apply' _ ((Set.toFinite D).measurableSet)]
  · intro ω _
    exact mul_nonneg (P.nonneg ω) (by split_ifs <;> norm_num)

instance t19_probability (P : FiniteLaw Ω) : IsProbabilityMeasure (t19_measure P) := by
  constructor
  rw [t19_measure_apply]
  simp [FiniteLaw.prob, mean_const]

lemma t19_integral (P : FiniteLaw Ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂t19_measure P) = P.mean f := by
  rw [t19_measure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), tsum_fintype]
  simp [FiniteLaw.mean, ENNReal.toReal_ofReal, P.nonneg, smul_eq_mul]

lemma t19_memLp (P : FiniteLaw Ω) (f : Ω → ℝ) : MemLp f 2 (t19_measure P) :=
  MemLp.of_discrete

lemma t19_variance (P : FiniteLaw Ω) (f : Ω → ℝ) :
    Var[f; t19_measure P] = P.variance f := by
  rw [variance_eq_sub (t19_memLp P f), t19_integral, t19_integral]
  rfl

/-- One common IID sample space, used only to prove statements about its finite marginals. -/
def t19_product (P : FiniteLaw Ω) : Measure (ℕ → Ω) :=
  Measure.infinitePi (fun _ : ℕ => t19_measure P)

instance t19_product_probability (P : FiniteLaw Ω) : IsProbabilityMeasure (t19_product P) := by
  unfold t19_product
  infer_instance

def t19_sample (n : ℕ) (ω : ℕ → Ω) : Fin n → Ω := fun i => ω i

lemma t19_sample_measurable (n : ℕ) : Measurable (t19_sample (Ω := Ω) n) := by
  exact measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

lemma t19_sample_law (P : FiniteLaw Ω) (n : ℕ) :
    (t19_product P).map (t19_sample n) = t19_measure (P.iid n) := by
  have hmap : (t19_product P).map (t19_sample n) = Measure.pi (fun _ : Fin n => t19_measure P) := by
    change (Measure.infinitePi (fun _ : ℕ => t19_measure P)).map
      (fun ω (i : Fin n) => ω i.val) = _
    rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun i : Fin n => i.val)
      Fin.val_injective, Measure.infinitePi_eq_pi]
  rw [hmap]
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.pi_singleton, t19_measure_apply]
  simp only [FiniteLaw.prob, FiniteLaw.mean, Set.mem_singleton_iff,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    FiniteLaw.iid]
  simp only [t19_measure_apply, FiniteLaw.prob, FiniteLaw.mean,
    Set.mem_singleton_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => P.nonneg (s i))).symm

lemma t19_sample_integral (P : FiniteLaw Ω) (n : ℕ) (f : (Fin n → Ω) → ℝ) :
    (∫ ω, f (t19_sample n ω) ∂t19_product P) = (P.iid n).mean f := by
  rw [← t19_integral, ← t19_sample_law]
  exact (integral_map (t19_sample_measurable n).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable).symm

lemma t19_sample_prob (P : FiniteLaw Ω) (n : ℕ) (D : (Fin n → Ω) → Prop) :
    (t19_product P).real {ω | D (t19_sample n ω)} = (P.iid n).prob D := by
  have h := congrArg (fun μ : Measure (Fin n → Ω) => μ {s | D s}) (t19_sample_law P n)
  rw [Measure.map_apply (t19_sample_measurable n) (Set.toFinite _).measurableSet,
    t19_measure_apply] at h
  change (t19_product P) {ω | D (t19_sample n ω)} = ENNReal.ofReal ((P.iid n).prob D) at h
  rw [measureReal_def, h, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg ((P.iid n).nonneg s)
    (by dsimp only; split_ifs <;> norm_num))

lemma t19_coordinate_ident (P : FiniteLaw Ω) (f : Ω → ℝ) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → Ω => f (ω i)) f (t19_product P) (t19_measure P) := by
  refine ⟨((measurable_of_finite f).comp (measurable_pi_apply i)).aemeasurable,
    (measurable_of_finite f).aemeasurable, ?_⟩
  change (t19_product P).map (f ∘ (fun ω : ℕ → Ω => ω i)) = _
  rw [← Measure.map_map (measurable_of_finite f) (measurable_pi_apply i)]
  congr 1
  exact Measure.infinitePi_map_eval _ _

lemma t19_average_ae (P : FiniteLaw Ω) (f : Ω → ℝ) :
    ∀ᵐ ω ∂t19_product P, Tendsto
      (fun (n : ℕ) => (∑ i : Fin n, f (ω i)) / (n : ℝ)) atTop (nhds (P.mean f)) := by
  have h := strong_law_ae_real (fun i (ω : ℕ → Ω) => f (ω i))
    ((t19_coordinate_ident P f 0).integrable_iff.mpr ((t19_memLp P f).integrable (by norm_num)))
    (fun i j hij => (iIndepFun_infinitePi (P := fun _ : ℕ => t19_measure P)
      (fun _ => measurable_of_finite f)).indepFun hij)
    (fun i => (t19_coordinate_ident P f i).trans (t19_coordinate_ident P f 0).symm)
  simpa only [← Fin.sum_univ_eq_sum_range,
    (t19_coordinate_ident P f 0).integral_eq, t19_integral] using h

lemma t19_average_clt (P : FiniteLaw Ω) (f : Ω → ℝ) (hf : P.mean f = 0) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → Ω) => (Real.sqrt n)⁻¹ * ∑ i : Fin n, f (ω i)) atTop
      id (fun _ => t19_product P) (gaussianReal 0 (P.variance f).toNNReal) := by
  have hvar : Var[(fun ω : ℕ → Ω => f (ω 0)); t19_product P] = P.variance f :=
    (t19_coordinate_ident P f 0).variance_eq.trans (t19_variance P f)
  have hmean : (∫ ω : ℕ → Ω, f (ω 0) ∂t19_product P) = 0 := by
    rw [(t19_coordinate_ident P f 0).integral_eq, t19_integral, hf]
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i (ω : ℕ → Ω) => f (ω i)) (Y := id)
    (P' := gaussianReal 0 (P.variance f).toNNReal)
    (by rw [hvar]; exact ⟨measurable_id.aemeasurable, Measure.map_id⟩)
    ((t19_coordinate_ident P f 0).memLp_iff.mpr (t19_memLp P f))
    (iIndepFun_infinitePi (P := fun _ : ℕ => t19_measure P)
      (fun _ => measurable_of_finite f))
    (fun i => (t19_coordinate_ident P f i).trans (t19_coordinate_ident P f 0).symm)
  simpa only [← Fin.sum_univ_eq_sum_range, hmean, mul_zero, sub_zero] using h

lemma t19_stat_measurable (n : ℕ) (f : (Fin n → Ω) → ℝ) :
    Measurable (fun ω : ℕ → Ω => f (t19_sample n ω)) :=
  (measurable_of_finite f).comp (t19_sample_measurable n)

lemma t19_count_sum (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) :
    (∑ i, if S.cell z y (s i) then (1 : ℝ) else 0) = (S.cellCount s z y : ℝ) := by
  simp [Study.cellCount, Nat.cast_sum, Nat.cast_ite]

lemma t19_cell_variance_identity (S : Study Ω) {n : ℕ} (s : Fin n → Ω)
    (z y : Bool) (hc : 2 ≤ S.cellCount s z y) :
    S.cellVariance s z y =
      ((∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ)^2 else 0) /
        (S.cellCount s z y : ℝ) - (S.cellMean s z y 0)^2) *
      (S.cellCount s z y : ℝ) / ((S.cellCount s z y : ℝ)-1) := by
  have h0 : S.cellCount s z y ≠ 0 := by omega
  have h0r : (S.cellCount s z y : ℝ) ≠ 0 := by exact_mod_cast h0
  have h1r : (S.cellCount s z y : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ (S.cellCount s z y : ℝ) := by exact_mod_cast hc
    linarith
  have he : (∑ i, if S.cell z y (s i) then
      ((S.V (s i) : ℝ)-S.cellMean s z y 0)^2 else 0) =
      (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ)^2 else 0) -
        2*S.cellMean s z y 0*(∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) +
        (S.cellMean s z y 0)^2*(S.cellCount s z y : ℝ) := by
    rw [← t19_count_sum S s z y, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [Study.cellVariance, if_neg (not_lt_of_ge hc), he]
  simp only [Study.cellMean, if_neg h0]
  field_simp
  <;> ring

lemma t19_cell_ae (S : Study Ω) (z y : Bool) (c : ℝ)
    (hp : 0 < S.law.prob (S.cell z y)) :
    ∀ᵐ ω ∂t19_product S.law,
      Tendsto (fun (n : ℕ) => (S.cellCount (t19_sample n ω) z y : ℝ)/(n : ℝ))
        atTop (nhds (S.law.prob (S.cell z y))) ∧
      (∀ᶠ n in atTop, 2 ≤ S.cellCount (t19_sample n ω) z y) ∧
      Tendsto (fun (n : ℕ) => S.cellMean (t19_sample n ω) z y c)
        atTop (nhds (S.listMean z y)) ∧
      Tendsto (fun (n : ℕ) => S.cellVariance (t19_sample n ω) z y)
        atTop (nhds (S.law.cv (fun t => (S.V t : ℝ)) (S.cell z y))) := by
  filter_upwards [t19_average_ae S.law (fun t => if S.cell z y t then 1 else 0),
    t19_average_ae S.law (fun t => if S.cell z y t then (S.V t : ℝ) else 0),
    t19_average_ae S.law (fun t => if S.cell z y t then (S.V t : ℝ)^2 else 0)] with ω hI hV hV2
  let C := fun (n : ℕ) => (S.cellCount (t19_sample n ω) z y : ℝ)
  let A := fun (n : ℕ) => ∑ i : Fin n, if S.cell z y (ω i) then (S.V (ω i) : ℝ) else 0
  let B := fun (n : ℕ) => ∑ i : Fin n, if S.cell z y (ω i) then (S.V (ω i) : ℝ)^2 else 0
  have hc : Tendsto (fun (n : ℕ) => C n/(n : ℝ)) atTop (nhds (S.law.prob (S.cell z y))) := by
    simpa only [C, ← t19_count_sum, t19_sample, FiniteLaw.prob] using hI
  have hN : Tendsto C atTop atTop := by
    have h := hc.pos_mul_atTop hp tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hn)
  have h2 : ∀ᶠ n in atTop, 2 ≤ S.cellCount (t19_sample n ω) z y := by
    filter_upwards [hN.eventually_ge_atTop 2] with n hn
    change (2 : ℝ) ≤ (S.cellCount (t19_sample n ω) z y : ℝ) at hn
    exact_mod_cast hn
  have hm : Tendsto (fun (n : ℕ) => S.cellMean (t19_sample n ω) z y c)
      atTop (nhds (S.listMean z y)) := by
    have h := hV.div hc (ne_of_gt hp)
    change Tendsto _ atTop (nhds (_/_)) at h
    apply h.congr'
    filter_upwards [h2, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
    have hcnt : S.cellCount (t19_sample n ω) z y ≠ 0 := by omega
    simp only [Study.cellMean, if_neg hcnt, t19_sample]
    dsimp only [C]
    exact div_div_div_cancel_right₀ hn' _ _
  have hm0 : Tendsto (fun (n : ℕ) => S.cellMean (t19_sample n ω) z y 0)
      atTop (nhds (S.listMean z y)) := by
    apply hm.congr'
    filter_upwards [h2] with n hn
    have hcnt : S.cellCount (t19_sample n ω) z y ≠ 0 := by omega
    simp [Study.cellMean, hcnt]
  have hInv : Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hfac := hc.div (hc.sub hInv) (by simpa using ne_of_gt hp)
  have hsecond := hV2.div hc (ne_of_gt hp)
  have hv := ((hsecond.sub (hm0.pow 2)).mul hfac)
  have hv' : Tendsto (fun (n : ℕ) => S.cellVariance (t19_sample n ω) z y) atTop
      (nhds (S.law.cv (fun t => (S.V t : ℝ)) (S.cell z y))) := by
    change Tendsto _ atTop (nhds ((_/_-_^2)*(_/(_-0)))) at hv
    rw [sub_zero, div_self (ne_of_gt hp), mul_one] at hv
    apply hv.congr'
    filter_upwards [h2, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
    rw [t19_cell_variance_identity S _ z y hn]
    have hcn : (S.cellCount (t19_sample n ω) z y : ℝ) ≠ 0 := by
      exact_mod_cast (show S.cellCount (t19_sample n ω) z y ≠ 0 by omega)
    have hcm : (S.cellCount (t19_sample n ω) z y : ℝ)-1 ≠ 0 := by
      have : (2 : ℝ) ≤ (S.cellCount (t19_sample n ω) z y : ℝ) := by exact_mod_cast hn
      linarith
    dsimp only [Pi.div_apply, Pi.sub_apply, C, t19_sample]
    field_simp
    <;> ring_nf <;> congr!
  exact ⟨hc, h2, hm, hv'⟩

/-- Portmanteau, expressed using real probabilities on the original sample space. -/
lemma t19_event_limit {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → A → ℝ} {Z : B → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (D : Set ℝ) (hD : MeasurableSet D) (hbd : ν.map Z (frontier D) = 0) :
    Tendsto (fun (n : ℕ) => μ.real {ω | X n ω ∈ D}) atTop
      (nhds (ν.real {ω | Z ω ∈ D})) := by
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto hbd
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (ν.map Z) D)).comp hp
  change Tendsto (fun n => ((μ.map (X n)) D).toReal) atTop
    (nhds ((ν.map Z D).toReal)) at hr
  have hz : (ν.map Z D).toReal = ν.real {ω | Z ω ∈ D} := by
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit hD]
    rfl
  rw [hz] at hr
  apply hr.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hD]
    rfl)

lemma t19_distribution_zero_probability {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : ℕ → A → ℝ}
    (h : TendstoInDistribution X atTop (fun _ : B => (0 : ℝ)) (fun _ => μ) ν) :
    TendstoInMeasure μ X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  let D : Set ℝ := {x | ε ≤ ‖x‖}
  have hD : IsClosed D := isClosed_le continuous_const continuous_norm
  have h0 : (0 : ℝ) ∉ frontier D := by
    intro hmem
    have := hD.frontier_subset hmem
    simpa [D, not_le.mpr hε] using this
  have hb : ν.map (fun _ : B => (0 : ℝ)) (frontier D) = 0 := by
    simp [Measure.map_const, h0]
  have hh := t19_event_limit h D hD.measurableSet hb
  simpa [D, hε.not_ge] using hh

lemma t19_small_product (P : FiniteLaw Ω) (f : Ω → ℝ) (hf : P.mean f = 0)
    (b : ℕ → (ℕ → Ω) → ℝ) (hb : ∀ n, Measurable (b n))
    (hb0 : ∀ᵐ ω ∂t19_product P, Tendsto (fun (n : ℕ) => b n ω) atTop (nhds 0)) :
    TendstoInMeasure (t19_product P)
      (fun (n : ℕ) ω => ((Real.sqrt n)⁻¹ * ∑ i : Fin n, f (ω i)) * b n ω)
      atTop (fun _ => 0) := by
  have hbp := tendstoInMeasure_of_tendsto_ae (fun (n : ℕ) => (hb n).aestronglyMeasurable) hb0
  have hm := (t19_average_clt P f hf).continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1*p.2) (by fun_prop) hbp
    (fun (n : ℕ) => (hb n).aemeasurable)
  apply t19_distribution_zero_probability (ν := gaussianReal 0 (P.variance f).toNNReal)
  simpa only [mul_zero] using hm

lemma t19_transfer_inMeasure {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsProbabilityMeasure μ] {X Y : ℕ → A → ℝ} {a : ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (h : TendstoInMeasure μ X atTop (fun _ => a))
    (he : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, X n ω = Y n ω) :
    TendstoInMeasure μ Y atTop (fun _ => a) := by
  have hz : TendstoInMeasure μ (fun (n : ℕ) ω => Y n ω-X n ω) atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun (n : ℕ) => ((hY n).sub (hX n)).aestronglyMeasurable)
    filter_upwards [he] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    simp [hn]
  have hh := AronowAudit.P015.ConvergenceCompletion.add_limit μ h hz
  simpa only [add_sub_cancel, add_zero] using hh

lemma t19_population_identity (S : Study Ω) (hs : S.standing) :
    S.mu = S.law.prob (fun t => S.Y t = true) +
      (1-S.law.prob (fun t => S.Y t = true))*(S.listMean true false-S.listMean false false) := by
  rw [prevalence_identity S hs]
  unfold Study.combined
  rw [mean_sub, mean_const, mean_bit]

lemma t19_ybar_ae (S : Study Ω) :
    ∀ᵐ ω ∂t19_product S.law,
      Tendsto (fun (n : ℕ) => S.ybar (t19_sample n ω)) atTop
        (nhds (S.law.prob (fun t => S.Y t = true))) := by
  simpa only [mean_bit, Study.ybar, t19_sample] using t19_average_ae S.law (fun t => bitVal (S.Y t))

lemma t19_gamma_ae (S : Study Ω) :
    ∀ᵐ ω ∂t19_product S.law,
      Tendsto (fun (n : ℕ) => S.gammaHat (t19_sample n ω)) atTop (nhds S.gamma) := by
  have hh := t19_average_ae S.law (fun t => if S.Z t = true then 1 else 0)
  simpa only [Study.gammaHat, Study.armCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Study.gamma, FiniteLaw.prob, t19_sample] using hh

lemma t19_consistency_ae (S : Study Ω) (hs : S.standing) (c1 c0 cV : ℝ) :
    ∀ᵐ ω ∂t19_product S.law,
      Tendsto (fun (n : ℕ) => S.muHat (t19_sample n ω) c1 c0) atTop (nhds S.mu) ∧
      Tendsto (fun (n : ℕ) => (n : ℝ)*S.muVarianceHat (t19_sample n ω) c1 c0 cV)
        atTop (nhds S.sigmaSq) := by
  have hp := regularity_probabilities S hs.2.2.2
  have hy : S.law.prob (fun t => S.Y t = true) < 1 := by
    have hh := hp.2 false
    rw [prob_false] at hh
    linarith
  have hg : 0 < S.gamma := hp.1 true
  have hg1 : S.gamma < 1 := by
    have hh := hp.1 false
    rw [prob_false] at hh
    change 0 < 1-S.gamma at hh
    linarith
  filter_upwards [t19_ybar_ae S, t19_gamma_ae S,
    t19_cell_ae S true false c1 (hs.2.2.2.1 true false).1,
    t19_cell_ae S false false c0 (hs.2.2.2.1 false false).1] with ω hY hG h1 h0
  have hmu : Tendsto (fun (n : ℕ) => S.muHat (t19_sample n ω) c1 c0) atTop (nhds S.mu) := by
    rw [t19_population_identity S hs]
    exact hY.add (((tendsto_const_nhds (x := (1 : ℝ))).sub hY).mul (h1.2.2.1.sub h0.2.2.1))
  have hgood : ∀ᶠ n in atTop,
      2 ≤ S.cellCount (t19_sample n ω) true false ∧
      2 ≤ S.cellCount (t19_sample n ω) false false ∧
      S.ybar (t19_sample n ω) < 1 ∧
      0 < S.gammaHat (t19_sample n ω) ∧ S.gammaHat (t19_sample n ω) < 1 := by
    filter_upwards [h1.2.1, h0.2.1, hY.eventually_lt_const hy,
      hG.eventually_const_lt hg, hG.eventually_lt_const hg1] with n h1 h0 hY hG hG1
    exact ⟨h1, h0, hY, hG, hG1⟩
  have hq : 1-S.law.prob (fun t => S.Y t = true) ≠ 0 := by linarith
  have hgg : 1-S.gamma ≠ 0 := by linarith
  have hformula :=
    ((((tendsto_const_nhds (x := (1 : ℝ))).sub hmu).pow 2).div ((tendsto_const_nhds (x := (1 : ℝ))).sub hY) hq).mul hY |>.add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hY).mul
        ((h1.2.2.2.div hG (ne_of_gt hg)).add
          (h0.2.2.2.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hG) hgg)))
  have hplugin : Tendsto (fun (n : ℕ) => (n : ℝ)*S.muVarianceHat (t19_sample n ω) c1 c0 cV)
      atTop (nhds S.sigmaSq) := by
    have hlim : ((1-S.mu)^2/(1-S.law.prob (fun t => S.Y t = true)))*
        S.law.prob (fun t => S.Y t = true) +
        (1-S.law.prob (fun t => S.Y t = true))*
          (S.law.cv (fun t => (S.V t : ℝ)) (S.cell true false)/S.gamma +
            S.law.cv (fun t => (S.V t : ℝ)) (S.cell false false)/(1-S.gamma)) = S.sigmaSq := by
      unfold Study.sigmaSq
      rw [← direct_response_probability S hs.1 hs.2.2.2]
    rw [hlim] at hformula
    apply hformula.congr'
    filter_upwards [hgood, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    rw [Study.muVarianceHat, if_pos hn]
    exact (mul_div_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hn0)).symm
  exact ⟨hmu, hplugin⟩

lemma t19_masked_residual (S : Study Ω) {n : ℕ} (s : Fin n → Ω)
    (z y : Bool) (c : ℝ) (hN : S.cellCount s z y ≠ 0) :
    S.cellMean s z y c-S.listMean z y =
      (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ)-S.listMean z y else 0) /
        (S.cellCount s z y : ℝ) := by
  have hNr : (S.cellCount s z y : ℝ) ≠ 0 := by exact_mod_cast hN
  have h := ratio_residual_identity
    (fun i => if S.cell z y (s i) then (1 : ℝ) else 0)
    (fun i => (S.V (s i) : ℝ)) (S.listMean z y)
    (by simpa only [t19_count_sum] using hNr)
  simpa only [ite_mul, one_mul, zero_mul, t19_count_sum,
    Study.cellMean, if_neg hN] using h

lemma t19_linearization_point (S : Study Ω) (hs : S.standing) {n : ℕ}
    (s : Fin n → Ω) (c1 c0 : ℝ) (hn : 0 < n)
    (h1 : S.cellCount s true false ≠ 0) (h0 : S.cellCount s false false ≠ 0) :
    Real.sqrt n*(S.muHat s c1 c0-S.mu) -
      (Real.sqrt n)⁻¹*(∑ i, S.combinedPsi (s i)) =
    ((Real.sqrt n)⁻¹*(∑ i, if S.cell true false (s i) then
        (S.V (s i) : ℝ)-S.listMean true false else 0)) *
      ((1-S.law.prob (fun t => S.Y t = true))/((S.cellCount s true false : ℝ)/(n : ℝ)) -
        1/S.gamma) -
    ((Real.sqrt n)⁻¹*(∑ i, if S.cell false false (s i) then
        (S.V (s i) : ℝ)-S.listMean false false else 0)) *
      ((1-S.law.prob (fun t => S.Y t = true))/((S.cellCount s false false : ℝ)/(n : ℝ)) -
        1/(1-S.gamma)) -
    ((Real.sqrt n)⁻¹*(∑ i, (bitVal (S.Y (s i))-S.law.prob (fun t => S.Y t = true)))) *
      ((S.cellMean s true false c1-S.listMean true false) -
        (S.cellMean s false false c0-S.listMean false false)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hinv : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt (n : ℝ)/(n : ℝ) := by
    apply (eq_div_iff hn').mpr
    calc
      (Real.sqrt (n : ℝ))⁻¹*(n : ℝ) =
          (Real.sqrt (n : ℝ))⁻¹*(Real.sqrt (n : ℝ))^2 := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      _ = Real.sqrt (n : ℝ) := by field_simp
  have h1r : (S.cellCount s true false : ℝ) ≠ 0 := by exact_mod_cast h1
  have h0r : (S.cellCount s false false : ℝ) ≠ 0 := by exact_mod_cast h0
  have hγ : S.gamma ≠ 0 := ne_of_gt ((regularity_probabilities S hs.2.2.2).1 true)
  have hγ0 : 1-S.gamma ≠ 0 := by
    have h := (regularity_probabilities S hs.2.2.2).1 false
    rw [prob_false] at h
    exact ne_of_gt h
  have hsum : (∑ i, S.combinedPsi (s i)) =
      (1-(S.listMean true false-S.listMean false false)) *
        (∑ i, (bitVal (S.Y (s i))-S.law.prob (fun t => S.Y t = true))) +
      (∑ i, if S.cell true false (s i) then
        (S.V (s i) : ℝ)-S.listMean true false else 0)/S.gamma -
      (∑ i, if S.cell false false (s i) then
        (S.V (s i) : ℝ)-S.listMean false false else 0)/(1-S.gamma) := by
    simp only [Study.combinedPsi, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_div, mul_sub]
  have hy : (∑ i, (bitVal (S.Y (s i))-S.law.prob (fun t => S.Y t = true))) =
      (n : ℝ)*(S.ybar s-S.law.prob (fun t => S.Y t = true)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Study.ybar]
    field_simp
  rw [hsum, hy, hinv, Study.muHat,
    estimator_error_decomposition _ _ _ _ _ _ _ (t19_population_identity S hs),
    t19_masked_residual S s true false c1 h1,
    t19_masked_residual S s false false c0 h0]
  field_simp
  <;> ring

lemma t19_combined_clt (S : Study Ω) (hs : S.standing) (c1 c0 : ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → Ω) => Real.sqrt n*(S.muHat (t19_sample n ω) c1 c0-S.mu))
      atTop id (fun _ => t19_product S.law) (gaussianReal 0 S.sigmaSq.toNNReal) := by
  let u1 : Ω → ℝ := fun t => if S.cell true false t then
    (S.V t : ℝ)-S.listMean true false else 0
  let u0 : Ω → ℝ := fun t => if S.cell false false t then
    (S.V t : ℝ)-S.listMean false false else 0
  let uY : Ω → ℝ := fun t => bitVal (S.Y t)-S.law.prob (fun t => S.Y t = true)
  let b1 : ℕ → (ℕ → Ω) → ℝ := fun (n : ℕ) ω =>
    (1-S.law.prob (fun t => S.Y t = true))/
      ((S.cellCount (t19_sample n ω) true false : ℝ)/(n : ℝ)) - 1/S.gamma
  let b0 : ℕ → (ℕ → Ω) → ℝ := fun (n : ℕ) ω =>
    (1-S.law.prob (fun t => S.Y t = true))/
      ((S.cellCount (t19_sample n ω) false false : ℝ)/(n : ℝ)) - 1/(1-S.gamma)
  let bY : ℕ → (ℕ → Ω) → ℝ := fun (n : ℕ) ω =>
    (S.cellMean (t19_sample n ω) true false c1-S.listMean true false) -
    (S.cellMean (t19_sample n ω) false false c0-S.listMean false false)
  have hp1 := (hs.2.2.2.1 true false).1
  have hp0 := (hs.2.2.2.1 false false).1
  have hcp1 : S.law.prob (S.cell true false) =
      S.gamma*(1-S.law.prob (fun t => S.Y t = true)) := by
    rw [cell_probability S hs.2.2.1, prob_false]
    rfl
  have hcp0 : S.law.prob (S.cell false false) =
      (1-S.gamma)*(1-S.law.prob (fun t => S.Y t = true)) := by
    rw [cell_probability S hs.2.2.1, prob_false, prob_false]
    rfl
  have hγ : S.gamma ≠ 0 := ne_of_gt ((regularity_probabilities S hs.2.2.2).1 true)
  have hγ0 : 1-S.gamma ≠ 0 := by
    have h := (regularity_probabilities S hs.2.2.2).1 false
    rw [prob_false] at h
    exact ne_of_gt h
  have hq : 1-S.law.prob (fun t => S.Y t = true) ≠ 0 := by
    have h := (regularity_probabilities S hs.2.2.2).2 false
    rw [prob_false] at h
    exact ne_of_gt h
  have hb1 : ∀ᵐ ω ∂t19_product S.law, Tendsto (fun (n : ℕ) => b1 n ω) atTop (nhds 0) := by
    filter_upwards [t19_cell_ae S true false c1 hp1] with ω h
    have hh := ((tendsto_const_nhds (x := 1-S.law.prob (fun t => S.Y t = true))).div h.1 (ne_of_gt hp1)).sub
      (tendsto_const_nhds (x := 1/S.gamma))
    have he : (1-S.law.prob (fun t => S.Y t = true))/S.law.prob (S.cell true false) -
        1/S.gamma = 0 := by rw [hcp1]; field_simp; ring
    simpa only [he, Pi.div_apply, b1] using hh
  have hb0 : ∀ᵐ ω ∂t19_product S.law, Tendsto (fun (n : ℕ) => b0 n ω) atTop (nhds 0) := by
    filter_upwards [t19_cell_ae S false false c0 hp0] with ω h
    have hh := ((tendsto_const_nhds (x := 1-S.law.prob (fun t => S.Y t = true))).div h.1 (ne_of_gt hp0)).sub
      (tendsto_const_nhds (x := 1/(1-S.gamma)))
    have he : (1-S.law.prob (fun t => S.Y t = true))/S.law.prob (S.cell false false) -
        1/(1-S.gamma) = 0 := by rw [hcp0]; field_simp; ring
    simpa only [he, Pi.div_apply, b0] using hh
  have hbY : ∀ᵐ ω ∂t19_product S.law, Tendsto (fun (n : ℕ) => bY n ω) atTop (nhds 0) := by
    filter_upwards [t19_cell_ae S true false c1 hp1,
      t19_cell_ae S false false c0 hp0] with ω h1 h0
    simpa only [sub_self] using
      ((h1.2.2.1.sub (tendsto_const_nhds (x := S.listMean true false))).sub
        (h0.2.2.1.sub (tendsto_const_nhds (x := S.listMean false false))))
  have hu1 : S.law.mean u1 = 0 :=
    (masked_central_moments S.law _ _ (ne_of_gt hp1)).1
  have hu0 : S.law.mean u0 = 0 :=
    (masked_central_moments S.law _ _ (ne_of_gt hp0)).1
  have huY : S.law.mean uY = 0 := by
    dsimp only [uY]
    rw [mean_sub, mean_const, mean_bit, sub_self]
  have hR1 := t19_small_product S.law u1 hu1 b1
    (fun (n : ℕ) => t19_stat_measurable n (fun s =>
      (1-S.law.prob (fun t => S.Y t = true))/((S.cellCount s true false : ℝ)/(n : ℝ))-1/S.gamma)) hb1
  have hR0 := t19_small_product S.law u0 hu0 b0
    (fun (n : ℕ) => t19_stat_measurable n (fun s =>
      (1-S.law.prob (fun t => S.Y t = true))/((S.cellCount s false false : ℝ)/(n : ℝ))-1/(1-S.gamma))) hb0
  have hRY := t19_small_product S.law uY huY bY
    (fun (n : ℕ) => t19_stat_measurable n (fun s =>
      (S.cellMean s true false c1-S.listMean true false)-
        (S.cellMean s false false c0-S.listMean false false))) hbY
  let R : ℕ → (ℕ → Ω) → ℝ := fun (n : ℕ) ω =>
    ((Real.sqrt n)⁻¹*∑ i : Fin n, u1 (ω i))*b1 n ω -
    ((Real.sqrt n)⁻¹*∑ i : Fin n, u0 (ω i))*b0 n ω -
    ((Real.sqrt n)⁻¹*∑ i : Fin n, uY (ω i))*bY n ω
  have hR : TendstoInMeasure (t19_product S.law) R atTop (fun _ => 0) := by
    simpa only [sub_zero] using
      AronowAudit.P015.ConvergenceCompletion.sub_limit _
        (AronowAudit.P015.ConvergenceCompletion.sub_limit _ hR1 hR0) hRY
  have hdiff : TendstoInMeasure (t19_product S.law)
      (fun (n : ℕ) ω => Real.sqrt n*(S.muHat (t19_sample n ω) c1 c0-S.mu) -
        (Real.sqrt n)⁻¹*∑ i : Fin n, S.combinedPsi (ω i)) atTop (fun _ => 0) := by
    apply t19_transfer_inMeasure (t19_product S.law) (X := R)
      (fun n => t19_stat_measurable n (fun s =>
        ((Real.sqrt n)⁻¹*∑ i : Fin n, u1 (s i))*
          ((1-S.law.prob (fun t => S.Y t = true))/((S.cellCount s true false : ℝ)/(n : ℝ))-1/S.gamma) -
        ((Real.sqrt n)⁻¹*∑ i : Fin n, u0 (s i))*
          ((1-S.law.prob (fun t => S.Y t = true))/((S.cellCount s false false : ℝ)/(n : ℝ))-1/(1-S.gamma)) -
        ((Real.sqrt n)⁻¹*∑ i : Fin n, uY (s i))*
          ((S.cellMean s true false c1-S.listMean true false)-
            (S.cellMean s false false c0-S.listMean false false))))
      (fun n => t19_stat_measurable n (fun s => Real.sqrt n*(S.muHat s c1 c0-S.mu)-
        (Real.sqrt n)⁻¹*∑ i : Fin n, S.combinedPsi (s i))) hR
    filter_upwards [t19_cell_ae S true false c1 hp1,
      t19_cell_ae S false false c0 hp0] with ω h1 h0
    filter_upwards [h1.2.1, h0.2.1, eventually_gt_atTop (0 : ℕ)] with n hn1 hn0 hn
    exact (t19_linearization_point S hs (t19_sample n ω) c1 c0 hn
      (by omega) (by omega)).symm
  have hCLT := t19_average_clt S.law S.combinedPsi
    (combined_influence_moments S hs.2.2.1 hs.2.2.2).1
  rw [combined_influence_variance S hs] at hCLT
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hCLT hdiff
    (fun n => (t19_stat_measurable n (fun s => Real.sqrt n*(S.muHat s c1 c0-S.mu))).aemeasurable)

lemma t19_weakLimit (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → ℝ)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (h : TendstoInDistribution (fun (n : ℕ) ω => T n (t19_sample n ω))
      atTop id (fun _ => t19_product P) Q) : WeakLimit P T Q := by
  intro f hf hbound
  obtain ⟨C, hC⟩ := hbound
  let F : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨f, hf⟩, ⟨2*C, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hC x) (hC y))⟩⟩
  have hh := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h F
  change Tendsto (fun (n : ℕ) => ∫ ω, f (T n (t19_sample n ω)) ∂t19_product P)
    atTop (nhds (∫ x, f x ∂Q)) at hh
  convert hh using 1
  funext n
  exact (t19_sample_integral P n (fun s => f (T n s))).symm

lemma t19_probabilityLimit (P : FiniteLaw Ω)
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (a : ℝ)
    (h : TendstoInMeasure (t19_product P) (fun (n : ℕ) ω => T n (t19_sample n ω))
      atTop (fun _ => a)) : ProbabilityLimit P T a := by
  intro ε hε
  have hh := (tendstoInMeasure_iff_measureReal_norm.mp h) ε hε
  rw [show (fun (n : ℕ) => (P.iid n).prob (fun s => ε < |T n s-a|)) =
      (fun (n : ℕ) => (t19_product P).real {ω | ε < |T n (t19_sample n ω)-a|}) by
        funext n; exact (t19_sample_prob P n _).symm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => measureReal_nonneg)
  intro n
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change ε < |T n (t19_sample n ω)-a| at hω
  change ε ≤ ‖T n (t19_sample n ω)-a‖
  simpa only [Real.norm_eq_abs] using hω.le

lemma t19_distribution_hasLaw {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → A → ℝ} {Z : B → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (h : TendstoInDistribution X atTop Z (fun _ => μ) ν) (hZ : HasLaw Z Q ν) :
    TendstoInDistribution X atTop id (fun _ => μ) Q := by
  refine ⟨h.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [hZ.map_eq, Measure.map_id] using h.tendsto

lemma t19_studentized_clt (S : Study Ω) (hs : S.standing) (c1 c0 cV : ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n*(S.muHat (t19_sample n ω) c1 c0-S.mu)) /
        Real.sqrt ((n : ℝ)*S.muVarianceHat (t19_sample n ω) c1 c0 cV))
      atTop id (fun _ => t19_product S.law) (gaussianReal 0 1) := by
  have hv := asymptotic_variance_positive S hs
  have hsqrt : Real.sqrt S.sigmaSq ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have ha : ∀ᵐ ω ∂t19_product S.law, Tendsto
      (fun (n : ℕ) => (Real.sqrt ((n : ℝ)*S.muVarianceHat (t19_sample n ω) c1 c0 cV))⁻¹)
      atTop (nhds (Real.sqrt S.sigmaSq)⁻¹) := by
    filter_upwards [t19_consistency_ae S hs c1 c0 cV] with ω hω
    exact hω.2.sqrt.inv₀ hsqrt
  have hi := tendstoInMeasure_of_tendsto_ae (μ := t19_product S.law)
    (fun n => (t19_stat_measurable n (fun s =>
      (Real.sqrt ((n : ℝ)*S.muVarianceHat s c1 c0 cV))⁻¹)).aestronglyMeasurable) ha
  have hh := (t19_combined_clt S hs c1 c0).continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1*p.2) (by fun_prop) hi
    (fun n => (t19_stat_measurable n (fun s =>
      (Real.sqrt ((n : ℝ)*S.muVarianceHat s c1 c0 cV))⁻¹)).aemeasurable)
  have hd : NNReal.mk ((Real.sqrt S.sigmaSq)^2) (sq_nonneg _) = S.sigmaSq.toNNReal := by
    apply NNReal.eq
    change (Real.sqrt S.sigmaSq)^2 = (S.sigmaSq.toNNReal : ℝ)
    rw [Real.sq_sqrt hv.le]
    exact (Real.coe_toNNReal S.sigmaSq hv.le).symm
  have hvnn : S.sigmaSq.toNNReal ≠ 0 := by
    simpa only [ne_eq, Real.toNNReal_eq_zero, not_le] using hv
  have hl := gaussianReal_div_const
    (HasLaw.id : HasLaw id (gaussianReal 0 S.sigmaSq.toNNReal)
      (gaussianReal 0 S.sigmaSq.toNNReal)) (Real.sqrt S.sigmaSq)
  rw [zero_div, hd, div_self hvnn] at hl
  apply t19_distribution_hasLaw (ν := gaussianReal 0 S.sigmaSq.toNNReal) (Q := gaussianReal 0 1)
    (by simpa only [div_eq_mul_inv] using hh)
  simpa only [div_eq_mul_inv] using hl

lemma t19_indicator_transfer (P : FiniteLaw Ω)
    (D E : (n : ℕ) → (Fin n → Ω) → Prop)
    (he : ∀ᵐ ω ∂t19_product P,
      ∀ᶠ n in atTop, D n (t19_sample n ω) ↔ E n (t19_sample n ω)) :
    Tendsto (fun (n : ℕ) => (P.iid n).prob (D n)-(P.iid n).prob (E n)) atTop (nhds 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := t19_product P)
    (F := fun (n : ℕ) ω => (if D n (t19_sample n ω) then (1 : ℝ) else 0) -
      (if E n (t19_sample n ω) then 1 else 0)) (f := fun _ => (0 : ℝ))
    (fun _ => (2 : ℝ))
    (fun (n : ℕ) => (t19_stat_measurable n (fun s =>
      (if D n s then (1 : ℝ) else 0)-(if E n s then 1 else 0))).aestronglyMeasurable)
    (integrable_const _)
    (fun (n : ℕ) => Filter.Eventually.of_forall (fun ω => by split_ifs <;> norm_num))
    (by
      filter_upwards [he] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      simp [hn])
  simp only [integral_zero] at hh
  convert hh using 1
  funext n
  rw [t19_sample_integral P n (fun s =>
    (if D n s then (1 : ℝ) else 0)-(if E n s then 1 else 0)), mean_sub]
  rfl

lemma t19_coverage_point {n : ℕ} (hn : 0 < n) (e v c : ℝ) (hv : 0 < (n : ℝ)*v) :
    (|e| ≤ c*Real.sqrt v) ↔
      (Real.sqrt n*e/Real.sqrt ((n : ℝ)*v)) ∈ Set.Icc (-c) c := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [Set.mem_Icc, ← abs_le, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    div_le_iff₀ (Real.sqrt_pos.mpr hv), abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [show c*(Real.sqrt (n : ℝ)*Real.sqrt v) = Real.sqrt n*(c*Real.sqrt v) by ring]
  exact (mul_le_mul_iff_right₀ hs).symm

lemma t19_Wald_coverage (S : Study Ω) (hs : S.standing) (c1 c0 cV : ℝ)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
      |S.muHat s c1 c0-S.mu| ≤ normalQuantile (1-α/2)*
        Real.sqrt (S.muVarianceHat s c1 c0 cV))) atTop (nhds (1-α)) := by
  let c := normalQuantile (1-α/2)
  have hc : c = AronowAudit.P053.normalCritical α := rfl
  have hcpos : 0 < c := by
    rw [hc]
    exact AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1
  haveI instNullSingletonT19 : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  let Z : (n : ℕ) → (Fin n → Ω) → ℝ := fun n s =>
    Real.sqrt n*(S.muHat s c1 c0-S.mu)/Real.sqrt ((n : ℝ)*S.muVarianceHat s c1 c0 cV)
  have hZ := t19_studentized_clt S hs c1 c0 cV
  have hp := t19_event_limit hZ (Set.Icc (-c) c) measurableSet_Icc
    (by
      rw [Measure.map_id, frontier_Icc (by linarith : -c ≤ c)]
      exact ((Set.finite_singleton c).insert (-c)).measure_zero _)
  have hmass : (gaussianReal 0 1).real (Set.Icc (-c) c) = 1-α := by
    rw [hc]
    exact AronowAudit.P053.NormalCompletion.normalCritical_interval_mass α hα hα1
  have hp' : Tendsto (fun (n : ℕ) => (S.law.iid n).prob (fun s => Z n s ∈ Set.Icc (-c) c))
      atTop (nhds (1-α)) := by
    change Tendsto (fun n => (t19_product S.law).real
      {ω | Z n (t19_sample n ω) ∈ Set.Icc (-c) c}) atTop
      (nhds ((gaussianReal 0 1).real (Set.Icc (-c) c))) at hp
    rw [hmass] at hp
    apply hp.congr'
    exact Filter.Eventually.of_forall (fun n => by
      dsimp only
      convert t19_sample_prob S.law n (fun s => Z n s ∈ Set.Icc (-c) c) using 1 <;> congr!)
  have hdiff := t19_indicator_transfer S.law
    (fun _ s => |S.muHat s c1 c0-S.mu| ≤ c*Real.sqrt (S.muVarianceHat s c1 c0 cV))
    (fun n s => Z n s ∈ Set.Icc (-c) c) (by
      filter_upwards [t19_consistency_ae S hs c1 c0 cV] with ω hω
      filter_upwards [hω.2.eventually_const_lt (asymptotic_variance_positive S hs),
        eventually_gt_atTop (0 : ℕ)] with n hv hn
      exact t19_coverage_point hn _ _ _ hv)
  have hh := hdiff.add hp'
  simp only [zero_add] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    convert sub_add_cancel
      ((S.law.iid n).prob (fun s => |S.muHat s c1 c0-S.mu| ≤ c*Real.sqrt (S.muVarianceHat s c1 c0 cV)))
      ((S.law.iid n).prob (fun s => Z n s ∈ Set.Icc (-c) c)) using 1 <;> congr!)

lemma t19_rootNTight (S : Study Ω) (hs : S.standing) (c1 c0 : ℝ) : RootNTight S c1 c0 := by
  have hv := asymptotic_variance_positive S hs
  let Q := gaussianReal 0 S.sigmaSq.toNNReal
  haveI instNullSingletonT19Root : NullSingletonClass Q :=
    nullSingletonClass_gaussianReal (by
      have : S.sigmaSq.toNNReal ≠ 0 := by
        simpa only [ne_eq, Real.toNNReal_eq_zero, not_le] using hv
      exact this)
  intro ε hε
  let M := S.sigmaSq/ε+1
  have hM1 : 1 < M := by dsimp [M]; linarith [div_pos hv hε]
  have hM : 0 < M := by linarith
  have hbound : S.sigmaSq/M^2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hM)).mpr
    have hprod : ε*M = S.sigmaSq+ε := by dsimp [M]; field_simp
    have hsq : M ≤ M^2 := by nlinarith
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hsq)]
  let D : Set ℝ := (Set.Icc (-M) M)ᶜ
  have htail : Q.real D ≤ S.sigmaSq/M^2 := by
    have hcheb := meas_ge_le_variance_div_sq (μ := Q) (X := id)
      (memLp_id_gaussianReal 2) hM
    have hle : Q.real {x : ℝ | M ≤ |x|} ≤ S.sigmaSq/M^2 := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      simpa [Q, integral_id_gaussianReal, variance_id_gaussianReal,
        Real.coe_toNNReal _ hv.le, ENNReal.toReal_ofReal (div_nonneg hv.le (sq_nonneg M)),
        measureReal_def] using hh
    exact (measureReal_mono (by
      intro x hx
      exact le_of_lt (by simpa [D, Set.mem_Icc, ← abs_le] using hx))).trans hle
  have hbd : Q.map id (frontier D) = 0 := by
    rw [Measure.map_id]
    dsimp only [D]
    rw [frontier_compl, frontier_Icc (by linarith : -M ≤ M)]
    exact ((Set.finite_singleton M).insert (-M)).measure_zero Q
  have hp := t19_event_limit (t19_combined_clt S hs c1 c0) D
    measurableSet_Icc.compl hbd
  have hP : Tendsto (fun (n : ℕ) => (S.law.iid n).prob (fun s =>
      M < |Real.sqrt n*(S.muHat s c1 c0-S.mu)|)) atTop (nhds (Q.real D)) := by
    change Tendsto (fun (n : ℕ) => (t19_product S.law).real
      {ω | Real.sqrt n*(S.muHat (t19_sample n ω) c1 c0-S.mu) ∈ D})
      atTop (nhds (Q.real D)) at hp
    apply hp.congr'
    filter_upwards [] with n
    rw [← t19_sample_prob S.law n (fun s => M < |Real.sqrt n*(S.muHat s c1 c0-S.mu)|)]
    congr 1
    ext ω
    simp only [D, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hP.eventually_lt_const (htail.trans_lt hbound))
  exact ⟨M, hM, N, hN⟩

end

noncomputable section
variable {Ω : Type*} [Fintype Ω]

theorem combined_asymptotic_inference_proof (S : Study Ω) (hs : S.standing) (c1 c0 cV : ℝ) :
    RootNTight S c1 c0 ∧
    WeakLimit S.law (fun n s => Real.sqrt n * (S.muHat s c1 c0-S.mu))
      (gaussianReal 0 S.sigmaSq.toNNReal) ∧
    ProbabilityLimit S.law (fun n s => (n : ℝ)*S.muVarianceHat s c1 c0 cV) S.sigmaSq ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        |S.muHat s c1 c0-S.mu| ≤ normalQuantile (1-α/2) *
          Real.sqrt (S.muVarianceHat s c1 c0 cV))) atTop (nhds (1-α))) := by
  letI instMeasurableT19Final : MeasurableSpace Ω := ⊤
  haveI instSingletonT19Final : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  refine ⟨t19_rootNTight S hs c1 c0, t19_weakLimit _ _ _ (t19_combined_clt S hs c1 c0), ?_,
    t19_Wald_coverage S hs c1 c0 cV⟩
  apply t19_probabilityLimit S.law (fun (n : ℕ) s => (n : ℝ)*S.muVarianceHat s c1 c0 cV) S.sigmaSq
  apply tendstoInMeasure_of_tendsto_ae (μ := t19_product S.law) (fun n =>
    (t19_stat_measurable n (fun s => (n : ℝ)*S.muVarianceHat s c1 c0 cV)).aestronglyMeasurable)
  filter_upwards [t19_consistency_ae S hs c1 c0 cV] with ω hω
  exact hω.2

end
end AronowAudit.P019.Wave1
