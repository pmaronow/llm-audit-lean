import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0012B1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

/-! The explicit bounded summand, its mean, and clipping. -/

def matching_score_summand (u : ℝ × Bool × Bool) : ℝ :=
  (if u.2.1 then (1 : ℝ) else 0) - (u.1 - 1/4)

def matching_score_density (u : ℝ × Bool × Bool) : ℝ :=
  if u.1 ∈ Set.Icc (1/4 : ℝ) (3/4) then
    (if u.2.1 then u.1 else 1-u.1) else 0

lemma matching_score_summand_measurable : Measurable matching_score_summand := by
  have hb : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
    measurable_of_finite _
  exact (hb.comp measurable_snd.fst).sub (measurable_fst.sub_const (1/4 : ℝ))

lemma matching_score_density_measurable : Measurable matching_score_density := by
  have hb : Measurable (fun u : ℝ × Bool × Bool =>
      if u.2.1 then u.1 else 1-u.1) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd.fst measurable_const)
      measurable_fst (measurable_const.sub measurable_fst)
  exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hb measurable_const

lemma matching_score_density_nonneg (u : ℝ × Bool × Bool) :
    0 ≤ matching_score_density u := by
  unfold matching_score_density
  split_ifs with hp hd
  · linarith [hp.1]
  · linarith [hp.2]
  · exact le_rfl

lemma matching_score_density_toReal (u : ℝ × Bool × Bool) :
    (ENNReal.ofReal (matching_score_density u)).toReal = matching_score_density u :=
  ENNReal.toReal_ofReal (matching_score_density_nonneg u)

lemma matching_score_support :
    ∀ᵐ u ∂matchingUnitLaw, u.1 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
  change ∀ᵐ u ∂(volume.prod (Measure.count.prod Measure.count)).withDensity
    (fun u => ENNReal.ofReal (matching_score_density u)),
      u.1 ∈ Set.Icc (1/4 : ℝ) (3/4)
  apply (ae_withDensity_iff matching_score_density_measurable.ennreal_ofReal).2
  exact Filter.Eventually.of_forall (fun u hu => by
    by_contra hp
    exact hu (by simp only [matching_score_density, if_neg hp, ENNReal.ofReal_zero]))

lemma matching_score_summand_bound (u : ℝ × Bool × Bool)
    (hp : u.1 ∈ Set.Icc (1/4 : ℝ) (3/4)) : ‖matching_score_summand u‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  cases hd : u.2.1 <;> simp only [matching_score_summand, hd,
    Bool.false_eq_true, ite_false, ite_true] <;>
    constructor <;> linarith [hp.1, hp.2]

lemma matching_score_summand_memLp [IsProbabilityMeasure matchingUnitLaw] :
    MemLp matching_score_summand 2 matchingUnitLaw := by
  apply MemLp.of_bound matching_score_summand_measurable.aestronglyMeasurable (1 : ℝ)
  filter_upwards [matching_score_support] with u hu
  exact matching_score_summand_bound u hu

lemma matching_score_summand_mean [IsProbabilityMeasure matchingUnitLaw] :
    mean matchingUnitLaw matching_score_summand = 1/4 := by
  let ν : Measure (ℝ × Bool × Bool) := volume.prod (Measure.count.prod Measure.count)
  have hρ : Measurable (fun u => ENNReal.ofReal (matching_score_density u)) :=
    matching_score_density_measurable.ennreal_ofReal
  have hρtop : ∀ᵐ u ∂ν, ENNReal.ofReal (matching_score_density u) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hg : Integrable matching_score_summand matchingUnitLaw :=
    matching_score_summand_memLp.integrable one_le_two
  have hw : Integrable (fun u => matching_score_density u * matching_score_summand u) ν := by
    change Integrable matching_score_summand
      (ν.withDensity (fun u => ENNReal.ofReal (matching_score_density u))) at hg
    have hh := (integrable_withDensity_iff_integrable_smul' hρ hρtop).1 hg
    simpa only [matching_score_density_toReal, smul_eq_mul] using hh
  have hbits (p : ℝ) :
      (∫ b : Bool × Bool,
        matching_score_density (p,b) * matching_score_summand (p,b)
        ∂(Measure.count.prod Measure.count)) =
        if p ∈ Set.Icc (1/4 : ℝ) (3/4) then (1/2 : ℝ) else 0 := by
    have hfin : Integrable (fun b : Bool × Bool =>
        matching_score_density (p,b) * matching_score_summand (p,b))
        (Measure.count.prod Measure.count) :=
      (MemLp.of_discrete (p := 2)).integrable one_le_two
    rw [integral_prod _ hfin]
    simp only [integral_count, Fintype.sum_bool]
    by_cases hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)
    · simp only [matching_score_density, matching_score_summand, if_pos hp,
        Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
      ring
    · simp only [matching_score_density, matching_score_summand, if_neg hp,
        Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
      ring
  unfold mean
  change (∫ u, matching_score_summand u
    ∂ν.withDensity (fun u => ENNReal.ofReal (matching_score_density u))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hρ hρtop]
  simp only [matching_score_density_toReal, smul_eq_mul]
  rw [integral_prod _ hw]
  change (∫ p : ℝ, ∫ b : Bool × Bool,
    matching_score_density (p,b) * matching_score_summand (p,b)
    ∂(Measure.count.prod Measure.count)) = _
  simp_rw [hbits]
  rw [show (fun p : ℝ => if p ∈ Set.Icc (1/4 : ℝ) (3/4) then (1/2 : ℝ) else 0) =
    (Set.Icc (1/4 : ℝ) (3/4)).indicator (fun _ => (1/2 : ℝ)) from (by
      funext p
      simp only [Set.indicator])]
  rw [integral_indicator measurableSet_Icc]
  norm_num [integral_const, measureReal_def, Real.volume_Icc]

lemma matching_score_iid_transform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) :
    IID μ (fun i => matching_score_summand ∘ Z i) := by
  refine ⟨fun i => matching_score_summand_measurable.comp (hiid.1 i), ?_, ?_⟩
  · exact hiid.2.1.comp (fun _ => matching_score_summand)
      (fun _ => matching_score_summand_measurable)
  · exact fun i => (hiid.2.2 i).comp matching_score_summand_measurable

theorem matching_score_intercept_consistent_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (hlaw : μ.map (Z 0)=matchingUnitLaw) :
   CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4) := by
  letI : IsProbabilityMeasure matchingUnitLaw := by
    rw [← hlaw]
    infer_instance
  let U : ℕ → Ω → ℝ := fun i => matching_score_summand ∘ Z i
  have hU : IID μ U := matching_score_iid_transform μ Z hiid
  have h2map : MemLp matching_score_summand 2 (μ.map (Z 0)) := by
    rw [hlaw]
    exact matching_score_summand_memLp
  have h2 : MemLp (U 0) 2 μ := h2map.comp_of_map (hiid.1 0).aemeasurable
  have hmean : mean μ (U 0) = 1/4 := by
    calc
      mean μ (U 0) = mean (μ.map (Z 0)) matching_score_summand := by
        exact (integral_map (hiid.1 0).aemeasurable
          matching_score_summand_measurable.aestronglyMeasurable).symm
      _ = mean matchingUnitLaw matching_score_summand := by rw [hlaw]
      _ = 1/4 := matching_score_summand_mean
  have hmeanCP : CP μ (sampleMean U) (1/4) := by
    simpa only [hmean] using weak_law_finite_variance μ U hU h2
  have hc : ContinuousAt (clip (1/8) (3/8)) (1/4 : ℝ) := by
    unfold clip
    fun_prop
  have hclip := probability_convergence_continuous_at μ (sampleMean U)
    (1/4 : ℝ) (clip (1/8) (3/8)) hmeanCP hc
  have heq (n : ℕ) (ω : Ω) : estimatedMatchIntercept (firstSample Z n ω) =
      clip (1/8) (3/8) (sampleMean U n ω) := by
    unfold estimatedMatchIntercept firstSample sampleMean
    dsimp only [U, Function.comp_apply, matching_score_summand]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (if (Z i ω).2.1 then (1 : ℝ) else 0) - ((Z i ω).1-1/4)) n]
  have hfix : clip (1/8) (3/8) (1/4 : ℝ) = 1/4 := by norm_num [clip]
  rw [hfix] at hclip
  have hseq : (fun (n : ℕ) (ω : Ω) => estimatedMatchIntercept (firstSample Z n ω)) =
      (fun n ω => clip (1/8) (3/8) (sampleMean U n ω)) := by
    funext n ω
    exact heq n ω
  simpa only [hseq] using hclip

/-! Donor regrouping and independent finite-product signs. -/

lemma causal_matching_donor_membership {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (i j : Fin n) (h : nearestDonor p r i = some j) :
    r j = true := by
  unfold nearestDonor at h
  split_ifs at h with hex
  · have hj : Classical.choose hex = j := Option.some.inj h
    exact hj ▸ (Classical.choose_spec hex).1

lemma causal_matching_match_sum {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (x : Fin n → ℝ) (i : Fin n) :
    (match nearestDonor p r i with | some j => x j | none => 0) =
      ∑ j, if nearestDonor p r i = some j then x j else 0 := by
  cases hj : nearestDonor p r i with
  | none => simp
  | some j => simp

lemma causal_matching_donor_regrouping {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (x : Fin n → ℝ) :
    (∑ i, if r i then x i else
      match nearestDonor p r i with | some j => x j | none => 0) =
      ∑ j, donorReuseWeight p r j * x j := by
  have hrow (i : Fin n) :
      (if r i then x i else
        match nearestDonor p r i with | some j => x j | none => 0) =
      (if r i then x i else 0) +
        ∑ j, if r i = false ∧ nearestDonor p r i = some j then x j else 0 := by
    rw [causal_matching_match_sum]
    cases hr : r i <;> simp [hr]
  have hcol (j : Fin n) :
      (if r j then x j else 0) +
        (∑ i, if r i = false ∧ nearestDonor p r i = some j then x j else 0) =
      donorReuseWeight p r j * x j := by
    cases hr : r j with
    | false =>
        have hnone (i : Fin n) : nearestDonor p r i ≠ some j := by
          intro hij
          have hh := causal_matching_donor_membership p r i j hij
          simp [hr] at hh
        simp [hr, hnone, donorReuseWeight]
    | true =>
        rw [← Finset.sum_filter]
        simp [donorReuseWeight, hr, nsmul_eq_mul] <;> ring
  calc
    _ = ∑ i, ((if r i then x i else 0) +
        ∑ j, if r i = false ∧ nearestDonor p r i = some j then x j else 0) :=
      Finset.sum_congr rfl (fun i _ => hrow i)
    _ = (∑ j, if r j then x j else 0) +
        ∑ i, ∑ j, if r i = false ∧ nearestDonor p r i = some j then x j else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j, if r j then x j else 0) +
        ∑ j, ∑ i, if r i = false ∧ nearestDonor p r i = some j then x j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j, ((if r j then x j else 0) +
        ∑ i, if r i = false ∧ nearestDonor p r i = some j then x j else 0) := by
      rw [Finset.sum_add_distrib]
    _ = _ := Finset.sum_congr rfl (fun j _ => hcol j)

lemma causal_matching_linear_identity {n : ℕ} (p : Fin n → ℝ)
    (d e : Fin n → Bool) :
    causalMatch (fun j => (p j,d j,e j)) =
      -(∑ j, donorReuseWeight p (fun i => !(d i)) j * noise (e j))/(n : ℝ) := by
  have hrow (i : Fin n) :
      (if d i then
        match nearestDonor p (fun j => !(d j)) i with
        | some j => noise (e j) | none => 0
      else noise (e i)) =
      (if !(d i) then noise (e i) else
        match nearestDonor p (fun j => !(d j)) i with
        | some j => noise (e j) | none => 0) := by
    cases d i <;> rfl
  unfold causalMatch
  change -(∑ i, if d i then
    match nearestDonor p (fun j => !(d j)) i with
    | some j => noise (e j) | none => 0
    else noise (e i))/(n : ℝ) = _
  simp_rw [hrow]
  rw [causal_matching_donor_regrouping]

def causal_matching_sign_measure : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac true + (1/2 : ℝ≥0∞) • Measure.dirac false

lemma causal_matching_sign_probability : IsProbabilityMeasure causal_matching_sign_measure := by
  constructor
  simp [causal_matching_sign_measure, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma causal_matching_sign_integral (f : Bool → ℝ) :
    (∫ b, f b ∂causal_matching_sign_measure) = (f true + f false)/2 := by
  have ht : Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac true) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hf : Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac false) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  unfold causal_matching_sign_measure
  rw [integral_add_measure ht hf, integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac, smul_eq_mul]
  norm_num <;> ring

lemma causal_matching_sign_mean :
    (∫ b, noise b ∂causal_matching_sign_measure) = 0 := by
  rw [causal_matching_sign_integral]
  norm_num [noise]

lemma causal_matching_sign_variance : variance noise causal_matching_sign_measure = 1 := by
  letI : IsProbabilityMeasure causal_matching_sign_measure := causal_matching_sign_probability
  rw [variance_eq_sub (MemLp.of_discrete : MemLp noise 2 causal_matching_sign_measure)]
  change (∫ b, (noise b)^2 ∂causal_matching_sign_measure) -
    (∫ b, noise b ∂causal_matching_sign_measure)^2 = 1
  rw [causal_matching_sign_mean, causal_matching_sign_integral]
  norm_num [noise]

lemma causal_matching_sign_product_probability (n : ℕ) :
    IsProbabilityMeasure (signProductLaw n) := by
  letI : IsProbabilityMeasure causal_matching_sign_measure := causal_matching_sign_probability
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => causal_matching_sign_measure))
  infer_instance

lemma causal_matching_sign_linear_moments {n : ℕ} (w : Fin n → ℝ) (c : ℝ) :
    mean (signProductLaw n) (fun e => c * ∑ j, w j * noise (e j)) = 0 ∧
    var (signProductLaw n) (fun e => c * ∑ j, w j * noise (e j)) =
      c^2 * ∑ j, (w j)^2 := by
  letI : IsProbabilityMeasure causal_matching_sign_measure := causal_matching_sign_probability
  letI : IsProbabilityMeasure (signProductLaw n) := causal_matching_sign_product_probability n
  have h2 (j : Fin n) :
      MemLp (fun b => w j * noise b) 2 causal_matching_sign_measure := MemLp.of_discrete
  have hi (j : Fin n) : Integrable (fun e : Fin n → Bool => w j * noise (e j))
      (signProductLaw n) :=
    (MemLp.of_discrete (p := 2)).integrable one_le_two
  have hmean (j : Fin n) :
      (∫ e : Fin n → Bool, w j * noise (e j) ∂signProductLaw n) = 0 := by
    change (∫ e : Fin n → Bool, w j * noise (e j)
      ∂Measure.pi (fun _ : Fin n => causal_matching_sign_measure)) = 0
    rw [integral_comp_eval (μ := fun _ : Fin n => causal_matching_sign_measure) (i := j)
      (f := fun b : Bool => w j * noise b) (h2 j).aestronglyMeasurable, integral_const_mul,
      causal_matching_sign_mean, mul_zero]
  constructor
  · unfold mean
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hi j)]
    simp only [hmean, Finset.sum_const_zero, mul_zero]
  · unfold var
    rw [variance_const_mul]
    have hv : variance (fun e : Fin n → Bool => ∑ j, w j * noise (e j))
        (signProductLaw n) = ∑ j, (w j)^2 := by
      change variance (fun e : Fin n → Bool => ∑ j, w j * noise (e j))
        (Measure.pi (fun _ : Fin n => causal_matching_sign_measure)) = _
      have hpi := variance_sum_pi h2
      have hs : (fun e : Fin n → Bool => ∑ j, w j * noise (e j)) =
          ∑ j : Fin n, (fun e : Fin n → Bool => w j * noise (e j)) := by
        funext e
        simp only [Finset.sum_apply]
      rw [hs, hpi]
      apply Finset.sum_congr rfl
      intro j _
      rw [variance_const_mul, causal_matching_sign_variance, mul_one]
    rw [hv]

theorem causal_matching_conditional_reuse_variance_proof {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (d : Fin n → Bool) :
   (∀ e : Fin n → Bool,causalMatch (fun j => (p j,d j,e j))=
     -(∑ j,donorReuseWeight p (fun i => !(d i)) j*noise (e j))/(n : ℝ)) ∧
   IsProbabilityMeasure (signProductLaw n) ∧
   mean (signProductLaw n) (fun e => causalMatch (fun j => (p j,d j,e j)))=0 ∧
   var (signProductLaw n) (fun e => causalMatch (fun j => (p j,d j,e j)))=
     (∑ j,(donorReuseWeight p (fun i => !(d i)) j)^2)/(n : ℝ)^2 := by
  have hlin := causal_matching_linear_identity p d
  let w : Fin n → ℝ := donorReuseWeight p (fun i => !(d i))
  let c : ℝ := -(n : ℝ)⁻¹
  have hfun : (fun e : Fin n → Bool => causalMatch (fun j => (p j,d j,e j))) =
      (fun e : Fin n → Bool => c * ∑ j, w j * noise (e j)) := by
    funext e
    rw [hlin e]
    dsimp only [c, w]
    simp only [div_eq_mul_inv, neg_mul]
    ring
  have hm := causal_matching_sign_linear_moments w c
  refine ⟨hlin, causal_matching_sign_product_probability n, ?_, ?_⟩
  · rw [hfun]
    exact hm.1
  · rw [hfun, hm.2]
    dsimp only [c, w]
    simp only [neg_sq, inv_pow, div_eq_mul_inv]
    ring

end
end AronowAudit.P001.Wave1
