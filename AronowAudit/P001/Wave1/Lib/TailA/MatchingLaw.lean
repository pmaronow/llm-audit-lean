import AronowAudit.P001.Wave1.Lib.TailA.FiniteBootstrap
import AronowAudit.P001.Wave1.Gap.GP0011B2
import AronowAudit.P001.Wave1.Gap.GP0011B3
import AronowAudit.P001.Wave1.Gap.GP0012B1
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Group.Measure

/-! The finite matching experiment, its measurable statistics, and sign disintegration.
The classical donor selector factors through finitely many Boolean comparisons.  This
also handles tied bootstrap copies without assigning them independent outcome signs. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace AronowAudit.P001.TailA

universe u
local instance instDecidableMatchingLaw (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

instance instMeasurableMatchingDonorOption (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤
instance instDiscreteMatchingDonorOption (n : ℕ) : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ => trivial⟩

def MatchProduct (n : ℕ) : Measure (Fin n → MatchUnit) :=
  Measure.pi (fun _ => matchingUnitLaw)

def W {n : ℕ} (z : Fin n → MatchUnit) (j : Fin n) : ℝ :=
  donorReuseWeight (fun i => (z i).1) (fun i => (z i).2.1) j

def U {n : ℕ} (z : Fin n → MatchUnit) (a : Fin n → Fin n) (j : Fin n) : ℝ :=
  bootstrapOriginalReuse (fun i => (z i).1) (fun i => (z i).2.1) a j

def pin (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit) : Fin (n+1) → MatchUnit :=
  Fin.cases (p,true,false) z

/-- Finite comparison data suffice for the original classical choice, including ties. -/
def matchingDonorChoice {n : ℕ} (r : Fin n → Bool)
    (c : Fin n → Fin n → Bool) : Option (Fin n) :=
  if h : ∃ j, r j = true ∧ ∀ k, r k = true → c j k = true then
    some (Classical.choose h) else none

theorem matching_donor_choice_eq {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (i : Fin n) :
    matchingDonorChoice r (fun j k => decide (|p j-p i| ≤ |p k-p i|)) =
      nearestDonor p r i := by
  simp only [matchingDonorChoice, decide_eq_true_eq, nearestDonor]

theorem matching_nearest_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun x : (Fin n → ℝ) × (Fin n → Bool) => nearestDonor x.1 x.2 i) := by
  have hc : Measurable (fun x : (Fin n → ℝ) × (Fin n → Bool) =>
      fun j k => decide (|x.1 j-x.1 i| ≤ |x.1 k-x.1 i|)) := by
    apply measurable_pi_lambda
    intro j
    apply measurable_pi_lambda
    intro k
    apply measurable_to_bool
    have hd (l : Fin n) : Measurable (fun x : (Fin n → ℝ) × (Fin n → Bool) =>
        |x.1 l-x.1 i|) := by fun_prop
    change MeasurableSet {x : (Fin n → ℝ) × (Fin n → Bool) | decide (|x.1 j-x.1 i| ≤ |x.1 k-x.1 i|) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le (hd j) (hd k))
  have hchoice : Measurable (fun y : (Fin n → Bool) × (Fin n → Fin n → Bool) =>
      matchingDonorChoice y.1 y.2) := measurable_of_finite _
  simpa only [Function.comp_def, matching_donor_choice_eq] using
    hchoice.comp (measurable_snd.prodMk hc)

theorem matching_weight_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun x : (Fin n → ℝ) × (Fin n → Bool) => donorReuseWeight x.1 x.2 j) := by
  have hsum : (fun x : (Fin n → ℝ) × (Fin n → Bool) =>
      ((Finset.univ.filter (fun i => x.2 i = false ∧
        nearestDonor x.1 x.2 i = some j)).card : ℝ)) =
      (fun x => ∑ i, if x.2 i = false ∧ nearestDonor x.1 x.2 i = some j
        then (1 : ℝ) else 0) := by
    funext x
    simp only [Finset.sum_boole]
  unfold donorReuseWeight
  apply Measurable.ite (measurableSet_eq_fun
    ((measurable_pi_apply j).comp measurable_snd) measurable_const)
  · apply measurable_const.add
    rw [hsum]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite ((measurableSet_eq_fun
      ((measurable_pi_apply i).comp measurable_snd) measurable_const).inter
        (measurableSet_eq_fun (matching_nearest_measurable i) measurable_const))
      measurable_const measurable_const
  · exact measurable_const

theorem matching_W_measurable {n : ℕ} (j : Fin n) : Measurable (fun z => @W n z j) := by
  exact (matching_weight_measurable j).comp
    ((Measurable.of_eval (fun i => (measurable_pi_apply i).fst)).prodMk
      (Measurable.of_eval (fun i => (measurable_pi_apply i).snd.fst)))

theorem matching_resample_measurable {n : ℕ} (a : Fin n → Fin n) :
    Measurable (fun z : Fin n → MatchUnit => resample z a) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (a i))

theorem matching_U_measurable {n : ℕ} (a : Fin n → Fin n) (j : Fin n) :
    Measurable (fun z => @U n z a j) := by
  unfold U bootstrapOriginalReuse
  apply Finset.measurable_sum
  intro i _
  by_cases hi : a i = j
  · simpa only [hi, ite_true, W, resample, Function.comp_def] using
      (matching_W_measurable i).comp (matching_resample_measurable a)
  · simpa only [hi, ite_false] using (measurable_const : Measurable
      (fun _ : Fin n → MatchUnit => (0 : ℝ)))

theorem matching_pin_measurable (n : ℕ) :
    Measurable (fun x : ℝ × (Fin n → MatchUnit) => pin n x.1 x.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst.prodMk (measurable_const.prodMk measurable_const)
  · exact (measurable_pi_apply j).comp measurable_snd

theorem matching_hotDeck_measurable (n : ℕ) : Measurable (@hotDeck n) := by
  have hlin (z : Fin n → MatchUnit) (hn : 0 < n) :
      hotDeck z = 50 + (∑ j, W z j * noise (z j).2.2) / (n : ℝ) := by
    have h := Wave1.t14_weight_regrouping hn (fun i => (z i).1)
      (fun i => (z i).2.1) (fun i => (z i).2.2)
    change hotDeck z - 50 = _ at h
    change hotDeck z - 50 = (∑ j, W z j * noise (z j).2.2) / (n : ℝ) at h
    linarith
  by_cases hn : 0 < n
  · rw [show (@hotDeck n) = (fun z => 50 + (∑ j, W z j * noise (z j).2.2) / (n : ℝ)) from funext (fun z => hlin z hn)]
    apply measurable_const.add
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro j _
    exact (matching_W_measurable j).mul
      ((measurable_of_finite noise).comp (measurable_pi_apply j).snd.snd)
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have heq : (@hotDeck 0) = fun _ => (50 : ℝ) := by
      funext z
      simp [hotDeck]
    rw [heq]
    exact measurable_const

theorem matching_causalMatch_measurable (n : ℕ) : Measurable (@causalMatch n) := by
  have hlin (z : Fin n → MatchUnit) :
      causalMatch z = -(∑ j, donorReuseWeight (fun i => (z i).1)
        (fun i => !(z i).2.1) j * noise (z j).2.2) / (n : ℝ) :=
    Wave1.causal_matching_linear_identity _ _ _
  rw [show (@causalMatch n) = (fun z => -(∑ j, donorReuseWeight (fun i => (z i).1)
    (fun i => !(z i).2.1) j * noise (z j).2.2) / (n : ℝ)) from funext hlin]
  apply Measurable.div_const
  apply Measurable.neg
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · exact (matching_weight_measurable j).comp
      ((Measurable.of_eval (fun i => ((measurable_pi_apply i) : Measurable (fun z : Fin n → MatchUnit => z i)).fst)).prodMk
        (Measurable.of_eval (fun i =>
          (measurable_of_finite Bool.not).comp (measurable_pi_apply i).snd.fst)))
  · exact (measurable_of_finite noise).comp (measurable_pi_apply j).snd.snd

theorem matching_density_bit_sum (p : ℝ) :
    (∫⁻ b : Bool × Bool, ENNReal.ofReal (Wave1.matching_score_density (p,b))
      ∂(Measure.count.prod Measure.count)) =
        if p ∈ Set.Icc (1/4 : ℝ) (3/4) then 2 else 0 := by
  rw [lintegral_prod _ (Measurable.of_discrete.aemeasurable)]
  simp only [lintegral_count, tsum_fintype, Fintype.sum_bool]
  by_cases hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)
  · have hp0 : 0 ≤ p := by linarith [hp.1]
    have hq0 : 0 ≤ 1-p := by linarith [hp.2]
    simp only [Wave1.matching_score_density, hp, ite_true, Bool.false_eq_true, ite_false]
    rw [← ENNReal.ofReal_add hp0 hp0, ← ENNReal.ofReal_add hq0 hq0,
      ← ENNReal.ofReal_add (add_nonneg hp0 hp0) (add_nonneg hq0 hq0)]
    norm_num [show p+p+(1-p+(1-p)) = 2 by ring]
  · simp only [Wave1.matching_score_density, if_neg hp, ENNReal.ofReal_zero, add_zero]

theorem matching_law_probability : IsProbabilityMeasure matchingUnitLaw := by
  constructor
  change ((volume.prod (Measure.count.prod Measure.count)).withDensity
    (fun u => ENNReal.ofReal (Wave1.matching_score_density u))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_prod _ Wave1.matching_score_density_measurable.ennreal_ofReal.aemeasurable]
  simp_rw [matching_density_bit_sum]
  rw [show (fun p : ℝ => if p ∈ Set.Icc (1/4 : ℝ) (3/4) then (2 : ℝ≥0∞) else 0) =
    (Set.Icc (1/4 : ℝ) (3/4)).indicator (fun _ => 2) from (by
      funext p; by_cases hp : p ∈ Set.Icc (1/4 : ℝ) (3/4) <;> simp only [Set.indicator, hp, ite_true, ite_false])]
  rw [lintegral_indicator measurableSet_Icc]
  norm_num [Real.volume_Icc]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

instance instProbabilityMatchingUnitLaw : IsProbabilityMeasure matchingUnitLaw :=
  matching_law_probability

instance instProbabilityMatchProduct (n : ℕ) : IsProbabilityMeasure (MatchProduct n) := by
  unfold MatchProduct
  infer_instance

theorem matching_finite_law {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → MatchUnit)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = matchingUnitLaw) (n : ℕ) :
    μ.map (firstSample Z n) = MatchProduct n := by
  have hind : iIndepFun (fun i : Fin n => Z i) μ :=
    hiid.2.1.precomp Fin.val_injective
  change μ.map (fun (ω : Ω) (i : Fin n) => Z i ω) = Measure.pi (fun _ => matchingUnitLaw)
  rw [hind.map_fun_eq_pi_map (fun (i : Fin n) => (hiid.1 i).aemeasurable)]
  congr 1
  funext i
  exact (hiid.2.2 i).map_eq.trans hlaw

/-- Transport a density through a measure-preserving map. -/
theorem matching_weighted_transport {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    (g : B → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = ν.withDensity g := by
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)
  rw [lintegral_map hφ hf.measurable]
  calc
    _ = ∫⁻ a, g (f a) * φ (f a) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ (hg.comp hf.measurable)
        (show Measurable (fun a => φ (f a)) from hφ.comp hf.measurable)
    _ = ∫⁻ b, g b * φ b ∂ν := hf.lintegral_comp (hg.mul hφ)
    _ = _ := (lintegral_withDensity_eq_lintegral_mul ν hg hφ).symm

abbrev MatchingDesign := ℝ × Bool

/-- Score and response, with density `2 p` or `2 (1-p)` on the score interval. -/
def MatchingDesignLaw : Measure MatchingDesign :=
  (volume.prod Measure.count).withDensity
    (fun d => 2 * ENNReal.ofReal (Wave1.matching_score_density (d.1,d.2,false)))

def MatchingDesignProduct (n : ℕ) : Measure (Fin n → MatchingDesign) :=
  Measure.pi (fun _ => MatchingDesignLaw)

def matchingFairSign : Measure Bool := Wave1.t14_signLaw

instance instProbabilityMatchingFairSign : IsProbabilityMeasure matchingFairSign :=
  Wave1.t14_signLaw_probability

instance instProbabilityMatchingSigns (n : ℕ) : IsProbabilityMeasure (signProductLaw n) :=
  Wave1.t14_product_probability n

theorem matching_fair_sign_count : matchingFairSign = (1/2 : ℝ≥0∞) • Measure.count := by
  apply Measure.ext_of_singleton
  intro b
  cases b <;> norm_num [matchingFairSign, Wave1.t14_signLaw,
    Measure.add_apply, Measure.smul_apply, Measure.count_singleton]

theorem matching_design_density_measurable :
    Measurable (fun d : MatchingDesign =>
      2 * ENNReal.ofReal (Wave1.matching_score_density (d.1,d.2,false))) := by
  exact measurable_const.mul ((Wave1.matching_score_density_measurable.comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).ennreal_ofReal)

theorem matching_unit_factorization :
    (MatchingDesignLaw.prod matchingFairSign).map
      (MeasurableEquiv.prodAssoc : (MatchingDesign × Bool) ≃ᵐ MatchUnit) =
        matchingUnitLaw := by
  rw [matching_fair_sign_count, Measure.prod_smul_right, MatchingDesignLaw,
    prod_withDensity_left matching_design_density_measurable,
    ← withDensity_smul' (1/2 : ℝ≥0∞) _ (by norm_num)]
  have hd : (fun z : MatchingDesign × Bool =>
      (1/2 : ℝ≥0∞) • (2 * ENNReal.ofReal
        (Wave1.matching_score_density (z.1.1,z.1.2,false)))) =
      (fun z : MatchingDesign × Bool => ENNReal.ofReal
        (Wave1.matching_score_density (MeasurableEquiv.prodAssoc z))) := by
    funext z
    simp only [smul_eq_mul, ← mul_assoc]
    have htwo0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have htwoTop : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel htwo0 htwoTop
    simpa only [one_div, htwo, one_mul] using
      (show ENNReal.ofReal (Wave1.matching_score_density (z.1.1,z.1.2,false)) =
        ENNReal.ofReal (Wave1.matching_score_density (MeasurableEquiv.prodAssoc z)) from rfl)
  change (((volume.prod Measure.count).prod Measure.count).withDensity
    (fun z : MatchingDesign × Bool => (1/2 : ℝ≥0∞) •
      (2 * ENNReal.ofReal (Wave1.matching_score_density (z.1.1,z.1.2,false))))).map
        MeasurableEquiv.prodAssoc = _
  rw [hd]
  exact matching_weighted_transport
    (measurePreserving_prodAssoc volume Measure.count Measure.count)
    _ Wave1.matching_score_density_measurable.ennreal_ofReal

instance instProbabilityMatchingDesignLaw : IsProbabilityMeasure MatchingDesignLaw := by
  constructor
  have h := congrArg (fun ν : Measure MatchUnit => ν Set.univ) matching_unit_factorization
  rw [Measure.map_apply MeasurableEquiv.prodAssoc.measurable MeasurableSet.univ,
    Set.preimage_univ] at h
  calc
    MatchingDesignLaw Set.univ = (MatchingDesignLaw.prod matchingFairSign) Set.univ := by
      rw [Measure.prod_apply MeasurableSet.univ]
      change MatchingDesignLaw Set.univ = ∫⁻ _ : MatchingDesign, matchingFairSign Set.univ ∂MatchingDesignLaw
      simp only [measure_univ, lintegral_one]
    _ = 1 := h.trans (measure_univ)

instance instProbabilityMatchingDesignProduct (n : ℕ) :
    IsProbabilityMeasure (MatchingDesignProduct n) := by
  unfold MatchingDesignProduct
  infer_instance

/-- Reattach one original sign to each original label. -/
def matchingAssemble {n : ℕ} (d : Fin n → MatchingDesign)
    (e : Fin n → Bool) : Fin n → MatchUnit := fun i => ((d i).1,(d i).2,e i)

theorem matching_assemble_measurable (n : ℕ) :
    Measurable (fun x : (Fin n → MatchingDesign) × (Fin n → Bool) =>
      matchingAssemble x.1 x.2) := by
  fun_prop [matchingAssemble]

theorem matching_sign_factorization (n : ℕ) :
    MeasurePreserving
      (fun x : (Fin n → MatchingDesign) × (Fin n → Bool) => matchingAssemble x.1 x.2)
      ((MatchingDesignProduct n).prod (signProductLaw n)) (MatchProduct n) := by
  have hunit : MeasurePreserving
      (MeasurableEquiv.prodAssoc : MatchingDesign × Bool ≃ᵐ MatchUnit)
      (MatchingDesignLaw.prod matchingFairSign) matchingUnitLaw :=
    ⟨MeasurableEquiv.prodAssoc.measurable, matching_unit_factorization⟩
  have hpi := measurePreserving_pi (fun _ : Fin n => MatchingDesignLaw.prod matchingFairSign)
    (fun _ => matchingUnitLaw) (fun _ => hunit)
  have hsplit := measurePreserving_arrowProdEquivProdArrow MatchingDesign Bool (Fin n)
    (fun _ => MatchingDesignLaw) (fun _ => matchingFairSign)
  exact hpi.comp (hsplit.symm (MeasurableEquiv.arrowProdEquivProdArrow MatchingDesign Bool (Fin n)))

theorem matching_noise_norm (b : Bool) : ‖noise b‖ = 1 := by
  cases b <;> norm_num [noise]

theorem matching_hotDeck_bound {n : ℕ} (z : Fin n → MatchUnit) : ‖hotDeck z‖ ≤ 51 := by
  by_cases hn : n = 0
  · subst n
    norm_num [hotDeck]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hb (b : Bool) : ‖(50 : ℝ)+noise b‖ ≤ 51 := by
    cases b <;> norm_num [noise]
  unfold hotDeck
  split_ifs
  · rw [norm_div, Real.norm_of_nonneg hnpos.le]
    apply (div_le_iff₀ hnpos).2
    calc
      _ ≤ ∑ i : Fin n, ‖if (z i).2.1 then 50+noise (z i).2.2 else
          match nearestDonor (fun j => (z j).1) (fun j => (z j).2.1) i with
          | some j => 50+noise (z j).2.2 | none => 50‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin n, (51 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact hb _
        · cases nearestDonor (fun j => (z j).1) (fun j => (z j).2.1) i
          · norm_num
          · exact hb _
      _ = 51 * n := by simp [nsmul_eq_mul, mul_comm]
  · norm_num

theorem matching_causalMatch_bound {n : ℕ} (z : Fin n → MatchUnit) :
    ‖causalMatch z‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [causalMatch]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold causalMatch
  rw [norm_div, norm_neg, Real.norm_of_nonneg hnpos.le]
  apply (div_le_iff₀ hnpos).2
  calc
    _ ≤ ∑ i : Fin n, ‖if (z i).2.1 then
        match nearestDonor (fun j => (z j).1) (fun j => !(z j).2.1) i with
        | some j => noise (z j).2.2 | none => 0
      else noise (z i).2.2‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · cases nearestDonor (fun j => (z j).1) (fun j => !(z j).2.1) i <;>
          simp only [norm_zero, zero_le_one, matching_noise_norm, le_refl]
      · exact (matching_noise_norm _).le
    _ = 1 * n := by simp

theorem matching_hotDeck_memLp {n : ℕ} (μ : Measure (Fin n → MatchUnit))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) : MemLp hotDeck p μ := by
  exact MemLp.of_bound (matching_hotDeck_measurable n).aestronglyMeasurable 51
    (ae_of_all _ matching_hotDeck_bound)

theorem matching_causalMatch_memLp {n : ℕ} (μ : Measure (Fin n → MatchUnit))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) : MemLp causalMatch p μ := by
  exact MemLp.of_bound (matching_causalMatch_measurable n).aestronglyMeasurable 1
    (ae_of_all _ matching_causalMatch_bound)

theorem matching_weight_bounds {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) :
    0 ≤ donorReuseWeight p r j ∧ donorReuseWeight p r j ≤ n+1 := by
  have hc : ((Finset.univ.filter (fun i => r i = false ∧
      nearestDonor p r i = some j)).card : ℝ) ≤ n := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i => r i = false ∧ nearestDonor p r i = some j)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  unfold donorReuseWeight
  split_ifs
  · constructor
    · positivity
    · linarith
  · exact ⟨le_rfl, by positivity⟩

theorem matching_W_memLp {n : ℕ} (μ : Measure (Fin n → MatchUnit)) [IsFiniteMeasure μ]
    (j : Fin n) (p : ℝ≥0∞) : MemLp (fun z => W z j) p μ := by
  apply MemLp.of_bound (matching_W_measurable j).aestronglyMeasurable (n+1 : ℝ)
  apply ae_of_all
  intro z
  obtain ⟨h0,h1⟩ := matching_weight_bounds (fun i => (z i).1) (fun i => (z i).2.1) j
  simpa only [W, Real.norm_eq_abs, abs_of_nonneg h0] using h1

theorem matching_U_memLp {n : ℕ} (μ : Measure (Fin n → MatchUnit)) [IsFiniteMeasure μ]
    (a : Fin n → Fin n) (j : Fin n) (p : ℝ≥0∞) : MemLp (fun z => U z a j) p μ := by
  unfold U bootstrapOriginalReuse
  apply memLp_finsetSum
  intro i _
  by_cases hi : a i = j
  · simp only [hi, ite_true]
    apply MemLp.of_bound
      ((matching_W_measurable i).comp (matching_resample_measurable a)).aestronglyMeasurable
      (n+1 : ℝ)
    apply ae_of_all
    intro z
    obtain ⟨h0,h1⟩ := matching_weight_bounds
      ((fun i => (z i).1) ∘ a) ((fun i => (z i).2.1) ∘ a) i
    change ‖donorReuseWeight ((fun i => (z i).1) ∘ a) ((fun i => (z i).2.1) ∘ a) i‖ ≤ n+1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  · simp only [hi, ite_false]
    exact MemLp.zero

/-- Pinned expectations are Borel functions of the pinned score. -/
theorem matching_pinned_integral_measurable (n : ℕ)
    {f : (Fin (n+1) → MatchUnit) → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ => mean (MatchProduct n) (fun z => f (pin n p z))) := by
  exact ((hf.comp (matching_pin_measurable n)).stronglyMeasurable.integral_prod_right').measurable


theorem matching_bootMean_measurable {n : ℕ} {T : (Fin n → MatchUnit) → ℝ}
    (hT : Measurable T) : Measurable (bootMean T) := by
  unfold bootMean
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun a _ => hT.comp (matching_resample_measurable a))

theorem matching_bootVar_measurable {n : ℕ} {T : (Fin n → MatchUnit) → ℝ}
    (hT : Measurable T) : Measurable (bootVar T) := by
  unfold bootVar
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun a _ =>
    ((hT.comp (matching_resample_measurable a)).sub
      (matching_bootMean_measurable hT)).pow_const 2)

theorem matching_expectation {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → MatchUnit)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = matchingUnitLaw) (n : ℕ)
    {f : (Fin n → MatchUnit) → ℝ} (hf : Measurable f) :
    mean μ (fun ω => f (firstSample Z n ω)) = mean (MatchProduct n) f := by
  unfold mean
  rw [← matching_finite_law μ Z hiid hlaw n]
  have hm : Measurable (firstSample Z n) := Measurable.of_eval (fun (i : Fin n) => hiid.1 i)
  exact (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm


/-- Ordinary Fubini for the explicit design/sign product experiment. -/
theorem matching_sign_expectation {n : ℕ} {f : (Fin n → MatchUnit) → ℝ}
    (hf : Measurable f) (hi : Integrable f (MatchProduct n)) :
    mean (MatchProduct n) f = mean (MatchingDesignProduct n)
      (fun d => mean (signProductLaw n) (fun e => f (matchingAssemble d e))) := by
  unfold mean
  rw [← (matching_sign_factorization n).map_eq,
    integral_map (matching_assemble_measurable n).aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ ((matching_sign_factorization n).integrable_comp_of_integrable hi)

theorem matching_product_unbiased (n : ℕ) (hn : 0 < n) :
    mean (MatchProduct n) hotDeck = 50 ∧ mean (MatchProduct n) causalMatch = 0 := by
  have hh (d : Fin n → MatchingDesign) :
      mean (signProductLaw n) (fun e => hotDeck (matchingAssemble d e)) = 50 :=
    (Wave1.hot_deck_conditional_reuse_variance_proof hn
      (fun i => (d i).1) (fun i => (d i).2)).2.2.1
  have hc (d : Fin n → MatchingDesign) :
      mean (signProductLaw n) (fun e => causalMatch (matchingAssemble d e)) = 0 :=
    (Wave1.causal_matching_conditional_reuse_variance_proof hn
      (fun i => (d i).1) (fun i => (d i).2)).2.2.1
  constructor
  · rw [matching_sign_expectation (matching_hotDeck_measurable n)
      ((matching_hotDeck_memLp (MatchProduct n) 1).integrable le_rfl)]
    simp_rw [hh]
    simp only [mean, integral_const, probReal_univ, smul_eq_mul, one_mul]
  · rw [matching_sign_expectation (matching_causalMatch_measurable n)
      ((matching_causalMatch_memLp (MatchProduct n) 1).integrable le_rfl)]
    simp_rw [hc]
    simp only [mean, integral_zero]

theorem matching_unbiased {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → MatchUnit)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = matchingUnitLaw) (n : ℕ) (hn : 0 < n) :
    mean μ (fun ω => hotDeck (firstSample Z n ω)) = 50 ∧
    mean μ (fun ω => causalMatch (firstSample Z n ω)) = 0 := by
  rw [matching_expectation μ Z hiid hlaw n (matching_hotDeck_measurable n),
    matching_expectation μ Z hiid hlaw n (matching_causalMatch_measurable n)]
  exact matching_product_unbiased n hn

/-- Simultaneously reflect the propensity and interchange response/treatment status. -/
def matchingReflection (u : MatchUnit) : MatchUnit := (1-u.1, !u.2.1, u.2.2)

def matchingReflectSample {n : ℕ} (z : Fin n → MatchUnit) : Fin n → MatchUnit :=
  fun i => matchingReflection (z i)


theorem matching_reflection_measurable : Measurable matchingReflection := by
  fun_prop [matchingReflection]

theorem matching_density_reflection (u : MatchUnit) :
    Wave1.matching_score_density (matchingReflection u) = Wave1.matching_score_density u := by
  have hs : 1-u.1 ∈ Set.Icc (1/4 : ℝ) (3/4) ↔ u.1 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold Wave1.matching_score_density matchingReflection
  dsimp only
  simp only [hs]
  by_cases hp : u.1 ∈ Set.Icc (1/4 : ℝ) (3/4)
  · simp only [if_pos hp]
    cases u.2.1 <;> simp <;> ring
  · simp only [if_neg hp]

theorem matching_reflection_law :
    MeasurePreserving matchingReflection matchingUnitLaw matchingUnitLaw := by
  have hnot : MeasurePreserving Bool.not (Measure.count : Measure Bool) Measure.count := by
    refine ⟨measurable_of_finite _, ?_⟩
    apply Measure.ext_of_singleton
    intro b
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
    have hb : Bool.not ⁻¹' ({b} : Set Bool) = {!b} := by
      ext c
      cases b <;> cases c <;> simp
    rw [hb]
    simp
  have hid : MeasurePreserving (fun b : Bool => b) Measure.count Measure.count :=
    ⟨measurable_id, Measure.map_id⟩
  have hbase : MeasurePreserving matchingReflection
      (volume.prod (Measure.count.prod Measure.count))
      (volume.prod (Measure.count.prod Measure.count)) :=
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) 1).prod (hnot.prod hid)
  refine ⟨matching_reflection_measurable, ?_⟩
  have hρ : (fun u => ENNReal.ofReal (Wave1.matching_score_density u)) ∘ matchingReflection =
      (fun u => ENNReal.ofReal (Wave1.matching_score_density u)) := by
    funext u
    simp only [Function.comp_apply, matching_density_reflection]
  have ht := matching_weighted_transport hbase
    (fun u => ENNReal.ofReal (Wave1.matching_score_density u))
    Wave1.matching_score_density_measurable.ennreal_ofReal
  rw [hρ] at ht
  simpa only [matchingUnitLaw, Wave1.matching_score_density] using ht

theorem matching_product_reflection (n : ℕ) :
    MeasurePreserving (@matchingReflectSample n) (MatchProduct n) (MatchProduct n) :=
  measurePreserving_pi (fun _ : Fin n => matchingUnitLaw) (fun _ => matchingUnitLaw)
    (fun _ => matching_reflection_law)

theorem matching_reflected_distance (p q : ℝ) : |(1-p)-(1-q)| = |p-q| := by
  rw [show (1-p)-(1-q) = -(p-q) by ring, abs_neg]

theorem matching_reflected_donor {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (i : Fin n) :
    nearestDonor (fun j => 1-p j) r i = nearestDonor p r i := by
  simp only [nearestDonor, matching_reflected_distance]

theorem matching_reflected_weight {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) :
    donorReuseWeight (fun i => 1-p i) r j = donorReuseWeight p r j := by
  simp only [donorReuseWeight, matching_reflected_donor]

/-- Exact comparison equality preserves the fixed tie choice; donor-free samples are included. -/
theorem matching_reflection_statistic {n : ℕ} (z : Fin n → MatchUnit) :
    causalMatch z = -(hotDeck (matchingReflectSample z)-50) := by
  by_cases hn : n = 0
  · subst n
    simp [causalMatch, hotDeck]
  have hh := Wave1.t14_weight_regrouping (Nat.pos_of_ne_zero hn)
    (fun i => 1-(z i).1) (fun i => !(z i).2.1) (fun i => (z i).2.2)
  have hc := Wave1.causal_matching_linear_identity
    (fun i => (z i).1) (fun i => (z i).2.1) (fun i => (z i).2.2)
  simp only [matching_reflected_weight] at hh
  change hotDeck (matchingReflectSample z)-50 = _ at hh
  change causalMatch z = _ at hc
  rw [hh, hc]
  ring

theorem matching_reflection_resample {n : ℕ} (z : Fin n → MatchUnit) (a : Fin n → Fin n) :
    matchingReflectSample (resample z a) = resample (matchingReflectSample z) a := rfl

theorem matching_bootMean_reflection {n : ℕ} (z : Fin n → MatchUnit) :
    bootMean causalMatch z = -(bootMean hotDeck (matchingReflectSample z)-50) := by
  have hT (T : (Fin n → MatchUnit) → ℝ) (s : Fin n → MatchUnit) :
      bootMean T s = mean (UniformResampling n) (fun a => T (resample s a)) :=
    (uniform_resampling_mean n _).symm
  rw [hT causalMatch z, hT hotDeck (matchingReflectSample z)]
  unfold mean
  simp_rw [matching_reflection_statistic, matching_reflection_resample]
  rw [integral_neg, integral_sub Integrable.of_finite (integrable_const 50)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem matching_bootVar_reflection {n : ℕ} (z : Fin n → MatchUnit) :
    bootVar causalMatch z = bootVar hotDeck (matchingReflectSample z) := by
  unfold bootVar
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [matching_reflection_statistic, matching_reflection_resample, matching_bootMean_reflection]
  ring

theorem matching_bootMean_bound {n : ℕ} (T : (Fin n → MatchUnit) → ℝ)
    (C : ℝ) (hT : ∀ z, ‖T z‖ ≤ C) (z : Fin n → MatchUnit) : ‖bootMean T z‖ ≤ C := by
  rw [show bootMean T z = mean (UniformResampling n) (fun a => T (resample z a)) from
    (uniform_resampling_mean n _).symm]
  simpa only [mean, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := UniformResampling n) (ae_of_all _ (fun a => hT (resample z a))))

theorem matching_bootVar_bound {n : ℕ} (T : (Fin n → MatchUnit) → ℝ)
    (C : ℝ) (hT : ∀ z, ‖T z‖ ≤ C) (z : Fin n → MatchUnit) :
    ‖bootVar T z‖ ≤ (2*C)^2 := by
  rw [show bootVar T z = mean (UniformResampling n)
    (fun a => (T (resample z a)-bootMean T z)^2) from (uniform_resampling_mean n _).symm]
  have hbd (a : Fin n → Fin n) : ‖(T (resample z a)-bootMean T z)^2‖ ≤ (2*C)^2 := by
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ‖T (resample z a)‖ + ‖bootMean T z‖ := norm_sub_le _ _
      _ ≤ C+C := add_le_add (hT _) (matching_bootMean_bound T C hT z)
      _ = 2*C := by ring
  simpa only [mean, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := UniformResampling n) (ae_of_all _ hbd))

theorem matching_bootVar_memLp {n : ℕ} (μ : Measure (Fin n → MatchUnit)) [IsFiniteMeasure μ]
    {T : (Fin n → MatchUnit) → ℝ} (hT : Measurable T) (C : ℝ)
    (hb : ∀ z, ‖T z‖ ≤ C) (p : ℝ≥0∞) : MemLp (bootVar T) p μ :=
  MemLp.of_bound (matching_bootVar_measurable hT).aestronglyMeasurable ((2*C)^2)
    (ae_of_all _ (matching_bootVar_bound T C hb))

theorem matching_conditional_hotDeck_second {n : ℕ} (hn : 0 < n)
    (d : Fin n → MatchingDesign) :
    mean (signProductLaw n) (fun e => (hotDeck (matchingAssemble d e)-50)^2) =
      (∑ j, (donorReuseWeight (fun i => (d i).1) (fun i => (d i).2) j)^2)/(n : ℝ)^2 := by
  unfold mean matchingAssemble
  simp_rw [Wave1.t14_weight_regrouping hn, div_pow]
  rw [integral_div, Wave1.t14_weighted_second]

theorem matching_original_variance (n : ℕ) (hn : 0 < n) :
    var (MatchProduct n) hotDeck =
      (∑ j, mean (MatchProduct n) (fun z => (W z j)^2))/(n : ℝ)^2 := by
  let S : (Fin n → MatchUnit) → ℝ := fun z => ∑ j, (W z j)^2
  have hSm : Measurable S := Finset.measurable_sum _
    (fun j _ => (matching_W_measurable j).pow_const 2)
  have hSi : Integrable S (MatchProduct n) := integrable_finsetSum _
    (fun j _ => (matching_W_memLp (MatchProduct n) j 2).integrable_sq)
  have hinner (d : Fin n → MatchingDesign) :
      mean (signProductLaw n) (fun e => S (matchingAssemble d e)) =
        ∑ j, (donorReuseWeight (fun i => (d i).1) (fun i => (d i).2) j)^2 := by
    simp only [mean, S, W, matchingAssemble, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have heq : mean (MatchProduct n) (fun z => (hotDeck z-50)^2) =
      mean (MatchProduct n) S/(n : ℝ)^2 := by
    rw [matching_sign_expectation (f := fun z => (hotDeck z-50)^2)
      ((matching_hotDeck_measurable n).sub measurable_const |>.pow_const 2)
      (((matching_hotDeck_memLp (MatchProduct n) 2).sub (memLp_const 50)).integrable_sq),
      matching_sign_expectation hSm hSi]
    simp_rw [matching_conditional_hotDeck_second hn, hinner]
    exact integral_div _ _
  have hm : (∫ z, hotDeck z ∂MatchProduct n) = 50 := (matching_product_unbiased n hn).1
  unfold var
  rw [variance_eq_integral (matching_hotDeck_measurable n).aemeasurable, hm]
  change mean (MatchProduct n) (fun z => (hotDeck z-50)^2) = _
  rw [heq]
  congr 1
  exact integral_finsetSum _ (fun j _ => (matching_W_memLp (MatchProduct n) j 2).integrable_sq)

/-- The finite two-replica formula, integrated over the actual iid experiment.
Every copy of an original label uses that label's single original sign. -/
theorem matching_bootstrap_expectation (n : ℕ) (hn : 0 < n) :
    mean (MatchProduct n) (bootVar hotDeck) =
      (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n, ∑ j : Fin n,
        mean (MatchProduct n) (fun z => (U z a j-U z b j)^2)) /
          (2*(n : ℝ)^2*((n : ℝ)^n)^2) := by
  let S : (Fin n → MatchUnit) → ℝ := fun z =>
    ∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n, ∑ j : Fin n, (U z a j-U z b j)^2
  have hterm (a b : Fin n → Fin n) (j : Fin n) :
      Integrable (fun z => (U z a j-U z b j)^2) (MatchProduct n) :=
    ((matching_U_memLp (MatchProduct n) a j 2).sub
      (matching_U_memLp (MatchProduct n) b j 2)).integrable_sq
  have hSm : Measurable S := Finset.measurable_sum _ (fun a _ =>
    Finset.measurable_sum _ (fun b _ => Finset.measurable_sum _ (fun j _ =>
      ((matching_U_measurable a j).sub (matching_U_measurable b j)).pow_const 2)))
  have hSi : Integrable S (MatchProduct n) := integrable_finsetSum _ (fun a _ =>
    integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun j _ => hterm a b j)))
  have hinner (d : Fin n → MatchingDesign) :
      mean (signProductLaw n) (fun e => S (matchingAssemble d e)) =
        ∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n, ∑ j : Fin n,
          (bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j-
            bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) b j)^2 := by
    simp only [mean, S, U, matchingAssemble, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have heq : mean (MatchProduct n) (bootVar hotDeck) =
      mean (MatchProduct n) S/(2*(n : ℝ)^2*((n : ℝ)^n)^2) := by
    rw [matching_sign_expectation (matching_bootVar_measurable (matching_hotDeck_measurable n))
      ((matching_bootVar_memLp (MatchProduct n) (matching_hotDeck_measurable n) 51
        matching_hotDeck_bound 1).integrable le_rfl), matching_sign_expectation hSm hSi]
    have hcond (d : Fin n → MatchingDesign) :=
      Wave1.hot_deck_two_bootstrap_draw_reuse_identity_proof hn
        (fun i => (d i).1) (fun i => (d i).2)
    simp_rw [hinner]
    change (∫ d, _ ∂MatchingDesignProduct n) = _
    simp_rw [show ∀ d : Fin n → MatchingDesign,
      mean (signProductLaw n) (fun e => bootVar hotDeck (matchingAssemble d e)) = _
      from hcond]
    exact integral_div _ _
  rw [heq]
  congr 1
  unfold mean S
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => integrable_finsetSum _ (fun j _ => hterm a b j)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun j _ => hterm a b j))]
  apply Finset.sum_congr rfl
  intro b _
  exact integral_finsetSum _ (fun j _ => hterm a b j)

/-- An explicit iterated integral, without conditioning on a singleton score. -/
theorem matching_lintegral (f : MatchUnit → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, f u ∂matchingUnitLaw) =
      ∫⁻ p in Set.Icc (1/4 : ℝ) (3/4),
        ENNReal.ofReal p * (f (p,true,true)+f (p,true,false)) +
        ENNReal.ofReal (1-p) * (f (p,false,true)+f (p,false,false)) := by
  change (∫⁻ u, f u ∂(volume.prod (Measure.count.prod Measure.count)).withDensity
    (fun u => ENNReal.ofReal (Wave1.matching_score_density u))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _
    Wave1.matching_score_density_measurable.ennreal_ofReal hf,
    lintegral_prod _ (Wave1.matching_score_density_measurable.ennreal_ofReal.mul hf).aemeasurable,
    ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro p
  rw [lintegral_prod _ Measurable.of_discrete.aemeasurable]
  simp only [lintegral_count, tsum_fintype, Fintype.sum_bool, Pi.mul_apply]
  by_cases hp : p ∈ Set.Icc (1/4 : ℝ) (3/4)
  · simp only [Wave1.matching_score_density, if_pos hp, Set.indicator_of_mem hp,
      Bool.false_eq_true, ite_false, ite_true]
    rw [mul_add, mul_add]
  · simp only [Wave1.matching_score_density, if_neg hp, Set.indicator_of_notMem hp,
      ENNReal.ofReal_zero, zero_mul, add_zero]

def MatchingScoreLaw : Measure ℝ := (2 : ℝ≥0∞) • volume.restrict (Set.Icc (1/4 : ℝ) (3/4))

theorem matching_score_marginal :
    MeasurePreserving (fun u : MatchUnit => u.1) matchingUnitLaw MatchingScoreLaw := by
  refine ⟨measurable_fst, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst]
  rw [matching_lintegral (fun u : MatchUnit => f u.1) (hf.comp measurable_fst)]
  have heq : (∫⁻ p in Set.Icc (1/4 : ℝ) (3/4),
      ENNReal.ofReal p * (f p+f p) + ENNReal.ofReal (1-p) * (f p+f p)) =
      ∫⁻ p in Set.Icc (1/4 : ℝ) (3/4), (2 : ℝ≥0∞)*f p := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    have hp0 : 0 ≤ p := by linarith [hp.1]
    have hq0 : 0 ≤ 1-p := by linarith [hp.2]
    rw [← add_mul, ← ENNReal.ofReal_add hp0 hq0,
      show p+(1-p) = 1 by ring, ENNReal.ofReal_one, one_mul, two_mul]
  change (∫⁻ p in Set.Icc (1/4 : ℝ) (3/4),
      ENNReal.ofReal p * (f p+f p) + ENNReal.ofReal (1-p) * (f p+f p)) = _
  rw [heq, lintegral_const_mul _ hf]
  simp only [MatchingScoreLaw, lintegral_smul_measure, smul_eq_mul]

instance instProbabilityMatchingScoreLaw : IsProbabilityMeasure MatchingScoreLaw := by
  rw [← matching_score_marginal.map_eq]
  infer_instance

instance instNullSingletonMatchingScoreLaw : NullSingletonClass MatchingScoreLaw := by
  constructor
  intro x
  simp only [MatchingScoreLaw, Measure.smul_apply, measure_singleton, smul_zero]

theorem matching_score_product_marginal (n : ℕ) :
    MeasurePreserving (fun z : Fin n → MatchUnit => fun i => (z i).1)
      (MatchProduct n) (Measure.pi (fun _ : Fin n => MatchingScoreLaw)) :=
  measurePreserving_pi (fun _ : Fin n => matchingUnitLaw) (fun _ => MatchingScoreLaw)
    (fun _ => matching_score_marginal)

/-- A continuous score coordinate avoids any measurable function of the other coordinates. -/
theorem matching_score_avoid {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) (hupdate : ∀ z x, f (Function.update z j x) = f z) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => MatchingScoreLaw), z j ≠ f z := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) j
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => MatchingScoreLaw) j
    have hmeas : MeasurableSet {q : ℝ × (Fin m → ℝ) | (e.symm q) j ≠ f (e.symm q)} :=
      (measurableSet_eq_fun ((measurable_pi_apply j).comp e.symm.measurable)
        (hf.comp e.symm.measurable)).compl
    have hprod : ∀ᵐ q ∂MatchingScoreLaw.prod (Measure.pi (fun _ : Fin m => MatchingScoreLaw)),
        (e.symm q) j ≠ f (e.symm q) := by
      apply (Measure.ae_prod_iff_ae_ae hmeas).2
      apply (Measure.ae_ae_comm hmeas).2
      apply ae_of_all
      intro z
      have hconst (x : ℝ) : f (j.insertNth x z) = f (j.insertNth 0 z) := by
        have hu := hupdate (j.insertNth (0 : ℝ) z) x
        simpa only [Fin.update_insertNth (α := fun _ : Fin (m+1) => ℝ)] using hu
      simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, hconst] using
        MatchingScoreLaw.ae_ne (f (j.insertNth (0 : ℝ) z))
    have hmapped : ∀ᵐ q ∂(Measure.pi (fun _ : Fin (m+1) => MatchingScoreLaw)).map e,
        (e.symm q) j ≠ f (e.symm q) := by
      rw [he.map_eq]
      exact hprod
    have hpull := ae_of_ae_map e.measurable.aemeasurable hmapped
    simpa only [e.symm_apply_apply] using hpull

theorem matching_score_ne {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => MatchingScoreLaw), z j ≠ z k := by
  apply matching_score_avoid j (fun z => z k) (measurable_pi_apply k)
  intro z x
  exact Function.update_of_ne hjk.symm _ _

theorem matching_distance_ne {n : ℕ} (i j k : Fin n) (hjk : j ≠ k) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => MatchingScoreLaw), |z j-z i| ≠ |z k-z i| := by
  by_cases hji : j = i
  · subst i
    filter_upwards [matching_score_ne j k hjk] with z hz
    intro h
    have he : z k-z j = 0 := abs_eq_zero.mp (by simpa using h.symm)
    exact hz (by linarith)
  by_cases hki : k = i
  · subst i
    filter_upwards [matching_score_ne j k hjk] with z hz
    intro h
    have he : z j-z k = 0 := abs_eq_zero.mp (by simpa using h)
    exact hz (by linarith)
  have hmirror : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => MatchingScoreLaw), z j ≠ 2*z i-z k := by
    apply matching_score_avoid j (fun z => 2*z i-z k) (by fun_prop)
    intro z x
    simp only [Function.update_of_ne (Ne.symm hji), Function.update_of_ne hjk.symm]
  filter_upwards [matching_score_ne j k hjk, hmirror] with z hz hm
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hz (by linarith)
  · exact hm (by linarith)

/-- Only original labels are asserted to have distinct distances. -/
theorem matching_original_distances_unique (n : ℕ) :
    ∀ᵐ z ∂MatchProduct n, ∀ (i j k : Fin n), j ≠ k →
      |(z j).1-(z i).1| ≠ |(z k).1-(z i).1| := by
  have hscore : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => MatchingScoreLaw),
      ∀ (i j k : Fin n), j ≠ k → |z j-z i| ≠ |z k-z i| := by
    apply ae_all_iff.2
    intro i
    apply ae_all_iff.2
    intro j
    apply ae_all_iff.2
    intro k
    by_cases hjk : j = k
    · exact ae_of_all _ (fun _ h => False.elim (h hjk))
    · exact (matching_distance_ne i j k hjk).mono (fun z hz _ => hz)
  have hmap : ∀ᵐ z ∂(MatchProduct n).map (fun z : Fin n → MatchUnit => fun i => (z i).1),
      ∀ (i j k : Fin n), j ≠ k → |z j-z i| ≠ |z k-z i| := by
    rw [(matching_score_product_marginal n).map_eq]
    exact hscore
  exact ae_of_ae_map (matching_score_product_marginal n).measurable.aemeasurable hmap

end AronowAudit.P001.TailA
