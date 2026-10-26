import AronowAudit.P002.Wave1.Gap.GP0021B1
import AronowAudit.P002.Wave1.Gap.GP0021B2
import AronowAudit.P002.Wave1.Gap.GP0022B2
import AronowAudit.P002.Wave1.Gap.GP0022B3
import AronowAudit.P002.Wave1.E61Eigenvalue.N1
import AronowAudit.P002.Wave1.E61Eigenvalue.N2
import AronowAudit.P002.Wave1.E61Eigenvalue.N3
import AronowAudit.P002.Wave1.E61Eigenvalue.N4
import AronowAudit.P002.Wave1.E61Eigenvalue.N5
import AronowAudit.P002.Wave1.E61Eigenvalue.N6
import AronowAudit.P002.Wave1.E61Eigenvalue.N7
import AronowAudit.P002.Wave1.E61Eigenvalue.N8
import AronowAudit.P002.Wave1.E61Eigenvalue.N11
import Mathlib.Topology.Order.Monotone

/-!
Finite algebra and order-theoretic statements for the limit-superior correction of
P002-T21. All probabilities below use the actual finite assignment law.
-/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem RepairT21_probability_nonneg {n} (P : Population n)
    (E : Finset (Fin n) → Prop) : 0 ≤ probability P E := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem RepairT21_probability_le_one {n} (P : Population n)
    (E : Finset (Fin n) → Prop) : probability P E ≤ 1 := by
  unfold probability
  by_cases h : (assignments P).card = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Finset.card_filter_le (assignments P) E

theorem RepairT21_probability_mono {n} (P : Population n)
    {E F : Finset (Fin n) → Prop}
    (h : ∀ S ∈ assignments P, E S → F S) : probability P E ≤ probability P F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    (assignments P).filter E ⊆ (assignments P).filter F from by
      intro S hS
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hS).1, h S (Finset.mem_filter.mp hS).1
          (Finset.mem_filter.mp hS).2⟩)

theorem RepairT21_probability_congr {n} (P : Population n)
    {E F : Finset (Fin n) → Prop}
    (h : ∀ S ∈ assignments P, E S ↔ F S) : probability P E = probability P F := by
  apply le_antisymm
  · exact RepairT21_probability_mono P (fun S hS => (h S hS).mp)
  · exact RepairT21_probability_mono P (fun S hS => (h S hS).mpr)

/-- The beta index can be removed without assuming the class is nonempty. -/
theorem RepairT21_supAdjustedTail_eq (n k : ℕ) (δ e A B r α κ : ℝ) :
    supAdjustedTail n k δ e A B r α κ =
      ⨆ P : {P : CovPopulation n k // Xi P δ e A B r},
        ENNReal.ofReal (probability P.val.pop (fun S =>
          normalCritical α - κ < 0 ∨
          adjustedAR P.val (observedW P.val.pop (late P.val.pop) S) S >
            ENNReal.ofReal (normalCritical α - κ))) := by
  unfold supAdjustedTail
  apply le_antisymm
  · refine iSup_le fun β => iSup_le fun P => ?_
    rcases P with ⟨P, hP, hβ⟩
    dsimp only
    rw [← hβ]
    exact le_iSup_of_le ⟨P, hP⟩ le_rfl
  · refine iSup_le fun P => ?_
    exact le_iSup_of_le (late P.val.pop)
      (le_iSup_of_le ⟨P.val, P.property, rfl⟩ le_rfl)

theorem RepairT21_supAdjustedTail_le_one (n k : ℕ) (δ e A B r α κ : ℝ) :
    supAdjustedTail n k δ e A B r α κ ≤ 1 := by
  unfold supAdjustedTail
  refine iSup_le fun β => iSup_le fun P => ?_
  exact (ENNReal.ofReal_le_ofReal (RepairT21_probability_le_one P.val.pop _)).trans_eq
    ENNReal.ofReal_one

theorem RepairT21_supAdjustedTail_mono (n k : ℕ) (δ e A B r α : ℝ) :
    Monotone (supAdjustedTail n k δ e A B r α) := by
  intro κ κ' hκ
  unfold supAdjustedTail
  refine iSup_le fun β => iSup_le fun P => ?_
  apply le_iSup_of_le β
  apply le_iSup_of_le P
  apply ENNReal.ofReal_le_ofReal
  apply RepairT21_probability_mono
  intro S hS h
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (lt_of_le_of_lt
      (ENNReal.ofReal_le_ofReal (by linarith : normalCritical α - κ' ≤ normalCritical α - κ)) h)

theorem RepairT21_limsup_mono (k : ℕ) (δ e A B r α : ℝ) :
    Monotone (fun κ : ℝ => Filter.limsup
      (fun n : ℕ => supAdjustedTail n k δ e A B r α κ) atTop) := by
  intro κ κ' hκ
  exact limsup_le_limsup (Eventually.of_forall fun n =>
    RepairT21_supAdjustedTail_mono n k δ e A B r α hκ)

/-- The outer ordinary right-hand limit exists before using any CLT. -/
theorem RepairT21_outer_limit_exists (k : ℕ) (δ e A B r α : ℝ) :
    ∃ u : ℝ≥0∞,
      Tendsto (fun κ : ℝ => Filter.limsup
        (fun n : ℕ => supAdjustedTail n k δ e A B r α κ) atTop)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds u) ∧ u ≤ 1 := by
  let H := fun κ : ℝ => Filter.limsup
    (fun n : ℕ => supAdjustedTail n k δ e A B r α κ) atTop
  refine ⟨sInf (H '' Set.Ioi 0), (RepairT21_limsup_mono k δ e A B r α).tendsto_nhdsGT 0, ?_⟩
  calc
    sInf (H '' Set.Ioi 0) ≤ H 1 := sInf_le ⟨1, by norm_num, rfl⟩
    _ ≤ 1 := limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall
      fun n => RepairT21_supAdjustedTail_le_one n k δ e A B r α 1)

theorem RepairT21_popVar_nonneg {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    0 ≤ popVar q := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _) (by linarith)

/-- A coercive finite matrix is invertible, with no symmetry premise needed. -/
theorem RepairT21_det_ne_zero_of_coercive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hG : ∀ b, c * normSq b ≤ dotProduct b (G *ᵥ b)) : G.det ≠ 0 := by
  have hker (b : ι → ℝ) (hb : G *ᵥ b = 0) : b = 0 := by
    have H := hG b
    rw [hb, dotProduct_zero] at H
    have hz : normSq b ≤ 0 := nonpos_of_mul_nonpos_right H hc
    funext i
    have hi : b i ^ 2 ≤ normSq b :=
      Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
    exact (sq_nonpos_iff _).mp (hi.trans hz)
  have hinj : Function.Injective G.mulVec := by
    intro b d hbd
    have hz : G *ᵥ (b - d) = 0 := by rw [Matrix.mulVec_sub, hbd]; simp
    exact sub_eq_zero.mp (hker (b - d) hz)
  have hunit : IsUnit G := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hunit)

theorem RepairT21_population_gram_coercive {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) :
    ∀ b, min 1 e * normSq b ≤ dotProduct b (gram P.x Finset.univ *ᵥ b) := by
  intro b
  have hn : 0 < n := by have := hP.1.1; omega
  rw [gram_quadratic]
  simpa only [groupMean, Finset.card_univ, Fintype.card_fin, mean] using
    (corrected_augmented_gram P.x hn e hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2).2.2.2 b

theorem RepairT21_population_gram_det {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) :
    (gram P.x Finset.univ).det ≠ 0 :=
  RepairT21_det_ne_zero_of_coercive _ (min 1 e) (lt_min zero_lt_one he)
    (RepairT21_population_gram_coercive P δ e A B r hP)

/-- P002's real-valued cutoff, defined using an ENNReal CDF comparison, agrees
with the real CDF quantile. -/
theorem RepairT21_normalCritical_eq (α : ℝ) :
    normalCritical α = AronowAudit.P053.normalCritical α := by
  unfold normalCritical AronowAudit.P053.normalCritical
  congr 1
  ext z
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  rfl

theorem RepairT21_normalCritical_pos (α : ℝ) (hα : 0 < α ∧ α < 1) :
    0 < normalCritical α := by
  rw [RepairT21_normalCritical_eq]
  exact AronowAudit.P053.NormalCompletion.normalCritical_pos α hα.1 hα.2

theorem RepairT21_normalCritical_cdf (α : ℝ) (hα : 0 < α ∧ α < 1) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (normalCritical α) =
      1 - α / 2 := by
  rw [RepairT21_normalCritical_eq,
    ← AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
  exact AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα.1 hα.2

theorem RepairT21_normalTail_formula (t : ℝ) (ht : 0 < t) :
    normalTail t = 2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t) := by
  letI instNullSingletonRepairT21TailFormula : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hset : {z : ℝ | t ≤ |z|} = Set.Iic (-t) ∪ Set.Ici t := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hz
      rcases le_abs.mp hz with hz | hz
      · exact Or.inr hz
      · exact Or.inl (by linarith)
    · rintro (hz | hz)
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl hz)
  have hdisj : Disjoint (Set.Iic (-t)) (Set.Ici t) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    simp only [Set.mem_Iic, Set.mem_Ici] at hz hz'
    linarith
  have hatom : ProbabilityTheory.gaussianReal 0 1 (Set.Ioi t) =
      ProbabilityTheory.gaussianReal 0 1 (Set.Ici t) :=
    measure_congr (Ioi_ae_eq_Ici' (measure_singleton t))
  have hc := measureReal_add_measureReal_compl
    (μ := ProbabilityTheory.gaussianReal 0 1) (s := Set.Iic t) measurableSet_Iic
  simp only [Set.compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one, hatom] at hc
  unfold normalTail
  rw [hset, measure_union hdisj measurableSet_Ici,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hn := AronowAudit.P053.NormalCompletion.normal_cdf_neg t
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, measureReal_def,
    measureReal_def] at hn
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  linarith

theorem RepairT21_normalTail_continuousAt (t : ℝ) (ht : 0 < t) :
    ContinuousAt normalTail t := by
  letI instNullSingletonRepairT21TailContinuity : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have heq : normalTail =ᶠ[nhds t] fun x =>
      2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact RepairT21_normalTail_formula x hx
  have h : ContinuousAt (fun x : ℝ =>
      2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x)) t :=
    continuousAt_const.mul (continuousAt_const.sub
      (AronowAudit.P053.NormalCompletion.cdf_continuousAt _ t))
  exact h.congr_of_eventuallyEq heq

theorem RepairT21_normalTail_critical (α : ℝ) (hα : 0 < α ∧ α < 1) :
    normalTail (normalCritical α) = α := by
  rw [RepairT21_normalTail_formula _ (RepairT21_normalCritical_pos α hα),
    RepairT21_normalCritical_cdf α hα]
  ring

/-- Population normal equations center every residual coordinate, including the intercept. -/
theorem RepairT21_population_score_zero {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    score P.x Finset.univ (residual P a (late P.pop)) = 0 := by
  change score P.x Finset.univ
    (fun i => w P.pop a (late P.pop) i - dotProduct (augmented P.x i) (psi P a (late P.pop))) = 0
  rw [score_residual]
  have h := ols_normal_equations P.x Finset.univ (w P.pop a (late P.pop))
    (RepairT21_population_gram_det P δ e A B r he hP)
  change gram P.x Finset.univ *ᵥ psi P a (late P.pop) = _ at h
  rw [h, sub_self]

theorem RepairT21_residual_mean_zero {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    mean (residual P a (late P.pop)) = 0 := by
  have h := congrFun (RepairT21_population_score_zero P δ e A B r he hP a) none
  simpa only [score, groupMean, augmented, one_mul, Finset.card_univ,
    Fintype.card_fin, mean, Pi.zero_apply] using h


theorem RepairT21_eq_zero_of_popVar_zero {n} (hn : 2 ≤ n) (q : Fin n → ℝ)
    (hm : mean q = 0) (hv : popVar q = 0) : ∀ i, q i = 0 := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (n : ℝ) - 1 ≠ 0 := by linarith
  have hs : (∑ i, q i ^ 2) = 0 := by
    simpa only [popVar, hm, sub_zero, div_eq_zero_iff, hden, or_false] using hv
  intro i
  have hi : q i ^ 2 ≤ ∑ j, q j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
  rw [hs] at hi
  exact (sq_nonpos_iff _).mp hi

theorem RepairT21_residual_zero_of_total_scale_zero {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (hz : popVar (residual P true (late P.pop)) +
      popVar (residual P false (late P.pop)) = 0) :
    ∀ a i, residual P a (late P.pop) i = 0 := by
  have h1 := RepairT21_popVar_nonneg hP.1.1 (residual P true (late P.pop))
  have h0 := RepairT21_popVar_nonneg hP.1.1 (residual P false (late P.pop))
  intro a
  apply RepairT21_eq_zero_of_popVar_zero hP.1.1 _
    (RepairT21_residual_mean_zero P δ e A B r he hP a)
  cases a <;> linarith

theorem RepairT21_fitted_error {n k} (P : CovPopulation n k)
    (β : ℝ) (S : Finset (Fin n)) (a : Bool)
    (hg : (gram P.x (if a then S else Sᶜ)).det ≠ 0) :
    fitted P (observedW P.pop β S) S a - psi P a β =
      (gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ
        score P.x (if a then S else Sᶜ) (residual P a β) := by
  unfold fitted
  rw [ols_error _ _ _ _ hg]
  congr 1
  apply score_congr
  intro i hi
  cases a
  · rw [observedW_control P.pop β S i hi]
    rfl
  · rw [observedW_treated P.pop β S i hi]
    rfl

/-- Exact RSS projection formula, on the observed arm, including zero residuals. -/
theorem RepairT21_arm_rss_identity {n k} (P : CovPopulation n k)
    (β : ℝ) (S : Finset (Fin n)) (a : Bool)
    (hS : (if a then S else Sᶜ).Nonempty)
    (hg : (gram P.x (if a then S else Sᶜ)).det ≠ 0) :
    rss P.x (if a then S else Sᶜ) (observedW P.pop β S)
        (fitted P (observedW P.pop β S) S a) /
        ((if a then S else Sᶜ).card : ℝ) =
      groupMean (if a then S else Sᶜ) (fun i => residual P a β i ^ 2) -
      dotProduct (score P.x (if a then S else Sᶜ) (residual P a β))
        ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ
          score P.x (if a then S else Sᶜ) (residual P a β)) := by
  have hr (i : Fin n) (hi : i ∈ if a then S else Sᶜ) :
      observedW P.pop β S i - dotProduct (augmented P.x i) (psi P a β) =
        residual P a β i := by
    cases a
    · rw [observedW_control P.pop β S i hi]
      rfl
    · rw [observedW_treated P.pop β S i hi]
      rfl
  have hs := score_congr P.x (if a then S else Sᶜ) _ _ hr
  have hm := groupMean_congr (if a then S else Sᶜ) _ _
    (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hr i hi))
  exact (residual_sum_squares_identity P.x _ (observedW P.pop β S)
    (psi P a β) hS hg).trans (by rw [hs, hm])

/-- With zero total scale the actual statistic is zero whenever both arms have full rank. -/
theorem RepairT21_zero_scale_statistic {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (hz : popVar (residual P true (late P.pop)) +
      popVar (residual P false (late P.pop)) = 0)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop)
    (h1 : (gram P.x S).det ≠ 0) (h0 : (gram P.x Sᶜ).det ≠ 0) :
    adjustedAR P (observedW P.pop (late P.pop) S) S = 0 := by
  have hr := RepairT21_residual_zero_of_total_scale_zero P δ e A B r he hP hz
  have hrfun (a : Bool) : residual P a (late P.pop) = 0 := funext (hr a)
  have hscore (a : Bool) : score P.x (if a then S else Sᶜ)
      (residual P a (late P.pop)) = 0 := by
    ext s
    simp only [score, groupMean, hrfun, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_div]
  have hf (a : Bool) : fitted P (observedW P.pop (late P.pop) S) S a =
      psi P a (late P.pop) := by
    apply sub_eq_zero.mp
    rw [RepairT21_fitted_error P _ S a (by cases a <;> assumption), hscore]
    simp
  have ht : adjustedTau P (observedW P.pop (late P.pop) S) S = 0 := by
    have hd := corrected_adjusted_difference P (late P.pop) S
    rw [hf true, hf false] at hd
    simp only [sub_self, slopeDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      groupMean, zero_div, neg_zero, add_zero, sub_eq_zero] at hd
    rw [hd]
    rw [(corrected_oracle_expansion P hP.1 hP.2.1 hP.2.2.1
      hP.2.2.2.2.2.2.2.1 (RepairT21_population_gram_det P δ e A B r he hP) S hS).2,
      hrfun, hrfun]
    simp [groupMean]
  have hR (a : Bool) : rss P.x (if a then S else Sᶜ)
      (observedW P.pop (late P.pop) S) (fitted P (observedW P.pop (late P.pop) S) S a) = 0 := by
    rw [hf]
    apply Finset.sum_eq_zero
    intro i hi
    have hobs : observedW P.pop (late P.pop) S i = w P.pop a (late P.pop) i := by
      cases a
      · exact observedW_control _ _ _ _ hi
      · exact observedW_treated _ _ _ _ hi
    rw [hobs]
    change residual P a (late P.pop) i ^ 2 = 0
    rw [hr, zero_pow (by decide : 2 ≠ 0)]
  have hs : adjustedSigma2 P (observedW P.pop (late P.pop) S) S = 0 := by
    unfold adjustedSigma2
    rw [show rss P.x S _ _ = 0 from hR true, show rss P.x Sᶜ _ _ = 0 from hR false]
    simp
  simp [adjustedAR, absStudent, ht, hs]

theorem RepairT21_zero_scale_tail_le_rank_failure {n k} (P : CovPopulation n k)
    (δ e A B r t : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (hz : popVar (residual P true (late P.pop)) +
      popVar (residual P false (late P.pop)) = 0) :
    probability P.pop (fun S =>
      adjustedAR P (observedW P.pop (late P.pop) S) S > ENNReal.ofReal t) ≤
    probability P.pop (fun S => (gram P.x S).det = 0 ∨ (gram P.x Sᶜ).det = 0) := by
  apply RepairT21_probability_mono
  intro S hS htail
  by_contra h
  push_neg at h
  rw [RepairT21_zero_scale_statistic P δ e A B r he hP hz S hS h.1 h.2] at htail
  exact (not_lt_of_ge bot_le) htail

theorem RepairT21_probability_exists_le_sum {n} (P : Population n)
    {ι : Type*} [Fintype ι] (E : ι → Finset (Fin n) → Prop) :
    probability P (fun S => ∃ i, E i S) ≤ ∑ i, probability P (E i) := by
  have hsub : (assignments P).filter (fun S => ∃ i, E i S) ⊆
      Finset.univ.biUnion (fun i : ι => (assignments P).filter (E i)) := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hS, i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hS, hi⟩⟩
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le (s := Finset.univ) (t := fun i : ι => (assignments P).filter (E i)))
  unfold probability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hreal := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at hreal
  convert hreal using 1 <;> congr!

theorem RepairT21_entry_tail : E61Eigenvalue.EntryTail :=
  E61Eigenvalue.n7_proof
    (E61Eigenvalue.n5_proof E61Eigenvalue.n1_proof
      (E61Eigenvalue.n4_proof E61Eigenvalue.n2_proof E61Eigenvalue.n3_proof))
    E61Eigenvalue.n6_proof

/-- A fixed entry tolerance transfers the population coercivity to each arm. -/
theorem RepairT21_arm_coercive_of_entries {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r)
    (S : Finset (Fin n)) (a : Bool)
    (hentry : ∀ s t, |gram P.x (if a then S else Sᶜ) s t - gram P.x Finset.univ s t| ≤
      min 1 e / (2 * ((k : ℝ) + 1))) :
    ∀ b, (min 1 e / 2) * normSq b ≤ dotProduct b (gram P.x (if a then S else Sᶜ) *ᵥ b) := by
  intro b
  have hq := E61Eigenvalue.n11_proof k _ _ _ hentry b
  have hg := RepairT21_population_gram_coercive P δ e A B r hP b
  have hdim : (k : ℝ) + 1 ≠ 0 := by positivity
  have heq : ((k : ℝ) + 1) * (min 1 e / (2 * ((k : ℝ) + 1))) = min 1 e / 2 := by
    field_simp
  rw [heq] at hq
  linarith [(abs_le.mp hq).1]

theorem RepairT21_rank_failure_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hA : 0 < A) (hr : 0 < r)
    (hP : Xi P δ e A B r) :
    probability P.pop (fun S => (gram P.x S).det = 0 ∨ (gram P.x Sᶜ).det = 0) ≤
      2 * ((k : ℝ) + 1) ^ 2 *
        (2 * ((n : ℝ) + 1) * Real.exp
          (-2 * r ^ 2 * n * (min 1 e / (2 * ((k : ℝ) + 1))) ^ 2 / max 1 A)) := by
  let τ := min 1 e / (2 * ((k : ℝ) + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hminpos : 0 < min 1 e / 2 := by positivity
  have hbad : ∀ S ∈ assignments P.pop,
      ((gram P.x S).det = 0 ∨ (gram P.x Sᶜ).det = 0) →
      ∃ a : Bool, ∃ s t : Option (Fin k),
        τ ≤ |gram P.x (if a then S else Sᶜ) s t - gram P.x Finset.univ s t| := by
    intro S hS hsing
    by_contra h
    push_neg at h
    have hg (a : Bool) : (gram P.x (if a then S else Sᶜ)).det ≠ 0 :=
      RepairT21_det_ne_zero_of_coercive _ _ hminpos
        (RepairT21_arm_coercive_of_entries P δ e A B r hP S a (fun s t => (h a s t).le))
    rcases hsing with hsing | hsing
    · exact hg true hsing
    · exact hg false hsing
  calc
    _ ≤ probability P.pop (fun S => ∃ a : Bool, ∃ s t : Option (Fin k),
        τ ≤ |gram P.x (if a then S else Sᶜ) s t - gram P.x Finset.univ s t|) :=
      RepairT21_probability_mono P.pop hbad
    _ ≤ ∑ a : Bool, ∑ s : Option (Fin k), ∑ t : Option (Fin k),
        probability P.pop (fun S =>
          τ ≤ |gram P.x (if a then S else Sᶜ) s t - gram P.x Finset.univ s t|) := by
      apply (RepairT21_probability_exists_le_sum P.pop _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (RepairT21_probability_exists_le_sum P.pop _).trans
      apply Finset.sum_le_sum
      intro s hs
      exact RepairT21_probability_exists_le_sum P.pop _
    _ ≤ ∑ a : Bool, ∑ s : Option (Fin k), ∑ t : Option (Fin k),
        2 * ((n : ℝ) + 1) * Real.exp (-2 * r ^ 2 * n * τ ^ 2 / max 1 A) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      exact RepairT21_entry_tail n k P δ e A B r hA hr hP a s t τ hτ
    _ = _ := by simp [Fintype.card_option, τ]; ring

theorem RepairT21_rank_failure_tendsto_zero (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hA : 0 < A) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r) :
    Tendsto (fun j => probability (P j).pop
      (fun S => (gram (P j).x S).det = 0 ∨ (gram (P j).x Sᶜ).det = 0)) atTop (nhds 0) := by
  let τ := min 1 e / (2 * ((k : ℝ) + 1))
  let c := 2 * r ^ 2 * τ ^ 2 / max 1 A
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hs := E61Eigenvalue.n8_proof sizes id hsizes strictMono_id c hc
  have ht : Tendsto (fun j =>
      2 * ((sizes j : ℝ) + 1) * Real.exp (-c * sizes j)) atTop (nhds 0) := by
    simpa only [id_eq] using hs.tendsto_atTop_zero
  have hbound := ht.const_mul (2 * ((k : ℝ) + 1) ^ 2)
  simp only [mul_zero] at hbound
  apply squeeze_zero (fun j => RepairT21_probability_nonneg _ _)
    (fun j => ?_) hbound
  convert RepairT21_rank_failure_le (P j) δ e A B r he hA hr (hP j) using 1
  dsimp [c, τ]
  congr 3
  ring

/-- The separate all-zero-scale tail bound; no normal approximation is used. -/
theorem RepairT21_zero_scale_tail_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hA : 0 < A) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hz : ∀ j, popVar (residual (P j) true (late (P j).pop)) +
      popVar (residual (P j) false (late (P j).pop)) = 0) (t : ℝ) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S) S > ENNReal.ofReal t))
      atTop (nhds 0) := by
  exact squeeze_zero (fun j => RepairT21_probability_nonneg _ _)
    (fun j => RepairT21_zero_scale_tail_le_rank_failure (P j) δ e A B r t he (hP j) (hz j))
    (RepairT21_rank_failure_tendsto_zero sizes hsizes k P δ e A B r he hA hr hP)

def RepairT21_totalScale {n k} (P : CovPopulation n k) : ℝ :=
  popVar (residual P true (late P.pop)) + popVar (residual P false (late P.pop))

def RepairT21_U {n k} (P : CovPopulation n k) : ℝ :=
  popVar (residual P true (late P.pop)) / (P.pop.n1 : ℝ) +
    popVar (residual P false (late P.pop)) / controlSize P.pop

def RepairT21_V {n k} (P : CovPopulation n k) : ℝ :=
  designVariance P.pop (oracleTau P (late P.pop))

def RepairT21_q {n k} (P : CovPopulation n k) (i : Fin n) : ℝ :=
  residual P true (late P.pop) i / (P.pop.n1 : ℝ) +
    residual P false (late P.pop) i / controlSize P.pop

theorem RepairT21_design_sizes {n} (P : Population n) (hP : ValidDesign P) :
    (0 : ℝ) < n ∧ (0 : ℝ) < P.n1 ∧ 0 < controlSize P ∧
      (P.n1 : ℝ) ≤ n ∧ controlSize P ≤ n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  unfold controlSize
  exact ⟨hn, hm, sub_pos.mpr hmn, hmn.le, by linarith⟩

theorem RepairT21_U_pos {n k} (P : CovPopulation n k) (hP : ValidDesign P.pop)
    (hpos : 0 < RepairT21_totalScale P) : 0 < RepairT21_U P := by
  have hs := RepairT21_design_sizes P.pop hP
  have h1 := RepairT21_popVar_nonneg hP.1 (residual P true (late P.pop))
  have h0 := RepairT21_popVar_nonneg hP.1 (residual P false (late P.pop))
  by_cases hp1 : 0 < popVar (residual P true (late P.pop))
  · exact add_pos_of_pos_of_nonneg (div_pos hp1 hs.2.1) (div_nonneg h0 hs.2.2.1.le)
  · have hp0 : 0 < popVar (residual P false (late P.pop)) := by
      dsimp only [RepairT21_totalScale] at hpos
      linarith
    exact add_pos_of_nonneg_of_pos (div_nonneg h1 hs.2.1.le) (div_pos hp0 hs.2.2.1)

theorem RepairT21_V_le_U {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) :
    RepairT21_V P ≤ RepairT21_U P := by
  have hid := (oracle_variances_proof P hP.1 (late P.pop) (fun _ => 0)
    hP.2.2.2.2.2.2.2.1 (RepairT21_population_gram_det P δ e A B r he hP)).1
  have hv := RepairT21_popVar_nonneg hP.1.1
    (fun i => residual P true (late P.pop) i - residual P false (late P.pop) i)
  have hn := (RepairT21_design_sizes P.pop hP.1).1
  exact hid.trans_le (sub_le_self _ (div_nonneg hv hn.le))

/-- The lower bound uses total scale; neither individual arm needs positive variance. -/
theorem RepairT21_V_lower {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1 / 2)
    (hP : Xi P δ e A B r) :
    ((1 - max δ 0) * r / (n : ℝ)) * RepairT21_totalScale P ≤ RepairT21_V P := by
  have hs := RepairT21_design_sizes P.pop hP.1
  have hn := hs.1
  have hm := hs.2.1
  have hc := hs.2.2.1
  have hbalance0 : r * (n : ℝ) ≤ controlSize P.pop := by
    have h := hP.2.2.2.2.1
    unfold controlSize
    linarith
  have hb1 : r * controlSize P.pop ≤ (P.pop.n1 : ℝ) :=
    (mul_le_mul_of_nonneg_left hs.2.2.2.2 hr.1.le).trans hP.2.2.2.1
  have hb0 : r * (P.pop.n1 : ℝ) ≤ controlSize P.pop :=
    (mul_le_mul_of_nonneg_left hs.2.2.2.1 hr.1.le).trans hbalance0
  have hcoef1 : r / (n : ℝ) ≤ controlSize P.pop / ((n : ℝ) * (P.pop.n1 : ℝ)) := by
    apply (div_le_div_iff₀ hn (mul_pos hn hm)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb0 hn.le]
  have hcoef0 : r / (n : ℝ) ≤ (P.pop.n1 : ℝ) / ((n : ℝ) * controlSize P.pop) := by
    apply (div_le_div_iff₀ hn (mul_pos hn hc)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb1 hn.le]
  have hv1 := RepairT21_popVar_nonneg hP.1.1 (residual P true (late P.pop))
  have hv0 := RepairT21_popVar_nonneg hP.1.1 (residual P false (late P.pop))
  have hmax : max δ 0 < 1 := max_lt hδ zero_lt_one
  have hscaled := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hcoef1 hv1)
      (mul_le_mul_of_nonneg_right hcoef0 hv0)) (sub_nonneg.mpr hmax.le)
  calc
    _ = (1 - max δ 0) *
        (r / (n : ℝ) * popVar (residual P true (late P.pop)) +
          r / (n : ℝ) * popVar (residual P false (late P.pop))) := by
      dsimp [RepairT21_totalScale]
      ring
    _ ≤ _ := hscaled
    _ ≤ _ := corrected_E10_proof P δ e A B r hk hδ he hA hB hr hP

theorem RepairT21_V_pos {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1 / 2)
    (hP : Xi P δ e A B r) (hpos : 0 < RepairT21_totalScale P) :
    0 < RepairT21_V P := by
  apply lt_of_lt_of_le _ (RepairT21_V_lower P δ e A B r hk hδ he hA hB hr hP)
  have hn := (RepairT21_design_sizes P.pop hP.1).1
  have hd : 0 < 1 - max δ 0 := sub_pos.mpr (max_lt hδ zero_lt_one)
  exact mul_pos (div_pos (mul_pos hd hr.1) hn) hpos

theorem RepairT21_q_mean_zero {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) :
    mean (RepairT21_q P) = 0 := by
  have h1 := RepairT21_residual_mean_zero P δ e A B r he hP true
  have h0 := RepairT21_residual_mean_zero P δ e A B r he hP false
  have heq : mean (RepairT21_q P) =
      mean (residual P true (late P.pop)) / (P.pop.n1 : ℝ) +
      mean (residual P false (late P.pop)) / controlSize P.pop := by
    simp only [mean, RepairT21_q, Finset.sum_add_distrib, ← Finset.sum_div, add_div]
    ring
  rw [heq, h1, h0]
  simp

/-- The oracle is precisely a scaled scalar SRS mean, on the assignment support. -/
theorem RepairT21_oracle_as_sample_mean {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    oracleTau P (late P.pop) S = (P.pop.n1 : ℝ) * groupMean S (RepairT21_q P) := by
  have hs := RepairT21_design_sizes P.pop hP.1
  rw [(corrected_oracle_expansion P hP.1 hP.2.1 hP.2.2.1
    hP.2.2.2.2.2.2.2.1 (RepairT21_population_gram_det P δ e A B r he hP) S hS).2,
    NV_contrast_as_mean P.pop hP.1 _ _ S hS,
    RepairT21_residual_mean_zero P δ e A B r he hP false, mul_zero, sub_zero]
  simp only [groupMean, RepairT21_q, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.mul_sum]
  field_simp [hs.2.1.ne']
  <;> ring

theorem RepairT21_V_eq_q_variance {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) :
    RepairT21_V P =
      ((P.pop.n1 : ℝ) * controlSize P.pop / (n : ℝ)) * popVar (RepairT21_q P) := by
  have hs := RepairT21_design_sizes P.pop hP.1
  have heq : designVariance P.pop (oracleTau P (late P.pop)) =
      designVariance P.pop (fun S => (P.pop.n1 : ℝ) * groupMean S (RepairT21_q P) - 0) := by
    apply NV_variance_congr
    intro S hS
    simpa only [sub_zero] using RepairT21_oracle_as_sample_mean P δ e A B r he hP S hS
  rw [RepairT21_V, heq, NV_variance_affine P.pop hP.1, NV_groupMean_variance P.pop hP.1]
  unfold controlSize
  field_simp [hs.1.ne', hs.2.1.ne']
  <;> ring

theorem RepairT21_q_variance_pos {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1 / 2)
    (hP : Xi P δ e A B r) (hpos : 0 < RepairT21_totalScale P) :
    0 < popVar (RepairT21_q P) := by
  have hv := RepairT21_V_pos P δ e A B r hk hδ he hA hB hr hP hpos
  rw [RepairT21_V_eq_q_variance P δ e A B r he hP] at hv
  have hs := RepairT21_design_sizes P.pop hP.1
  exact (mul_pos_iff_of_pos_left (div_pos (mul_pos hs.2.1 hs.2.2.1) hs.1)).mp hv

theorem RepairT21_expectation_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (h : ∀ S ∈ assignments P, f S = g S) :
    expectation P f = expectation P g := by
  unfold expectation
  rw [Finset.sum_congr rfl h]


theorem RepairT21_expectation_sum {n} (P : Population n) {ι : Type*} [Fintype ι]
    (f : ι → Finset (Fin n) → ℝ) :
    expectation P (fun S => ∑ i, f i S) = ∑ i, expectation P (f i) := by
  unfold expectation
  rw [Finset.sum_comm, Finset.sum_div]

def RepairT21_armSize {n} (P : Population n) (a : Bool) : ℝ :=
  if a then (P.n1 : ℝ) else controlSize P

theorem RepairT21_armSize_pos {n} (P : Population n) (hP : ValidDesign P) (a : Bool) :
    0 < RepairT21_armSize P a := by
  have hs := RepairT21_design_sizes P hP
  cases a
  · exact hs.2.2.1
  · exact hs.2.1

theorem RepairT21_armSize_balance {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) (a : Bool) :
    r * (n : ℝ) ≤ RepairT21_armSize P.pop a := by
  cases a
  · have h := hP.2.2.2.2.1
    change r * (n : ℝ) ≤ (n : ℝ) - (P.pop.n1 : ℝ)
    linarith
  · exact hP.2.2.2.1

/-- Both arms have the exact without-replacement mean variance. -/
theorem RepairT21_arm_second_moment {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (a : Bool) :
    expectation P (fun S => (groupMean (if a then S else Sᶜ) q - mean q) ^ 2) =
      (1 / RepairT21_armSize P a - 1 / (n : ℝ)) * popVar q := by
  have hs := RepairT21_design_sizes P hP
  have hN1 : (n : ℝ) - 1 ≠ 0 := by
    have hN2 : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
    linarith
  have ht : expectation P (fun S => (groupMean S q - mean q) ^ 2) =
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
    rw [sample_mean_variance_proof P hP]
    unfold popVar controlSize
    field_simp [hs.1.ne', hs.2.1.ne', hN1]
  cases a
  · have hc (S : Finset (Fin n)) (hS : S ∈ assignments P) :
        groupMean Sᶜ q - mean q =
          -((P.n1 : ℝ) / controlSize P) * (groupMean S q - mean q) := by
      have hcard : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
      have hCcard : (Sᶜ.card : ℝ) = controlSize P := by
        rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hP.2.2.le]
        rfl
      simp only [groupMean, hcard, hCcard, sum_complement_eq, mean]
      field_simp [hs.1.ne', hs.2.1.ne', hs.2.2.1.ne']
      unfold controlSize
      ring
    change expectation P (fun S => (groupMean Sᶜ q - mean q) ^ 2) = _
    calc
      _ = expectation P (fun S => ((P.n1 : ℝ) / controlSize P) ^ 2 *
          (groupMean S q - mean q) ^ 2) := by
        apply RepairT21_expectation_congr
        intro S hS
        rw [hc S hS]
        ring
      _ = ((P.n1 : ℝ) / controlSize P) ^ 2 *
          ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q) := by
        rw [expectation_mul, ht]
      _ = _ := by
        change _ = (1 / controlSize P - 1 / (n : ℝ)) * popVar q
        field_simp [hs.1.ne', hs.2.1.ne', hs.2.2.1.ne']
        unfold controlSize
        ring
  · exact ht

theorem RepairT21_popVar_le_two_mean_sq {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    popVar q ≤ 2 * mean (fun i => q i ^ 2) := by
  have hN2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < n := by linarith
  have hden : 0 < (n : ℝ) - 1 := by linarith
  have hsum : (∑ i, q i) = (n : ℝ) * mean q := by
    unfold mean
    field_simp
  have hid : (∑ i, (q i - mean q) ^ 2) = (∑ i, q i ^ 2) - (n : ℝ) * mean q ^ 2 := by
    simp only [sub_sq, mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    ring
  have hnon : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  calc
    popVar q ≤ (∑ i, q i ^ 2) / ((n : ℝ) - 1) := by
      unfold popVar
      rw [hid]
      exact div_le_div_of_nonneg_right
        (sub_le_self _ (mul_nonneg hN.le (sq_nonneg _))) hden.le
    _ ≤ (2 * ∑ i, q i ^ 2) / (n : ℝ) := by
      apply (div_le_div_iff₀ hden hN).mpr
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) hnon]
    _ = _ := by unfold mean; ring

/-- A uniform mean-square bound at the deterministic scale 1/N for either arm. -/
theorem RepairT21_arm_mean_square_bound {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hr : 0 < r) (hP : Xi P δ e A B r)
    (q : Fin n → ℝ) (a : Bool) :
    expectation P.pop (fun S => (groupMean (if a then S else Sᶜ) q - mean q) ^ 2) ≤
      2 * mean (fun i => q i ^ 2) / (r * (n : ℝ)) := by
  have hn := (RepairT21_design_sizes P.pop hP.1).1
  have hcoef : 1 / RepairT21_armSize P.pop a - 1 / (n : ℝ) ≤ 1 / (r * (n : ℝ)) := by
    apply (sub_le_self _ (by positivity : 0 ≤ 1 / (n : ℝ))).trans
    exact one_div_le_one_div_of_le (mul_pos hr hn)
      (RepairT21_armSize_balance P δ e A B r hP a)
  rw [RepairT21_arm_second_moment P.pop hP.1]
  calc
    _ ≤ (1 / (r * (n : ℝ))) * popVar q :=
      mul_le_mul_of_nonneg_right hcoef (RepairT21_popVar_nonneg hP.1.1 q)
    _ ≤ (1 / (r * (n : ℝ))) * (2 * mean (fun i => q i ^ 2)) :=
      mul_le_mul_of_nonneg_left (RepairT21_popVar_le_two_mean_sq hP.1.1 q) (by positivity)
    _ = _ := by ring

theorem RepairT21_mean_product_sq_le {n} (hn : 0 < n) (x y : Fin n → ℝ)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : mean (fun i => x i ^ 4) ≤ X) (hy : mean (fun i => y i ^ 4) ≤ Y) :
    mean (fun i => x i ^ 2 * y i ^ 2) ≤ Real.sqrt X * Real.sqrt Y := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' : (∑ i, x i ^ 4) ≤ X * (n : ℝ) := (div_le_iff₀ hN).mp hx
  have hy' : (∑ i, y i ^ 4) ≤ Y * (n : ℝ) := (div_le_iff₀ hN).mp hy
  have hcs : (∑ i, x i ^ 2 * y i ^ 2) ^ 2 ≤ (∑ i, x i ^ 4) * ∑ i, y i ^ 4 := by
    convert Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => x i ^ 2) (fun i => y i ^ 2) using 1 <;> congr! 2 <;> ring
  have hmean : 0 ≤ mean (fun i => x i ^ 2 * y i ^ 2) :=
    div_nonneg (Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hN.le
  apply (sq_le_sq₀ hmean (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  calc
    _ = (∑ i, x i ^ 2 * y i ^ 2) ^ 2 / (n : ℝ) ^ 2 := by rw [mean, div_pow]
    _ ≤ ((∑ i, x i ^ 4) * ∑ i, y i ^ 4) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _ ≤ ((X * (n : ℝ)) * (Y * (n : ℝ))) / (n : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hx' hy' (Finset.sum_nonneg fun i hi => by positivity) (mul_nonneg hX hN.le)
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt hX, Real.sq_sqrt hY]
      field_simp

theorem RepairT21_residual_fourth_moment {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hB : 0 < B) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => residual P a (late P.pop) i ^ 4) ≤
      B ^ 4 * popVar (residual P a (late P.pop)) ^ 2 := by
  have hv := RepairT21_popVar_nonneg hP.1.1 (residual P a (late P.pop))
  have hm : 0 ≤ mean (fun i => residual P a (late P.pop) i ^ 4) :=
    div_nonneg (Finset.sum_nonneg fun i hi => by positivity) (Nat.cast_nonneg _)
  have hf := hP.2.2.2.2.2.2.1 a
  change Real.sqrt (Real.sqrt (mean (fun i => residual P a (late P.pop) i ^ 4))) ≤
    B * Real.sqrt (popVar (residual P a (late P.pop))) at hf
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hB.le (Real.sqrt_nonneg _))).mpr hf
  rw [Real.sq_sqrt (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hv] at hsq
  have hsq' := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (sq_nonneg B) hv)).mpr hsq
  rw [Real.sq_sqrt hm] at hsq'
  calc
    _ ≤ (B ^ 2 * popVar (residual P a (late P.pop))) ^ 2 := hsq'
    _ = _ := by ring

theorem RepairT21_score_coordinate_mean_sq {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hB : 0 < B) (hP : Xi P δ e A B r)
    (a : Bool) (s : Option (Fin k)) :
    mean (fun i => (augmented P.x i s * residual P a (late P.pop) i) ^ 2) ≤
      Real.sqrt (max 1 A) * B ^ 2 * popVar (residual P a (late P.pop)) := by
  have hn : 0 < n := by have := hP.1.1; omega
  have hD : 0 ≤ max (1 : ℝ) A := (le_max_left _ _).trans' zero_le_one
  have hx : mean (fun i => augmented P.x i s ^ 4) ≤ max 1 A := by
    convert E61Eigenvalue.n6_proof n k P δ e A B r hP s s using 1 <;>
      congr 1 <;> funext i <;> ring
  have hv := RepairT21_popVar_nonneg hP.1.1 (residual P a (late P.pop))
  have h := RepairT21_mean_product_sq_le hn (fun i => augmented P.x i s)
    (residual P a (late P.pop)) (max 1 A)
    (B ^ 4 * popVar (residual P a (late P.pop)) ^ 2) hD (by positivity) hx
    (RepairT21_residual_fourth_moment P δ e A B r hB hP a)
  have heq : B ^ 4 * popVar (residual P a (late P.pop)) ^ 2 =
      (B ^ 2 * popVar (residual P a (late P.pop))) ^ 2 := by ring
  rw [heq, Real.sqrt_sq (mul_nonneg (sq_nonneg B) hv)] at h
  simpa only [mul_pow, mul_assoc] using h

def RepairT21_gramErrorSq {n k} (P : CovPopulation n k) (S : Finset (Fin n)) (a : Bool) : ℝ :=
  ∑ s : Option (Fin k), ∑ t : Option (Fin k),
    (gram P.x (if a then S else Sᶜ) s t - gram P.x Finset.univ s t) ^ 2

/-- An explicit Frobenius mean-square bound for each arm. -/
theorem RepairT21_gramErrorSq_expectation_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hr : 0 < r) (hP : Xi P δ e A B r) (a : Bool) :
    expectation P.pop (fun S => RepairT21_gramErrorSq P S a) ≤
      2 * ((k : ℝ) + 1) ^ 2 * max 1 A / (r * (n : ℝ)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  unfold RepairT21_gramErrorSq
  rw [RepairT21_expectation_sum]
  calc
    _ ≤ ∑ s : Option (Fin k), ∑ t : Option (Fin k),
        2 * max 1 A / (r * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [RepairT21_expectation_sum]
      apply Finset.sum_le_sum
      intro t ht
      have hb := RepairT21_arm_mean_square_bound P δ e A B r hr hP
        (fun i => augmented P.x i s * augmented P.x i t) a
      have hm := E61Eigenvalue.n6_proof n k P δ e A B r hP s t
      have hbound : 2 * mean (fun i => (augmented P.x i s * augmented P.x i t) ^ 2) /
          (r * (n : ℝ)) ≤ 2 * max 1 A / (r * (n : ℝ)) := by gcongr
      apply le_trans _ hbound
      simpa only [gram, groupMean, Finset.card_univ, Fintype.card_fin, mean] using hb
    _ = _ := by simp [Fintype.card_option]; ring

/-- The score bound has the residual variance as a factor, also when it is zero. -/
theorem RepairT21_score_normSq_expectation_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hB : 0 < B) (hr : 0 < r)
    (hP : Xi P δ e A B r) (a : Bool) :
    expectation P.pop (fun S => normSq
      (score P.x (if a then S else Sᶜ) (residual P a (late P.pop)))) ≤
      2 * ((k : ℝ) + 1) * Real.sqrt (max 1 A) * B ^ 2 *
        popVar (residual P a (late P.pop)) / (r * (n : ℝ)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  simp only [normSq]
  rw [RepairT21_expectation_sum]
  calc
    _ ≤ ∑ s : Option (Fin k),
        2 * (Real.sqrt (max 1 A) * B ^ 2 * popVar (residual P a (late P.pop))) /
          (r * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hm : mean (fun i => augmented P.x i s * residual P a (late P.pop) i) = 0 := by
        have h := congrFun (RepairT21_population_score_zero P δ e A B r he hP a) s
        simpa only [score, groupMean, mean, Finset.card_univ,
          Fintype.card_fin, Pi.zero_apply] using h
      have hb := RepairT21_arm_mean_square_bound P δ e A B r hr hP
        (fun i => augmented P.x i s * residual P a (late P.pop) i) a
      simp only [hm, sub_zero] at hb
      have hbound : 2 * mean (fun i => (augmented P.x i s * residual P a (late P.pop) i) ^ 2) /
          (r * (n : ℝ)) ≤
          2 * (Real.sqrt (max 1 A) * B ^ 2 * popVar (residual P a (late P.pop))) /
            (r * (n : ℝ)) := by
        gcongr
        exact RepairT21_score_coordinate_mean_sq P δ e A B r hB hP a s
      exact hb.trans hbound
    _ = _ := by simp [Fintype.card_option]; ring

theorem RepairT21_probability_le_expectation_div {n} (P : Population n)
    (f : Finset (Fin n) → ℝ) (hf : ∀ S ∈ assignments P, 0 ≤ f S)
    (t : ℝ) (ht : 0 < t) : probability P (fun S => t ≤ f S) ≤ expectation P f / t := by
  have hsum : t * (((assignments P).filter (fun S => t ≤ f S)).card : ℝ) ≤
      ∑ S ∈ assignments P, f S := by
    calc
      _ = ∑ S ∈ assignments P, if t ≤ f S then t else 0 := by
        rw [← Finset.sum_filter]
        simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S hS
        split_ifs with h
        · exact h
        · exact hf S hS
  have hnum : (((assignments P).filter (fun S => t ≤ f S)).card : ℝ) ≤
      (∑ S ∈ assignments P, f S) / t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using hsum
  calc
    _ ≤ ((∑ S ∈ assignments P, f S) / t) / ((assignments P).card : ℝ) :=
      div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
    _ = _ := by unfold expectation; ring

theorem RepairT21_covariate_mean_sq {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) (s : Fin k) :
    mean (fun i => P.x i s ^ 2) ≤ Real.sqrt (max 1 A) := by
  have hn : 0 < n := by have := hP.1.1; omega
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx : mean (fun i => P.x i s ^ 4) ≤ max 1 A :=
    (hP.2.2.2.2.2.2.2.2.1 s).trans (le_max_right _ _)
  have hy : mean (fun _ : Fin n => (1 : ℝ) ^ 4) ≤ 1 := by simp [mean, hN]
  have h := RepairT21_mean_product_sq_le hn (fun i => P.x i s) (fun _ => 1)
    (max 1 A) 1 (le_trans zero_le_one (le_max_left _ _)) zero_le_one hx hy
  simpa only [one_pow, mul_one, Real.sqrt_one] using h

def RepairT21_armMeanX {n k} (P : CovPopulation n k) (S : Finset (Fin n))
    (a : Bool) (s : Fin k) : ℝ := groupMean (if a then S else Sᶜ) (fun i => P.x i s)

theorem RepairT21_meanX_normSq_expectation_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hr : 0 < r) (hP : Xi P δ e A B r) (a : Bool) :
    expectation P.pop (fun S => normSq (RepairT21_armMeanX P S a)) ≤
      2 * (k : ℝ) * Real.sqrt (max 1 A) / (r * (n : ℝ)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  simp only [normSq]
  rw [RepairT21_expectation_sum]
  calc
    _ ≤ ∑ s : Fin k, 2 * Real.sqrt (max 1 A) / (r * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hm : mean (fun i => P.x i s) = 0 := by
        simp only [mean, hP.2.2.2.2.2.2.2.1 s, zero_div]
      have hb := RepairT21_arm_mean_square_bound P δ e A B r hr hP (fun i => P.x i s) a
      simp only [hm, sub_zero] at hb
      apply hb.trans
      apply div_le_div_of_nonneg_right _ (mul_nonneg hr.le hN.le)
      exact mul_le_mul_of_nonneg_left (RepairT21_covariate_mean_sq P δ e A B r hP s) (by norm_num)
    _ = _ := by simp; ring

theorem RepairT21_score_zero_of_variance_zero {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool)
    (hz : popVar (residual P a (late P.pop)) = 0) (S : Finset (Fin n)) :
    score P.x (if a then S else Sᶜ) (residual P a (late P.pop)) = 0 := by
  have hr := RepairT21_eq_zero_of_popVar_zero hP.1.1 _
    (RepairT21_residual_mean_zero P δ e A B r he hP a) hz
  ext s
  simp only [score, groupMean, hr, mul_zero, Finset.sum_const_zero, zero_div, Pi.zero_apply]

/-- A finite score tail bound with a deterministic moving residual scale. -/
theorem RepairT21_score_tail_le {n k} (P : CovPopulation n k)
    (δ e A B r C : ℝ) (he : 0 < e) (hB : 0 < B) (hr : 0 < r) (hC : 0 < C)
    (hP : Xi P δ e A B r) (a : Bool) :
    probability P.pop (fun S => normSq
      (score P.x (if a then S else Sᶜ) (residual P a (late P.pop))) >
        C * popVar (residual P a (late P.pop)) / (n : ℝ)) ≤
      (2 * ((k : ℝ) + 1) * Real.sqrt (max 1 A) * B ^ 2 / r) / C := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hv := RepairT21_popVar_nonneg hP.1.1 (residual P a (late P.pop))
  by_cases hz : popVar (residual P a (late P.pop)) = 0
  · have heq : probability P.pop (fun S => normSq
        (score P.x (if a then S else Sᶜ) (residual P a (late P.pop))) >
          C * popVar (residual P a (late P.pop)) / (n : ℝ)) = 0 := by
      have hfalse := RepairT21_probability_congr P.pop
        (E := fun S => normSq
          (score P.x (if a then S else Sᶜ) (residual P a (late P.pop))) >
            C * popVar (residual P a (late P.pop)) / (n : ℝ)) (F := fun _ => False)
        (fun S hS => by simp [RepairT21_score_zero_of_variance_zero P δ e A B r he hP a hz S,
          hz, normSq])
      exact hfalse.trans (by simp [probability])
    rw [heq]
    positivity
  · have hvpos : 0 < popVar (residual P a (late P.pop)) := lt_of_le_of_ne hv (Ne.symm hz)
    have ht : 0 < C * popVar (residual P a (late P.pop)) / (n : ℝ) := by positivity
    calc
      _ ≤ probability P.pop (fun S =>
          C * popVar (residual P a (late P.pop)) / (n : ℝ) ≤
            normSq (score P.x (if a then S else Sᶜ) (residual P a (late P.pop)))) :=
        RepairT21_probability_mono P.pop (fun S hS h => h.le)
      _ ≤ expectation P.pop (fun S =>
          normSq (score P.x (if a then S else Sᶜ) (residual P a (late P.pop)))) /
          (C * popVar (residual P a (late P.pop)) / (n : ℝ)) :=
        RepairT21_probability_le_expectation_div P.pop _
          (fun S hS => Finset.sum_nonneg fun s hs => sq_nonneg _) _ ht
      _ ≤ (2 * ((k : ℝ) + 1) * Real.sqrt (max 1 A) * B ^ 2 *
            popVar (residual P a (late P.pop)) / (r * (n : ℝ))) /
          (C * popVar (residual P a (late P.pop)) / (n : ℝ)) :=
        div_le_div_of_nonneg_right
          (RepairT21_score_normSq_expectation_le P δ e A B r he hB hr hP a) ht.le
      _ = _ := by field_simp

theorem RepairT21_meanX_tail_le {n k} (P : CovPopulation n k)
    (δ e A B r C : ℝ) (hr : 0 < r) (hC : 0 < C)
    (hP : Xi P δ e A B r) (a : Bool) :
    probability P.pop (fun S => normSq (RepairT21_armMeanX P S a) > C / (n : ℝ)) ≤
      (2 * (k : ℝ) * Real.sqrt (max 1 A) / r) / C := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have ht : 0 < C / (n : ℝ) := div_pos hC hN
  calc
    _ ≤ probability P.pop (fun S => C / (n : ℝ) ≤ normSq (RepairT21_armMeanX P S a)) :=
      RepairT21_probability_mono P.pop (fun S hS h => h.le)
    _ ≤ expectation P.pop (fun S => normSq (RepairT21_armMeanX P S a)) / (C / (n : ℝ)) :=
      RepairT21_probability_le_expectation_div P.pop _
        (fun S hS => Finset.sum_nonneg fun s hs => sq_nonneg _) _ ht
    _ ≤ (2 * (k : ℝ) * Real.sqrt (max 1 A) / (r * (n : ℝ))) / (C / (n : ℝ)) :=
      div_le_div_of_nonneg_right (RepairT21_meanX_normSq_expectation_le P δ e A B r hr hP a) ht.le
    _ = _ := by field_simp

/-- Constants in both tightness bounds are uniform in size, model, and arm. -/
theorem RepairT21_quantified_score_mean_bounds (k : ℕ) (δ e A B r : ℝ)
    (he : 0 < e) (hB : 0 < B) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (P : CovPopulation n k), Xi P δ e A B r → ∀ a : Bool,
      probability P.pop (fun S => normSq
        (score P.x (if a then S else Sᶜ) (residual P a (late P.pop))) >
          C * popVar (residual P a (late P.pop)) / (n : ℝ)) < ε ∧
      probability P.pop (fun S => normSq (RepairT21_armMeanX P S a) > C / (n : ℝ)) < ε := by
  let K1 := 2 * ((k : ℝ) + 1) * Real.sqrt (max 1 A) * B ^ 2 / r
  let K0 := 2 * (k : ℝ) * Real.sqrt (max 1 A) / r
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  let C := (K1 + K0 + 1) / ε
  have hC : 0 < C := div_pos (by linarith) hε
  have hCE : ε * C = K1 + K0 + 1 := by dsimp [C]; field_simp
  have h1 : K1 / C < ε := (div_lt_iff₀ hC).mpr (by linarith)
  have h0 : K0 / C < ε := (div_lt_iff₀ hC).mpr (by linarith)
  refine ⟨C, hC, ?_⟩
  intro n P hP a
  exact ⟨(RepairT21_score_tail_le P δ e A B r C he hB hr hC hP a).trans_lt h1,
    (RepairT21_meanX_tail_le P δ e A B r C hr hC hP a).trans_lt h0⟩

theorem RepairT21_normSq_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ normSq b := Finset.sum_nonneg fun i hi => sq_nonneg _

/-- Deterministic inverse control used in the regression error estimates. -/
theorem RepairT21_coefficient_normSq_le {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hH : ∀ b, c * normSq b ≤ dotProduct b (H *ᵥ b))
    (b g : ι → ℝ) (hbg : H *ᵥ b = g) : c ^ 2 * normSq b ≤ normSq g := by
  have hb := RepairT21_normSq_nonneg b
  have hg := RepairT21_normSq_nonneg g
  have hlow := hH b
  rw [hbg] at hlow
  have hdot : 0 ≤ dotProduct b g := (mul_nonneg hc.le hb).trans hlow
  have hcs : dotProduct b g ^ 2 ≤ normSq b * normSq g :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b g
  have hsq := (sq_le_sq₀ (mul_nonneg hc.le hb) hdot).mpr hlow
  by_cases hzero : normSq b = 0
  · rw [hzero, mul_zero]
    exact hg
  · have hbpos : 0 < normSq b := lt_of_le_of_ne hb (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ hbpos).mp
    nlinarith [hcs, hsq]

theorem RepairT21_inverse_normSq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hH : ∀ b, c * normSq b ≤ dotProduct b (H *ᵥ b)) (g : ι → ℝ) :
    normSq (H⁻¹ *ᵥ g) ≤ normSq g / c ^ 2 := by
  have hdet := RepairT21_det_ne_zero_of_coercive H c hc hH
  have heq : H *ᵥ (H⁻¹ *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  simpa only [mul_comm] using RepairT21_coefficient_normSq_le H c hc hH _ g heq

/-- The sharp Frobenius quadratic bound has no dimension factor. -/
theorem RepairT21_frobenius_quadratic_bound {ι : Type*} [Fintype ι]
    (H G : Matrix ι ι ℝ) (b : ι → ℝ) :
    |dotProduct b (H *ᵥ b) - dotProduct b (G *ᵥ b)| ≤
      Real.sqrt (∑ s, ∑ t, (H s t - G s t) ^ 2) * normSq b := by
  let F := ∑ s, ∑ t, (H s t - G s t) ^ 2
  have hF : 0 ≤ F := Finset.sum_nonneg fun s hs =>
    Finset.sum_nonneg fun t ht => sq_nonneg _
  have hd : dotProduct b (H *ᵥ b) - dotProduct b (G *ᵥ b) =
      ∑ p : ι × ι, (H p.1 p.2 - G p.1 p.2) * (b p.1 * b p.2) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Fintype.sum_prod_type]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hbn : (∑ p : ι × ι, (b p.1 * b p.2) ^ 2) = normSq b ^ 2 := by
    simp only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, normSq]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => H p.1 p.2 - G p.1 p.2) (fun p => b p.1 * b p.2)
  rw [← hd, hbn] at hcs
  simp only [Fintype.sum_prod_type] at hcs
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (RepairT21_normSq_nonneg b))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hF]
  exact hcs

def RepairT21_gramGood {n k} (P : CovPopulation n k) (e : ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ (a : Bool) (b : Option (Fin k) → ℝ),
    (min 1 e / 2) * normSq b ≤ dotProduct b (gram P.x (if a then S else Sᶜ) *ᵥ b)

theorem RepairT21_gramGood_of_frobenius {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) (S : Finset (Fin n))
    (hF : ∀ a, Real.sqrt (RepairT21_gramErrorSq P S a) ≤ min 1 e / 2) :
    RepairT21_gramGood P e S := by
  intro a b
  have hq := RepairT21_frobenius_quadratic_bound
    (gram P.x (if a then S else Sᶜ)) (gram P.x Finset.univ) b
  change |dotProduct b (gram P.x (if a then S else Sᶜ) *ᵥ b) -
    dotProduct b (gram P.x Finset.univ *ᵥ b)| ≤
      Real.sqrt (RepairT21_gramErrorSq P S a) * normSq b at hq
  have hg := RepairT21_population_gram_coercive P δ e A B r hP b
  have hnorm := RepairT21_normSq_nonneg b
  have hbound := mul_le_mul_of_nonneg_right (hF a) hnorm
  change Real.sqrt (RepairT21_gramErrorSq P S a) * normSq b ≤ _ at hbound
  linarith [(abs_le.mp hq).1]

/-- The exact finite rank/coercivity failure constant. -/
theorem RepairT21_gramGood_failure_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hr : 0 < r) (hP : Xi P δ e A B r) :
    probability P.pop (fun S => ¬ RepairT21_gramGood P e S) ≤
      16 * ((k : ℝ) + 1) ^ 2 * max 1 A / (r * (min 1 e) ^ 2 * (n : ℝ)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hc : 0 < min 1 e / 2 := by positivity
  have hF (S : Finset (Fin n)) (a : Bool) : 0 ≤ RepairT21_gramErrorSq P S a :=
    Finset.sum_nonneg fun s hs => Finset.sum_nonneg fun t ht => sq_nonneg _
  let f := fun S => RepairT21_gramErrorSq P S true + RepairT21_gramErrorSq P S false
  have hf (S : Finset (Fin n)) : 0 ≤ f S := add_nonneg (hF S true) (hF S false)
  have hbad : ∀ S ∈ assignments P.pop, ¬ RepairT21_gramGood P e S → (min 1 e / 2) ^ 2 ≤ f S := by
    intro S hS hnot
    by_contra h
    have hsmall : f S < (min 1 e / 2) ^ 2 := lt_of_not_ge h
    apply hnot
    apply RepairT21_gramGood_of_frobenius P δ e A B r hP S
    intro a
    apply Real.sqrt_le_iff.mpr
    refine ⟨hc.le, ?_⟩
    have hsub : RepairT21_gramErrorSq P S a ≤ f S := by
      cases a
      · exact le_add_of_nonneg_left (hF S true)
      · exact le_add_of_nonneg_right (hF S false)
    exact hsub.trans hsmall.le
  have hE : expectation P.pop f ≤
      4 * ((k : ℝ) + 1) ^ 2 * max 1 A / (r * (n : ℝ)) := by
    unfold f expectation
    rw [Finset.sum_add_distrib, add_div]
    exact (add_le_add (RepairT21_gramErrorSq_expectation_le P δ e A B r hr hP true)
      (RepairT21_gramErrorSq_expectation_le P δ e A B r hr hP false)).trans_eq (by ring)
  calc
    _ ≤ probability P.pop (fun S => (min 1 e / 2) ^ 2 ≤ f S) :=
      RepairT21_probability_mono P.pop hbad
    _ ≤ expectation P.pop f / (min 1 e / 2) ^ 2 :=
      RepairT21_probability_le_expectation_div P.pop f (fun S hS => hf S) _ (sq_pos_of_pos hc)
    _ ≤ (4 * ((k : ℝ) + 1) ^ 2 * max 1 A / (r * (n : ℝ))) / (min 1 e / 2) ^ 2 :=
      div_le_div_of_nonneg_right hE (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem RepairT21_gramGood_failure_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r) :
    Tendsto (fun j => probability (P j).pop (fun S => ¬ RepairT21_gramGood (P j) e S))
      atTop (nhds 0) := by
  have hsize : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  let K := 16 * ((k : ℝ) + 1) ^ 2 * max 1 A / (r * (min 1 e) ^ 2)
  have ht : Tendsto (fun j => K / (sizes j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsize
  apply squeeze_zero (fun j => RepairT21_probability_nonneg _ _) (fun j => ?_) ht
  convert RepairT21_gramGood_failure_le (P j) δ e A B r he hr (hP j) using 1
  dsimp [K]
  ring

theorem RepairT21_groupMean_slopeDot {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (b : Option (Fin k) → ℝ) :
    groupMean S (fun i => slopeDot (x i) b) =
      dotProduct (fun s => groupMean S (fun i => x i s)) (fun s => b (some s)) := by
  unfold groupMean slopeDot dotProduct
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.sum_mul, div_mul_eq_mul_div]

theorem RepairT21_slope_normSq_le {k} (b : Option (Fin k) → ℝ) :
    normSq (fun s => b (some s)) ≤ normSq b := by
  simp only [normSq, Fintype.sum_option]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Squared control of a slope correction on a coercive arm. -/
theorem RepairT21_slope_correction_bound {n k} (P : CovPopulation n k)
    (β c : ℝ) (hc : 0 < c) (S : Finset (Fin n)) (a : Bool)
    (hG : ∀ b, c * normSq b ≤ dotProduct b (gram P.x (if a then S else Sᶜ) *ᵥ b)) :
    c ^ 2 * groupMean (if a then S else Sᶜ)
        (fun i => slopeDot (P.x i) (fitted P (observedW P.pop β S) S a - psi P a β)) ^ 2 ≤
      normSq (RepairT21_armMeanX P S a) *
        normSq (score P.x (if a then S else Sᶜ) (residual P a β)) := by
  let b := fitted P (observedW P.pop β S) S a - psi P a β
  let g := score P.x (if a then S else Sᶜ) (residual P a β)
  have hdet := RepairT21_det_ne_zero_of_coercive _ c hc hG
  have hbg : gram P.x (if a then S else Sᶜ) *ᵥ b = g := by
    rw [show b = (gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ g from
      RepairT21_fitted_error P β S a hdet,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  have hcoef := RepairT21_coefficient_normSq_le _ c hc hG b g hbg
  have hcs : dotProduct (RepairT21_armMeanX P S a) (fun s => b (some s)) ^ 2 ≤
      normSq (RepairT21_armMeanX P S a) * normSq b := by
    apply (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _).trans
    exact mul_le_mul_of_nonneg_left (RepairT21_slope_normSq_le b) (RepairT21_normSq_nonneg _)
  rw [RepairT21_groupMean_slopeDot]
  calc
    _ ≤ c ^ 2 * (normSq (RepairT21_armMeanX P S a) * normSq b) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = normSq (RepairT21_armMeanX P S a) * (c ^ 2 * normSq b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoef (RepairT21_normSq_nonneg _)

/-- A finite product bound: no independence between sample means and scores is used. -/
theorem RepairT21_numerator_square_bound {n k} (P : CovPopulation n k)
    (e C : ℝ) (he : 0 < e) (hC : 0 < C) (hD : ValidDesign P.pop)
    (S : Finset (Fin n)) (hgood : RepairT21_gramGood P e S)
    (hX : ∀ a, normSq (RepairT21_armMeanX P S a) ≤ C / (n : ℝ))
    (hg : ∀ a, normSq (score P.x (if a then S else Sᶜ) (residual P a (late P.pop))) ≤
      C * popVar (residual P a (late P.pop)) / (n : ℝ)) :
    (min 1 e / 2) ^ 2 *
      (adjustedTau P (observedW P.pop (late P.pop) S) S - oracleTau P (late P.pop) S) ^ 2 ≤
      2 * C ^ 2 * RepairT21_totalScale P / (n : ℝ) ^ 2 := by
  have hN := (RepairT21_design_sizes P.pop hD).1
  have hc : 0 < min 1 e / 2 := by positivity
  let d := fun a => groupMean (if a then S else Sᶜ) (fun i => slopeDot (P.x i)
    (fitted P (observedW P.pop (late P.pop) S) S a - psi P a (late P.pop)))
  have hb (a : Bool) : (min 1 e / 2) ^ 2 * d a ^ 2 ≤
      (C / (n : ℝ)) * (C * popVar (residual P a (late P.pop)) / (n : ℝ)) := by
    apply (RepairT21_slope_correction_bound P (late P.pop) _ hc S a (hgood a)).trans
    exact mul_le_mul (hX a) (hg a) (RepairT21_normSq_nonneg _) (div_nonneg hC.le hN.le)
  have hd : adjustedTau P (observedW P.pop (late P.pop) S) S - oracleTau P (late P.pop) S =
      -d true + d false := corrected_adjusted_difference P (late P.pop) S
  rw [hd]
  have hsq : (-d true + d false) ^ 2 ≤ 2 * d true ^ 2 + 2 * d false ^ 2 := by
    nlinarith [sq_nonneg (d true + d false)]
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (min 1 e / 2))
  dsimp only [RepairT21_totalScale]
  calc
    _ ≤ 2 * ((min 1 e / 2) ^ 2 * d true ^ 2) + 2 * ((min 1 e / 2) ^ 2 * d false ^ 2) := by
      nlinarith [hmul]
    _ ≤ 2 * ((C / (n : ℝ)) * (C * popVar (residual P true (late P.pop)) / (n : ℝ))) +
        2 * ((C / (n : ℝ)) * (C * popVar (residual P false (late P.pop)) / (n : ℝ))) := by
      linarith [hb true, hb false]
    _ = _ := by ring

theorem RepairT21_probability_or_le {n} (P : Population n)
    (E F : Finset (Fin n) → Prop) :
    probability P (fun S => E S ∨ F S) ≤ probability P E + probability P F := by
  have h := RepairT21_probability_exists_le_sum P (fun a : Bool => if a then E else F)
  simpa [Bool.exists_bool, add_comm, or_comm] using h

/-- Positive-total-scale numerator limit, with zero variance in either arm allowed. -/
theorem RepairT21_numerator_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (hP : ∀ j, Xi (P j) δ e A B r)
    (hpos : ∀ j, 0 < RepairT21_totalScale (P j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      |adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S -
        oracleTau (P j) (late (P j).pop) S| > η * Real.sqrt (RepairT21_V (P j))))
      atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Eventually.of_forall fun j => hl.trans_le (RepairT21_probability_nonneg _ _)
  · intro b hb
    obtain ⟨C, hC, htails⟩ := RepairT21_quantified_score_mean_bounds k δ e A B r
      he hB hr.1 (b / 8) (by positivity)
    let E := fun j S => ∃ a : Bool, normSq
      (score (P j).x (if a then S else Sᶜ) (residual (P j) a (late (P j).pop))) >
        C * popVar (residual (P j) a (late (P j).pop)) / (sizes j : ℝ)
    let F := fun j S => ∃ a : Bool, normSq (RepairT21_armMeanX (P j) S a) > C / (sizes j : ℝ)
    have hE (j : ℕ) : probability (P j).pop (E j) ≤ b / 4 := by
      apply (RepairT21_probability_exists_le_sum (P j).pop _).trans
      calc
        _ ≤ ∑ a : Bool, b / 8 := Finset.sum_le_sum fun a ha =>
          (htails (sizes j) (P j) (hP j) a).1.le
        _ = _ := by simp; ring
    have hF (j : ℕ) : probability (P j).pop (F j) ≤ b / 4 := by
      apply (RepairT21_probability_exists_le_sum (P j).pop _).trans
      calc
        _ ≤ ∑ a : Bool, b / 8 := Finset.sum_le_sum fun a ha =>
          (htails (sizes j) (P j) (hP j) a).2.le
        _ = _ := by simp; ring
    have hsize : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
    have hreg : 0 < min 1 e / 2 := by positivity
    have hdelta : 0 < 1 - max δ 0 := sub_pos.mpr (max_lt hδ zero_lt_one)
    have hR : 0 < (min 1 e / 2) ^ 2 * η ^ 2 * (1 - max δ 0) * r :=
      mul_pos (mul_pos (mul_pos (sq_pos_of_pos hreg) (sq_pos_of_pos hη)) hdelta) hr.1
    have hdet : ∀ᶠ j in atTop,
        2 * C ^ 2 / (sizes j : ℝ) < (min 1 e / 2) ^ 2 * η ^ 2 * (1 - max δ 0) * r :=
      (tendsto_const_nhds.div_atTop hsize).eventually (eventually_lt_nhds hR)
    have hgood := (RepairT21_gramGood_failure_tendsto_zero sizes hsizes k P δ e A B r he hr.1 hP).eventually
      (eventually_lt_nhds (show (0 : ℝ) < b / 2 by positivity))
    filter_upwards [hdet, hgood] with j hdetj hgoodj
    have hN := (RepairT21_design_sizes (P j).pop (hP j).1).1
    have hv := RepairT21_V_pos (P j) δ e A B r hk hδ he hA hB hr (hP j) (hpos j)
    have hsub : ∀ S ∈ assignments (P j).pop,
        |adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S -
          oracleTau (P j) (late (P j).pop) S| > η * Real.sqrt (RepairT21_V (P j)) →
        E j S ∨ F j S ∨ ¬ RepairT21_gramGood (P j) e S := by
      intro S hS htail
      by_contra h
      dsimp only [E, F] at h
      push_neg at h
      rcases h with ⟨hg, hX, hgood⟩
      have hnum := RepairT21_numerator_square_bound (P j) e C he hC (hP j).1 S hgood hX hg
      have hstrict : 2 * C ^ 2 * RepairT21_totalScale (P j) / (sizes j : ℝ) ^ 2 <
          (min 1 e / 2) ^ 2 * (η ^ 2 * RepairT21_V (P j)) := by
        calc
          _ = (2 * C ^ 2 / (sizes j : ℝ)) * (RepairT21_totalScale (P j) / (sizes j : ℝ)) := by ring
          _ < ((min 1 e / 2) ^ 2 * η ^ 2 * (1 - max δ 0) * r) *
              (RepairT21_totalScale (P j) / (sizes j : ℝ)) :=
            mul_lt_mul_of_pos_right hdetj (div_pos (hpos j) hN)
          _ = ((min 1 e / 2) ^ 2 * η ^ 2) *
              (((1 - max δ 0) * r / (sizes j : ℝ)) * RepairT21_totalScale (P j)) := by ring
          _ ≤ _ := by
            convert mul_le_mul_of_nonneg_left
              (RepairT21_V_lower (P j) δ e A B r hk hδ he hA hB hr (hP j))
              (mul_nonneg (sq_nonneg (min 1 e / 2)) (sq_nonneg η)) using 1 <;> ring
      have hsq : (adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S -
          oracleTau (P j) (late (P j).pop) S) ^ 2 < η ^ 2 * RepairT21_V (P j) :=
        (mul_lt_mul_iff_right₀ (sq_pos_of_pos hreg)).mp (hnum.trans_lt hstrict)
      have habs : |adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S -
          oracleTau (P j) (late (P j).pop) S| ≤ η * Real.sqrt (RepairT21_V (P j)) := by
        apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hη.le (Real.sqrt_nonneg _))).mp
        rw [sq_abs, mul_pow, Real.sq_sqrt hv.le]
        exact hsq.le
      exact not_lt_of_ge habs htail
    calc
      _ ≤ probability (P j).pop (fun S => E j S ∨ F j S ∨ ¬ RepairT21_gramGood (P j) e S) :=
        RepairT21_probability_mono (P j).pop hsub
      _ ≤ probability (P j).pop (E j) +
          (probability (P j).pop (F j) + probability (P j).pop (fun S => ¬ RepairT21_gramGood (P j) e S)) :=
        (RepairT21_probability_or_le (P j).pop (E j)
          (fun S => F j S ∨ ¬ RepairT21_gramGood (P j) e S)).trans
          (add_le_add le_rfl (RepairT21_probability_or_le (P j).pop (F j)
            (fun S => ¬ RepairT21_gramGood (P j) e S)))
      _ < b := by linarith [hE j, hF j]

theorem RepairT21_residual_second_moment {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => residual P a (late P.pop) i ^ 2) =
      ((n : ℝ) - 1) / (n : ℝ) * popVar (residual P a (late P.pop)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hN1 : (n : ℝ) - 1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
    linarith
  rw [popVar, RepairT21_residual_mean_zero P δ e A B r he hP a]
  simp only [sub_zero, mean]
  field_simp [hN.ne', hN1]

theorem RepairT21_residual_square_mean_moment {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hB : 0 < B) (hr : 0 < r)
    (hP : Xi P δ e A B r) (a : Bool) :
    expectation P.pop (fun S =>
      (groupMean (if a then S else Sᶜ) (fun i => residual P a (late P.pop) i ^ 2) -
        mean (fun i => residual P a (late P.pop) i ^ 2)) ^ 2) ≤
      2 * B ^ 4 * popVar (residual P a (late P.pop)) ^ 2 / (r * (n : ℝ)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hb := RepairT21_arm_mean_square_bound P δ e A B r hr hP
    (fun i => residual P a (late P.pop) i ^ 2) a
  have hp (x : ℝ) : (x ^ 2) ^ 2 = x ^ 4 := by ring
  simp only [hp] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (mul_nonneg hr.le hN.le)
  have hfour := mul_le_mul_of_nonneg_left
    (RepairT21_residual_fourth_moment P δ e A B r hB hP a) (show (0 : ℝ) ≤ 2 by norm_num)
  convert hfour using 1 <;> ring

/-- Uniform concentration of each residual-square mean, including zero residual scale. -/
theorem RepairT21_residual_square_mean_tail_le {n k} (P : CovPopulation n k)
    (δ e A B r η : ℝ) (he : 0 < e) (hB : 0 < B) (hr : 0 < r) (hη : 0 < η)
    (hP : Xi P δ e A B r) (a : Bool) :
    probability P.pop (fun S =>
      |groupMean (if a then S else Sᶜ) (fun i => residual P a (late P.pop) i ^ 2) -
        mean (fun i => residual P a (late P.pop) i ^ 2)| >
          η * popVar (residual P a (late P.pop))) ≤
      2 * B ^ 4 / (r * (n : ℝ) * η ^ 2) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hv := RepairT21_popVar_nonneg hP.1.1 (residual P a (late P.pop))
  let v := popVar (residual P a (late P.pop))
  let f := fun S => (groupMean (if a then S else Sᶜ) (fun i => residual P a (late P.pop) i ^ 2) -
    mean (fun i => residual P a (late P.pop) i ^ 2)) ^ 2
  by_cases hz : v = 0
  · have hrzero := RepairT21_eq_zero_of_popVar_zero hP.1.1 _
      (RepairT21_residual_mean_zero P δ e A B r he hP a) hz
    have heq : probability P.pop (fun S =>
        |groupMean (if a then S else Sᶜ) (fun i => residual P a (late P.pop) i ^ 2) -
          mean (fun i => residual P a (late P.pop) i ^ 2)| > η * v) = 0 := by
      simp only [hrzero, zero_pow (by decide : 2 ≠ 0), groupMean, mean,
        Finset.sum_const_zero, zero_div, sub_self, abs_zero, hz, mul_zero, lt_self_iff_false,
        probability, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    rw [heq]
    positivity
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
    have ht : 0 < η ^ 2 * v ^ 2 := mul_pos (sq_pos_of_pos hη) (sq_pos_of_pos hvpos)
    calc
      _ ≤ probability P.pop (fun S => η ^ 2 * v ^ 2 ≤ f S) := by
        apply RepairT21_probability_mono
        intro S hS htail
        have hsq := (sq_le_sq₀ (mul_nonneg hη.le hv) (abs_nonneg _)).mpr htail.le
        simpa only [mul_pow, sq_abs] using hsq
      _ ≤ expectation P.pop f / (η ^ 2 * v ^ 2) :=
        RepairT21_probability_le_expectation_div P.pop f (fun S hS => sq_nonneg _) _ ht
      _ ≤ (2 * B ^ 4 * v ^ 2 / (r * (n : ℝ))) / (η ^ 2 * v ^ 2) :=
        div_le_div_of_nonneg_right
          (RepairT21_residual_square_mean_moment P δ e A B r hB hr hP a) ht.le
      _ = _ := by field_simp

theorem RepairT21_residual_square_mean_tail_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r η : ℝ)
    (he : 0 < e) (hB : 0 < B) (hr : 0 < r) (hη : 0 < η)
    (hP : ∀ j, Xi (P j) δ e A B r) (a : Bool) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      |groupMean (if a then S else Sᶜ) (fun i => residual (P j) a (late (P j).pop) i ^ 2) -
        mean (fun i => residual (P j) a (late (P j).pop) i ^ 2)| >
          η * popVar (residual (P j) a (late (P j).pop)))) atTop (nhds 0) := by
  have hsize : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  let K := 2 * B ^ 4 / (r * η ^ 2)
  have ht : Tendsto (fun j => K / (sizes j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsize
  apply squeeze_zero (fun j => RepairT21_probability_nonneg _ _) (fun j => ?_) ht
  convert RepairT21_residual_square_mean_tail_le (P j) δ e A B r η he hB hr hη (hP j) a using 1
  dsimp [K]
  ring

/-- The projection reduction is bounded linearly by the squared score norm. -/
theorem RepairT21_projection_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hH : ∀ b, c * normSq b ≤ dotProduct b (H *ᵥ b)) (g : ι → ℝ) :
    0 ≤ dotProduct g (H⁻¹ *ᵥ g) ∧ dotProduct g (H⁻¹ *ᵥ g) ≤ normSq g / c := by
  let b := H⁻¹ *ᵥ g
  have hdet := RepairT21_det_ne_zero_of_coercive H c hc hH
  have hHb : H *ᵥ b = g := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  have hlow := hH b
  rw [hHb, dotProduct_comm b g] at hlow
  have hnon : 0 ≤ dotProduct g b := (mul_nonneg hc.le (RepairT21_normSq_nonneg b)).trans hlow
  refine ⟨hnon, ?_⟩
  have hcs : dotProduct g b ^ 2 ≤ normSq g * normSq b :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g b
  have hbound := RepairT21_inverse_normSq_le H c hc hH g
  apply (sq_le_sq₀ hnon (div_nonneg (RepairT21_normSq_nonneg g) hc.le)).mp
  calc
    _ ≤ normSq g * normSq b := hcs
    _ ≤ normSq g * (normSq g / c ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (RepairT21_normSq_nonneg g)
    _ = _ := by ring

def RepairT21_armRSSMean {n k} (P : CovPopulation n k) (S : Finset (Fin n)) (a : Bool) : ℝ :=
  rss P.x (if a then S else Sᶜ) (observedW P.pop (late P.pop) S)
    (fitted P (observedW P.pop (late P.pop) S) S a) / RepairT21_armSize P.pop a

theorem RepairT21_arm_card {n} (P : Population n) (hD : ValidDesign P)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) (a : Bool) :
    ((if a then S else Sᶜ).card : ℝ) = RepairT21_armSize P a := by
  have hs : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte, RepairT21_armSize,
      Finset.card_compl, Fintype.card_fin, hs, Nat.cast_sub hD.2.2.le, controlSize]
  · simpa only [RepairT21_armSize, ↓reduceIte] using congrArg (fun m : ℕ => (m : ℝ)) hs

theorem RepairT21_arm_nonempty {n} (P : Population n) (hD : ValidDesign P)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) (a : Bool) :
    (if a then S else Sᶜ).Nonempty := by
  apply Finset.card_pos.mp
  have h := RepairT21_armSize_pos P hD a
  rw [← RepairT21_arm_card P hD S hS a] at h
  exact_mod_cast h

theorem RepairT21_sigma2_eq_armRSSMean {n k} (P : CovPopulation n k) (S : Finset (Fin n)) :
    adjustedSigma2 P (observedW P.pop (late P.pop) S) S =
      RepairT21_armRSSMean P S true / (P.pop.n1 : ℝ) +
        RepairT21_armRSSMean P S false / controlSize P.pop := by
  simp only [adjustedSigma2, RepairT21_armRSSMean, RepairT21_armSize, ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

theorem RepairT21_armRSSMean_error_le {n k} (P : CovPopulation n k)
    (δ e A B r C ζ η : ℝ) (he : 0 < e) (hC : 0 < C) (hP : Xi P δ e A B r)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) (hgood : RepairT21_gramGood P e S)
    (hsmall : ζ + 1 / (n : ℝ) + C / ((min 1 e / 2) * (n : ℝ)) ≤ η)
    (a : Bool)
    (hg : normSq (score P.x (if a then S else Sᶜ) (residual P a (late P.pop))) ≤
      C * popVar (residual P a (late P.pop)) / (n : ℝ))
    (hM : |groupMean (if a then S else Sᶜ) (fun i => residual P a (late P.pop) i ^ 2) -
      mean (fun i => residual P a (late P.pop) i ^ 2)| ≤ ζ * popVar (residual P a (late P.pop))) :
    |RepairT21_armRSSMean P S a - popVar (residual P a (late P.pop))| ≤
      η * popVar (residual P a (late P.pop)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hc : 0 < min 1 e / 2 := by positivity
  have hv := RepairT21_popVar_nonneg hP.1.1 (residual P a (late P.pop))
  have hdet := RepairT21_det_ne_zero_of_coercive _ _ hc (hgood a)
  have hid := RepairT21_arm_rss_identity P (late P.pop) S a
    (RepairT21_arm_nonempty P.pop hP.1 S hS a) hdet
  rw [RepairT21_arm_card P.pop hP.1 S hS a] at hid
  change RepairT21_armRSSMean P S a = _ at hid
  let v := popVar (residual P a (late P.pop))
  let g := score P.x (if a then S else Sᶜ) (residual P a (late P.pop))
  let p := dotProduct g ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ g)
  have hp := RepairT21_projection_le _ _ hc (hgood a) g
  have hpu : p ≤ (C / ((min 1 e / 2) * (n : ℝ))) * v := by
    apply hp.2.trans
    apply (div_le_div_of_nonneg_right hg hc.le).trans_eq
    dsimp [v]
    ring
  have hmean : mean (fun i => residual P a (late P.pop) i ^ 2) - v = -v / (n : ℝ) := by
    rw [RepairT21_residual_second_moment P δ e A B r he hP a]
    dsimp [v]
    field_simp
    ring
  have hscaled := mul_le_mul_of_nonneg_right hsmall hv
  have hnon : 0 ≤ v / (n : ℝ) := div_nonneg hv hN.le
  have hscaled' : ζ * popVar (residual P a (late P.pop)) +
      popVar (residual P a (late P.pop)) / (n : ℝ) +
      (C / ((min 1 e / 2) * (n : ℝ))) * popVar (residual P a (late P.pop)) ≤
      η * popVar (residual P a (late P.pop)) := by
    convert hscaled using 1 <;> ring
  have hnon2 : 0 ≤ (C / ((min 1 e / 2) * (n : ℝ))) * popVar (residual P a (late P.pop)) :=
    mul_nonneg (div_nonneg hC.le (mul_nonneg hc.le hN.le)) hv
  dsimp only [v] at hmean hnon hpu
  simp only [neg_div] at hmean
  apply abs_le.mpr
  constructor <;> dsimp [p, g] at hp hpu
  · linarith only [hid, hmean, hpu, hscaled', (abs_le.mp hM).1]
  · linarith only [hid, hmean, hscaled', hnon, hnon2, (abs_le.mp hM).2, hp.1]

theorem RepairT21_sigma2_relative_error_le {n k} (P : CovPopulation n k)
    (hD : ValidDesign P.pop) (hpos : 0 < RepairT21_totalScale P) (S : Finset (Fin n))
    (η : ℝ)
    (hR : ∀ a, |RepairT21_armRSSMean P S a - popVar (residual P a (late P.pop))| ≤
      η * popVar (residual P a (late P.pop))) :
    |adjustedSigma2 P (observedW P.pop (late P.pop) S) S / RepairT21_U P - 1| ≤ η := by
  have hs := RepairT21_design_sizes P.pop hD
  have hU := RepairT21_U_pos P hD hpos
  have heq : adjustedSigma2 P (observedW P.pop (late P.pop) S) S - RepairT21_U P =
      (RepairT21_armRSSMean P S true - popVar (residual P true (late P.pop))) / (P.pop.n1 : ℝ) +
      (RepairT21_armRSSMean P S false - popVar (residual P false (late P.pop))) / controlSize P.pop := by
    rw [RepairT21_sigma2_eq_armRSSMean]
    unfold RepairT21_U
    ring
  have hb : |adjustedSigma2 P (observedW P.pop (late P.pop) S) S - RepairT21_U P| ≤ η * RepairT21_U P := by
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_div, abs_div, abs_of_pos hs.2.1, abs_of_pos hs.2.2.1]
    apply (add_le_add (div_le_div_of_nonneg_right (hR true) hs.2.1.le)
      (div_le_div_of_nonneg_right (hR false) hs.2.2.1.le)).trans_eq
    unfold RepairT21_U
    ring
  have hquot : adjustedSigma2 P (observedW P.pop (late P.pop) S) S / RepairT21_U P - 1 =
      (adjustedSigma2 P (observedW P.pop (late P.pop) S) S - RepairT21_U P) / RepairT21_U P := by
    field_simp
  rw [hquot, abs_div, abs_of_pos hU]
  exact (div_le_iff₀ hU).mpr hb

/-- Relative variance consistency against U, rather than the feasible numerator variance. -/
theorem RepairT21_denominator_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hB : 0 < B) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hpos : ∀ j, 0 < RepairT21_totalScale (P j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      |adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S /
        RepairT21_U (P j) - 1| > η)) atTop (nhds 0) := by
  let ζ := η / 4
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  let M1 := fun j S =>
    |groupMean S (fun i => residual (P j) true (late (P j).pop) i ^ 2) -
      mean (fun i => residual (P j) true (late (P j).pop) i ^ 2)| >
        ζ * popVar (residual (P j) true (late (P j).pop))
  let M0 := fun j S =>
    |groupMean Sᶜ (fun i => residual (P j) false (late (P j).pop) i ^ 2) -
      mean (fun i => residual (P j) false (late (P j).pop) i ^ 2)| >
        ζ * popVar (residual (P j) false (late (P j).pop))
  let M := fun j S => M1 j S ∨ M0 j S
  have hM1 : Tendsto (fun j => probability (P j).pop (M1 j)) atTop (nhds 0) :=
    RepairT21_residual_square_mean_tail_tendsto_zero sizes hsizes k P δ e A B r ζ he hB hr hζ hP true
  have hM0 : Tendsto (fun j => probability (P j).pop (M0 j)) atTop (nhds 0) :=
    RepairT21_residual_square_mean_tail_tendsto_zero sizes hsizes k P δ e A B r ζ he hB hr hζ hP false
  have hM : Tendsto (fun j => probability (P j).pop (M j)) atTop (nhds 0) := by
    have ht := hM1.add hM0
    simp only [add_zero] at ht
    exact squeeze_zero (fun j => RepairT21_probability_nonneg _ _)
      (fun j => RepairT21_probability_or_le (P j).pop (M1 j) (M0 j)) ht
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Eventually.of_forall fun j => hl.trans_le (RepairT21_probability_nonneg _ _)
  · intro b hb
    obtain ⟨C, hC, htails⟩ := RepairT21_quantified_score_mean_bounds k δ e A B r he hB hr
      (b / 8) (by positivity)
    let E := fun j S => ∃ a : Bool, normSq
      (score (P j).x (if a then S else Sᶜ) (residual (P j) a (late (P j).pop))) >
        C * popVar (residual (P j) a (late (P j).pop)) / (sizes j : ℝ)
    have hE (j : ℕ) : probability (P j).pop (E j) ≤ b / 4 := by
      apply (RepairT21_probability_exists_le_sum (P j).pop _).trans
      calc
        _ ≤ ∑ a : Bool, b / 8 := Finset.sum_le_sum fun a ha =>
          (htails (sizes j) (P j) (hP j) a).1.le
        _ = _ := by simp; ring
    have hsize : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
    have hc : 0 < min 1 e / 2 := by positivity
    have hsmalllim : Tendsto (fun j => 1 / (sizes j : ℝ) + C / ((min 1 e / 2) * (sizes j : ℝ)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun j => (1 : ℝ) / (sizes j : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hsize
      have h2 : Tendsto (fun j => C / ((min 1 e / 2) * (sizes j : ℝ))) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (hsize.const_mul_atTop hc)
      simpa only [add_zero] using h1.add h2
    have hsmall := hsmalllim.eventually (eventually_lt_nhds (show 0 < η - ζ by dsimp [ζ]; linarith))
    have hgood := (RepairT21_gramGood_failure_tendsto_zero sizes hsizes k P δ e A B r he hr hP).eventually
      (eventually_lt_nhds (show (0 : ℝ) < b / 4 by positivity))
    have hMevent := hM.eventually (eventually_lt_nhds (show (0 : ℝ) < b / 4 by positivity))
    filter_upwards [hsmall, hgood, hMevent] with j hsmallj hgoodj hMj
    have hsub : ∀ S ∈ assignments (P j).pop,
        |adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S / RepairT21_U (P j) - 1| > η →
        E j S ∨ M j S ∨ ¬ RepairT21_gramGood (P j) e S := by
      intro S hS htail
      by_contra h
      have hEnot : ¬ E j S := fun hE => h (Or.inl hE)
      have hMnot : ¬ M j S := fun hM => h (Or.inr (Or.inl hM))
      have hG : RepairT21_gramGood (P j) e S := by
        by_contra hG
        exact h (Or.inr (Or.inr hG))
      have hR (a : Bool) : |RepairT21_armRSSMean (P j) S a - popVar (residual (P j) a (late (P j).pop))| ≤
          η * popVar (residual (P j) a (late (P j).pop)) := by
        apply RepairT21_armRSSMean_error_le (P j) δ e A B r C ζ η he hC (hP j) S hS hG
          (by linarith) a
        · exact le_of_not_gt (fun hscore => hEnot ⟨a, hscore⟩)
        · cases a
          · exact le_of_not_gt (fun hsq => hMnot (Or.inr hsq))
          · exact le_of_not_gt (fun hsq => hMnot (Or.inl hsq))
      exact not_lt_of_ge (RepairT21_sigma2_relative_error_le (P j) (hP j).1 (hpos j) S η hR) htail
    calc
      _ ≤ probability (P j).pop (fun S => E j S ∨ M j S ∨ ¬ RepairT21_gramGood (P j) e S) :=
        RepairT21_probability_mono (P j).pop hsub
      _ ≤ probability (P j).pop (E j) +
          (probability (P j).pop (M j) + probability (P j).pop (fun S => ¬ RepairT21_gramGood (P j) e S)) :=
        (RepairT21_probability_or_le (P j).pop (E j)
          (fun S => M j S ∨ ¬ RepairT21_gramGood (P j) e S)).trans
          (add_le_add le_rfl (RepairT21_probability_or_le (P j).pop (M j)
            (fun S => ¬ RepairT21_gramGood (P j) e S)))
      _ < b := by linarith [hE j]

theorem RepairT21_q_variance_lower {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1 / 2) (hP : Xi P δ e A B r) :
    (1 - max δ 0) *
      (popVar (residual P true (late P.pop)) / (P.pop.n1 : ℝ) ^ 2 +
        popVar (residual P false (late P.pop)) / (controlSize P.pop) ^ 2) ≤
      popVar (RepairT21_q P) := by
  have hs := RepairT21_design_sizes P.pop hP.1
  have hf : 0 < (P.pop.n1 : ℝ) * controlSize P.pop / (n : ℝ) :=
    div_pos (mul_pos hs.2.1 hs.2.2.1) hs.1
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    _ = (1 - max δ 0) *
        (controlSize P.pop / ((n : ℝ) * (P.pop.n1 : ℝ)) * popVar (residual P true (late P.pop)) +
          (P.pop.n1 : ℝ) / ((n : ℝ) * controlSize P.pop) * popVar (residual P false (late P.pop))) := by
      field_simp [hs.1.ne', hs.2.1.ne', hs.2.2.1.ne'] <;> ring
    _ ≤ RepairT21_V P := corrected_E10_proof P δ e A B r hk hδ he hA hB hr hP
    _ = _ := RepairT21_V_eq_q_variance P δ e A B r he hP

theorem RepairT21_residual_coordinate_sq_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hB : 0 < B) (hP : Xi P δ e A B r) (a : Bool) (i : Fin n) :
    residual P a (late P.pop) i ^ 2 ≤
      B ^ 2 * Real.sqrt (n : ℝ) * popVar (residual P a (late P.pop)) := by
  have hN := (RepairT21_design_sizes P.pop hP.1).1
  have hv := RepairT21_popVar_nonneg hP.1.1 (residual P a (late P.pop))
  have hsum := (div_le_iff₀ hN).mp (RepairT21_residual_fourth_moment P δ e A B r hB hP a)
  have hi : residual P a (late P.pop) i ^ 4 ≤
      ∑ j, residual P a (late P.pop) j ^ 4 :=
    Finset.single_le_sum (f := fun j => residual P a (late P.pop) j ^ 4)
      (fun j hj => by positivity) (Finset.mem_univ i)
  apply (sq_le_sq₀ (sq_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg B) (Real.sqrt_nonneg _)) hv)).mp
  calc
    _ = residual P a (late P.pop) i ^ 4 := by ring
    _ ≤ B ^ 4 * popVar (residual P a (late P.pop)) ^ 2 * (n : ℝ) := hi.trans hsum
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hN.le]; ring

theorem RepairT21_q_maximum_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1 / 2) (hP : Xi P δ e A B r) :
    maximum (fun i => RepairT21_q P i ^ 2) ≤
      (2 * B ^ 2 * Real.sqrt (n : ℝ) / (1 - max δ 0)) * popVar (RepairT21_q P) := by
  have hdelta : 0 < 1 - max δ 0 := sub_pos.mpr (max_lt hδ zero_lt_one)
  have hv := RepairT21_popVar_nonneg hP.1.1 (RepairT21_q P)
  have hw : popVar (residual P true (late P.pop)) / (P.pop.n1 : ℝ) ^ 2 +
      popVar (residual P false (late P.pop)) / (controlSize P.pop) ^ 2 ≤
        popVar (RepairT21_q P) / (1 - max δ 0) := by
    apply (le_div_iff₀ hdelta).mpr
    simpa only [mul_comm] using RepairT21_q_variance_lower P δ e A B r hk hδ he hA hB hr hP
  apply maximum_le _ _ (by positivity)
  intro i
  have h1 := div_le_div_of_nonneg_right
    (RepairT21_residual_coordinate_sq_le P δ e A B r hB hP true i) (sq_nonneg (P.pop.n1 : ℝ))
  have h0 := div_le_div_of_nonneg_right
    (RepairT21_residual_coordinate_sq_le P δ e A B r hB hP false i) (sq_nonneg (controlSize P.pop))
  calc
    _ ≤ 2 * (residual P true (late P.pop) i ^ 2 / (P.pop.n1 : ℝ) ^ 2 +
        residual P false (late P.pop) i ^ 2 / (controlSize P.pop) ^ 2) := by
      dsimp [RepairT21_q]
      have hadd : (residual P true (late P.pop) i / (P.pop.n1 : ℝ) +
          residual P false (late P.pop) i / controlSize P.pop) ^ 2 ≤
          2 * ((residual P true (late P.pop) i / (P.pop.n1 : ℝ)) ^ 2 +
            (residual P false (late P.pop) i / controlSize P.pop) ^ 2) := by
        nlinarith [sq_nonneg (residual P true (late P.pop) i / (P.pop.n1 : ℝ) -
          residual P false (late P.pop) i / controlSize P.pop)]
      simpa only [div_pow] using hadd
    _ ≤ 2 * (B ^ 2 * Real.sqrt (n : ℝ) * popVar (residual P true (late P.pop)) / (P.pop.n1 : ℝ) ^ 2 +
        B ^ 2 * Real.sqrt (n : ℝ) * popVar (residual P false (late P.pop)) / (controlSize P.pop) ^ 2) := by
      linarith
    _ = 2 * B ^ 2 * Real.sqrt (n : ℝ) *
        (popVar (residual P true (late P.pop)) / (P.pop.n1 : ℝ) ^ 2 +
          popVar (residual P false (late P.pop)) / (controlSize P.pop) ^ 2) := by ring
    _ ≤ (2 * B ^ 2 * Real.sqrt (n : ℝ)) * (popVar (RepairT21_q P) / (1 - max δ 0)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

theorem RepairT21_q_maximum_ratio_le {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1 / 2)
    (hP : Xi P δ e A B r) (hpos : 0 < RepairT21_totalScale P) :
    maximum (fun i => (RepairT21_q P i - mean (RepairT21_q P)) ^ 2) /
      (((min P.pop.n1 (n - P.pop.n1) : ℕ) : ℝ) * popVar (RepairT21_q P)) ≤
      2 * B ^ 2 / ((1 - max δ 0) * r * Real.sqrt (n : ℝ)) := by
  have hs := RepairT21_design_sizes P.pop hP.1
  have hdelta : 0 < 1 - max δ 0 := sub_pos.mpr (max_lt hδ zero_lt_one)
  have hv := RepairT21_q_variance_pos P δ e A B r hk hδ he hA hB hr hP hpos
  have hbal : r * (n : ℝ) ≤ ((min P.pop.n1 (n - P.pop.n1) : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_sub hP.1.2.2.le]
    apply le_min hP.2.2.2.1
    have h := hP.2.2.2.2.1
    linarith
  have hmin : 0 < ((min P.pop.n1 (n - P.pop.n1) : ℕ) : ℝ) := (mul_pos hr.1 hs.1).trans_le hbal
  simp only [RepairT21_q_mean_zero P δ e A B r he hP, sub_zero]
  calc
    _ ≤ ((2 * B ^ 2 * Real.sqrt (n : ℝ) / (1 - max δ 0)) * popVar (RepairT21_q P)) /
        (((min P.pop.n1 (n - P.pop.n1) : ℕ) : ℝ) * popVar (RepairT21_q P)) :=
      div_le_div_of_nonneg_right (RepairT21_q_maximum_le P δ e A B r hk hδ he hA hB hr hP)
        (mul_nonneg hmin.le hv.le)
    _ = (2 * B ^ 2 * Real.sqrt (n : ℝ) / (1 - max δ 0)) /
        ((min P.pop.n1 (n - P.pop.n1) : ℕ) : ℝ) := by field_simp
    _ ≤ (2 * B ^ 2 * Real.sqrt (n : ℝ) / (1 - max δ 0)) / (r * (n : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hr.1 hs.1) hbal
    _ = _ := by
      have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hs.1
      have hrootId : Real.sqrt (n : ℝ) / (n : ℝ) = 1 / Real.sqrt (n : ℝ) := by
        apply (div_eq_div_iff hs.1.ne' hroot.ne').mpr
        nlinarith [Real.sq_sqrt hs.1.le]
      calc
        _ = (2 * B ^ 2 / ((1 - max δ 0) * r)) * (Real.sqrt (n : ℝ) / (n : ℝ)) := by
          field_simp [hdelta.ne', hr.1.ne', hs.1.ne'] <;> ring
        _ = _ := by
          rw [hrootId]
          field_simp [hdelta.ne', hr.1.ne', hroot.ne'] <;> ring

theorem RepairT21_maximum_nonneg {n} (q : Fin n → ℝ) : 0 ≤ maximum q := by
  unfold maximum
  apply Finset.le_max'
  exact Finset.mem_insert_self _ _

theorem RepairT21_q_maximum_ratio_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (hP : ∀ j, Xi (P j) δ e A B r)
    (hpos : ∀ j, 0 < RepairT21_totalScale (P j)) :
    Tendsto (fun j => maximum (fun i => (RepairT21_q (P j) i - mean (RepairT21_q (P j))) ^ 2) /
      (((min (P j).pop.n1 (sizes j - (P j).pop.n1) : ℕ) : ℝ) * popVar (RepairT21_q (P j))))
      atTop (nhds 0) := by
  have hsize : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hroot : Tendsto (fun j => Real.sqrt (sizes j : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hsize
  have ht : Tendsto (fun j => (2 * B ^ 2 / ((1 - max δ 0) * r)) / Real.sqrt (sizes j : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hroot
  apply squeeze_zero (fun j => div_nonneg (RepairT21_maximum_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (RepairT21_popVar_nonneg (hP j).1.1 _)))
    (fun j => ?_) ht
  convert RepairT21_q_maximum_ratio_le (P j) δ e A B r hk hδ he hA hB hr (hP j) (hpos j) using 1
  field_simp <;> ring

/-- The finite-population CLT hypothesis, with all its quantifiers. -/
def RepairT21_FinitePopulationCLT : Prop :=
  ∀ (sizes : ℕ → ℕ), StrictMono sizes →
  ∀ (D : ∀ j, Population (sizes j)) (q : ∀ j, Fin (sizes j) → ℝ),
    (∀ j, ValidDesign (D j)) →
    (∀ j, 0 < popVar (q j)) →
    Tendsto (fun j => maximum (fun i => (q j i - mean (q j)) ^ 2) /
      (((min (D j).n1 (sizes j - (D j).n1) : ℕ) : ℝ) * popVar (q j))) atTop (nhds 0) →
    ∀ t : ℝ, Tendsto (fun j => probability (D j) (fun S =>
      (groupMean S (q j) - mean (q j)) /
        Real.sqrt ((1 / ((D j).n1 : ℝ) - 1 / (sizes j : ℝ)) * popVar (q j)) ≤ t))
      atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic t)).toReal))

theorem RepairT21_oracle_standardized {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    oracleTau P (late P.pop) S / Real.sqrt (RepairT21_V P) =
      (groupMean S (RepairT21_q P) - mean (RepairT21_q P)) /
        Real.sqrt ((1 / (P.pop.n1 : ℝ) - 1 / (n : ℝ)) * popVar (RepairT21_q P)) := by
  have hs := RepairT21_design_sizes P.pop hP.1
  have hid : RepairT21_V P = (P.pop.n1 : ℝ) ^ 2 *
      ((1 / (P.pop.n1 : ℝ) - 1 / (n : ℝ)) * popVar (RepairT21_q P)) := by
    rw [RepairT21_V_eq_q_variance P δ e A B r he hP]
    unfold controlSize
    field_simp [hs.1.ne', hs.2.1.ne'] <;> ring
  have hroot : Real.sqrt (RepairT21_V P) = (P.pop.n1 : ℝ) *
      Real.sqrt ((1 / (P.pop.n1 : ℝ) - 1 / (n : ℝ)) * popVar (RepairT21_q P)) := by
    rw [hid, Real.sqrt_mul (sq_nonneg (P.pop.n1 : ℝ)), Real.sqrt_sq hs.2.1.le]
  rw [RepairT21_oracle_as_sample_mean P δ e A B r he hP S hS,
    RepairT21_q_mean_zero P δ e A B r he hP, sub_zero, hroot]
  field_simp [hs.2.1.ne']

/-- The oracle CDF converges under the generic finite-population CLT hypothesis. -/
theorem RepairT21_oracle_cdf_tendsto
    (hFinitePopulationCLT : RepairT21_FinitePopulationCLT)
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (hP : ∀ j, Xi (P j) δ e A B r)
    (hpos : ∀ j, 0 < RepairT21_totalScale (P j)) (t : ℝ) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      oracleTau (P j) (late (P j).pop) S / Real.sqrt (RepairT21_V (P j)) ≤ t))
      atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic t)).toReal)) := by
  have h := hFinitePopulationCLT sizes hsizes (fun j => (P j).pop) (fun j => RepairT21_q (P j))
    (fun j => (hP j).1)
    (fun j => RepairT21_q_variance_pos (P j) δ e A B r hk hδ he hA hB hr (hP j) (hpos j))
    (RepairT21_q_maximum_ratio_tendsto_zero sizes hsizes k P δ e A B r hk hδ he hA hB hr hP hpos) t
  apply h.congr'
  apply Eventually.of_forall
  intro j
  apply RepairT21_probability_congr
  intro S hS
  rw [RepairT21_oracle_standardized (P j) δ e A B r he (hP j) S hS]

theorem RepairT21_probability_not {n} (P : Population n) (hD : ValidDesign P)
    (E : Finset (Fin n) → Prop) : probability P (fun S => ¬ E S) = 1 - probability P E := by
  have hne : (assignments P).Nonempty := Finset.powersetCard_nonempty.mpr
    (by simpa using hD.2.2.le)
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hne)
  have hsum : probability P E + probability P (fun S => ¬ E S) = 1 := by
    unfold probability
    rw [← add_div, ← Nat.cast_add, Finset.card_filter_add_card_filter_not, div_self hcard]
  linarith

theorem RepairT21_abs_tail_le_cdf {n} (P : Population n) (hD : ValidDesign P)
    (X : Finset (Fin n) → ℝ) (s : ℝ) :
    probability P (fun S => |X S| > s) ≤
      probability P (fun S => X S ≤ -s) + 1 - probability P (fun S => X S ≤ s) := by
  calc
    _ ≤ probability P (fun S => X S ≤ -s ∨ ¬ X S ≤ s) := by
      apply RepairT21_probability_mono
      intro S hS htail
      rcases lt_abs.mp htail with h | h
      · exact Or.inr (not_le_of_gt h)
      · exact Or.inl (by linarith)
    _ ≤ probability P (fun S => X S ≤ -s) + probability P (fun S => ¬ X S ≤ s) :=
      RepairT21_probability_or_le P _ _
    _ = _ := by rw [RepairT21_probability_not P hD]; ring

/-- Deterministic conservative studentization, including the zero-denominator convention. -/
theorem RepairT21_student_tail_imp (N T S V U t η : ℝ)
    (hV : 0 < V) (hVU : V ≤ U) (ht : 0 < t) (hη : 0 < η) (hη1 : η < 1)
    (hN : |N - T| ≤ η * Real.sqrt V) (hS : |S / U - 1| ≤ η)
    (htail : absStudent N S > ENNReal.ofReal t) :
    t * (1 - η) - η < |T| / Real.sqrt V := by
  have hU : 0 < U := hV.trans_le hVU
  have hc : 0 < 1 - η := sub_pos.mpr hη1
  have hslow : (1 - η) * U ≤ S := by
    apply (le_div_iff₀ hU).mp
    linarith [(abs_le.mp hS).1]
  have hSpos : 0 < S := (mul_pos hc hU).trans_le hslow
  have hrootV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hrootS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  have hsq : ((1 - η) * Real.sqrt V) ^ 2 ≤ S := by
    rw [mul_pow, Real.sq_sqrt hV.le]
    calc
      _ ≤ (1 - η) * V := mul_le_mul_of_nonneg_right (by nlinarith : (1 - η) ^ 2 ≤ 1 - η) hV.le
      _ ≤ (1 - η) * U := mul_le_mul_of_nonneg_left hVU hc.le
      _ ≤ S := hslow
  have hroot : (1 - η) * Real.sqrt V ≤ Real.sqrt S := by
    apply (sq_le_sq₀ (mul_nonneg hc.le hrootV.le) hrootS.le).mp
    rw [Real.sq_sqrt hSpos.le]
    exact hsq
  by_contra h
  have hT : |T| ≤ (t * (1 - η) - η) * Real.sqrt V :=
    (div_le_iff₀ hrootV).mp (le_of_not_gt h)
  have htriangle : |N| ≤ |T| + |N - T| := by
    calc
      _ = |T + (N - T)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hNum : |N| ≤ t * Real.sqrt S := by
    calc
      _ ≤ t * ((1 - η) * Real.sqrt V) := by nlinarith [htriangle, hN, hT]
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot ht.le
  have hAR : absStudent N S ≤ ENNReal.ofReal t := by
    rw [absStudent, if_neg hSpos.ne']
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hrootS).mpr hNum)
  exact not_lt_of_ge hAR htail

/-- Positive-scale sequential upper tail, stated as an eventual bound at every larger level. -/
theorem RepairT21_positive_tail_eventually_lt
    (hFinitePopulationCLT : RepairT21_FinitePopulationCLT)
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (hP : ∀ j, Xi (P j) δ e A B r)
    (hpos : ∀ j, 0 < RepairT21_totalScale (P j)) (t b : ℝ)
    (ht : 0 < t) (hb : normalTail t < b) :
    ∀ᶠ j in atTop, probability (P j).pop (fun S =>
      adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S) S > ENNReal.ofReal t) < b := by
  have hs : Tendsto (fun η : ℝ => t * (1 - η) - η) (nhds 0) (nhds t) := by
    have hcont : ContinuousAt (fun η : ℝ => t * (1 - η) - η) 0 := by fun_prop
    simpa using hcont.tendsto
  have htail := (RepairT21_normalTail_continuousAt t ht).tendsto.comp hs
  have hchoose : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < η ∧ η < 1 ∧ 0 < t * (1 - η) - η ∧ normalTail (t * (1 - η) - η) < b := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      (hs.mono_left nhdsWithin_le_nhds).eventually (eventually_gt_nhds ht),
      (htail.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hb)] with η h0 h1 hs htail
    exact ⟨h0, h1, hs, htail⟩
  obtain ⟨η, hη, hη1, hspos, hsb⟩ := hchoose.exists
  let s := t * (1 - η) - η
  let E := fun j S => |adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S -
    oracleTau (P j) (late (P j).pop) S| > η * Real.sqrt (RepairT21_V (P j))
  let F := fun j S => |adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S /
    RepairT21_U (P j) - 1| > η
  let X := fun j S => oracleTau (P j) (late (P j).pop) S / Real.sqrt (RepairT21_V (P j))
  have hE : Tendsto (fun j => probability (P j).pop (E j)) atTop (nhds 0) :=
    RepairT21_numerator_tendsto_zero sizes hsizes k P δ e A B r hk hδ he hA hB hr hP hpos η hη
  have hF : Tendsto (fun j => probability (P j).pop (F j)) atTop (nhds 0) :=
    RepairT21_denominator_tendsto_zero sizes hsizes k P δ e A B r he hB hr.1 hP hpos η hη
  have hneg := RepairT21_oracle_cdf_tendsto hFinitePopulationCLT sizes hsizes k P δ e A B r hk hδ he hA hB hr hP hpos (-s)
  have hposCDF := RepairT21_oracle_cdf_tendsto hFinitePopulationCLT sizes hsizes k P δ e A B r hk hδ he hA hB hr hP hpos s
  have hnormal : (ProbabilityTheory.gaussianReal 0 1 (Set.Iic (-s))).toReal + 1 -
      (ProbabilityTheory.gaussianReal 0 1 (Set.Iic s)).toReal = normalTail s := by
    have hn := AronowAudit.P053.NormalCompletion.normal_cdf_neg s
    simp only [ProbabilityTheory.cdf_eq_real, measureReal_def] at hn
    rw [RepairT21_normalTail_formula s hspos]
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
    linarith
  have hmajor : Tendsto (fun j => probability (P j).pop (E j) + probability (P j).pop (F j) +
      (probability (P j).pop (fun S => X j S ≤ -s) + 1 - probability (P j).pop (fun S => X j S ≤ s)))
      atTop (nhds (normalTail s)) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa only [zero_add, add_zero, hnormal] using (hE.add hF).add ((hneg.add hc).sub hposCDF)
  filter_upwards [hmajor.eventually (eventually_lt_nhds hsb)] with j hj
  have hv := RepairT21_V_pos (P j) δ e A B r hk hδ he hA hB hr (hP j) (hpos j)
  have hsub : ∀ S ∈ assignments (P j).pop,
      adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S) S > ENNReal.ofReal t →
      E j S ∨ F j S ∨ |X j S| > s := by
    intro S hS hAR
    by_contra h
    have hEnot : ¬ E j S := fun hevent => h (Or.inl hevent)
    have hFnot : ¬ F j S := fun hevent => h (Or.inr (Or.inl hevent))
    have hXnot : ¬ |X j S| > s := fun hevent => h (Or.inr (Or.inr hevent))
    have htail := RepairT21_student_tail_imp _ _ _ _ _ t η hv
      (RepairT21_V_le_U (P j) δ e A B r he (hP j)) ht hη hη1
      (le_of_not_gt hEnot) (le_of_not_gt hFnot) hAR
    have hroot : 0 < Real.sqrt (RepairT21_V (P j)) := Real.sqrt_pos.mpr hv
    have hbound : |oracleTau (P j) (late (P j).pop) S| / Real.sqrt (RepairT21_V (P j)) ≤ s := by
      simpa only [X, abs_div, abs_of_pos hroot] using le_of_not_gt hXnot
    exact not_lt_of_ge hbound htail
  calc
    _ ≤ probability (P j).pop (fun S => E j S ∨ F j S ∨ |X j S| > s) :=
      RepairT21_probability_mono (P j).pop hsub
    _ ≤ probability (P j).pop (E j) +
        (probability (P j).pop (F j) + probability (P j).pop (fun S => |X j S| > s)) :=
      (RepairT21_probability_or_le (P j).pop (E j) (fun S => F j S ∨ |X j S| > s)).trans
        (add_le_add le_rfl (RepairT21_probability_or_le (P j).pop (F j) (fun S => |X j S| > s)))
    _ ≤ probability (P j).pop (E j) + probability (P j).pop (F j) +
        (probability (P j).pop (fun S => X j S ≤ -s) + 1 - probability (P j).pop (fun S => X j S ≤ s)) := by
      have hb := RepairT21_abs_tail_le_cdf (P j).pop (hP j).1 (X j) s
      linarith
    _ < b := hj

theorem RepairT21_normalTail_nonneg (t : ℝ) : 0 ≤ normalTail t := ENNReal.toReal_nonneg

/-- Arbitrary selected sequences can mix positive total scale and zero total scale. -/
theorem RepairT21_selected_tail_eventually_lt
    (hFinitePopulationCLT : RepairT21_FinitePopulationCLT)
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (hP : ∀ j, Xi (P j) δ e A B r)
    (t b : ℝ) (ht : 0 < t) (hb : normalTail t < b) :
    ∀ᶠ j in atTop, probability (P j).pop (fun S =>
      adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S) S > ENNReal.ofReal t) < b := by
  have hbpos : 0 < b := (RepairT21_normalTail_nonneg t).trans_lt hb
  by_contra h
  have hbad : ∃ᶠ j in atTop, b ≤ probability (P j).pop (fun S =>
      adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S) S > ENNReal.ofReal t) := by
    simpa only [not_eventually, not_lt] using h
  obtain ⟨sub, hsub, hviol⟩ := extraction_of_frequently_atTop hbad
  by_cases hz : ∃ᶠ j in atTop, RepairT21_totalScale (P (sub j)) = 0
  · obtain ⟨z, hzmono, hzall⟩ := extraction_of_frequently_atTop hz
    have hlim := RepairT21_zero_scale_tail_tendsto_zero
      (fun j => sizes (sub (z j))) (hsizes.comp (hsub.comp hzmono)) k
      (fun j => P (sub (z j))) δ e A B r he hA hr.1
      (fun j => hP (sub (z j))) hzall t
    obtain ⟨j, hj⟩ := (hlim.eventually (eventually_lt_nhds hbpos)).exists
    exact not_lt_of_ge (hviol (z j)) hj
  · have hne : ∀ᶠ j in atTop, 0 < RepairT21_totalScale (P (sub j)) := by
      filter_upwards [not_frequently.mp hz] with j hj
      have hnon : 0 ≤ RepairT21_totalScale (P (sub j)) :=
        add_nonneg (RepairT21_popVar_nonneg (hP (sub j)).1.1 _)
          (RepairT21_popVar_nonneg (hP (sub j)).1.1 _)
      exact lt_of_le_of_ne hnon (Ne.symm hj)
    obtain ⟨z, hzmono, hzall⟩ := extraction_of_eventually_atTop hne
    have hlim := RepairT21_positive_tail_eventually_lt hFinitePopulationCLT
      (fun j => sizes (sub (z j))) (hsizes.comp (hsub.comp hzmono)) k
      (fun j => P (sub (z j))) δ e A B r hk hδ he hA hB hr
      (fun j => hP (sub (z j))) hzall t b ht hb
    obtain ⟨j, hj⟩ := hlim.exists
    exact not_lt_of_ge (hviol (z j)) hj

def RepairT21_supTail (n k : ℕ) (δ e A B r t : ℝ) : ℝ≥0∞ :=
  ⨆ P : {P : CovPopulation n k // Xi P δ e A B r},
    ENNReal.ofReal (probability P.val.pop (fun S =>
      adjustedAR P.val (observedW P.val.pop (late P.val.pop) S) S > ENNReal.ofReal t))

/-- Approximate supremum selection uses actual models only at violating sizes. -/
theorem RepairT21_uniform_tail_eventually_le
    (hFinitePopulationCLT : RepairT21_FinitePopulationCLT)
    (k : ℕ) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (t b : ℝ) (ht : 0 < t) (hb : normalTail t < b) :
    ∀ᶠ n in atTop, RepairT21_supTail n k δ e A B r t ≤ ENNReal.ofReal b := by
  have hbpos : 0 < b := (RepairT21_normalTail_nonneg t).trans_lt hb
  by_contra h
  have hbad : ∃ᶠ n in atTop, ENNReal.ofReal b < RepairT21_supTail n k δ e A B r t := by
    simpa only [not_eventually, not_le] using h
  obtain ⟨sizes, hsizes, hviol⟩ := extraction_of_frequently_atTop hbad
  have hpick : ∀ j, ∃ P : {P : CovPopulation (sizes j) k // Xi P δ e A B r},
      b < probability P.val.pop (fun S =>
        adjustedAR P.val (observedW P.val.pop (late P.val.pop) S) S > ENNReal.ofReal t) := by
    intro j
    obtain ⟨P, hP⟩ := lt_iSup_iff.mp (hviol j)
    exact ⟨P, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hbpos.le).mp hP⟩
  choose Q hQ using hpick
  have hseq := RepairT21_selected_tail_eventually_lt hFinitePopulationCLT sizes hsizes k
    (fun j => (Q j).val) δ e A B r hk hδ he hA hB hr (fun j => (Q j).property) t b ht hb
  obtain ⟨j, hj⟩ := hseq.exists
  exact not_lt_of_ge (hQ j).le hj

theorem RepairT21_uniform_tail_limsup_le
    (hFinitePopulationCLT : RepairT21_FinitePopulationCLT)
    (k : ℕ) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (t : ℝ) (ht : 0 < t) :
    Filter.limsup (fun n => RepairT21_supTail n k δ e A B r t) atTop ≤ ENNReal.ofReal (normalTail t) := by
  have hbound (ε : ℝ) (hε : 0 < ε) :
      Filter.limsup (fun n => RepairT21_supTail n k δ e A B r t) atTop ≤
        ENNReal.ofReal (normalTail t + ε) := by
    exact limsup_le_of_le (by isBoundedDefault)
      (RepairT21_uniform_tail_eventually_le hFinitePopulationCLT k δ e A B r hk hδ he hA hB hr
        t (normalTail t + ε) ht (by linarith))
  have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (normalTail t + ε)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (normalTail t + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (normalTail t))) := by
    simpa only [add_zero] using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  have hevent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Filter.limsup (fun n => RepairT21_supTail n k δ e A B r t) atTop ≤
        ENNReal.ofReal (normalTail t + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hbound ε hε
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hevent

theorem RepairT21_supAdjustedTail_eq_supTail (n k : ℕ) (δ e A B r α κ : ℝ)
    (ht : 0 ≤ normalCritical α - κ) :
    supAdjustedTail n k δ e A B r α κ = RepairT21_supTail n k δ e A B r (normalCritical α - κ) := by
  rw [RepairT21_supAdjustedTail_eq]
  simp only [not_lt_of_ge ht, false_or, RepairT21_supTail]

theorem corrected_theorem7_limsup_of_finitePopulationCLT
    (hFinitePopulationCLT :
      ∀ (sizes : ℕ → ℕ), StrictMono sizes →
      ∀ (D : ∀ j, Population (sizes j))
        (q : ∀ j, Fin (sizes j) → ℝ),
        (∀ j, ValidDesign (D j)) →
        (∀ j, 0 < popVar (q j)) →
        Tendsto (fun j =>
          maximum (fun i => (q j i - mean (q j)) ^ 2) /
            (((min (D j).n1 (sizes j - (D j).n1) : ℕ) : ℝ) *
              popVar (q j))) atTop (nhds 0) →
        ∀ t : ℝ, Tendsto (fun j => probability (D j) (fun S =>
          (groupMean S (q j) - mean (q j)) /
            Real.sqrt ((1 / ((D j).n1 : ℝ) - 1 / (sizes j : ℝ)) *
              popVar (q j)) ≤ t))
          atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic t)).toReal)))
    (k : ℕ) (δ e A B r α : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hα : 0 < α ∧ α < 1) :
    ∃ u : ℝ≥0∞,
      Tendsto (fun κ : ℝ => Filter.limsup
        (fun n : ℕ => supAdjustedTail n k δ e A B r α κ) atTop)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds u) ∧
      u ≤ ENNReal.ofReal α := by
  obtain ⟨u, hu, _⟩ := RepairT21_outer_limit_exists k δ e A B r α
  have hq := RepairT21_normalCritical_pos α hα
  have hlocal : ∀ᶠ κ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Filter.limsup (fun n : ℕ => supAdjustedTail n k δ e A B r α κ) atTop ≤
        ENNReal.ofReal (normalTail (normalCritical α - κ)) := by
    filter_upwards [(eventually_lt_nhds hq).filter_mono nhdsWithin_le_nhds] with κ hκ
    have ht : 0 < normalCritical α - κ := sub_pos.mpr hκ
    simpa only [RepairT21_supAdjustedTail_eq_supTail _ _ _ _ _ _ _ _ _ ht.le] using
      RepairT21_uniform_tail_limsup_le hFinitePopulationCLT k δ e A B r hk hδ he hA hB hr
        (normalCritical α - κ) ht
  have hsub : Tendsto (fun κ : ℝ => normalCritical α - κ) (nhds 0) (nhds (normalCritical α)) := by
    have hc : ContinuousAt (fun κ : ℝ => normalCritical α - κ) 0 := by fun_prop
    simpa only [sub_zero] using hc.tendsto
  have htail : Tendsto (fun κ : ℝ => ENNReal.ofReal (normalTail (normalCritical α - κ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal α)) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp
      ((RepairT21_normalTail_continuousAt _ hq).tendsto.comp hsub)
    rw [RepairT21_normalTail_critical α hα] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ⟨u, hu, le_of_tendsto_of_tendsto hu htail hlocal⟩


end
end AronowAudit.P002.Wave1
