import AronowAudit.P006.Wave1.Gap.GLP006B2
import Mathlib.Probability.Independence.Integration

/-! The exact finite-sample ATT identity and corrected ATT regret. -/
namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section
local instance GP006B2b_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

lemma GP006B2b_count_nonneg {n : ℕ} (T : Fin n → Bool) : 0 ≤ treatedCount T := by
  unfold treatedCount
  exact Finset.sum_nonneg fun i _ => by cases T i <;> norm_num [bit]

lemma GP006B2b_count_zero_iff {n : ℕ} (T : Fin n → Bool) :
    treatedCount T = 0 ↔ T = fun _ => false := by
  constructor
  · intro h
    funext i
    have hi : bit (T i) ≤ treatedCount T := by
      unfold treatedCount
      exact Finset.single_le_sum (f := fun j => bit (T j))
        (fun j _ => by cases T j <;> norm_num [bit]) (Finset.mem_univ i)
    cases ht : T i
    · rfl
    · norm_num [ht, bit, h] at hi
  · rintro rfl
    simp [treatedCount, bit]

lemma GP006B2b_nonempty_mass (n : ℕ) (q : ℝ) :
    (∑ T : Fin n → Bool,
      if 0 < treatedCount T then ∏ i, coinMass q (T i) else 0) =
      1 - (1-q)^n := by
  have total : (∑ T : Fin n → Bool, ∏ i, coinMass q (T i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [coinMass, Fintype.sum_bool]
  have pos (T : Fin n → Bool) :
      0 < treatedCount T ↔ T ≠ (fun _ => false) := by
    constructor
    · intro hp he
      have hz := (GP006B2b_count_zero_iff T).mpr he
      linarith
    · intro hne
      have hz : treatedCount T ≠ 0 := fun hz => hne ((GP006B2b_count_zero_iff T).mp hz)
      exact lt_of_le_of_ne (GP006B2b_count_nonneg T) (Ne.symm hz)
  have split :
      (∑ T : Fin n → Bool, ∏ i, coinMass q (T i)) =
        (∑ T : Fin n → Bool,
          if 0 < treatedCount T then ∏ i, coinMass q (T i) else 0) +
        (1-q)^n := by
    have each (T : Fin n → Bool) :
        (∏ i, coinMass q (T i)) =
          (if T ≠ (fun _ => false) then ∏ i, coinMass q (T i) else 0) +
          (if T = (fun _ => false) then (1-q)^n else 0) := by
      by_cases hT : T = (fun _ => false)
      · subst T
        simp [coinMass]
      · simp [hT]
    calc
      _ = ∑ T : Fin n → Bool,
          ((if T ≠ (fun _ => false) then ∏ i, coinMass q (T i) else 0) +
          (if T = (fun _ => false) then (1-q)^n else 0)) := by
        exact Finset.sum_congr rfl (fun T _ => each T)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp_rw [pos]
        simp
  linarith

lemma GP006B2b_geometric (n : ℕ) (q : ℝ) :
    q * emptyFactor n q = 1 - (1-q)^n := by
  induction n with
  | zero => simp [emptyFactor]
  | succ n ih =>
      rw [emptyFactor, Finset.sum_range_succ, mul_add]
      change q * emptyFactor n q + q * (1-q)^n = _
      rw [ih, pow_succ]
      ring

/-- Coefficient of one mark in the zero-on-empty average. -/
def GP006B2b_coeff {n : ℕ} (t : Fin n → Bool) (i : Fin n) : ℝ :=
  if 0 < treatedCount t then bit (t i) / treatedCount t else 0

lemma GP006B2b_coeff_bound {n : ℕ} (t : Fin n → Bool) (i : Fin n) :
    ‖GP006B2b_coeff t i‖ ≤ 1 := by
  have hb : 0 ≤ bit (t i) := by cases t i <;> norm_num [bit]
  have hle : bit (t i) ≤ treatedCount t := by
    exact Finset.single_le_sum (f := fun j => bit (t j))
      (fun j _ => by cases t j <;> norm_num [bit]) (Finset.mem_univ i)
  unfold GP006B2b_coeff
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb h.le)]
    exact (div_le_one h).mpr hle
  · norm_num

lemma GP006B2b_average_sum {n : ℕ} (t : Fin n → Bool) (d : Fin n → ℝ) :
    wATO t d = ∑ i, GP006B2b_coeff t i * d i := by
  by_cases h : 0 < treatedCount t
  · simp only [wATO, GP006B2b_coeff, if_pos h, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [wATO, GP006B2b_coeff, h]

/-- Independent marked Bernoulli observations: the exact zero-on-empty average. -/
lemma GP006B2b_marked_average {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (D : Fin n → Ω → ℝ) (T : Fin n → Ω → Bool)
    (hmD : ∀ i, Measurable (D i)) (hmT : ∀ i, Measurable (T i))
    (hiD : ∀ i, Integrable (D i) P)
    (hI : iIndepFun (fun i ω => (D i ω, T i ω)) P)
    (q r : ℝ)
    (hbit : ∀ i, (∫ ω, bit (T i ω) ∂P) = q)
    (hmark : ∀ i, (∫ ω, D i ω * bit (T i ω) ∂P) = q*r) :
    (∫ ω, wATO (fun i => T i ω) (fun i => D i ω) ∂P) =
      emptyFactor n q * (q*r) := by
  let S : Ω → (Fin n → Bool) := fun ω i => T i ω
  have hS : Measurable S := measurable_pi_lambda hmT
  have hmass (i : Fin n) (b : Bool) :
      (∫ ω, if T i ω = b then (1 : ℝ) else 0 ∂P) = coinMass q b := by
    cases b
    · have heq : (fun ω => if T i ω = false then (1 : ℝ) else 0) =
          (fun ω => 1 - bit (T i ω)) := by
        funext ω; cases T i ω <;> norm_num [bit]
      rw [heq, integral_sub (f := fun _ : Ω => (1 : ℝ))
        (g := fun ω => bit (T i ω)) (integrable_const 1)
        ((integrable_const (1 : ℝ)).mono'
          ((measurable_of_finite bit).comp (hmT i)).aestronglyMeasurable
          (ae_of_all _ (fun ω => T6_bit_norm _))), hbit]
      simp [coinMass]
    · have heq : (fun ω => if T i ω = true then (1 : ℝ) else 0) =
          (fun ω => bit (T i ω)) := by
        funext ω; cases T i ω <;> norm_num [bit]
      rw [heq, hbit]
      rfl
  have hpattern (t : Fin n → Bool) (i : Fin n) :
      (∫ ω, (if S ω = t then (1 : ℝ) else 0) *
        (D i ω * bit (t i)) ∂P) =
        (∏ j, coinMass q (t j)) * (r * bit (t i)) := by
    let F : Fin n → ℝ × Bool → ℝ := fun j z =>
      (if z.2 = t j then (1 : ℝ) else 0) *
        (if j = i then z.1 * bit (t i) else 1)
    have hmF (j : Fin n) : Measurable (F j) := by
      dsimp only [F]
      apply Measurable.mul
      · exact (measurable_of_finite (fun b : Bool => if b = t j then (1 : ℝ) else 0)).comp
          measurable_snd
      · by_cases h : j = i
        · simp only [if_pos h]; fun_prop
        · simp only [if_neg h]; exact measurable_const
    have heach (j : Fin n) :
        (∫ ω, F j (D j ω, T j ω) ∂P) =
          coinMass q (t j) * (if j = i then r * bit (t i) else 1) := by
      by_cases hj : j = i
      · subst j
        cases ht : t i
        · simp [F, ht, bit]
        · have heq : (fun ω => F i (D i ω, T i ω)) =
              (fun ω => D i ω * bit (T i ω)) := by
            funext ω
            cases T i ω <;> simp [F, ht, bit]
          rw [heq, hmark]
          simp [ht, coinMass, bit]
      · simpa [F, hj] using hmass j (t j)
    have heq (ω : Ω) :
        (∏ j, F j (D j ω, T j ω)) =
          (if S ω = t then (1 : ℝ) else 0) * (D i ω * bit (t i)) := by
      dsimp only [F]
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
      congr 1
      by_cases h : S ω = t
      · have hh (j : Fin n) : T j ω = t j := congrFun h j
        simp [hh, h]
      · have hh : ∃ j, T j ω ≠ t j := by
          by_contra! hh
          exact h (funext hh)
        obtain ⟨j, hj⟩ := hh
        rw [if_neg h]
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    calc
      _ = ∫ ω, ∏ j, F j (D j ω, T j ω) ∂P := by simp_rw [heq]
      _ = ∏ j, ∫ ω, F j (D j ω, T j ω) ∂P :=
        hI.integral_fun_prod_comp (fun j => ((hmD j).prodMk (hmT j)).aemeasurable)
          (fun j => (hmF j).aestronglyMeasurable)
      _ = _ := by simp_rw [heach]; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  have hint (t : Fin n → Bool) (i : Fin n) :
      Integrable (fun ω => (if S ω = t then (1 : ℝ) else 0) *
        (D i ω * bit (t i))) P := by
    exact (hiD i |>.mul_const _).bdd_mul (c := 1)
      (((measurable_of_finite (fun u : Fin n → Bool => if u = t then (1 : ℝ) else 0)).comp
        hS).aestronglyMeasurable)
      (ae_of_all _ (fun ω => by split_ifs <;> norm_num))
  have hfixed (t : Fin n → Bool) :
      (∫ ω, if S ω = t then wATO t (fun i => D i ω) else 0 ∂P) =
        (if 0 < treatedCount t then r else 0) * ∏ j, coinMass q (t j) := by
    by_cases ht : 0 < treatedCount t
    · have heq (ω : Ω) :
          (if S ω = t then wATO t (fun i => D i ω) else 0) =
            (∑ i, (if S ω = t then (1 : ℝ) else 0) *
              (D i ω * bit (t i))) / treatedCount t := by
        by_cases h : S ω = t <;> simp [wATO, ht, h, Finset.mul_sum]
      simp_rw [heq]
      rw [integral_div, integral_finset_sum _ (fun i _ => hint t i)]
      simp_rw [hpattern]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      change ((∏ j, coinMass q (t j)) * (r * treatedCount t)) / treatedCount t = _
      rw [if_pos ht]
      field_simp [ne_of_gt ht]
      <;> ring
    · simp [wATO, ht]
  have hintfixed (t : Fin n → Bool) :
      Integrable (fun ω => if S ω = t then wATO t (fun i => D i ω) else 0) P := by
    have heq : (fun ω => if S ω = t then wATO t (fun i => D i ω) else 0) =
        (fun ω => ∑ i, GP006B2b_coeff t i *
          ((if S ω = t then (1 : ℝ) else 0) * (D i ω * bit (t i)))) := by
      funext ω
      by_cases h : S ω = t
      · simp only [if_pos h, one_mul]
        rw [GP006B2b_average_sum]
        apply Finset.sum_congr rfl
        intro i _
        cases ht : t i <;> simp [GP006B2b_coeff, bit, ht]
      · simp [h]
    rw [heq]
    exact integrable_finset_sum _ (fun i _ => (hint t i).const_mul _)
  have heq (ω : Ω) : wATO (fun i => T i ω) (fun i => D i ω) =
      ∑ t : Fin n → Bool, if S ω = t then wATO t (fun i => D i ω) else 0 := by
    simp [S]
  simp_rw [heq]
  rw [integral_finset_sum _ (fun t _ => hintfixed t)]
  simp_rw [hfixed]
  have hterm (t : Fin n → Bool) :
      (if 0 < treatedCount t then r else 0) * ∏ j, coinMass q (t j) =
        r * (if 0 < treatedCount t then ∏ j, coinMass q (t j) else 0) := by
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, GP006B2b_nonempty_mass, ← GP006B2b_geometric]
  ring

/-- Vector-unbiased baselines can be replaced inside the actual sample average. -/
lemma GP006B2b_replace_baseline {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π)
    (hU : ∀ i, (E.law π)[fun ω => E.μhat π ω (E.X i ω) | E.vectorSigma π]
      =ᵐ[E.law π] fun ω => E.μ0 (E.X i ω)) :
    E.expectedATT π =
      ∫ ω, wATO (fun i => E.T π i ω)
        (fun i => E.Y1 i ω - E.μ0 (E.X i ω)) ∂E.law π := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  let S : Ω → Fin n → Bool := fun ω i => E.T π i ω
  let V : Ω → (Fin n → C) × (Fin n → Bool) :=
    fun ω => ((fun i => E.X i ω), S ω)
  have hV : Measurable V :=
    (measurable_pi_lambda (fun i => (hS.measurable_units π hπ i).1)).prodMk
      (measurable_pi_lambda (fun i => (hS.measurable_units π hπ i).2.2.2))
  have hvle : E.vectorSigma π ≤ ‹MeasurableSpace Ω› := hV.comap_le
  have hSv : Measurable[E.vectorSigma π] S :=
    measurable_snd.comp (comap_measurable V)
  have hcm (i : Fin n) : Measurable[E.vectorSigma π]
      (fun ω => GP006B2b_coeff (S ω) i) :=
    (measurable_of_finite (fun t => GP006B2b_coeff t i)).comp hSv
  have hci (i : Fin n) {f : Ω → ℝ} (hf : Integrable f (E.law π)) :
      Integrable (fun ω => GP006B2b_coeff (S ω) i * f ω) (E.law π) :=
    hf.bdd_mul ((hcm i).mono hvle le_rfl).aestronglyMeasurable
      (ae_of_all _ (fun ω => GP006B2b_coeff_bound (S ω) i))
  have hGi (i : Fin n) : Integrable (fun ω => E.μ0 (E.X i ω)) (E.law π) :=
    (T6_law_transport E hS hπ i hS.means_measurable.1 hS.means_integrable.1).1
  have hcancel (i : Fin n) :
      (∫ ω, GP006B2b_coeff (S ω) i * E.μhat π ω (E.X i ω) ∂E.law π) =
        ∫ ω, GP006B2b_coeff (S ω) i * E.μ0 (E.X i ω) ∂E.law π := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (hcm i).stronglyMeasurable (hci i (hS.integrable_units π hπ i).2.2)
      (hS.integrable_units π hπ i).2.2
    rw [← integral_condExp hvle]
    apply integral_congr_ae
    filter_upwards [hpull, hU i] with ω hp hu
    exact hp.trans (congrArg (fun z => GP006B2b_coeff (S ω) i * z) hu)
  have hsutva (ω : Ω) :
      wATT (E.μhat π ω) (fun i => E.X i ω) (S ω) (E.observed π ω) =
        wATO (S ω) (fun i => E.Y1 i ω - E.μhat π ω (E.X i ω)) :=
    (realized_rewards_SUTVA (E.μhat π ω) (fun _ => 1)
      (fun i => E.X i ω) (S ω) (fun i => E.Y0 i ω) (fun i => E.Y1 i ω)).2.1
  unfold Experiment.expectedATT
  change (∫ ω, wATT (E.μhat π ω) (fun i => E.X i ω) (S ω)
    (E.observed π ω) ∂E.law π) = _
  simp_rw [hsutva, GP006B2b_average_sum]
  rw [integral_finset_sum (f := fun i ω => GP006B2b_coeff (S ω) i *
      (E.Y1 i ω - E.μhat π ω (E.X i ω))) _ (fun i _ => by
        exact hci i ((hS.integrable_units π hπ i).2.1.sub
          (hS.integrable_units π hπ i).2.2)),
    integral_finset_sum (f := fun i ω => GP006B2b_coeff (S ω) i *
      (E.Y1 i ω - E.μ0 (E.X i ω))) _ (fun i _ => by
        exact hci i ((hS.integrable_units π hπ i).2.1.sub (hGi i)))]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_sub]
  rw [integral_sub (hci i (hS.integrable_units π hπ i).2.1)
      (hci i (hS.integrable_units π hπ i).2.2),
    integral_sub (hci i (hS.integrable_units π hπ i).2.1) (hci i (hGi i)), hcancel]

/-- The treated potential gain has the population weighted-gain mean. -/
lemma GP006B2b_mark_mean {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π) (i : Fin n) :
    (∫ ω, (E.Y1 i ω - E.μ0 (E.X i ω)) * bit (E.T π i ω) ∂E.law π) =
      E.A E.τ π := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  have hu := hS.measurable_units π hπ i
  have hi := hS.integrable_units π hπ i
  have hm : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hu.1.comap_le
  have hG := T6_law_transport E hS hπ i hS.means_measurable.1 hS.means_integrable.1
  have hbit : Integrable (fun ω => bit (E.T π i ω)) (E.law π) :=
    T6_mul_integrable ((measurable_of_finite bit).comp hu.2.2.2)
      (fun ω => T6_bit_norm _) (integrable_const 1) |>.congr (by simp)
  have hprod : Integrable (fun ω => bit (E.T π i ω) * E.μ0 (E.X i ω))
      (E.law π) := T6_mul_integrable ((measurable_of_finite bit).comp hu.2.2.2)
    (fun ω => T6_bit_norm _) hG.1
  have hceG : (E.law π)[fun ω => bit (E.T π i ω) * E.μ0 (E.X i ω) |
      E.covariateSigma i] =ᵐ[E.law π]
        fun ω => π (E.X i ω) * E.μ0 (E.X i ω) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (m := E.covariateSigma i)
      (f := fun ω => E.μ0 (E.X i ω)) (g := fun ω => bit (E.T π i ω))
      (hS.means_measurable.1.comp (comap_measurable (E.X i))).stronglyMeasurable
      (by simpa only [Pi.mul_def, mul_comm] using hprod) hbit
    filter_upwards [hpull, hS.bernoulli π hπ i] with ω hp hb
    change (E.law π)[fun η => E.μ0 (E.X i η) * bit (E.T π i η) |
      E.covariateSigma i] ω = E.μ0 (E.X i ω) *
        (E.law π)[fun η => bit (E.T π i η) | E.covariateSigma i] ω at hp
    rw [hb] at hp
    simpa only [mul_comm] using hp
  have hY : Integrable (fun ω => bit (E.T π i ω) * E.Y1 i ω)
      (E.law π) := T6_mul_integrable ((measurable_of_finite bit).comp hu.2.2.2)
    (fun ω => T6_bit_norm _) hi.2.1
  have hce := condExp_sub hY hprod (E.covariateSigma i)
  have heq : (fun ω => (E.Y1 i ω - E.μ0 (E.X i ω)) * bit (E.T π i ω)) =
      ((fun ω => bit (E.T π i ω) * E.Y1 i ω) -
        (fun ω => bit (E.T π i ω) * E.μ0 (E.X i ω))) := by
    funext ω; simp only [Pi.sub_apply]; ring
  rw [heq, ← integral_condExp hm]
  calc
    _ = ∫ ω, π (E.X i ω) * E.τ (E.X i ω) ∂E.law π := by
      apply integral_congr_ae
      filter_upwards [hce, hceG, (T6_unit_outcome_moments E hS hπ i).2]
        with ω hc hg hy
      simpa only [Pi.sub_apply, hg, hy, Experiment.τ, mul_sub] using hc
    _ = ∫ x, π x * E.τ x ∂E.PX :=
      ((hS.covariate_law π hπ i).comp
        (show Measurable (fun x => π x * E.τ x) from
          hπ.1.mul (hS.means_measurable.2.sub hS.means_measurable.1))).integral_eq
    _ = E.A E.τ π := by simp only [Experiment.A, mul_comm]

lemma GP006B2b_actual_average {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π)
    (hU : ∀ i, (E.law π)[fun ω => E.μhat π ω (E.X i ω) | E.vectorSigma π]
      =ᵐ[E.law π] fun ω => E.μ0 (E.X i ω)) :
    E.expectedATT π = emptyFactor n (E.q π) * E.A E.τ π := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  let D : Fin n → Ω → ℝ := fun i ω => E.Y1 i ω - E.μ0 (E.X i ω)
  have hmD (i : Fin n) : Measurable (D i) :=
    (hS.measurable_units π hπ i).2.2.1.sub
      (hS.means_measurable.1.comp (hS.measurable_units π hπ i).1)
  have hiD (i : Fin n) : Integrable (D i) (E.law π) :=
    (hS.integrable_units π hπ i).2.1.sub
      (T6_law_transport E hS hπ i hS.means_measurable.1 hS.means_integrable.1).1
  have hI : iIndepFun (fun i ω => (D i ω, E.T π i ω)) (E.law π) := by
    exact (hS.iid_independent π hπ).comp
      (fun _ z => (z.2.2.1 - E.μ0 z.1, z.2.2.2))
      (fun _ => (measurable_snd.snd.fst.sub
        (hS.means_measurable.1.comp measurable_fst)).prodMk measurable_snd.snd.snd)
  have hbit (i : Fin n) : (∫ ω, bit (E.T π i ω) ∂E.law π) = E.q π := by
    have hm : E.covariateSigma i ≤ ‹MeasurableSpace Ω› :=
      (hS.measurable_units π hπ i).1.comap_le
    have htrim : IsFiniteMeasure ((E.law π).trim hm) := isFiniteMeasure_trim hm
    have hsig : SigmaFinite ((E.law π).trim hm) := inferInstance
    rw [← integral_condExp (μ := E.law π) (m := E.covariateSigma i)
      (hμm := hsig) hm]
    calc
      _ = ∫ ω, π (E.X i ω) ∂E.law π := integral_congr_ae (hS.bernoulli π hπ i)
      _ = E.q π := by
        exact ((hS.covariate_law π hπ i).comp hπ.1).integral_eq
  have hzero : E.q π = 0 → E.A E.τ π = 0 := by
    intro hq
    let i : Fin n := ⟨0, E.hn⟩
    have hbi : Integrable (fun ω => bit (E.T π i ω)) (E.law π) :=
      (integrable_const (1 : ℝ)).mono'
        ((measurable_of_finite bit).comp (hS.measurable_units π hπ i).2.2.2).aestronglyMeasurable
        (ae_of_all _ (fun ω => T6_bit_norm _))
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun ω => by cases E.T π i ω <;> norm_num [bit]) hbi).mp ((hbit i).trans hq)
    rw [← GP006B2b_mark_mean E hS π hπ i]
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply] at hω ⊢
    simp only [hω, mul_zero]
  let r : ℝ := E.A E.τ π / E.q π
  have hr : E.q π * r = E.A E.τ π := by
    by_cases hq : E.q π = 0
    · simp [hq, hzero hq]
    · dsimp [r]; field_simp
  rw [GP006B2b_replace_baseline E hS π hπ hU]
  have hav := GP006B2b_marked_average (E.law π) D (E.T π) hmD
    (fun i => (hS.measurable_units π hπ i).2.2.2) hiD hI (E.q π) r hbit
    (fun i => (GP006B2b_mark_mean E hS π hπ i).trans hr.symm)
  simpa only [hr] using hav

lemma GP006B2b_assemble {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hS : Standing E) (PiSet : Set (C → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hz : (fun _ => 0) ∈ PiSet)
    (b s : C → ℝ)
    (hb : IsBest PiSet E.expectedATT b) (hs : IsBest PiSet E.V s)
    (haverage : ∀ π ∈ PiSet,
      E.expectedATT π = emptyFactor n (E.q π) * E.A E.τ π)
    (hwelfare : ∀ π ∈ PiSet, E.V π = E.A E.τ π) :
    (∀ π ∈ PiSet, E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧
      1 ≤ emptyFactor n (E.q π)) ∧
    E.expectedATT (fun _ => 0) = 0 ∧ E.V (fun _ => 0) = 0 ∧
    0 ≤ E.expectedATT b ∧ 0 ≤ E.V b ∧ regret PiSet E.V b ≤ bestValue PiSet E.V := by
  letI : IsProbabilityMeasure E.PX := hS.px_probability
  have policywise (π : C → ℝ) (hπ : π ∈ PiSet) :
      E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧
      1 ≤ emptyFactor n (E.q π) := by
    have ha := hPiSet π hπ
    have hπint : Integrable π E.PX :=
      (integrable_const (1 : ℝ)).mono' ha.1.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (ha.2 x).1]
          exact (ha.2 x).2)
    have hq : 0 ≤ E.q π ∧ E.q π ≤ 1 := by
      constructor
      · exact integral_nonneg fun x => (ha.2 x).1
      · have hh := integral_mono hπint (integrable_const (1 : ℝ))
          (fun x => (ha.2 x).2)
        simpa [Experiment.q] using hh
    refine ⟨hwelfare π hπ, ?_, emptyFactor_ge_one n E.hn (E.q π) hq⟩
    rw [haverage π hπ, hwelfare π hπ]
  have hVz : E.V (fun _ => 0) = 0 := by
    rw [hwelfare _ hz]
    simp [Experiment.A]
  have hRz : E.expectedATT (fun _ => 0) = 0 := by
    rw [(policywise _ hz).2.1, hVz, mul_zero]
  have hRb : 0 ≤ E.expectedATT b := by
    have hh := hb.2 (fun _ => 0) hz
    rwa [hRz] at hh
  have hbest : IsBest PiSet (fun π => emptyFactor n (E.q π)*E.V π) b := by
    refine ⟨hb.1, ?_⟩
    intro π hπ
    change emptyFactor n (E.q π)*E.V π ≤ emptyFactor n (E.q b)*E.V b
    rw [← (policywise π hπ).2.1, ← (policywise b hb.1).2.1]
    exact hb.2 π hπ
  have hfinish := positive_factor_regret PiSet E.V
    (fun π => emptyFactor n (E.q π)) (fun _ => 0) b s hz hVz
    (fun π hπ => (policywise π hπ).2.2) hbest hs
  exact ⟨policywise, hRz, hVz, hRb, hfinish.1, hfinish.2⟩


theorem T3_corrected_ATT_regret_proof {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hS : Standing E) (PiSet : Set (C → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hz : (fun _ => 0) ∈ PiSet)
    (hU : VectorUnbiased E PiSet) (b s : C → ℝ)
    (hb : IsBest PiSet E.expectedATT b) (hs : IsBest PiSet E.V s) :
    (∀ π ∈ PiSet, E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧
      1 ≤ emptyFactor n (E.q π)) ∧
    E.expectedATT (fun _ => 0) = 0 ∧ E.V (fun _ => 0) = 0 ∧
    0 ≤ E.expectedATT b ∧ 0 ≤ E.V b ∧ regret PiSet E.V b ≤ bestValue PiSet E.V := by
  apply GP006B2b_assemble E hS PiSet hPiSet hz b s hb hs
  · intro π hπ
    exact GP006B2b_actual_average E hS π (hPiSet π hπ) (hU π hπ)
  · intro π hπ
    rw [T6_actual_welfare E hS (hPiSet π hπ)]
    simp only [Experiment.meanWelfare, Experiment.A, mul_comm]

end
end AronowAudit.P006.Wave1
