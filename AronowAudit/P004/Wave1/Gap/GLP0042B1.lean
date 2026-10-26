import AronowAudit.P004.P004_SpatialCLTCompletion
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
P004-T2: the actual constrained logistic fit, corrected IPW expansion,
Gaussian limit, and fitted raw-SAH/HAC conservative intervals.

All stochastic assertions use the changing finite Bernoulli design laws.
The information and plug-in bounds are proved below; no consistency,
score-expansion, CLT, or coverage conclusion is assumed.
-/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical Topology
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
  [∀ N, MeasurableSpace (Space N)]

lemma T2_logistic_eq_sigmoid (t : ℝ) : logistic t = Real.sigmoid t := by
  unfold logistic Real.sigmoid
  rw [Real.exp_neg]
  have he := Real.exp_pos t
  field_simp
  ring

lemma T2_logistic_pos (t : ℝ) : 0 < logistic t := by
  rw [T2_logistic_eq_sigmoid]
  exact Real.sigmoid_pos t

lemma T2_logistic_lt_one (t : ℝ) : logistic t < 1 := by
  rw [T2_logistic_eq_sigmoid]
  exact Real.sigmoid_lt_one t

lemma T2_logistic_deriv (t : ℝ) :
    HasDerivAt logistic (logistic t * (1 - logistic t)) t := by
  rw [show logistic = Real.sigmoid from funext T2_logistic_eq_sigmoid]
  exact Real.hasDerivAt_sigmoid t

lemma T2_logistic_mono : Monotone logistic := by
  rw [show logistic = Real.sigmoid from funext T2_logistic_eq_sigmoid]
  exact Real.sigmoid_monotone

lemma T2_softplus_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.log (1 + Real.exp s)) (logistic t) t := by
  exact ((Real.hasDerivAt_exp t).const_add 1).log (by positivity)

lemma T2_curvature_bound (T t : ℝ) (ht : |t| ≤ T) :
    logistic (-T) * (1 - logistic T) ≤ logistic t * (1 - logistic t) := by
  have hl := T2_logistic_mono (abs_le.mp ht).1
  have hu := T2_logistic_mono (abs_le.mp ht).2
  exact mul_le_mul hl (sub_le_sub_left hu 1)
    (sub_pos.mpr (T2_logistic_lt_one T)).le (T2_logistic_pos t).le

lemma T2_softplus_quadratic (T x y : ℝ) (hx : |x| ≤ T) (hy : |y| ≤ T) :
    Real.log (1 + Real.exp x) + logistic x * (y-x) +
      (logistic (-T) * (1 - logistic T)) / 2 * (y-x)^2 ≤
        Real.log (1 + Real.exp y) := by
  let w := logistic (-T) * (1 - logistic T)
  let f : ℝ → ℝ := fun t => Real.log (1 + Real.exp t) - w / 2 * t^2
  let f' : ℝ → ℝ := fun t => logistic t - w * t
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    convert (T2_softplus_deriv t).sub (((hasDerivAt_id' t).pow 2).const_mul (w/2)) using 1 <;>
      dsimp [f, f'] <;> ring
  have hd' (t : ℝ) :
      HasDerivAt f' (logistic t * (1-logistic t) - w) t := by
    convert! (T2_logistic_deriv t).sub ((hasDerivAt_id' t).const_mul w) using 1 <;>
      simp only [f', Pi.sub_apply, mul_one]
  have hcv : ConvexOn ℝ (Set.Icc (-T) T) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f')
      (f'' := fun t => logistic t * (1-logistic t) - w) (convex_Icc _ _)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).hasDerivWithinAt
    · exact fun t _ => (hd' t).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc (-T) T := interior_subset ht
      exact sub_nonneg.mpr (T2_curvature_bound T t (abs_le.mpr ht'))
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := hcv.le_slope_of_hasDerivAt (abs_le.mp hx) (abs_le.mp hy) hxy (hd x)
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    dsimp [f, f', w] at hm ⊢
    nlinarith
  · simp
  · have hs := hcv.slope_le_of_hasDerivAt (abs_le.mp hy) (abs_le.mp hx) hyx (hd x)
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp hs
    dsimp [f, f', w] at hm ⊢
    nlinarith

lemma T2_dot_sub {k : ℕ} (u v w : Fin k → ℝ) :
    dot u (v-w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma T2_dot_sq {k : ℕ} (u v : Fin k → ℝ) :
    (dot u v)^2 ≤ (∑ j, (u j)^2) * ∑ j, (v j)^2 := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

lemma T2_norm_sq_le_energy {k : ℕ} (v : Fin k → ℝ) :
    ‖v‖^2 ≤ ∑ j, (v j)^2 := by
  by_cases h : k = 0
  · subst k
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · letI instT2Nonempty : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero h)
    obtain ⟨j, hj⟩ := Finite.exists_max (fun j => ‖v j‖)
    have hn : ‖v‖ = ‖v j‖ := by
      apply le_antisymm
      · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hj
      · exact norm_le_pi_norm v j
    rw [hn, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ j)

lemma T2_score_dot {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ)
    (z : Assignment N) (v : Fin k → ℝ) :
    dot (logisticScore p O z) v =
      (∑ i, (bit (z i)-p i) * dot (O i) v) / N := by
  simp only [dot, logisticScore, div_mul_eq_mul_div, ← Finset.sum_div,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Finite likelihood maximization and a Gram bound force a score-sized error.
The covariate predictors need only be bounded at the two endpoints. -/
lemma T2_mle_energy {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) (T c : ℝ) (hc : 0 < c)
    (hN : 0 < N) (ht : ∀ i, |dot (O i) θ₀| ≤ T ∧ |dot (O i) θ| ≤ T)
    (hg : ∀ v : Fin k → ℝ,
      c * (∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2) / N)
    (hmax : (∑ i : Fin N, (bit (z i) * dot (O i) θ₀ - Real.log (1+Real.exp (dot (O i) θ₀)))) ≤
      (∑ i : Fin N, (bit (z i) * dot (O i) θ - Real.log (1+Real.exp (dot (O i) θ))))) :
    (∑ j, (θ j-θ₀ j)^2) ≤
      4 / (logistic (-T) * (1-logistic T) * c)^2 *
        ∑ j, (logisticScore (propensities O θ₀) O z j)^2 := by
  let w := logistic (-T) * (1-logistic T)
  let v := θ-θ₀
  let E := ∑ j, (v j)^2
  let S := logisticScore (propensities O θ₀) O z
  have hw : 0 < w := mul_pos (T2_logistic_pos _) (sub_pos.mpr (T2_logistic_lt_one _))
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hquad : w / 2 * (∑ i, (dot (O i) v)^2) ≤
      ∑ i, (bit (z i)-propensities O θ₀ i) * dot (O i) v := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      T2_softplus_quadratic T (dot (O i) θ₀) (dot (O i) θ) (ht i).1 (ht i).2)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    have hv (i : Fin N) : dot (O i) v = dot (O i) θ - dot (O i) θ₀ := T2_dot_sub _ _ _
    simp_rw [hv]
    have hbit : (∑ i, (bit (z i)-propensities O θ₀ i) *
        (dot (O i) θ-dot (O i) θ₀)) =
        (∑ i, bit (z i)*dot (O i) θ) - (∑ i, bit (z i)*dot (O i) θ₀) -
          ∑ i, logistic (dot (O i) θ₀)*(dot (O i) θ-dot (O i) θ₀) := by
      simp only [propensities, sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hbit]
    simp only [Finset.sum_sub_distrib] at hmax
    dsimp only [w] at h ⊢
    linarith
  have he : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hgs : w*c/2*E ≤ dot S v := by
    rw [T2_score_dot]
    have hb' := mul_le_mul_of_nonneg_left (hg v) (by positivity : 0 ≤ w/2)
    have hq := (div_le_div_of_nonneg_right hquad hn.le)
    dsimp [E] at *
    calc
      _ ≤ w/2 * ((∑ i, (dot (O i) v)^2)/N) := by nlinarith [hb']
      _ ≤ _ := by simpa only [mul_div_assoc] using hq
  have hsq : (w*c/2*E)^2 ≤ (dot S v)^2 := by
    exact pow_le_pow_left₀ (by positivity) hgs 2
  have hcs := T2_dot_sq S v
  have hE : (w*c/2)^2 * E ≤ ∑ j, (S j)^2 := by
    by_cases hzero : E = 0
    · simp only [hzero, mul_zero]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · have hpos : 0 < E := lt_of_le_of_ne he (Ne.symm hzero)
      apply (mul_le_mul_iff_left₀ hpos).mp
      dsimp [E] at hsq hcs ⊢
      nlinarith [hsq.trans hcs]
  have hwc : w*c ≠ 0 := (mul_pos hw hc).ne'
  have hfinal : E ≤ 4/(w*c)^2 * ∑ j, (S j)^2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_ne_zero hwc)).mpr
    nlinarith
  convert hfinal using 1 <;> rfl

lemma T2_bit_moments {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i : Fin N) :
    expect p (fun z => bit (z i)) = p i ∧
      expect p (fun z => (bit (z i))^2) = p i := by
  constructor
  · simpa only [pow_one, mul_one, expect_const] using
      bernoulli_positive_power p (fun _ => 1) i 1 (by decide) hp
  · simpa only [mul_one, expect_const] using
      bernoulli_positive_power p (fun _ => 1) i 2 (by decide) hp

lemma T2_centered_coin_pair {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i j : Fin N) :
    expect p (fun z => (bit (z i)-p i)*(bit (z j)-p j)) =
      if i=j then p i*(1-p i) else 0 := by
  by_cases hij : i=j
  · subst j
    have hfun : (fun z : Assignment N => (bit (z i)-p i)*(bit (z i)-p i)) =
        fun z => (bit (z i))^2 - (2*p i)*bit (z i) + (p i)^2 := by
      funext z
      ring
    rw [hfun, expect_add, expect_sub, expect_mul, expect_const,
      (T2_bit_moments p hp i).1, (T2_bit_moments p hp i).2, if_pos rfl]
    ring
  · have hpair : expect p (fun z => bit (z i)*bit (z j)) = p i*p j := by
      simpa only [pow_one, mul_one, expect_const] using
        bernoulli_pair_positive_powers p (fun _ => 1) i j hij 1 1 (by decide) (by decide) hp
    have hfun : (fun z : Assignment N => (bit (z i)-p i)*(bit (z j)-p j)) =
        fun z => bit (z i)*bit (z j) - p j*bit (z i) - p i*bit (z j) + p i*p j := by
      funext z
      ring
    rw [hfun, expect_add, expect_sub, expect_sub, expect_mul, expect_mul, expect_const,
      hpair, (T2_bit_moments p hp i).1, (T2_bit_moments p hp j).1, if_neg hij]
    ring

lemma T2_score_coordinate_second {N k : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (O : Fin N → Fin k → ℝ) (j : Fin k) :
    expect p (fun z => (logisticScore p O z j)^2) =
      (∑ i, p i*(1-p i)*(O i j)^2) / (N : ℝ)^2 := by
  have he : (fun z => (logisticScore p O z j)^2) = fun z =>
      (∑ i, ∑ l, (O i j*O l j)*((bit (z i)-p i)*(bit (z l)-p l))) / (N : ℝ)^2 := by
    funext z
    dsimp only [logisticScore]
    rw [div_pow]
    congr 1
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, expect_div, expect_sum]
  simp_rw [expect_sum, expect_mul, T2_centered_coin_pair p hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite, pow_two, mul_assoc, mul_comm, mul_left_comm]

lemma T2_score_energy_second {N k : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (O : Fin N → Fin k → ℝ)
    (U : ℝ) (hU : 0 ≤ U) (hO : ∀ i j, |O i j| ≤ U) (hN : 0 < N) :
    expect p (fun z => ∑ j, (logisticScore p O z j)^2) ≤ (k : ℝ)*U^2/N := by
  rw [expect_sum]
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  calc
    _ ≤ ∑ _j : Fin k, U^2/(N : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [T2_score_coordinate_second p hp O j]
      calc
        _ ≤ (∑ _i : Fin N, U^2)/(N : ℝ)^2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          apply Finset.sum_le_sum
          intro i _
          have ho : (O i j)^2 ≤ U^2 := (sq_le_sq₀ (abs_nonneg _) hU).mpr (hO i j) |>
            (by simpa only [sq_abs] using ·)
          have hw : 0 ≤ p i*(1-p i) := mul_nonneg (hp i).1.le (sub_pos.mpr (hp i).2).le
          have hw1 : p i*(1-p i) ≤ 1 := by nlinarith [(hp i).1, (hp i).2, sq_nonneg (p i)]
          exact (mul_le_mul_of_nonneg_left ho hw).trans
            (by nlinarith [sq_nonneg U])
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
    _ = _ := by simp [mul_div_assoc]

lemma T2_dot_bound {k : ℕ} (u v : Fin k → ℝ) (U T : ℝ) (hU : 0 ≤ U)
    (hu : ∀ j, |u j| ≤ U) (hv : ∀ j, |v j| ≤ T) :
    |dot u v| ≤ (k : ℝ)*U*T := by
  calc
    _ ≤ ∑ j, |u j*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, U*T := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hu j) (hv j) (abs_nonneg _) hU
    _ = _ := by simp [mul_assoc]

lemma T2_uniform_mle_energy {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ)
    (hlog : LogisticConditions O θ₀ Θ θhat) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, ∀ z,
      ‖θhat N z-θ₀‖^2 ≤ C * ∑ j,
        (logisticScore (propensities (O N) θ₀) (O N) z j)^2 := by
  obtain ⟨U, hO⟩ := hlog.2.2.1
  obtain ⟨c, hc, hg⟩ := hlog.2.2.2.1
  obtain ⟨T, hT, hΘ⟩ := hlog.1.isBounded.exists_pos_norm_le
  let U' := max U 0
  let A := (k : ℝ)*U'*T
  let w := logistic (-A)*(1-logistic A)
  have hU' : 0 ≤ U' := le_max_right _ _
  have hw : 0 < w := mul_pos (T2_logistic_pos _) (sub_pos.mpr (T2_logistic_lt_one _))
  refine ⟨4/(w*c)^2, by positivity, ?_⟩
  filter_upwards [hg, eventually_gt_atTop 0] with N hgN hN z
  apply (T2_norm_sq_le_energy (θhat N z-θ₀)).trans
  apply T2_mle_energy (O N) θ₀ (θhat N z) z A c hc hN _ hgN
    ((hlog.2.2.2.2 N z).2 θ₀ hlog.2.1)
  intro i
  have hcoord (θ : Fin k → ℝ) (hθ : θ ∈ Θ) (j : Fin k) : |θ j| ≤ T := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm θ j).trans (hΘ θ hθ)
  exact ⟨T2_dot_bound (O N i) θ₀ U' T hU'
      (fun j => (hO N i j).trans (le_max_left _ _)) (hcoord θ₀ hlog.2.1),
    T2_dot_bound (O N i) (θhat N z) U' T hU'
      (fun j => (hO N i j).trans (le_max_left _ _)) (hcoord _ (hlog.2.2.2.2 N z).1)⟩

lemma T2_prob_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop) : 0 ≤ prob p A := by
  unfold prob
  unfold expect
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (design_weight_nonneg p hp z)
    (by dsimp only; split_ifs <;> norm_num))

lemma T2_prob_mono {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop)
    (h : ∀ z, A z → B z) : prob p A ≤ prob p B := by
  apply expect_mono p hp
  intro z
  by_cases hz : A z
  · simp only [if_pos hz, if_pos (h z hz), le_refl]
  · simp only [if_neg hz]
    split_ifs <;> norm_num

lemma T2_chebyshev {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (U : Assignment N → ℝ) (t : ℝ) (ht : 0 < t) :
    prob p (fun z => t < |U z|) ≤ expect p (fun z => (U z)^2) / t^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  have h := expect_mono p hp (fun z => t^2*(if t < |U z| then 1 else 0))
    (fun z => (U z)^2) (fun z => by
      split_ifs with hz
      · simp only [mul_one]
        nlinarith [sq_abs (U z)]
      · simpa using sq_nonneg (U z))
  rw [expect_mul] at h
  simpa only [prob, mul_comm] using h

lemma T2_bigop_of_second (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U : ∀ N, Assignment N → ℝ)
    (K : ℝ) (hK : 0 < K)
    (hU : ∀ᶠ N in atTop, expect (p N) (fun z => (U N z)^2) ≤ K/N) :
    BigOp p U (fun N => (Real.sqrt N)⁻¹) := by
  intro ε hε
  let C := Real.sqrt (2*K/ε)
  have hC : 0 < C := Real.sqrt_pos.mpr (by positivity)
  have hC2 : C^2 = 2*K/ε := Real.sq_sqrt (by positivity)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hU, eventually_gt_atTop 0] with N hUN hN
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  rw [abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ expect (p N) (fun z => (U N z)^2) / (C*(Real.sqrt (N : ℝ))⁻¹)^2 :=
      T2_chebyshev (p N) (hp N) _ _ (by positivity)
    _ ≤ (K/N) / (C*(Real.sqrt (N : ℝ))⁻¹)^2 :=
      div_le_div_of_nonneg_right hUN (sq_nonneg _)
    _ = ε/2 := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hn.le, hC2]
      field_simp
    _ < ε := by linarith

lemma T2_inprob_of_bigop (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U : ∀ N, Assignment N → ℝ)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (nhds 0)) (hU : BigOp p U r) : InProb p U := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N => ha.trans_le (T2_prob_nonneg (p N) (hp N) _))
  · intro η hη
    obtain ⟨C, hC, htail⟩ := hU η hη
    have hscale : Tendsto (fun N => C*|r N|) atTop (nhds 0) := by
      simpa using hr.abs.const_mul C
    filter_upwards [htail, hscale.eventually (eventually_lt_nhds hε)] with N ht hs
    exact (T2_prob_mono (p N) (hp N) _ _ (fun z hz => hs.trans hz)).trans_lt ht

lemma T2_mle_second {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ)
    (hlog : LogisticConditions O θ₀ Θ θhat)
    (hp : ∀ N i, 0 < propensities (O N) θ₀ i ∧ propensities (O N) θ₀ i < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N in atTop,
      expect (propensities (O N) θ₀) (fun z => ‖θhat N z-θ₀‖^2) ≤ K/N := by
  obtain ⟨C, hC, hbound⟩ := T2_uniform_mle_energy O θ₀ Θ θhat hlog
  obtain ⟨U, hO⟩ := hlog.2.2.1
  let U' := max U 0
  refine ⟨C*(k : ℝ)*U'^2+1, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with N hN hpos
  calc
    _ ≤ expect (propensities (O N) θ₀) (fun z =>
        C*∑ j, (logisticScore (propensities (O N) θ₀) (O N) z j)^2) :=
      expect_mono _ (hp N) _ _ hN
    _ = C * expect (propensities (O N) θ₀) (fun z =>
        ∑ j, (logisticScore (propensities (O N) θ₀) (O N) z j)^2) := expect_mul _ _ _
    _ ≤ C*((k : ℝ)*U'^2/N) := mul_le_mul_of_nonneg_left
      (T2_score_energy_second _ (hp N) (O N) U' (le_max_right _ _)
        (fun i j => (hO N i j).trans (le_max_left _ _)) hpos) hC.le
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by ring_nf; linarith) (Nat.cast_nonneg N)


lemma T2_logistic_lipschitz (x y : ℝ) : |logistic y-logistic x| ≤ |y-x| := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => (T2_logistic_deriv t).hasDerivWithinAt)
    (C := 1) (fun t _ => ?_) (Set.mem_univ x) (Set.mem_univ y)
  · simpa only [Real.norm_eq_abs, one_mul] using h
  · rw [Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (T2_logistic_pos t).le (sub_pos.mpr (T2_logistic_lt_one t)).le)]
    nlinarith [T2_logistic_pos t, T2_logistic_lt_one t, sq_nonneg (logistic t)]

lemma T2_logistic_deriv_lipschitz (x y : ℝ) :
    |logistic y*(1-logistic y)-logistic x*(1-logistic x)| ≤ |y-x| := by
  have he : logistic y*(1-logistic y)-logistic x*(1-logistic x) =
      (logistic y-logistic x)*(1-logistic y-logistic x) := by ring
  rw [he, abs_mul]
  have ha : |1-logistic y-logistic x| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [T2_logistic_pos x, T2_logistic_pos y,
      T2_logistic_lt_one x, T2_logistic_lt_one y]
  calc
    _ ≤ |logistic y-logistic x| * 1 := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    _ ≤ |y-x| := by simpa using T2_logistic_lipschitz x y

lemma T2_logistic_taylor (x y : ℝ) :
    |logistic y-logistic x-logistic x*(1-logistic x)*(y-x)| ≤ (y-x)^2 := by
  let f : ℝ → ℝ := fun t => logistic (x+t*(y-x))-logistic x-
    logistic x*(1-logistic x)*(t*(y-x))
  have hd (t : ℝ) : HasDerivAt f
      ((logistic (x+t*(y-x))*(1-logistic (x+t*(y-x)))-logistic x*(1-logistic x))*(y-x)) t := by
    have ha := ((hasDerivAt_id' t).mul_const (y-x)).const_add x
    convert! ((T2_logistic_deriv _).comp t ha).sub_const (logistic x) |>.sub
      (((hasDerivAt_id' t).mul_const (y-x)).const_mul (logistic x*(1-logistic x))) using 1 <;>
        ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (C := (y-x)^2) (fun t ht => ?_)
  · simpa [f, Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |x+t*(y-x)-x| * |y-x| :=
        mul_le_mul_of_nonneg_right (T2_logistic_deriv_lipschitz x _) (abs_nonneg _)
      _ = |t| * |y-x|^2 := by rw [add_sub_cancel_left, abs_mul]; ring
      _ ≤ (y-x)^2 := by
        rw [sq_abs]
        have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
        nlinarith [sq_nonneg (y-x)]

lemma T2_likelihood_directional {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (z : Assignment N) (θ v : Fin k → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ i, (bit (z i)*dot (O i) (θ+t • v)-
      Real.log (1+Real.exp (dot (O i) (θ+t • v)))))
      (∑ i, (bit (z i)-propensities O θ i)*dot (O i) v) 0 := by
  have hdot (i : Fin N) (t : ℝ) : dot (O i) (θ+t • v) = dot (O i) θ+t*dot (O i) v := by
    simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hdot]
  apply HasDerivAt.fun_sum
  intro i _
  have ha : HasDerivAt (fun t : ℝ => dot (O i) θ+t*dot (O i) v) (dot (O i) v) 0 := by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (dot (O i) v)).const_add _
  have hb := (T2_softplus_deriv (dot (O i) θ+0*dot (O i) v)).comp (0 : ℝ) ha
  convert! (ha.const_mul (bit (z i))).sub hb using 1 <;>
    simp only [propensities, zero_mul, add_zero] <;> ring

lemma T2_interior_score {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (z : Assignment N) (Θ : Set (Fin k → ℝ)) (θ : Fin k → ℝ)
    (hθ : θ ∈ interior Θ)
    (hmax : ∀ γ ∈ Θ, (∑ i : Fin N, (bit (z i)*dot (O i) γ-
      Real.log (1+Real.exp (dot (O i) γ)))) ≤
        (∑ i : Fin N, (bit (z i)*dot (O i) θ-Real.log (1+Real.exp (dot (O i) θ))))) :
    logisticScore (propensities O θ) O z = 0 := by
  funext j
  let v : Fin k → ℝ := Pi.single j 1
  have ht : Tendsto (fun t : ℝ => θ+t • v) (nhds 0) (nhds θ) := by
    have hc : ContinuousAt (fun t : ℝ => θ+t • v) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto
  have hmem : ∀ᶠ t : ℝ in nhds 0, θ+t • v ∈ Θ :=
    ht.eventually (mem_interior_iff_mem_nhds.mp hθ)
  have hlocal : IsLocalMax (fun t : ℝ => ∑ i, (bit (z i)*dot (O i) (θ+t • v)-
      Real.log (1+Real.exp (dot (O i) (θ+t • v))))) 0 := by
    filter_upwards [hmem] with t ht
    simpa using hmax (θ+t • v) ht
  have hz := hlocal.hasDerivAt_eq_zero (T2_likelihood_directional O z θ v)
  have hd (i : Fin N) : dot (O i) v = O i j := by
    simp [v, dot, Pi.single_apply]
  simp_rw [hd] at hz
  simp only [logisticScore, hz, zero_div, Pi.zero_apply]

lemma T2_information_mulvec {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (v : Fin k → ℝ) (j : Fin k) :
    (information p O *ᵥ v) j =
      (∑ i, p i*(1-p i)*O i j*dot (O i) v) / N := by
  simp only [information, Matrix.mulVec, dotProduct, dot, div_mul_eq_mul_div,
    ← Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma T2_information_quadratic {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (v : Fin k → ℝ) :
    dot v (information p O *ᵥ v) =
      (∑ i, p i*(1-p i)*(dot (O i) v)^2) / N := by
  change (∑ j, v j*(information p O *ᵥ v) j) = _
  simp_rw [T2_information_mulvec, ← mul_div_assoc]
  rw [← Finset.sum_div]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (p i*(1-p i)*dot (O i) v) * ∑ j, O i j*v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← dot]; ring

lemma T2_information_coercive {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (w c : ℝ) (hw : 0 ≤ w)
    (hweight : ∀ i, w ≤ p i*(1-p i))
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (v : Fin k → ℝ) :
    w*c*(∑ j, (v j)^2) ≤ dot v (information p O *ᵥ v) := by
  rw [T2_information_quadratic]
  calc
    _ ≤ w*((∑ i, (dot (O i) v)^2)/N) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hgram v) hw
    _ = (∑ i, w*(dot (O i) v)^2)/N := by rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hweight i) (sq_nonneg _)))
      (Nat.cast_nonneg _)

lemma T2_coercive_unit {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (c : ℝ) (hc : 0 < c)
    (hA : ∀ v, c*(∑ j, (v j)^2) ≤ dot v (A *ᵥ v)) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hzero : A *ᵥ (u-v) = 0 := by simp only [Matrix.mulVec_sub, huv, sub_self]
  have hb := hA (u-v)
  rw [hzero] at hb
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hb
  have hnorm := mul_le_mul_of_nonneg_left (T2_norm_sq_le_energy (u-v)) hc.le
  have hz : ‖u-v‖^2 = 0 := by nlinarith [sq_nonneg ‖u-v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

lemma T2_inverse_bound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (c : ℝ) (hc : 0 < c)
    (hA : ∀ v, c*(∑ j, (v j)^2) ≤ dot v (A *ᵥ v)) (u : Fin k → ℝ) :
    ‖A⁻¹ *ᵥ u‖ ≤ (k : ℝ)/c*‖u‖ := by
  letI instT2InverseBound := (T2_coercive_unit A c hc hA).invertible
  let v := A⁻¹ *ᵥ u
  have hAv : A *ᵥ v = u := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hlow := mul_le_mul_of_nonneg_left (T2_norm_sq_le_energy v) hc.le
  have hdot := hA v
  rw [hAv] at hdot
  have hupper := (le_abs_self (dot v u)).trans (T2_dot_bound v u ‖v‖ ‖u‖
    (norm_nonneg _) (fun j => by simpa using norm_le_pi_norm v j)
    (fun j => by simpa using norm_le_pi_norm u j))
  by_cases hv : ‖v‖=0
  · change ‖v‖ ≤ _
    rw [hv]
    positivity
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hmul : c*‖v‖ ≤ (k : ℝ)*‖u‖ := by
      apply (mul_le_mul_iff_right₀ hvpos).mp
      nlinarith [hlow.trans hdot |>.trans hupper]
    change ‖v‖ ≤ _
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hc).mpr (by nlinarith)

def T2_score_error {N k : ℕ} (O : Fin N → Fin k → ℝ) (θ₀ θ : Fin k → ℝ) : Fin k → ℝ :=
  fun j => (∑ i, (propensities O θ i-propensities O θ₀ i-
    propensities O θ₀ i*(1-propensities O θ₀ i)*dot (O i) (θ-θ₀))*O i j)/N

lemma T2_score_identity {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) :
    logisticScore (propensities O θ) O z = logisticScore (propensities O θ₀) O z -
      information (propensities O θ₀) O *ᵥ (θ-θ₀) - T2_score_error O θ₀ θ := by
  funext j
  simp only [Pi.sub_apply, logisticScore, T2_information_mulvec, T2_score_error,
    ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma T2_score_error_bound {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hO : ∀ i j, |O i j| ≤ U) (hN : 0 < N) :
    ‖T2_score_error O θ₀ θ‖ ≤ ((k : ℝ)*U)^2*U*‖θ-θ₀‖^2 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change |T2_score_error O θ₀ θ j| ≤ _
  unfold T2_score_error
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |(propensities O θ i-propensities O θ₀ i-
        propensities O θ₀ i*(1-propensities O θ₀ i)*dot (O i) (θ-θ₀))*O i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ((k : ℝ)*U)^2*U*‖θ-θ₀‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have ht := T2_logistic_taylor (dot (O i) θ₀) (dot (O i) θ)
      rw [← T2_dot_sub] at ht
      change |propensities O θ i-propensities O θ₀ i-
        propensities O θ₀ i*(1-propensities O θ₀ i)*dot (O i) (θ-θ₀)| ≤ _ at ht
      have hd := T2_dot_bound (O i) (θ-θ₀) U ‖θ-θ₀‖ hU (hO i)
        (fun l => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ-θ₀) l)
      have hd2 : (dot (O i) (θ-θ₀))^2 ≤ ((k : ℝ)*U*‖θ-θ₀‖)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [abs_mul]
      calc
        _ ≤ (dot (O i) (θ-θ₀))^2 * U := mul_le_mul ht (hO i j) (abs_nonneg _) (by positivity)
        _ ≤ ((k : ℝ)*U*‖θ-θ₀‖)^2*U := mul_le_mul_of_nonneg_right hd2 hU
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma T2_mle_remainder_bound {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) (w c U : ℝ)
    (hw : 0 < w) (hc : 0 < c) (hU : 0 ≤ U) (hN : 0 < N)
    (hO : ∀ i j, |O i j| ≤ U)
    (hweight : ∀ i, w ≤ propensities O θ₀ i*(1-propensities O θ₀ i))
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hscore : logisticScore (propensities O θ) O z = 0) :
    ‖θ-θ₀-(information (propensities O θ₀) O)⁻¹ *ᵥ
        logisticScore (propensities O θ₀) O z‖ ≤
      ((k : ℝ)/(w*c))*(((k : ℝ)*U)^2*U)*‖θ-θ₀‖^2 := by
  let A := information (propensities O θ₀) O
  have hA (v : Fin k → ℝ) : w*c*(∑ j, (v j)^2) ≤ dot v (A *ᵥ v) :=
    T2_information_coercive _ O w c hw.le hweight hgram v
  letI instT2MleRemainder := (T2_coercive_unit A (w*c) (mul_pos hw hc) hA).invertible
  have hid := T2_score_identity O θ₀ θ z
  rw [hscore] at hid
  have hdelta : θ-θ₀-A⁻¹ *ᵥ logisticScore (propensities O θ₀) O z =
      -(A⁻¹ *ᵥ T2_score_error O θ₀ θ) := by
    have he : A *ᵥ (θ-θ₀) = logisticScore (propensities O θ₀) O z-T2_score_error O θ₀ θ := by
      change 0 = logisticScore (propensities O θ₀) O z-A *ᵥ (θ-θ₀)-T2_score_error O θ₀ θ at hid
      calc
        _ = A *ᵥ (θ-θ₀)+(logisticScore (propensities O θ₀) O z-
          A *ᵥ (θ-θ₀)-T2_score_error O θ₀ θ) := by rw [← hid]; simp
        _ = _ := by abel
    have hi := congrArg (fun v => A⁻¹ *ᵥ v) he
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec,
      Matrix.mulVec_sub] at hi
    rw [hi]
    abel
  change ‖θ-θ₀-A⁻¹ *ᵥ _‖ ≤ _
  rw [hdelta, norm_neg]
  calc
    _ ≤ (k : ℝ)/(w*c)*‖T2_score_error O θ₀ θ‖ :=
      T2_inverse_bound A (w*c) (mul_pos hw hc) hA _
    _ ≤ (k : ℝ)/(w*c)*(((k : ℝ)*U)^2*U*‖θ-θ₀‖^2) :=
      mul_le_mul_of_nonneg_left (T2_score_error_bound O θ₀ θ U hU hO hN) (by positivity)
    _ = _ := by ring

lemma T2_prob_union {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop) :
    prob p (fun z => A z ∨ B z) ≤ prob p A+prob p B := by
  unfold prob
  rw [← expect_add]
  apply expect_mono p hp
  intro z
  by_cases ha : A z <;> by_cases hb : B z <;> simp [ha, hb]

lemma T2_markov {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (H : Assignment N → ℝ)
    (hH : ∀ z, 0 ≤ H z) (t : ℝ) (ht : 0 < t) :
    prob p (fun z => t < H z) ≤ expect p H/t := by
  apply (le_div_iff₀ ht).mpr
  have hb := expect_mono p hp (fun z => t*(if t < H z then 1 else 0)) H (fun z => by
    by_cases hz : t < H z
    · simpa only [if_pos hz, mul_one] using hz.le
    · simpa only [if_neg hz, mul_zero] using hH z)
  rw [expect_mul] at hb
  simpa only [prob, mul_comm] using hb

lemma T2_bigop_quadratic_good (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U V : ∀ N, Assignment N → ℝ)
    (K A r : ℝ) (hK : 0 < K) (hA : 0 ≤ A) (hr : 0 < r)
    (hU : InProb p U)
    (hmoment : ∀ᶠ N in atTop, expect (p N) (fun z => (U N z)^2) ≤ K/N)
    (hbound : ∀ᶠ N in atTop, ∀ z, |U N z| ≤ r → |V N z| ≤ A*(U N z)^2) :
    BigOp p V (fun N => (N : ℝ)⁻¹) := by
  intro ε hε
  let C := 4*A*K/ε+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCK : A*K/C < ε/2 := by
    apply (div_lt_iff₀ hC).mpr
    dsimp [C]
    have hε0 : ε ≠ 0 := hε.ne'
    field_simp
    nlinarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmoment, hbound, eventually_gt_atTop 0,
    (hU r hr).eventually (eventually_lt_nhds (by linarith : (0 : ℝ)<ε/2))]
    with N hMN hBN hN hbad
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [abs_of_pos (inv_pos.mpr hn)]
  have hevent : ∀ z, C*(N : ℝ)⁻¹ < |V N z| →
      r < |U N z| ∨ C*(N : ℝ)⁻¹ < A*(U N z)^2 := by
    intro z hz
    by_cases hu : r < |U N z|
    · exact Or.inl hu
    · exact Or.inr (hz.trans_le (hBN z (le_of_not_gt hu)))
  have hm : prob (p N) (fun z => C*(N : ℝ)⁻¹ < A*(U N z)^2) ≤ A*K/C := by
    calc
      _ ≤ expect (p N) (fun z => A*(U N z)^2)/(C*(N : ℝ)⁻¹) :=
        T2_markov _ (hp N) _ (fun z => by positivity) _ (by positivity)
      _ ≤ (A*(K/N))/(C*(N : ℝ)⁻¹) := by
        rw [expect_mul]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMN hA) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ prob (p N) (fun z => r < |U N z| ∨ C*(N : ℝ)⁻¹ < A*(U N z)^2) :=
      T2_prob_mono _ (hp N) _ _ hevent
    _ ≤ prob (p N) (fun z => r < |U N z|)+
        prob (p N) (fun z => C*(N : ℝ)⁻¹ < A*(U N z)^2) := T2_prob_union _ (hp N) _ _
    _ < ε := by linarith


lemma T2_local_depends {N : ℕ} (R : CircleTable N)
    (f : Fin N → Bool → ℝ → ℝ) (i : Fin N) :
    DependsOn (fun z : Assignment N => f i (z i) (R i z)) {j | interferes R i j} := by
  apply GraphCompletion.depends_of_update
  intro z j hj b
  have hji : j ≠ i := by intro h; subst j; exact hj (Or.inl rfl)
  have he : R i (Function.update z j b) = R i z := by
    by_contra hr
    exact hj (Or.inr ⟨Function.update z j b, z,
      (fun l hl => Function.update_of_ne hl _ _), hr⟩)
  simp only [Function.update_of_ne hji.symm, he]

lemma T2_local_cov_zero {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (f : Fin N → Bool → ℝ → ℝ) (i j : Fin N) (hij : ¬ sharesSource R i j) :
    cov p (fun z => f i (z i) (R i z)) (fun z => f j (z j) (R j z)) = 0 := by
  have hj : DependsOn (fun z : Assignment N => f j (z j) (R j z))
      ({l | interferes R i l}ᶜ) :=
    (T2_local_depends R f j).mono (by intro l hl hli; exact hij ⟨l, hli, hl⟩)
  unfold cov
  rw [GraphCompletion.expect_mul_of_disjoint_depends p _ _ _ (T2_local_depends R f i) hj,
    sub_self]

lemma T2_local_empirical_second {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (f : Fin N → Bool → ℝ → ℝ) (B : Fin N → Finset (Fin N)) (D M : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N) (hM : 0 ≤ M)
    (hbound : ∀ i z, |f i (z i) (R i z)| ≤ M)
    (hcount : ∀ i, ((B i).card : ℝ) ≤ D)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    let X := fun z => (∑ i, f i (z i) (R i z))/N
    expect p (fun z => (X z-expect p X)^2) ≤ D*M^2/N := by
  let X := fun z => (∑ i, f i (z i) (R i z))/N
  have hvar := finite_covariance_degree_bound p hp (fun i z => f i (z i) (R i z)) B
    hsymm (fun i j hj => T2_local_cov_zero p R f i j (hout i j hj))
  have hsecond (i : Fin N) : expect p (fun z => (f i (z i) (R i z))^2) ≤ M^2 := by
    apply (expect_mono p hp _ (fun _ => M^2) (fun z => ?_)).trans_eq (expect_const p _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound i z) 2
  have hdeg : (∑ i, (B i).card*expect p (fun z => (f i (z i) (R i z))^2)) ≤
      (N : ℝ)*(D*M^2) := by
    calc
      _ ≤ ∑ _i : Fin N, D*M^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hsecond i) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hcount i) (sq_nonneg _))
      _ = _ := by simp
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hv : variance p X ≤ D*M^2/N := by
    calc
      _ ≤ (∑ i, (B i).card*expect p (fun z => (f i (z i) (R i z))^2))/(N : ℝ)^2 := hvar
      _ ≤ ((N : ℝ)*(D*M^2))/(N : ℝ)^2 := div_le_div_of_nonneg_right hdeg (sq_nonneg _)
      _ = _ := by field_simp
  simpa only [variance, cov_centered, ← pow_two] using hv

lemma T2_marginal_abs_le {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (M : ℝ) (hR : ∀ i z, |R i z| ≤ M)
    (i : Fin N) (a : Bool) : |marginal p R i a| ≤ M := by
  rw [marginal_is_marginalization p R i a hp]
  apply abs_le.mpr
  constructor
  · have hb := expect_mono p hp (fun _ => -M) (fun z => R i (Function.update z i a))
      (fun z => (abs_le.mp (hR i _)).1)
    simpa only [expect_const] using hb
  · have hb := expect_mono p hp (fun z => R i (Function.update z i a)) (fun _ => M)
      (fun z => (abs_le.mp (hR i _)).2)
    simpa only [expect_const] using hb

def T2_ht_gradient {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) : Fin k → ℝ :=
  fun j => (∑ i, (bit (z i)*R i z*(1-p i)/p i+
    (1-bit (z i))*R i z*p i/(1-p i))*O i j)/N

def T2_population_gradient {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) : Fin k → ℝ :=
  fun j => (∑ i, ((1-p i)*marginal p R i true+p i*marginal p R i false)*O i j)/N

lemma T2_ht_gradient_mean {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (j : Fin k) :
    expect p (fun z => T2_ht_gradient p R O z j) = T2_population_gradient p R O j := by
  have hselected (i : Fin N) (a : Bool) :
      expect p (fun z => if z i=a then R i z else 0) = coin (p i) a*marginal p R i a :=
    bernoulli_selection p R i a (by
      cases a
      · simpa only [coin, Bool.false_eq_true, if_false] using (sub_pos.mpr (hp i).2).ne'
      · simpa only [coin, if_true] using (hp i).1.ne')
  have hfun (i : Fin N) :
      (fun z => (bit (z i)*R i z*(1-p i)/p i+
        (1-bit (z i))*R i z*p i/(1-p i))*O i j) =
      fun z => (O i j*(1-p i)/p i)*(if z i=true then R i z else 0)+
        (O i j*p i/(1-p i))*(if z i=false then R i z else 0) := by
    funext z
    cases hz : z i <;> simp [bit, hz] <;> ring
  unfold T2_ht_gradient T2_population_gradient
  rw [expect_div, expect_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hfun, expect_add, expect_mul, expect_mul, hselected i true, hselected i false]
  simp only [coin, Bool.false_eq_true, if_true, if_false]
  field_simp [(hp i).1.ne', (sub_pos.mpr (hp i).2).ne'] <;> ring

lemma T2_gradient_atom_bound (b : Bool) (p μ o ε M U : ℝ)
    (hε : 0 < ε) (hp : 0 < p ∧ p < 1) (hπ : ε ≤ p ∧ ε ≤ 1-p)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hμ : |μ| ≤ M) (ho : |o| ≤ U) :
    |(bit b*μ*(1-p)/p+(1-bit b)*μ*p/(1-p))*o| ≤ M*U/ε := by
  have hp0 := hp.1
  have hp1 := sub_pos.mpr hp.2
  have hw1 : |(1-p)/p| ≤ 1/ε := by
    rw [abs_div, abs_of_pos hp0, abs_of_pos hp1]
    apply (div_le_div_iff₀ hp0 hε).mpr
    nlinarith [hπ.1, hπ.2]
  have hw0 : |p/(1-p)| ≤ 1/ε := by
    rw [abs_div, abs_of_pos hp0, abs_of_pos hp1]
    apply (div_le_div_iff₀ hp1 hε).mpr
    nlinarith [hπ.1, hπ.2]
  have hprod (w : ℝ) (hw : |w| ≤ 1/ε) : |μ*o*w| ≤ M*U/ε := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (M*U)*(1/ε) := mul_le_mul
        (mul_le_mul hμ ho (abs_nonneg _) hM) hw (abs_nonneg _) (mul_nonneg hM hU)
      _ = _ := by ring
  cases b
  · simpa [bit, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hprod _ hw0
  · simpa [bit, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hprod _ hw1

lemma T2_gradient_second {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (B : Fin N → Finset (Fin N)) (D M U ε : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hε : 0 < ε)
    (hπ : ∀ i, ε ≤ p i ∧ ε ≤ 1-p i) (hN : 0 < N)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hR : ∀ i z, |R i z| ≤ M)
    (hO : ∀ i j, |O i j| ≤ U) (hcount : ∀ i, ((B i).card : ℝ) ≤ D)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    expect p (fun z => ‖T2_ht_gradient p R O z-T2_population_gradient p R O‖^2) ≤
      (k : ℝ)*D*(M*U/ε)^2/N := by
  calc
    _ ≤ expect p (fun z => ∑ j, (T2_ht_gradient p R O z j-T2_population_gradient p R O j)^2) :=
      expect_mono _ hp _ _ (fun z => T2_norm_sq_le_energy _)
    _ = ∑ j, expect p (fun z => (T2_ht_gradient p R O z j-T2_population_gradient p R O j)^2) :=
      expect_sum _ _
    _ ≤ ∑ _j : Fin k, D*(M*U/ε)^2/N := by
      apply Finset.sum_le_sum
      intro j _
      have h := T2_local_empirical_second p R
        (fun i b μ => (bit b*μ*(1-p i)/p i+(1-bit b)*μ*p i/(1-p i))*O i j)
        B D (M*U/ε) hp hN (by positivity)
        (fun i z => T2_gradient_atom_bound _ _ _ _ ε M U hε (hp i) (hπ i) hM hU
          (hR i z) (hO i j)) hcount hsymm hout
      change expect p (fun z => (T2_ht_gradient p R O z j-
        expect p (fun z => T2_ht_gradient p R O z j))^2) ≤ _ at h
      rw [T2_ht_gradient_mean p R O hp j] at h
      exact h
    _ = _ := by simp [mul_div_assoc]; ring

lemma T2_population_gradient_bound {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (M U : ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hN : 0 < N) (hM : 0 ≤ M) (hU : 0 ≤ U) (hR : ∀ i z, |R i z| ≤ M)
    (hO : ∀ i j, |O i j| ≤ U) : ‖T2_population_gradient p R O‖ ≤ M*U := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hU)).mpr
  intro j
  change |T2_population_gradient p R O j| ≤ _
  unfold T2_population_gradient
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |((1-p i)*marginal p R i true+p i*marginal p R i false)*O i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, M*U := by
      apply Finset.sum_le_sum
      intro i _
      have ht := T2_marginal_abs_le p R hp M hR i true
      have hf := T2_marginal_abs_le p R hp M hR i false
      have hmean : |(1-p i)*marginal p R i true+p i*marginal p R i false| ≤ M := by
        calc
          _ ≤ |(1-p i)*marginal p R i true|+|p i*marginal p R i false| := abs_add_le _ _
          _ = (1-p i)*|marginal p R i true|+p i*|marginal p R i false| := by
            rw [abs_mul, abs_mul, abs_of_pos (hp i).1, abs_of_pos (sub_pos.mpr (hp i).2)]
          _ ≤ (1-p i)*M+p i*M := add_le_add
            (mul_le_mul_of_nonneg_left ht (sub_pos.mpr (hp i).2).le)
            (mul_le_mul_of_nonneg_left hf (hp i).1.le)
          _ = M := by ring
      rw [abs_mul]
      exact mul_le_mul hmean (hO i j) (abs_nonneg _) hM
    _ = _ := by simp [mul_comm]

lemma T2_inv_logistic (t : ℝ) : (logistic t)⁻¹ = 1+Real.exp (-t) := by
  rw [logistic, Real.exp_neg]
  field_simp <;> ring

lemma T2_logistic_neg (t : ℝ) : logistic (-t) = 1-logistic t := by
  simpa only [T2_logistic_eq_sigmoid] using Real.sigmoid_neg t

lemma T2_inv_complement (t : ℝ) : (1-logistic t)⁻¹ = 1+Real.exp t := by
  rw [← T2_logistic_neg, T2_inv_logistic, neg_neg]

lemma T2_logistic_odds (t : ℝ) :
    (1-logistic t)/logistic t = Real.exp (-t) ∧
      logistic t/(1-logistic t) = Real.exp t := by
  have hp := (T2_logistic_pos t).ne'
  have hq := (sub_pos.mpr (T2_logistic_lt_one t)).ne'
  constructor
  · rw [sub_div, div_self hp, one_div, T2_inv_logistic]
    ring
  · calc
      _ = (1-logistic t)⁻¹-1 := by field_simp <;> ring
      _ = _ := by rw [T2_inv_complement]; ring

lemma T2_exp_taylor_local (x y : ℝ) (hxy : |y-x| ≤ 1) :
    |Real.exp y-Real.exp x-Real.exp x*(y-x)| ≤ Real.exp x*(y-x)^2 := by
  have he : Real.exp y = Real.exp x*Real.exp (y-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : Real.exp y-Real.exp x-Real.exp x*(y-x) =
      Real.exp x*(Real.exp (y-x)-1-(y-x)) := by rw [he]; ring
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_sub_id_le hxy) (Real.exp_pos _).le

lemma T2_ht_atom_taylor (b : Bool) (μ x y T M : ℝ) (hx : |x| ≤ T)
    (hxy : |y-x| ≤ 1) (hM : 0 ≤ M) (hμ : |μ| ≤ M) :
    |(bit b*μ/logistic y-(1-bit b)*μ/(1-logistic y))-
      (bit b*μ/logistic x-(1-bit b)*μ/(1-logistic x))+
      (bit b*μ*(1-logistic x)/logistic x+(1-bit b)*μ*logistic x/(1-logistic x))*(y-x)| ≤
        M*Real.exp T*(y-x)^2 := by
  have hbound (s t : ℝ) (hs : s ≤ T) (hst : |t-s| ≤ 1) :
      |μ*(Real.exp t-Real.exp s-Real.exp s*(t-s))| ≤ M*Real.exp T*(t-s)^2 := by
    rw [abs_mul]
    calc
      _ ≤ M*(Real.exp s*(t-s)^2) :=
        mul_le_mul hμ (T2_exp_taylor_local s t hst) (abs_nonneg _) hM
      _ ≤ _ := by
        have he := Real.exp_le_exp.mpr hs
        convert mul_le_mul_of_nonneg_left he (mul_nonneg hM (sq_nonneg (t-s))) using 1 <;> ring
  cases b
  · simp only [bit, Bool.false_eq_true, if_false, zero_mul, zero_div, sub_zero,
      one_mul, zero_sub, zero_add]
    have hb := hbound x y (abs_le.mp hx).2 hxy
    have he : -(μ/(1-logistic y))-(-(μ/(1-logistic x)))+
        μ*logistic x/(1-logistic x)*(y-x) =
        -(μ*(Real.exp y-Real.exp x-Real.exp x*(y-x))) := by
      rw [show μ*logistic x/(1-logistic x) = μ*Real.exp x by
        rw [mul_div_assoc, (T2_logistic_odds x).2]]
      simp only [div_eq_mul_inv, T2_inv_complement]
      ring
    rw [he, abs_neg]
    exact hb
  · simp only [bit, if_true, one_mul, sub_self, zero_mul, zero_div, sub_zero, add_zero]
    have hb := hbound (-x) (-y) (by linarith [(abs_le.mp hx).1])
      (by simpa only [neg_sub_neg, abs_sub_comm] using hxy)
    have he : μ/logistic y-μ/logistic x+μ*(1-logistic x)/logistic x*(y-x) =
        μ*(Real.exp (-y)-Real.exp (-x)-Real.exp (-x)*((-y)-(-x))) := by
      rw [show μ*(1-logistic x)/logistic x = μ*Real.exp (-x) by
        rw [mul_div_assoc, (T2_logistic_odds x).1]]
      simp only [div_eq_mul_inv, T2_inv_logistic]
      ring
    rw [he]
    convert hb using 1 <;> ring

lemma T2_dot_average {N k : ℕ} (X : Fin N → ℝ) (O : Fin N → Fin k → ℝ)
    (v : Fin k → ℝ) :
    dot (fun j => (∑ i, X i*O i j)/N) v = (∑ i, X i*dot (O i) v)/N := by
  simp only [dot, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma T2_ht_taylor {N k : ℕ} (R : CircleTable N) (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) (T M U : ℝ)
    (hN : 0 < N) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hO : ∀ i j, |O i j| ≤ U) (hR : ∀ i, |R i z| ≤ M)
    (hθ : ∀ i, |dot (O i) θ₀| ≤ T) (hδ : (k : ℝ)*U*‖θ-θ₀‖ ≤ 1) :
    |ht (propensities O θ) R z-ht (propensities O θ₀) R z+
        dot (T2_ht_gradient (propensities O θ₀) R O z) (θ-θ₀)| ≤
      M*Real.exp T*((k : ℝ)*U)^2*‖θ-θ₀‖^2 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hid : ht (propensities O θ) R z-ht (propensities O θ₀) R z+
      dot (T2_ht_gradient (propensities O θ₀) R O z) (θ-θ₀) =
      (∑ i, ((bit (z i)*R i z/propensities O θ i-(1-bit (z i))*R i z/(1-propensities O θ i))-
        (bit (z i)*R i z/propensities O θ₀ i-(1-bit (z i))*R i z/(1-propensities O θ₀ i))+
        (bit (z i)*R i z*(1-propensities O θ₀ i)/propensities O θ₀ i+
          (1-bit (z i))*R i z*propensities O θ₀ i/(1-propensities O θ₀ i))*
          dot (O i) (θ-θ₀)))/N := by
    rw [show T2_ht_gradient (propensities O θ₀) R O z = fun j =>
      (∑ i, (bit (z i)*R i z*(1-propensities O θ₀ i)/propensities O θ₀ i+
        (1-bit (z i))*R i z*propensities O θ₀ i/(1-propensities O θ₀ i))*O i j)/N from rfl,
      T2_dot_average]
    simp only [ht, ← sub_div, ← add_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hid, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |(bit (z i)*R i z/propensities O θ i-(1-bit (z i))*R i z/(1-propensities O θ i))-
        (bit (z i)*R i z/propensities O θ₀ i-(1-bit (z i))*R i z/(1-propensities O θ₀ i))+
        (bit (z i)*R i z*(1-propensities O θ₀ i)/propensities O θ₀ i+
          (1-bit (z i))*R i z*propensities O θ₀ i/(1-propensities O θ₀ i))*
          dot (O i) (θ-θ₀)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, M*Real.exp T*((k : ℝ)*U)^2*‖θ-θ₀‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hd := T2_dot_bound (O i) (θ-θ₀) U ‖θ-θ₀‖ hU (hO i)
        (fun j => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ-θ₀) j)
      have hb := T2_ht_atom_taylor (z i) (R i z) (dot (O i) θ₀) (dot (O i) θ)
        T M (hθ i) (by rw [← T2_dot_sub]; exact hd.trans hδ) hM (hR i)
      rw [← T2_dot_sub] at hb
      apply hb.trans
      have hd2 : (dot (O i) (θ-θ₀))^2 ≤ ((k : ℝ)*U*‖θ-θ₀‖)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
      convert mul_le_mul_of_nonneg_left hd2 (mul_nonneg hM (Real.exp_pos T).le) using 1 <;> ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma T2_spatial_tail (P : PopulationSequence Space) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h) :
    ∃ M D : ℝ, 0 < M ∧ 0 < D ∧ ∀ᶠ N in atTop,
      (∀ i z, |circleSequence P d N i z| ≤ M) ∧
      (∀ i, i ∈ spatialNeighborhoods P h N i) ∧
      (∀ i j, j ∈ spatialNeighborhoods P h N i ↔ i ∈ spatialNeighborhoods P h N j) ∧
      (∀ i, ((spatialNeighborhoods P h N i).card : ℝ) ≤ D) ∧
      (∀ i j, j ∉ spatialNeighborhoods P h N i → ¬ sharesSource (circleSequence P d N) i j) := by
  obtain ⟨M, hM, hraw⟩ := hP.1
  obtain ⟨c, hcount⟩ := hP.2.2
  refine ⟨M, max (c h) 0+1, hM, by positivity, ?_⟩
  filter_upwards [hraw, hWD, hloc, hcount h hh] with N hr hw hl hc
  refine ⟨CLTCompletion.circleAverage_abs_le (P N) d M hw (fun x z => (hr x z).le), ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and,
      CLTCompletion.nodeSeparation_self]
    exact hh
  · intro i j
    simp only [spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [CLTCompletion.nodeSeparation_symm (P N) i j]
  · intro i
    exact (hc i).trans (by linarith [le_max_left (c h) 0])
  · intro i j hj
    apply hl i j
    apply lt_of_not_ge
    intro hle
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)

lemma T2_information_transpose {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ) :
    (information p O)ᵀ = information p O := by
  ext a b
  simp only [Matrix.transpose_apply, information]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma T2_score_correction {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) :
    dot (T2_population_gradient p R O) ((information p O)⁻¹ *ᵥ logisticScore p O z) =
      (∑ i, (bit (z i)-p i)*dot (O i) (scoreGamma p R O))/N := by
  have hsym : (information p O)⁻¹ᵀ = (information p O)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, T2_information_transpose]
  have hid := Matrix.dotProduct_transpose_mulVec ((information p O)⁻¹)
    (T2_population_gradient p R O) (logisticScore p O z)
  rw [hsym] at hid
  rw [← T2_score_dot]
  change _ = dot (logisticScore p O z) ((information p O)⁻¹ *ᵥ T2_population_gradient p R O)
  simpa only [dot, dotProduct] using hid

lemma T2_ipw_remainder_bound {N k : ℕ} (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (θ₀ θ : Fin k → ℝ) (z : Assignment N)
    (T M U w c : ℝ) (hN : 0 < N) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hw : 0 < w) (hc : 0 < c) (hR : ∀ i z, |R i z| ≤ M)
    (hO : ∀ i j, |O i j| ≤ U) (hθ : ∀ i, |dot (O i) θ₀| ≤ T)
    (hδ : (k : ℝ)*U*‖θ-θ₀‖ ≤ 1)
    (hweight : ∀ i, w ≤ propensities O θ₀ i*(1-propensities O θ₀ i))
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hscore : logisticScore (propensities O θ) O z = 0) :
    let A := M*Real.exp T*((k : ℝ)*U)^2 + (k : ℝ) +
      (k : ℝ)*(M*U)*((k : ℝ)/(w*c)*(((k : ℝ)*U)^2*U)) + 1
    |ht (propensities O θ) R z-(ht (propensities O θ₀) R z-
      (∑ i, (bit (z i)-propensities O θ₀ i)*dot (O i) (scoreGamma (propensities O θ₀) R O))/N)| ≤
        A*(‖θ-θ₀‖^2+‖T2_ht_gradient (propensities O θ₀) R O z-
          T2_population_gradient (propensities O θ₀) R O‖^2) := by
  let p := propensities O θ₀
  let Δ := θ-θ₀
  let S := logisticScore p O z
  let D := T2_population_gradient p R O
  let G := T2_ht_gradient p R O z
  let e := Δ-(information p O)⁻¹ *ᵥ S
  let C := (k : ℝ)/(w*c)*(((k : ℝ)*U)^2*U)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (i : Fin N) : 0 < p i ∧ p i < 1 := ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  have htaylor := T2_ht_taylor R O θ₀ θ z T M U hN hM hU hO (fun i => hR i z) hθ hδ
  have he : ‖e‖ ≤ C*‖Δ‖^2 :=
    T2_mle_remainder_bound O θ₀ θ z w c U hw hc hU hN hO hweight hgram hscore
  have hD : ‖D‖ ≤ M*U := T2_population_gradient_bound p R O M U hp hN hM hU hR hO
  have hdot (u v : Fin k → ℝ) : |dot u v| ≤ (k : ℝ)*‖u‖*‖v‖ :=
    T2_dot_bound u v ‖u‖ ‖v‖ (norm_nonneg _)
      (fun j => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u j)
      (fun j => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j)
  have hDe : |dot D e| ≤ (k : ℝ)*(M*U)*C*‖Δ‖^2 := by
    calc
      _ ≤ (k : ℝ)*‖D‖*‖e‖ := hdot D e
      _ ≤ (k : ℝ)*(M*U)*(C*‖Δ‖^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)) he
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hG : |dot (G-D) Δ| ≤ (k : ℝ)*(‖Δ‖^2+‖G-D‖^2) := by
    apply (hdot _ _).trans
    have h := sq_nonneg (‖Δ‖-‖G-D‖)
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hk h, mul_nonneg hk (sq_nonneg ‖Δ‖),
      mul_nonneg hk (sq_nonneg ‖G-D‖)]
  have hid : ht (propensities O θ) R z-(ht p R z-
      (∑ i, (bit (z i)-p i)*dot (O i) (scoreGamma p R O))/N) =
      (ht (propensities O θ) R z-ht p R z+dot G Δ)-dot (G-D) Δ-dot D e := by
    rw [← T2_score_correction]
    dsimp only [e]
    simp only [dot, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hid]
  dsimp only
  have htri : |(ht (propensities O θ) R z-ht p R z+dot G Δ)-dot (G-D) Δ-dot D e| ≤
      |ht (propensities O θ) R z-ht p R z+dot G Δ|+|dot (G-D) Δ|+|dot D e| := by
    calc
      _ ≤ |ht (propensities O θ) R z-ht p R z+dot G Δ-dot (G-D) Δ|+|dot D e| := abs_sub _ _
      _ ≤ _ := add_le_add (abs_sub _ _) le_rfl
  apply htri.trans
  have hδ0 : 0 ≤ ‖Δ‖^2 := sq_nonneg _
  have hG0 : 0 ≤ ‖G-D‖^2 := sq_nonneg _
  have hT0 : 0 ≤ M*Real.exp T*((k : ℝ)*U)^2 := by positivity
  have hDC : 0 ≤ (k : ℝ)*(M*U)*C := by positivity
  change |ht (propensities O θ) R z-ht p R z+dot G Δ| ≤
    M*Real.exp T*((k : ℝ)*U)^2*‖Δ‖^2 at htaylor
  change _ ≤ _
  dsimp only [C] at hDe hDC
  nlinarith [htaylor, hG, hDe, mul_nonneg hT0 hG0, mul_nonneg hDC hG0]

lemma T2_ipw_expansion {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) (hinterior : θ₀ ∈ interior Θ)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀)) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    BigOp p (fun N z => fittedIPW (R N) (O N) (θhat N) z-
      (ht (p N) (R N) z-(∑ i, (bit (z i)-p N i)*dot (O N i)
        (scoreGamma (p N) (R N) (O N)))/N)) (fun N => (N : ℝ)⁻¹) := by
  let p := fun N => propensities (O N) θ₀
  let R := circleSequence P d
  let B := spatialNeighborhoods P h
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  obtain ⟨ε, hε, hε1, hπ⟩ := hoverlap
  have hπ' (N : ℕ) (i : Fin N) : ε ≤ p N i ∧ ε ≤ 1-p N i :=
    ⟨(hπ N i).1.le, by linarith [(hπ N i).2]⟩
  obtain ⟨U₀, hO₀⟩ := hlog.2.2.1
  let U := max U₀ 0
  have hU : 0 ≤ U := le_max_right _ _
  have hO (N : ℕ) (i : Fin N) (j : Fin k) : |O N i j| ≤ U :=
    (hO₀ N i j).trans (le_max_left _ _)
  obtain ⟨c, hc, hgram⟩ := hlog.2.2.2.1
  obtain ⟨M, D, hM, hD, hspatial⟩ := T2_spatial_tail P d h hh hP hWD hloc
  obtain ⟨K₀, hK₀, hmle⟩ := T2_mle_second O θ₀ Θ θhat hlog hp
  let K := K₀+(k : ℝ)*D*(M*U/ε)^2+1
  have hK : 0 < K := by dsimp [K]; positivity
  let J : ∀ N, Assignment N → ℝ := fun N z =>
    Real.sqrt (‖θhat N z-θ₀‖^2+‖T2_ht_gradient (p N) (R N) (O N) z-
      T2_population_gradient (p N) (R N) (O N)‖^2)
  have hJ2 (N : ℕ) (z : Assignment N) : (J N z)^2 =
      ‖θhat N z-θ₀‖^2+‖T2_ht_gradient (p N) (R N) (O N) z-
        T2_population_gradient (p N) (R N) (O N)‖^2 := Real.sq_sqrt (by positivity)
  have hdelta (N : ℕ) (z : Assignment N) : ‖θhat N z-θ₀‖ ≤ J N z := by
    calc
      _ = Real.sqrt (‖θhat N z-θ₀‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ J N z := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hJmoment : ∀ᶠ N in atTop, expect (p N) (fun z => (J N z)^2) ≤ K/N := by
    filter_upwards [hmle, hspatial, eventually_gt_atTop 0] with N hm hs hN
    simp_rw [hJ2]
    rw [expect_add]
    have hg := T2_gradient_second (p N) (R N) (O N) (B N) D M U ε (hp N) hε (hπ' N)
      hN hM.le hU hs.1 (hO N) hs.2.2.2.1 hs.2.2.1 hs.2.2.2.2
    calc
      _ ≤ K₀/N+((k : ℝ)*D*(M*U/ε)^2)/N := add_le_add hm hg
      _ ≤ K/N := by rw [← add_div]; apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N); dsimp [K]; linarith
  have hJprob : InProb p J :=
    T2_inprob_of_bigop p hp J _
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      (T2_bigop_of_second p hp J K hK hJmoment)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hinterior)
  let r := min (r₀/2) (1/((k : ℝ)*U+1))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  let T := (k : ℝ)*U*‖θ₀‖
  let A := M*Real.exp T*((k : ℝ)*U)^2+(k : ℝ)+
    (k : ℝ)*(M*U)*((k : ℝ)/(ε^2*c)*(((k : ℝ)*U)^2*U))+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply T2_bigop_quadratic_good p hp J _ K A r hK hA hr hJprob hJmoment
  filter_upwards [hgram, hspatial, eventually_gt_atTop 0] with N hg hs hN z hz
  have hz' : J N z ≤ r := (le_abs_self _).trans hz
  have hδr := (hdelta N z).trans hz'
  have hθ : θhat N z ∈ interior Θ := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hb : ‖θhat N z-θ₀‖ ≤ r₀/2 := hδr.trans (min_le_left _ _)
    linarith
  have hδ : (k : ℝ)*U*‖θhat N z-θ₀‖ ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left (hδr.trans (min_le_right _ _))
      (mul_nonneg (Nat.cast_nonneg k) hU)
    have hc0 : 0 < (k : ℝ)*U+1 := by positivity
    have hratio : (k : ℝ)*U*(1/((k : ℝ)*U+1)) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one hc0).mpr (by linarith)
    exact hb.trans hratio
  have hscore := T2_interior_score (O N) z Θ (θhat N z) hθ (hlog.2.2.2.2 N z).2
  have hb := T2_ipw_remainder_bound (R N) (O N) θ₀ (θhat N z) z T M U (ε^2) c
    hN hM.le hU (sq_pos_of_pos hε) hc hs.1 (hO N)
    (fun i => T2_dot_bound (O N i) θ₀ U ‖θ₀‖ hU (hO N i)
      (fun j => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm θ₀ j)) hδ
    (fun i => by simpa only [pow_two] using mul_le_mul (hπ' N i).1 (hπ' N i).2 hε.le (hp N i).1.le)
    hg hscore
  rw [hJ2]
  exact hb

lemma T2_bigop_ninv_little_root (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U : ∀ N, Assignment N → ℝ)
    (hU : BigOp p U (fun N => (N : ℝ)⁻¹)) :
    LittleOp p U (fun N => (Real.sqrt N)⁻¹) := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N => ha.trans_le (T2_prob_nonneg (p N) (hp N) _))
  · intro η hη
    obtain ⟨C, hC, htail⟩ := hU η hη
    have hscale : Tendsto (fun N : ℕ => C*(Real.sqrt N)⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
    filter_upwards [htail, hscale.eventually (eventually_lt_nhds hε), eventually_gt_atTop 0]
      with N ht hs hN
    have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
    have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
    apply (T2_prob_mono (p N) (hp N) _ _ ?_).trans_lt ht
    intro z hz
    by_contra hnot
    have hb : |U N z| ≤ C*(N : ℝ)⁻¹ := by
      simpa only [abs_of_pos (inv_pos.mpr hn)] using le_of_not_gt hnot
    have hb' := mul_le_mul_of_nonneg_left hb hroot.le
    have hid : Real.sqrt (N : ℝ)*(C*(N : ℝ)⁻¹) = C*(Real.sqrt (N : ℝ))⁻¹ := by
      have hsq := Real.sq_sqrt hn.le
      field_simp
      nlinarith
    rw [hid] at hb'
    rw [div_inv_eq_mul, abs_mul, abs_of_pos hroot] at hz
    linarith

lemma T2_ipw_little {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) (hinterior : θ₀ ∈ interior Θ)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀)) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    LittleOp p (fun N z => augmented (p N) (R N) (scoreFits (p N) (R N) (O N)) z-
      fittedIPW (R N) (O N) (θhat N) z) (fun N => (Real.sqrt N)⁻¹) := by
  let p := fun N => propensities (O N) θ₀
  let R := circleSequence P d
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  have hb := T2_ipw_expansion P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior hoverlap
  apply T2_bigop_ninv_little_root p hp
  intro ε hε
  obtain ⟨C, hC, hTail⟩ := hb ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hTail] with N hN
  have hid := (corrected_ipw_finite (p N) (R N) (O N) (hp N)).1
  have heq : prob (p N) (fun z => C*|(N : ℝ)⁻¹| <
      |augmented (p N) (R N) (scoreFits (p N) (R N) (O N)) z-
        fittedIPW (R N) (O N) (θhat N) z|) =
      prob (p N) (fun z => C*|(N : ℝ)⁻¹| <
      |fittedIPW (R N) (O N) (θhat N) z-(ht (p N) (R N) z-
        (∑ i, (bit (z i)-p N i)*dot (O N i) (scoreGamma (p N) (R N) (O N)))/N)|) := by
    congr 1
    funext z
    rw [hid z, abs_sub_comm]
  rw [heq]
  exact hN

lemma T2_average_bound {N k : ℕ} (X : Fin N → Fin k → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hN : 0 < N) (hX : ∀ i j, |X i j| ≤ C) :
    ‖fun j => (∑ i, X i j)/N‖ ≤ C := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |X i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hX i j)
    _ = _ := by simp [mul_comm]

lemma T2_beta_bound {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (w c M U : ℝ) (hw : 0 < w) (hc : 0 < c)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hN : 0 < N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hweight : ∀ i, w ≤ p i*(1-p i))
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hR : ∀ i z, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U) (a : Bool) :
    ‖beta p R O a‖ ≤ (k : ℝ)/(w*c)*(M*U) := by
  have hnum : ‖fun j => (∑ i, marginal p R i a*p i*(1-p i)*O i j)/N‖ ≤ M*U := by
    apply T2_average_bound _ _ (mul_nonneg hM hU) hN
    intro i j
    have hw0 : 0 ≤ p i*(1-p i) := mul_nonneg (hp i).1.le (sub_pos.mpr (hp i).2).le
    have hw1 : p i*(1-p i) ≤ 1 := by nlinarith [(hp i).1, (hp i).2, sq_nonneg (p i)]
    rw [show marginal p R i a*p i*(1-p i)*O i j =
      (marginal p R i a*O i j)*(p i*(1-p i)) by ring, abs_mul, abs_mul,
      abs_of_nonneg hw0]
    calc
      _ ≤ (M*U)*1 := mul_le_mul (mul_le_mul (T2_marginal_abs_le p R hp M hR i a)
        (hO i j) (abs_nonneg _) hM) hw1 hw0 (mul_nonneg hM hU)
      _ = _ := mul_one _
  exact (T2_inverse_bound (information p O) (w*c) (mul_pos hw hc)
    (T2_information_coercive p O w c hw.le hweight hgram) _).trans
      (mul_le_mul_of_nonneg_left hnum (by positivity))

lemma T2_gamma_bound {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (w c M U : ℝ) (hw : 0 < w) (hc : 0 < c)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hN : 0 < N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hweight : ∀ i, w ≤ p i*(1-p i))
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hR : ∀ i z, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U) :
    ‖scoreGamma p R O‖ ≤ (k : ℝ)/(w*c)*(M*U) := by
  exact (T2_inverse_bound (information p O) (w*c) (mul_pos hw hc)
    (T2_information_coercive p O w c hw.le hweight hgram) (T2_population_gradient p R O)).trans
      (mul_le_mul_of_nonneg_left (T2_population_gradient_bound p R O M U hp hN hM hU hR hO)
        (by positivity))

lemma T2_scorefits_bound {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (w c M U : ℝ) (hw : 0 < w) (hc : 0 < c)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hN : 0 < N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hweight : ∀ i, w ≤ p i*(1-p i))
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hR : ∀ i z, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U) (i : Fin N) (a : Bool) :
    |scoreFits p R O i a| ≤ 3*((k : ℝ)*U*((k : ℝ)/(w*c)*(M*U))) := by
  let K := (k : ℝ)*U*((k : ℝ)/(w*c)*(M*U))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hβ (a : Bool) : |printedFits p R O i a| ≤ K := by
    exact T2_dot_bound (O i) (beta p R O a) U ((k : ℝ)/(w*c)*(M*U)) hU (hO i)
      (fun j => by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (beta p R O a) j).trans
          (T2_beta_bound p R O w c M U hw hc hM hU hN hp hweight hgram hR hO a))
  have hγ : |dot (O i) (scoreGamma p R O)| ≤ K := by
    exact T2_dot_bound (O i) (scoreGamma p R O) U ((k : ℝ)/(w*c)*(M*U)) hU (hO i)
      (fun j => by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (scoreGamma p R O) j).trans
          (T2_gamma_bound p R O w c M U hw hc hM hU hN hp hweight hgram hR hO))
  have hδ : |printedFits p R O i true-printedFits p R O i false| ≤ 2*K :=
    (abs_sub _ _).trans (by linarith [hβ true, hβ false])
  have hw0 : 0 ≤ p i*(1-p i) := mul_nonneg (hp i).1.le (sub_pos.mpr (hp i).2).le
  have hw1 : p i*(1-p i) ≤ 1 := by nlinarith [(hp i).1, (hp i).2, sq_nonneg (p i)]
  have hweighted : |p i*(1-p i)*dot (O i) (scoreGamma p R O)| ≤ K := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact (mul_le_mul_of_nonneg_left hγ hw0).trans (by nlinarith)
  cases a
  · change |-(1-p i)*(printedFits p R O i true-printedFits p R O i false)+
      p i*(1-p i)*dot (O i) (scoreGamma p R O)| ≤ 3*K
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_neg, abs_of_pos (sub_pos.mpr (hp i).2)]
    have hm := mul_le_mul_of_nonneg_left hδ (sub_pos.mpr (hp i).2).le
    nlinarith [(hp i).1]
  · change |p i*(printedFits p R O i true-printedFits p R O i false)+
      p i*(1-p i)*dot (O i) (scoreGamma p R O)| ≤ 3*K
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_pos (hp i).1]
    have hm := mul_le_mul_of_nonneg_left hδ (hp i).1.le
    nlinarith [(hp i).2]

def T2_center_residual {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) : CircleTable N :=
  fun i z => residualContrast p R g i z-expect p (residualContrast p R g i)

lemma T2_center_residual_mean {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) : expect p (T2_center_residual p R g i) = 0 := by
  unfold T2_center_residual
  rw [expect_sub, expect_const, sub_self]

lemma T2_center_residual_sum {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N) (z : Assignment N) :
    (∑ i, T2_center_residual p R g i z) = (N : ℝ)*(augmented p R g z-ame p R) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [T2_center_residual, residualContrast_mean p R g _ hp, residualEffect,
    Finset.sum_sub_distrib, ame, augmented, residualContrast, sub_div]
  field_simp
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma T2_center_residual_second {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N) :
    expect p (fun z => (∑ i, T2_center_residual p R g i z)^2) =
      (N : ℝ)^2*variance p (augmented p R g) := by
  simp_rw [T2_center_residual_sum p R g hp hN, mul_pow]
  rw [expect_mul]
  congr 1
  rw [variance, cov_centered, augmented_unbiased p R g hp]
  congr 1
  funext z
  ring

lemma T2_residual_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (ε M F : ℝ) (hε : 0 < ε) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hπ : ∀ i, ε ≤ p i ∧ ε ≤ 1-p i) (hR : ∀ i z, |R i z| ≤ M)
    (hg : ∀ i a, |g i a| ≤ F) (i : Fin N) (z : Assignment N) :
    |residualContrast p R g i z| ≤ (M+F)/ε := by
  have hdiff (a : Bool) : |R i z-g i a| ≤ M+F :=
    (abs_sub _ _).trans (add_le_add (hR i z) (hg i a))
  cases hz : z i
  · have hp : 0 < 1-p i := hε.trans_le (hπ i).2
    simp only [residualContrast, hz, bit, Bool.false_eq_true, if_false, zero_mul, zero_div,
      sub_zero, one_mul, zero_sub, abs_neg, abs_div, abs_of_pos hp]
    exact (div_le_div_of_nonneg_right (hdiff false) hp.le).trans
      (div_le_div_of_nonneg_left (add_nonneg hM hF) hε (hπ i).2)
  · have hp : 0 < p i := hε.trans_le (hπ i).1
    simp only [residualContrast, hz, bit, if_true, one_mul, sub_self, zero_mul,
      zero_div, sub_zero, abs_div, abs_of_pos hp]
    exact (div_le_div_of_nonneg_right (hdiff true) hp.le).trans
      (div_le_div_of_nonneg_left (add_nonneg hM hF) hε (hπ i).1)

lemma T2_center_residual_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (C : ℝ)
    (hC : ∀ i z, |residualContrast p R g i z| ≤ C) (i : Fin N) (z : Assignment N) :
    |T2_center_residual p R g i z| ≤ 2*C := by
  have hm : |expect p (residualContrast p R g i)| ≤ C := by
    apply abs_le.mpr
    constructor
    · have h := expect_mono p hp (fun _ => -C) (residualContrast p R g i)
        (fun z => (abs_le.mp (hC i z)).1)
      simpa only [expect_const] using h
    · have h := expect_mono p hp (residualContrast p R g i) (fun _ => C)
        (fun z => (abs_le.mp (hC i z)).2)
      simpa only [expect_const] using h
  exact (abs_sub _ _).trans (by linarith [hC i z])

lemma T2_center_residual_graph {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hG : FiniteDependencyGraph p (fun i z => residualContrast p R g i z) B) :
    DependencyGraph (CLTCompletion.designMeasure p hp) (T2_center_residual p R g) B := by
  have h := CLTCompletion.finiteGraph_to_measureGraph p hp _ B hG
  refine ⟨h.1, h.2.1, ?_⟩
  intro I J hsep
  exact (h.2.2 I J hsep).comp
    (φ := fun v : I → ℝ => fun i => v i-expect p (residualContrast p R g i))
    (ψ := fun v : J → ℝ => fun i => v i-expect p (residualContrast p R g i))
    (by fun_prop) (by fun_prop)

lemma T2_augmented_clt (p : ∀ N, Fin N → ℝ) (R : ∀ N, CircleTable N)
    (g : ∀ N, Fin N → Bool → ℝ) (B : ∀ N, Fin N → Finset (Fin N))
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (ε M F : ℝ)
    (hε : 0 < ε) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hπ : ∀ N i, ε ≤ p N i ∧ ε ≤ 1-p N i)
    (D : ℕ) (hregular : ∀ᶠ N in atTop, (∀ i z, |R N i z| ≤ M) ∧
      (∀ i a, |g N i a| ≤ F) ∧ (∀ i, (B N i).card ≤ D) ∧
      FiniteDependencyGraph (p N) (fun i z => residualContrast (p N) (R N) (g N) i z) (B N))
    (hv : Nondegenerate (fun N => variance (p N) (augmented (p N) (R N) (g N)))) :
    NormalLimit p (fun N z => (augmented (p N) (R N) (g N) z-ame (p N) (R N))/
      Real.sqrt (variance (p N) (augmented (p N) (R N) (g N)))) := by
  obtain ⟨v, hv, hvar⟩ := hv
  have htail : ∀ᶠ N in atTop, 0 < N ∧ (∀ i z, |R N i z| ≤ M) ∧
      (∀ i a, |g N i a| ≤ F) ∧ (∀ i, (B N i).card ≤ D) ∧
      FiniteDependencyGraph (p N) (fun i z => residualContrast (p N) (R N) (g N) i z) (B N) ∧
      v ≤ (N : ℝ)*variance (p N) (augmented (p N) (R N) (g N)) := by
    filter_upwards [hregular, hvar, eventually_gt_atTop 0] with N hr hvN hN
    exact ⟨hN, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hvN⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp htail
  have hk (n : ℕ) := hK (n+K) (Nat.le_add_left _ _)
  let μ := fun n => CLTCompletion.designMeasure (p (n+K)) (hp (n+K))
  let X := fun n => T2_center_residual (p (n+K)) (R (n+K)) (g (n+K))
  have hgraph (n : ℕ) : DependencyGraph (μ n) (X n) (B (n+K)) :=
    T2_center_residual_graph _ _ _ _ (hp (n+K)) (hk n).2.2.2.2.1
  let Dep : ∀ n, Causalean.Mathlib.Probability.SteinMethod.DepGraph (X n) (μ n) := fun n => {
    G := fun i j => j ∈ B (n+K) i
    decG := inferInstance
    refl := (hgraph n).1
    symm := fun i j hij => ((hgraph n).2.1 i j).mp hij
    meas := fun i => measurable_of_finite _
    indep := (hgraph n).2.2 }
  have hdeg (n : ℕ) (i : Fin (n+K)) : ((Dep n).nbhd i).card ≤ D := by
    have he : (Dep n).nbhd i = B (n+K) i := by ext j; exact (Dep n).mem_nbhd_iff
    rw [he]
    exact (hk n).2.2.2.1 i
  let V := fun n => ((n+K : ℕ) : ℝ)^2*variance (p (n+K))
    (augmented (p (n+K)) (R (n+K)) (g (n+K)))
  have hmean (n : ℕ) (i : Fin (n+K)) : (∫ z, X n i z ∂μ n) = 0 := by
    rw [CLTCompletion.designMeasure_integral]
    exact T2_center_residual_mean _ _ _ i
  have hsecond (n : ℕ) :
      (∫ z, (Causalean.Mathlib.Probability.SteinMethod.depSum (X n) z)^2 ∂μ n) = V n := by
    rw [CLTCompletion.designMeasure_integral]
    exact T2_center_residual_second _ _ _ (hp (n+K)) (hk n).1
  have hfloor : ∀ᶠ n in atTop, v*(Fintype.card (Fin (n+K)) : ℝ) ≤ V n := by
    filter_upwards [] with n
    simpa only [V, Fintype.card_fin, pow_two, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left (hk n).2.2.2.2.2 (Nat.cast_nonneg (n+K) : (0 : ℝ) ≤ (n+K : ℕ))
  have hbound (n : ℕ) (i : Fin (n+K)) : ∀ᵐ z ∂μ n, |X n i z| ≤ 2*((M+F)/ε) := by
    apply Eventually.of_forall
    exact T2_center_residual_bound _ _ _ (hp (n+K)) _
      (T2_residual_bound _ _ _ ε M F hε hM hF (hπ (n+K)) (hk n).2.1 (hk n).2.2.1) i
  intro x
  apply (tendsto_add_atTop_iff_nat K).mp
  have hclt := Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt_ae
    μ X Dep D hdeg (2*((M+F)/ε)) hbound hmean V hsecond v hv hfloor
    (by simpa only [Fintype.card_fin] using tendsto_add_atTop_nat K) x
  apply hclt.congr
  intro n
  rw [MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  change (CLTCompletion.designMeasure (p (n+K)) (hp (n+K)) _).toReal = _
  rw [CLTCompletion.designMeasure_apply]
  congr 1
  funext z
  have hn : ((n+K : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hk n).1.ne'
  have hsqrt : Real.sqrt (V n) = ((n+K : ℕ) : ℝ)*
      Real.sqrt (variance (p (n+K)) (augmented (p (n+K)) (R (n+K)) (g (n+K)))) := by
    dsimp only [V]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  simp only [Causalean.Mathlib.Probability.SteinMethod.depSum, X,
    T2_center_residual_sum _ _ _ (hp (n+K)) (hk n).1, hsqrt,
    mul_div_mul_left _ _ hn, Set.mem_preimage, Set.mem_Iic]

lemma T2_leading_normal {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀))
    (hv : Nondegenerate (fun N => variance (propensities (O N) θ₀)
      (augmented (propensities (O N) θ₀) (circleSequence P d N)
        (scoreFits (propensities (O N) θ₀) (circleSequence P d N) (O N))))) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    NormalLimit p (fun N z => (augmented (p N) (R N) (scoreFits (p N) (R N) (O N)) z-
      ame (p N) (R N))/Real.sqrt (variance (p N) (augmented (p N) (R N) (scoreFits (p N) (R N) (O N))))) := by
  let p := fun N => propensities (O N) θ₀
  let R := circleSequence P d
  let B := spatialNeighborhoods P h
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  obtain ⟨ε, hε, hε1, hπ⟩ := hoverlap
  have hπ' (N : ℕ) (i : Fin N) : ε ≤ p N i ∧ ε ≤ 1-p N i :=
    ⟨(hπ N i).1.le, by linarith [(hπ N i).2]⟩
  obtain ⟨U₀, hO₀⟩ := hlog.2.2.1
  let U := max U₀ 0
  have hU : 0 ≤ U := le_max_right _ _
  have hO (N : ℕ) (i : Fin N) (j : Fin k) : |O N i j| ≤ U :=
    (hO₀ N i j).trans (le_max_left _ _)
  obtain ⟨c, hc, hgram⟩ := hlog.2.2.2.1
  obtain ⟨M, D, hM, hD, hspatial⟩ := T2_spatial_tail P d h hh hP hWD hloc
  let F := 3*((k : ℝ)*U*((k : ℝ)/(ε^2*c)*(M*U)))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  apply T2_augmented_clt p R (fun N => scoreFits (p N) (R N) (O N)) B hp ε M F hε hM.le hF
    hπ' (Nat.ceil D) _ hv
  filter_upwards [hspatial, hgram, eventually_gt_atTop 0] with N hs hg hN
  refine ⟨hs.1, ?_, ?_, design_dependency_graph _ _ _ _ (hp N)
    hs.2.1 hs.2.2.1 hs.2.2.2.2⟩
  · intro i a
    apply T2_scorefits_bound (p N) (R N) (O N) (ε^2) c M U (sq_pos_of_pos hε) hc hM.le hU
      hN (hp N) _ hg hs.1 (hO N) i a
    intro i
    simpa only [pow_two] using mul_le_mul (hπ' N i).1 (hπ' N i).2 hε.le (hp N i).1.le
  · intro i
    exact_mod_cast (hs.2.2.2.1 i).trans (Nat.le_ceil D)

lemma T2_standardized_remainder (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (A F : ∀ N, Assignment N → ℝ)
    (V : ℕ → ℝ) (hv : Nondegenerate V)
    (hrem : LittleOp p (fun N z => A N z-F N z) (fun N => (Real.sqrt N)⁻¹)) :
    InProb p (fun N z => (F N z-A N z)/Real.sqrt (V N)) := by
  obtain ⟨v, hv, hvar⟩ := hv
  intro ε hε
  have hlim := hrem (ε*Real.sqrt v) (mul_pos hε (Real.sqrt_pos.mpr hv))
  have hbound : ∀ᶠ N in atTop,
      prob (p N) (fun z => ε < |(F N z-A N z)/Real.sqrt (V N)|) ≤
      prob (p N) (fun z => ε*Real.sqrt v < |(A N z-F N z)/((Real.sqrt N)⁻¹)|) := by
    filter_upwards [hvar, eventually_gt_atTop 0] with N hV hN
    have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
    have hvN : 0 < V N := by nlinarith
    have hroot := Real.sqrt_pos.mpr hvN
    have hrootN := Real.sqrt_pos.mpr hn
    have hscale : Real.sqrt v ≤ Real.sqrt (N : ℝ)*Real.sqrt (V N) := by
      rw [← Real.sqrt_mul hn.le]
      exact Real.sqrt_le_sqrt hV
    apply T2_prob_mono _ (hp N)
    intro z hz
    rw [abs_div, abs_of_pos hroot, lt_div_iff₀ hroot] at hz
    have hm := mul_lt_mul_of_pos_left hz hrootN
    rw [div_inv_eq_mul, abs_mul, abs_of_pos hrootN, abs_sub_comm]
    nlinarith [mul_le_mul_of_nonneg_left hscale hε.le]
  exact squeeze_zero' (Eventually.of_forall (fun N => T2_prob_nonneg _ (hp N) _)) hbound hlim

lemma T2_fitted_normal {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) (hinterior : θ₀ ∈ interior Θ)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀))
    (hv : Nondegenerate (fun N => variance (propensities (O N) θ₀)
      (augmented (propensities (O N) θ₀) (circleSequence P d N)
        (scoreFits (propensities (O N) θ₀) (circleSequence P d N) (O N))))) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    NormalLimit p (fun N z => (fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N))/
      Real.sqrt (variance (p N) (augmented (p N) (R N) (scoreFits (p N) (R N) (O N))))) := by
  let p := fun N => propensities (O N) θ₀
  let R := circleSequence P d
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  have hnormal := T2_leading_normal P O θ₀ Θ θhat d h hh hP hWD hloc hlog hoverlap hv
  have hrem := T2_standardized_remainder p hp
    (fun N => augmented (p N) (R N) (scoreFits (p N) (R N) (O N)))
    (fun N => fittedIPW (R N) (O N) (θhat N)) _ hv
    (T2_ipw_little P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior hoverlap)
  apply T42_slutsky p hp _ _ hnormal
  convert hrem using 1
  funext N z
  ring

lemma T2_normalcdf_eq_cdf (t : ℝ) :
    normalCDF t = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t := by
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

lemma T2_quantile_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < normalQuantile (1-α/2) :=
  AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1

lemma T2_quantile_cdf (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    normalCDF (normalQuantile (1-α/2)) = 1-α/2 :=
  AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1

lemma T2_normalcdf_neg (t : ℝ) : normalCDF (-t) = 1-normalCDF t := by
  simp_rw [T2_normalcdf_eq_cdf]
  exact AronowAudit.P053.NormalCompletion.normal_cdf_neg t

lemma T2_wald_conservative (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U W : ∀ N, Assignment N → ℝ)
    (V b : ℕ → ℝ) (hv : Nondegenerate V)
    (hEV : ∀ᶠ N in atTop, V N ≤ b N)
    (hW : InProb p (fun N z => (N : ℝ)*(W N z-b N)))
    (hU : NormalLimit p (fun N z => U N z/Real.sqrt (V N)))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Conservative (fun N => prob (p N) (fun z => |U N z| ≤
      normalQuantile (1-α/2)*Real.sqrt (W N z))) α := by
  obtain ⟨v, hv, hvar⟩ := hv
  intro ε hε
  let η := min (ε/4) ((1-α)/2)
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  let α' := α+η
  have hα' : 0 < α' := by dsimp [α']; linarith
  have hα'1 : α' < 1 := by have h := min_le_right (ε/4) ((1-α)/2); dsimp [α', η]; linarith
  let q := normalQuantile (1-α/2)
  let t := normalQuantile (1-α'/2)
  have hq : 0 < q := T2_quantile_pos α hα hα1
  have ht : 0 < t := T2_quantile_pos α' hα' hα'1
  have htq : t < q := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [← T2_normalcdf_eq_cdf, ← T2_normalcdf_eq_cdf]
    rw [show normalCDF t = 1-α'/2 from T2_quantile_cdf α' hα' hα'1,
      show normalCDF q = 1-α/2 from T2_quantile_cdf α hα hα1]
    dsimp [α']
    linarith
  let r := (t/q)^2
  have hr0 : 0 < r := sq_pos_of_pos (div_pos ht hq)
  have hr1 : r < 1 := by
    have hr : 0 < t/q := div_pos ht hq
    have hr' : t/q < 1 := (div_lt_one hq).mpr htq
    dsimp [r]
    nlinarith
  let c := (1-r)*v
  have hc : 0 < c := mul_pos (sub_pos.mpr hr1) hv
  have hmass : normalCDF t-normalCDF (-t) = 1-α' := by
    rw [T2_normalcdf_neg, show normalCDF t = 1-α'/2 from T2_quantile_cdf α' hα' hα'1]
    ring
  have hupper := (hU (-t)).eventually (eventually_lt_nhds (show normalCDF (-t)<normalCDF (-t)+ε/4 by linarith))
  have hlower := (hU t).eventually (eventually_gt_nhds (show normalCDF t-ε/4<normalCDF t by linarith))
  have hbad := (hW c hc).eventually (eventually_lt_nhds (by linarith : (0 : ℝ)<ε/4))
  filter_upwards [hEV, hvar, eventually_gt_atTop 0, hupper, hlower, hbad]
    with N hEN hvN hN hCDFlo hCDFhi hbadN
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hVpos : 0 < V N := by nlinarith
  have hroot := Real.sqrt_pos.mpr hVpos
  have hevent : ∀ z, U N z/Real.sqrt (V N) ≤ t →
      U N z/Real.sqrt (V N) ≤ -t ∨
        |U N z| ≤ q*Real.sqrt (W N z) ∨ c < |(N : ℝ)*(W N z-b N)| := by
    intro z hz
    by_cases hleft : U N z/Real.sqrt (V N) ≤ -t
    · exact Or.inl hleft
    · right
      by_cases hsmall : W N z < r*V N
      · right
        have hlt : c < (N : ℝ)*(b N-W N z) := by
          have hmul := mul_lt_mul_of_pos_left hsmall hn
          have hv' := mul_le_mul_of_nonneg_left hvN (sub_pos.mpr hr1).le
          dsimp [c]
          nlinarith
        have hab : (N : ℝ)*(b N-W N z) ≤ |(N : ℝ)*(W N z-b N)| := by
          convert neg_le_abs ((N : ℝ)*(W N z-b N)) using 1 <;> ring
        exact hlt.trans_le hab
      · left
        have hWgood : r*V N ≤ W N z := le_of_not_gt hsmall
        have hscale : t*Real.sqrt (V N) ≤ q*Real.sqrt (W N z) := by
          have hs := Real.sqrt_le_sqrt hWgood
          rw [Real.sqrt_mul hr0.le, show Real.sqrt r = t/q by
            dsimp [r]; rw [Real.sqrt_sq (div_pos ht hq).le]] at hs
          have hm := mul_le_mul_of_nonneg_left hs hq.le
          calc
            _ = q*((t/q)*Real.sqrt (V N)) := by field_simp
            _ ≤ _ := hm
        have hab : |U N z/Real.sqrt (V N)| ≤ t := abs_le.mpr ⟨by linarith, hz⟩
        rw [abs_div, abs_of_pos hroot, div_le_iff₀ hroot] at hab
        exact hab.trans hscale
  have hm := T2_prob_mono (p N) (hp N) _ _ hevent
  have hu1 := T2_prob_union (p N) (hp N) (fun z => U N z/Real.sqrt (V N) ≤ -t)
    (fun z => |U N z| ≤ q*Real.sqrt (W N z) ∨ c < |(N : ℝ)*(W N z-b N)|)
  have hu2 := T2_prob_union (p N) (hp N) (fun z => |U N z| ≤ q*Real.sqrt (W N z))
    (fun z => c < |(N : ℝ)*(W N z-b N)|)
  have hηε : η ≤ ε/4 := min_le_left _ _
  change 1-α-ε ≤ _
  dsimp only [α'] at hmass
  change prob (p N) (fun z => U N z/Real.sqrt (V N) ≤ -t) < _ at hCDFlo
  change _ < prob (p N) (fun z => U N z/Real.sqrt (V N) ≤ t) at hCDFhi
  change prob (p N) (fun z => c < |(N : ℝ)*(W N z-b N)|) < _ at hbadN
  linarith

lemma T2_empirical_second_general {N : ℕ} (p : Fin N → ℝ) (Y : CircleTable N)
    (B : Fin N → Finset (Fin N)) (D C : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N)
    (hbound : ∀ i z, |Y i z| ≤ C) (hcount : ∀ i, ((B i).card : ℝ) ≤ D)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → cov p (Y i) (Y j) = 0) :
    let X := fun z => (∑ i, Y i z)/N
    expect p (fun z => (X z-expect p X)^2) ≤ D*C^2/N := by
  let X := fun z => (∑ i, Y i z)/N
  have hvar := finite_covariance_degree_bound p hp Y B hsymm hout
  have hsecond (i : Fin N) : expect p (fun z => (Y i z)^2) ≤ C^2 := by
    apply (expect_mono p hp _ (fun _ => C^2) (fun z => ?_)).trans_eq (expect_const p _)
    have hC : 0 ≤ C := (abs_nonneg _).trans (hbound i (fun _ => false))
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound i z) 2
  have hdeg : (∑ i, (B i).card*expect p (fun z => (Y i z)^2)) ≤ (N : ℝ)*(D*C^2) := by
    calc
      _ ≤ ∑ _i : Fin N, D*C^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hsecond i) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hcount i) (sq_nonneg _))
      _ = _ := by simp
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hv : variance p X ≤ D*C^2/N := by
    calc
      _ ≤ (∑ i, (B i).card*expect p (fun z => (Y i z)^2))/(N : ℝ)^2 := hvar
      _ ≤ ((N : ℝ)*(D*C^2))/(N : ℝ)^2 := div_le_div_of_nonneg_right hdeg (sq_nonneg _)
      _ = _ := by field_simp
  simpa only [variance, cov_centered, ← pow_two] using hv

def T2_B3 {N : ℕ} (B : Fin N → Finset (Fin N)) (i : Fin N) : Finset (Fin N) :=
  (B i).biUnion (fun j => (B j).biUnion B)

lemma T2_B3_symm {N : ℕ} (B : Fin N → Finset (Fin N))
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j) (i k : Fin N) :
    k ∈ T2_B3 B i ↔ i ∈ T2_B3 B k := by
  have hf (i k : Fin N) (h : k ∈ T2_B3 B i) : i ∈ T2_B3 B k := by
    obtain ⟨j, hj, l, hl, hk⟩ := by simpa only [T2_B3, Finset.mem_biUnion] using h
    exact Finset.mem_biUnion.mpr ⟨l, (hsymm l k).mp hk,
      Finset.mem_biUnion.mpr ⟨j, (hsymm j l).mp hl, (hsymm i j).mp hj⟩⟩
  exact ⟨hf i k, hf k i⟩

lemma T2_B3_card {N : ℕ} (B : Fin N → Finset (Fin N)) (D : ℕ)
    (hD : ∀ i, (B i).card ≤ D) (i : Fin N) : (T2_B3 B i).card ≤ D^3 := by
  have htwo (j : Fin N) : ((B j).biUnion B).card ≤ D^2 := by
    calc
      _ ≤ (B j).card*D := Finset.card_biUnion_le_card_mul _ _ _ (fun l _ => hD l)
      _ ≤ D*D := Nat.mul_le_mul_right D (hD j)
      _ = _ := by ring
  calc
    _ ≤ (B i).card*(D^2) := Finset.card_biUnion_le_card_mul _ _ _ (fun j _ => htwo j)
    _ ≤ D*(D^2) := Nat.mul_le_mul_right _ (hD i)
    _ = _ := by ring

def T2_Hrow {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) : CircleTable N :=
  fun i z => ∑ j ∈ B i, residualContrast p R g i z*residualContrast p R g j z

lemma T2_Hrow_depends {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hself : ∀ i, i ∈ B i) (i : Fin N) :
    DependsOn (T2_Hrow p R g B i) (GraphCompletion.sources R (B i)) := by
  intro x y hxy
  have hvec := GraphCompletion.residual_family_depends p R g (B i) hxy
  have hi : residualContrast p R g i x = residualContrast p R g i y := congrFun hvec ⟨i, hself i⟩
  unfold T2_Hrow
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : residualContrast p R g j x = residualContrast p R g j y := congrFun hvec ⟨j, hj⟩
  rw [hi, hj']

lemma T2_Hrow_cov_zero {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hself : ∀ i, i ∈ B i) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j)
    (i k : Fin N) (hik : k ∉ T2_B3 B i) :
    cov p (T2_Hrow p R g B i) (T2_Hrow p R g B k) = 0 := by
  have hdisj : Disjoint (GraphCompletion.sources R (B i)) (GraphCompletion.sources R (B k)) := by
    rw [Set.disjoint_left]
    rintro s ⟨j, hj, hjs⟩ ⟨l, hl, hls⟩
    have hjl : l ∈ B j := by
      by_contra h
      exact hout j l h ⟨s, hjs, hls⟩
    exact hik (Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_biUnion.mpr ⟨l, hjl, (hsymm k l).mp hl⟩⟩)
  have hk : DependsOn (T2_Hrow p R g B k) (GraphCompletion.sources R (B i))ᶜ :=
    (T2_Hrow_depends p R g B hself k).mono
    (by intro s hsk hsi; exact Set.disjoint_left.mp hdisj hsi hsk)
  unfold cov
  rw [GraphCompletion.expect_mul_of_disjoint_depends p _ _ _
    (T2_Hrow_depends p R g B hself i) hk, sub_self]

lemma T2_Hrow_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) (D : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ i z, |residualContrast p R g i z| ≤ C)
    (hD : ∀ i, (B i).card ≤ D) (i : Fin N) (z : Assignment N) :
    |T2_Hrow p R g B i z| ≤ (D : ℝ)*C^2 := by
  calc
    _ ≤ ∑ j ∈ B i, |residualContrast p R g i z*residualContrast p R g j z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ B i, C^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hbound i z) (hbound j z) (abs_nonneg _) hC
    _ = ((B i).card : ℝ)*C^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (sq_nonneg _)

lemma T2_hac_center_second {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) (D : ℕ) (C : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hC : 0 ≤ C) (hN : 0 < N)
    (hbound : ∀ i z, |residualContrast p R g i z| ≤ C)
    (hD : ∀ i, (B i).card ≤ D) (hself : ∀ i, i ∈ B i)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    expect p (fun z => ((N : ℝ)*(oracleHAC p R B g z-expect p (oracleHAC p R B g)))^2) ≤
      ((D : ℝ)^3)*((D : ℝ)*C^2)^2/N := by
  let X := fun z => (∑ i, T2_Hrow p R g B i z)/N
  have h := T2_empirical_second_general p (T2_Hrow p R g B) (T2_B3 B)
    ((D : ℝ)^3) ((D : ℝ)*C^2) hp hN (T2_Hrow_bound p R g B D C hC hbound hD)
    (fun i => by exact_mod_cast T2_B3_card B D hD i) (T2_B3_symm B hsymm)
    (T2_Hrow_cov_zero p R g B hself hsymm hout)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have heq : X = fun z => (N : ℝ)*oracleHAC p R B g z := by
    funext z
    dsimp [X, T2_Hrow, oracleHAC]
    field_simp
  change expect p (fun z => (X z-expect p X)^2) ≤ _ at h
  rw [heq, expect_mul] at h
  convert h using 1
  congr 1
  funext z
  ring

def T2_Srow {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) : CircleTable N :=
  fun i z => (B i).card*(residualContrast p R g i z)^2

lemma T2_sah_row_identity {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) :
    rawSAH p R B g = fun z => (∑ i, T2_Srow p R g B i z)/(N : ℝ)^2 := by
  funext z
  unfold rawSAH T2_Srow
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases hz : z i <;> simp [residualContrast, bit, hz, div_pow]

lemma T2_sah_center_second {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) (D : ℕ) (C : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hC : 0 ≤ C) (hN : 0 < N)
    (hbound : ∀ i z, |residualContrast p R g i z| ≤ C)
    (hD : ∀ i, (B i).card ≤ D)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    expect p (fun z => ((N : ℝ)*(rawSAH p R B g z-expect p (rawSAH p R B g)))^2) ≤
      (D : ℝ)*((D : ℝ)*C^2)^2/N := by
  have hb (i : Fin N) (z : Assignment N) : |T2_Srow p R g B i z| ≤ (D : ℝ)*C^2 := by
    rw [T2_Srow, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (sq_nonneg _)]
    have hsq : (residualContrast p R g i z)^2 ≤ C^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound i z) 2
    exact mul_le_mul (by exact_mod_cast hD i) hsq (sq_nonneg _) (Nat.cast_nonneg _)
  have hcov (i j : Fin N) (hj : j ∉ B i) :
      cov p (T2_Srow p R g B i) (T2_Srow p R g B j) = 0 := by
    exact T2_local_cov_zero p R (fun i b μ => (B i).card*
      (bit b*(μ-g i true)/p i-(1-bit b)*(μ-g i false)/(1-p i))^2) i j (hout i j hj)
  let X := fun z => (∑ i, T2_Srow p R g B i z)/N
  have h := T2_empirical_second_general p (T2_Srow p R g B) B (D : ℝ) ((D : ℝ)*C^2)
    hp hN hb (fun i => by exact_mod_cast hD i) hsymm hcov
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have heq : X = fun z => (N : ℝ)*rawSAH p R B g z := by
    funext z
    rw [T2_sah_row_identity]
    dsimp [X]
    field_simp
  change expect p (fun z => (X z-expect p X)^2) ≤ _ at h
  rw [heq, expect_mul] at h
  convert h using 1
  congr 1
  funext z
  ring

lemma T2_oracles_concentrate (p : ∀ N, Fin N → ℝ) (R : ∀ N, CircleTable N)
    (g : ∀ N, Fin N → Bool → ℝ) (B : ∀ N, Fin N → Finset (Fin N))
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (D : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hregular : ∀ᶠ N in atTop, (∀ i z, |residualContrast (p N) (R N) (g N) i z| ≤ C) ∧
      (∀ i, (B N i).card ≤ D) ∧ (∀ i, i ∈ B N i) ∧
      (∀ i j, j ∈ B N i ↔ i ∈ B N j) ∧
      (∀ i j, j ∉ B N i → ¬ sharesSource (R N) i j)) :
    InProb p (fun N z => (N : ℝ)*(rawSAH (p N) (R N) (B N) (g N) z-
      expect (p N) (rawSAH (p N) (R N) (B N) (g N)))) ∧
    InProb p (fun N z => (N : ℝ)*(oracleHAC (p N) (R N) (B N) (g N) z-
      expect (p N) (oracleHAC (p N) (R N) (B N) (g N)))) := by
  have hroot : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  constructor
  · apply T2_inprob_of_bigop p hp _ _ hroot
    apply T2_bigop_of_second p hp _ ((D : ℝ)*((D : ℝ)*C^2)^2+1) (by positivity)
    filter_upwards [hregular, eventually_gt_atTop 0] with N hr hN
    exact (T2_sah_center_second (p N) (R N) (g N) (B N) D C (hp N) hC hN
      hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.2.2).trans
      (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  · apply T2_inprob_of_bigop p hp _ _ hroot
    apply T2_bigop_of_second p hp _ ((D : ℝ)^3*((D : ℝ)*C^2)^2+1) (by positivity)
    filter_upwards [hregular, eventually_gt_atTop 0] with N hr hN
    exact (T2_hac_center_second (p N) (R N) (g N) (B N) D C (hp N) hC hN
      hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2).trans
      (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

def T2_beta_num {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) (z : Assignment N) : Fin k → ℝ :=
  fun j => (∑ i, if z i=a then R i z*coin (p i) (!a)*O i j else 0)/N

def T2_beta_pop {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) : Fin k → ℝ :=
  fun j => (∑ i, marginal p R i a*p i*(1-p i)*O i j)/N

lemma T2_beta_num_mean {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) (hp : ∀ i, 0 < p i ∧ p i < 1) (j : Fin k) :
    expect p (fun z => T2_beta_num p R O a z j) = T2_beta_pop p R O a j := by
  unfold T2_beta_num T2_beta_pop
  rw [expect_div, expect_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun z => if z i=a then R i z*coin (p i) (!a)*O i j else 0) =
      fun z => (coin (p i) (!a)*O i j)*(if z i=a then R i z else 0) := by
    funext z
    split_ifs <;> ring
  rw [heq, expect_mul, bernoulli_selection p R i a (by
    cases a
    · simpa only [coin, Bool.false_eq_true, if_false] using (sub_pos.mpr (hp i).2).ne'
    · simpa only [coin, if_true] using (hp i).1.ne')]
  cases a <;> simp [coin] <;> ring

lemma T2_beta_atom_bound (a b : Bool) (p μ o M U : ℝ)
    (hp : 0 < p ∧ p < 1) (hM : 0 ≤ M) (hU : 0 ≤ U) (hμ : |μ| ≤ M) (ho : |o| ≤ U) :
    |if b=a then μ*coin p (!a)*o else 0| ≤ M*U := by
  split_ifs
  · have hc0 : 0 ≤ coin p (!a) := by cases a <;> simp [coin] <;> linarith [hp.1, hp.2]
    have hc1 : coin p (!a) ≤ 1 := by cases a <;> simp [coin] <;> linarith [hp.1, hp.2]
    rw [show μ*coin p (!a)*o = (μ*o)*coin p (!a) by ring,
      abs_mul, abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul (mul_le_mul hμ ho (abs_nonneg _) hM) hc1 hc0 (mul_nonneg hM hU)).trans_eq (mul_one _)
  · simpa using mul_nonneg hM hU

lemma T2_beta_num_second {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (B : Fin N → Finset (Fin N)) (D M U : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hR : ∀ i z, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U)
    (hcount : ∀ i, ((B i).card : ℝ) ≤ D)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) (a : Bool) :
    expect p (fun z => ‖T2_beta_num p R O a z-T2_beta_pop p R O a‖^2) ≤
      (k : ℝ)*D*(M*U)^2/N := by
  calc
    _ ≤ expect p (fun z => ∑ j, (T2_beta_num p R O a z j-T2_beta_pop p R O a j)^2) :=
      expect_mono _ hp _ _ (fun z => T2_norm_sq_le_energy _)
    _ = ∑ j, expect p (fun z => (T2_beta_num p R O a z j-T2_beta_pop p R O a j)^2) := expect_sum _ _
    _ ≤ ∑ _j : Fin k, D*(M*U)^2/N := by
      apply Finset.sum_le_sum
      intro j _
      have h := T2_local_empirical_second p R
        (fun i b μ => if b=a then μ*coin (p i) (!a)*O i j else 0) B D (M*U) hp hN
        (mul_nonneg hM hU)
        (fun i z => T2_beta_atom_bound a (z i) (p i) (R i z) (O i j) M U (hp i) hM hU (hR i z) (hO i j))
        hcount hsymm hout
      change expect p (fun z => (T2_beta_num p R O a z j-
        expect p (fun z => T2_beta_num p R O a z j))^2) ≤ _ at h
      rw [T2_beta_num_mean p R O a hp j] at h
      exact h
    _ = _ := by simp [mul_div_assoc]; ring

lemma T2_uniform_propensities {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (Θ : Set (Fin k → ℝ)) (hΘ : IsCompact Θ)
    (U : ℝ) (hU : 0 ≤ U) (hO : ∀ N i j, |O N i j| ≤ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N, ∀ θ ∈ Θ, ∀ i,
      ε ≤ propensities (O N) θ i ∧ ε ≤ 1-propensities (O N) θ i := by
  obtain ⟨T, hT, hbound⟩ := hΘ.isBounded.exists_pos_norm_le
  let A := (k : ℝ)*U*T
  refine ⟨logistic (-A), T2_logistic_pos _, ?_⟩
  intro N θ hθ i
  have ht : |dot (O N i) θ| ≤ A := T2_dot_bound (O N i) θ U T hU (hO N i)
    (fun j => by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm θ j).trans (hbound θ hθ))
  constructor
  · exact T2_logistic_mono (abs_le.mp ht).1
  · change logistic (-A) ≤ 1-logistic (dot (O N i) θ)
    rw [← T2_logistic_neg]
    exact T2_logistic_mono (by linarith [(abs_le.mp ht).2])

lemma T2_beta_num_difference {N k : ℕ} (p q : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) (z : Assignment N) (M U δ : ℝ)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hδ : 0 ≤ δ) (hN : 0 < N)
    (hR : ∀ i, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U)
    (hpq : ∀ i, |q i-p i| ≤ δ) :
    ‖T2_beta_num q R O a z-T2_beta_num p R O a z‖ ≤ M*U*δ := by
  have heq : T2_beta_num q R O a z-T2_beta_num p R O a z =
      fun j => (∑ i, if z i=a then R i z*(coin (q i) (!a)-coin (p i) (!a))*O i j else 0)/N := by
    funext j
    simp only [Pi.sub_apply, T2_beta_num, ← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq]
  apply T2_average_bound _ _ (by positivity) hN
  intro i j
  split_ifs
  · have hc : |coin (q i) (!a)-coin (p i) (!a)| ≤ δ := by
      cases a <;> simpa [coin, abs_sub_comm] using hpq i
    rw [show R i z*(coin (q i) (!a)-coin (p i) (!a))*O i j =
      (R i z*O i j)*(coin (q i) (!a)-coin (p i) (!a)) by ring, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hR i) (hO i j) (abs_nonneg _) hM) hc (abs_nonneg _) (mul_nonneg hM hU)
  · simpa using mul_nonneg (mul_nonneg hM hU) hδ

lemma T2_inverse_scalar_difference (p q ε δ : ℝ) (hε : 0 < ε)
    (hp : ε ≤ p) (hq : ε ≤ q) (hδ : 0 ≤ δ) (hpq : |q-p| ≤ δ) :
    |q⁻¹-p⁻¹| ≤ δ/ε^2 := by
  have hp0 : 0 < p := hε.trans_le hp
  have hq0 : 0 < q := hε.trans_le hq
  have heq : q⁻¹-p⁻¹ = (p-q)/(p*q) := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hp0 hq0)]
  have hd : ε^2 ≤ p*q := by simpa only [pow_two] using mul_le_mul hp hq hε.le hp0.le
  exact (div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hpq) (mul_pos hp0 hq0).le).trans
    (div_le_div_of_nonneg_left hδ (sq_pos_of_pos hε) hd)

lemma T2_gradient_atom_difference (b : Bool) (p q μ o ε M U δ : ℝ)
    (hε : 0 < ε) (hπ : ε ≤ p ∧ ε ≤ 1-p) (hθ : ε ≤ q ∧ ε ≤ 1-q)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hδ : 0 ≤ δ) (hμ : |μ| ≤ M) (ho : |o| ≤ U)
    (hpq : |q-p| ≤ δ) :
    |(bit b*μ*(1-q)/q+(1-bit b)*μ*q/(1-q))*o-
      (bit b*μ*(1-p)/p+(1-bit b)*μ*p/(1-p))*o| ≤ M*U*δ/ε^2 := by
  have hp0 : 0 < p := hε.trans_le hπ.1
  have hq0 : 0 < q := hε.trans_le hθ.1
  have hp1 : 0 < 1-p := hε.trans_le hπ.2
  have hq1 : 0 < 1-q := hε.trans_le hθ.2
  have hfactor (s : ℝ) (hs : |s| ≤ δ/ε^2) : |(μ*o)*s| ≤ M*U*δ/ε^2 := by
    rw [abs_mul, abs_mul]
    convert mul_le_mul (mul_le_mul hμ ho (abs_nonneg _) hM) hs (abs_nonneg _) (mul_nonneg hM hU)
      using 1 <;> ring
  cases b
  · have hc := T2_inverse_scalar_difference (1-p) (1-q) ε δ hε hπ.2 hθ.2 hδ
      (by simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hpq)
    have heq : (bit false*μ*(1-q)/q+(1-bit false)*μ*q/(1-q))*o-
        (bit false*μ*(1-p)/p+(1-bit false)*μ*p/(1-p))*o =
        (μ*o)*((1-q)⁻¹-(1-p)⁻¹) := by
      simp only [bit, Bool.false_eq_true, if_false]
      field_simp
      ring
    rw [heq]
    exact hfactor _ hc
  · have hc := T2_inverse_scalar_difference p q ε δ hε hπ.1 hθ.1 hδ hpq
    have heq : (bit true*μ*(1-q)/q+(1-bit true)*μ*q/(1-q))*o-
        (bit true*μ*(1-p)/p+(1-bit true)*μ*p/(1-p))*o = (μ*o)*(q⁻¹-p⁻¹) := by
      simp only [bit, if_true]
      field_simp
      ring
    rw [heq]
    exact hfactor _ hc

lemma T2_gradient_difference {N k : ℕ} (p q : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) (ε M U δ : ℝ)
    (hε : 0 < ε) (hπ : ∀ i, ε ≤ p i ∧ ε ≤ 1-p i) (hθ : ∀ i, ε ≤ q i ∧ ε ≤ 1-q i)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hδ : 0 ≤ δ) (hN : 0 < N)
    (hR : ∀ i, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U) (hpq : ∀ i, |q i-p i| ≤ δ) :
    ‖T2_ht_gradient q R O z-T2_ht_gradient p R O z‖ ≤ M*U*δ/ε^2 := by
  have heq : T2_ht_gradient q R O z-T2_ht_gradient p R O z = fun j =>
      (∑ i, ((bit (z i)*R i z*(1-q i)/q i+(1-bit (z i))*R i z*q i/(1-q i))*O i j-
        (bit (z i)*R i z*(1-p i)/p i+(1-bit (z i))*R i z*p i/(1-p i))*O i j))/N := by
    funext j
    simp only [Pi.sub_apply, T2_ht_gradient, ← sub_div, Finset.sum_sub_distrib]
  rw [heq]
  apply T2_average_bound _ _ (by positivity) hN
  intro i j
  exact T2_gradient_atom_difference (z i) (p i) (q i) (R i z) (O i j) ε M U δ hε
    (hπ i) (hθ i) hM hU hδ (hR i) (hO i j) (hpq i)

lemma T2_weight_difference (p q δ : ℝ) (hp : 0 < p ∧ p < 1) (hq : 0 < q ∧ q < 1)
    (hδ : 0 ≤ δ) (hpq : |q-p| ≤ δ) : |q*(1-q)-p*(1-p)| ≤ δ := by
  rw [show q*(1-q)-p*(1-p) = (q-p)*(1-p-q) by ring, abs_mul]
  have hfactor : |1-p-q| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  exact (mul_le_mul hpq hfactor (abs_nonneg _) hδ).trans_eq (mul_one _)

lemma T2_information_difference {N k : ℕ} (p q : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (v : Fin k → ℝ) (U δ : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (hU : 0 ≤ U) (hδ : 0 ≤ δ) (hN : 0 < N)
    (hO : ∀ i j, |O i j| ≤ U) (hpq : ∀ i, |q i-p i| ≤ δ) :
    ‖(information q O-information p O) *ᵥ v‖ ≤ (k : ℝ)*U^2*‖v‖*δ := by
  have heq : (information q O-information p O) *ᵥ v = fun j =>
      (∑ i, (q i*(1-q i)-p i*(1-p i))*O i j*dot (O i) v)/N := by
    funext j
    simp only [Matrix.sub_mulVec, Pi.sub_apply, T2_information_mulvec,
      ← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  apply T2_average_bound _ _ (by positivity) hN
  intro i j
  rw [abs_mul, abs_mul]
  have hw := T2_weight_difference (p i) (q i) δ (hp i) (hq i) hδ (hpq i)
  have hd := T2_dot_bound (O i) v U ‖v‖ hU (hO i)
    (fun l => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v l)
  convert mul_le_mul (mul_le_mul hw (hO i j) (abs_nonneg _) hδ) hd
    (abs_nonneg _) (mul_nonneg hδ hU) using 1 <;> ring

lemma T2_inverse_solve_error {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v, c*(∑ j, (v j)^2) ≤ dot v (A *ᵥ v))
    (b b₀ β : Fin k → ℝ) :
    ‖A⁻¹ *ᵥ b-β‖ ≤ (k : ℝ)/c*(‖b-b₀‖+‖A *ᵥ β-b₀‖) := by
  letI instT2InverseSolve := (T2_coercive_unit A c hc hA).invertible
  have heq : A⁻¹ *ᵥ b-β = A⁻¹ *ᵥ ((b-b₀)-(A *ᵥ β-b₀)) := by
    have hin : A⁻¹ *ᵥ (A *ᵥ β) = β := by
      rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
    rw [show (b-b₀)-(A *ᵥ β-b₀) = b-A *ᵥ β by abel, Matrix.mulVec_sub, hin]
  rw [heq]
  exact (T2_inverse_bound A c hc hA _).trans
    (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity))

lemma T2_projection_error {N k : ℕ} (p q : Fin N → ℝ) (O : Fin N → Fin k → ℝ)
    (β bq bp b₀ : Fin k → ℝ) (ε c U C B δ : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hU : 0 ≤ U) (hC : 0 ≤ C) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (hπ : ∀ i, ε ≤ q i ∧ ε ≤ 1-q i) (hN : 0 < N) (hO : ∀ i j, |O i j| ≤ U)
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hβ : information p O *ᵥ β = b₀) (hβbound : ‖β‖ ≤ B)
    (hnum : ‖bq-bp‖ ≤ C*δ) (hpq : ∀ i, |q i-p i| ≤ δ) :
    ‖(information q O)⁻¹ *ᵥ bq-β‖ ≤
      (k : ℝ)/(ε^2*c)*(‖bp-b₀‖+(C+(k : ℝ)*U^2*B)*δ) := by
  have hweight (i : Fin N) : ε^2 ≤ q i*(1-q i) := by
    simpa only [pow_two] using mul_le_mul (hπ i).1 (hπ i).2 hε.le (hq i).1.le
  have hA := T2_information_coercive q O (ε^2) c (sq_nonneg _) hweight hgram
  have hb : ‖bq-b₀‖ ≤ C*δ+‖bp-b₀‖ := by
    calc
      _ = ‖(bq-bp)+(bp-b₀)‖ := by congr 1; abel
      _ ≤ ‖bq-bp‖+‖bp-b₀‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hnum le_rfl
  have hinfo : ‖information q O *ᵥ β-b₀‖ ≤ (k : ℝ)*U^2*B*δ := by
    rw [← hβ, ← Matrix.sub_mulVec]
    exact (T2_information_difference p q O β U δ hp hq hU hδ hN hO hpq).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hβbound (by positivity)) hδ)
  exact (T2_inverse_solve_error (information q O) (ε^2*c) (mul_pos (sq_pos_of_pos hε) hc)
    hA bq b₀ β).trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))

def T2_scalar_fit (p δ L : ℝ) (a : Bool) : ℝ :=
  (if a then p else p-1)*δ+p*(1-p)*L

lemma T2_scalar_fit_difference (p q δ δhat L Lhat : ℝ) (a : Bool)
    (hp : 0 < p ∧ p < 1) (hq : 0 < q ∧ q < 1) :
    |T2_scalar_fit q δhat Lhat a-T2_scalar_fit p δ L a| ≤
      |δhat-δ|+|Lhat-L|+|q-p| * (|δ|+|L|) := by
  let c := if a then q else q-1
  have hc : |c| ≤ 1 := by
    dsimp [c]
    cases a <;> simp only [Bool.false_eq_true, if_false, if_true]
    all_goals apply abs_le.mpr; constructor <;> linarith [hq.1, hq.2]
  have hw0 : 0 ≤ q*(1-q) := mul_nonneg hq.1.le (sub_pos.mpr hq.2).le
  have hw1 : q*(1-q) ≤ 1 := by nlinarith [hq.1, hq.2, sq_nonneg q]
  have hw : |q*(1-q)-p*(1-p)| ≤ |q-p| :=
    T2_weight_difference p q |q-p| hp hq (abs_nonneg _) le_rfl
  have heq : T2_scalar_fit q δhat Lhat a-T2_scalar_fit p δ L a =
      (c*(δhat-δ)+(q-p)*δ)+(q*(1-q)*(Lhat-L)+(q*(1-q)-p*(1-p))*L) := by
    cases a <;> simp only [T2_scalar_fit, c, Bool.false_eq_true, if_false, if_true] <;> ring
  rw [heq]
  calc
    _ ≤ (|c*(δhat-δ)|+|(q-p)*δ|)+(|q*(1-q)*(Lhat-L)|+|(q*(1-q)-p*(1-p))*L|) :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ (|δhat-δ|+|q-p| * |δ|)+(|Lhat-L|+|q-p| * |L|) := by
      simp only [abs_mul, abs_of_nonneg hw0]
      exact add_le_add (add_le_add (by nlinarith [abs_nonneg (δhat-δ)]) le_rfl)
        (add_le_add (by nlinarith [abs_nonneg (Lhat-L)])
          (mul_le_mul_of_nonneg_right hw (abs_nonneg _)))
    _ = _ := by ring

lemma T2_propensity_difference {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (U : ℝ) (hU : 0 ≤ U) (hO : ∀ i j, |O i j| ≤ U) (i : Fin N) :
    |propensities O θ i-propensities O θ₀ i| ≤ (k : ℝ)*U*‖θ-θ₀‖ := by
  apply (T2_logistic_lipschitz (dot (O i) θ₀) (dot (O i) θ)).trans
  rw [← T2_dot_sub]
  exact T2_dot_bound (O i) (θ-θ₀) U ‖θ-θ₀‖ hU (hO i)
    (fun j => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ-θ₀) j)

lemma T2_fittedscore_difference {N k : ℕ} (p q : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) (ε c M U s : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hM : 0 ≤ M) (hU : 0 ≤ U) (hs : 0 ≤ s) (hN : 0 < N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (hπ : ∀ i, ε ≤ p i ∧ ε ≤ 1-p i) (hθ : ∀ i, ε ≤ q i ∧ ε ≤ 1-q i)
    (hR : ∀ i z, |R i z| ≤ M) (hO : ∀ i j, |O i j| ≤ U)
    (hgram : ∀ v : Fin k → ℝ, c*(∑ j, (v j)^2) ≤ (∑ i, (dot (O i) v)^2)/N)
    (hpq : ∀ i, |q i-p i| ≤ s)
    (hβmom : ∀ a, ‖T2_beta_num p R O a z-T2_beta_pop p R O a‖ ≤ s)
    (hγmom : ‖T2_ht_gradient p R O z-T2_population_gradient p R O‖ ≤ s) :
    let L := (k : ℝ)/(ε^2*c)
    let B := L*(M*U)
    let Cβ := L*(1+M*U+(k : ℝ)*U^2*B)
    let Cγ := L*(1+M*U/ε^2+(k : ℝ)*U^2*B)
    ∀ i a, |fittedScoreFits q R O z i a-scoreFits p R O i a| ≤
      ((k : ℝ)*U*(2*Cβ+Cγ)+3*((k : ℝ)*U)*B)*s := by
  let L := (k : ℝ)/(ε^2*c)
  let B := L*(M*U)
  let Cβ := L*(1+M*U+(k : ℝ)*U^2*B)
  let Cγ := L*(1+M*U/ε^2+(k : ℝ)*U^2*B)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCβ : 0 ≤ Cβ := by dsimp [Cβ]; positivity
  have hCγ : 0 ≤ Cγ := by dsimp [Cγ]; positivity
  have hweight (i : Fin N) : ε^2 ≤ p i*(1-p i) := by
    simpa only [pow_two] using mul_le_mul (hπ i).1 (hπ i).2 hε.le (hp i).1.le
  have hA := T2_information_coercive p O (ε^2) c (sq_nonneg _) hweight hgram
  letI instT2ProjectionTrue := (T2_coercive_unit (information p O) (ε^2*c)
    (mul_pos (sq_pos_of_pos hε) hc) hA).invertible
  have hβbound (a : Bool) : ‖beta p R O a‖ ≤ B :=
    T2_beta_bound p R O (ε^2) c M U (sq_pos_of_pos hε) hc hM hU hN hp hweight hgram hR hO a
  have hγbound : ‖scoreGamma p R O‖ ≤ B :=
    T2_gamma_bound p R O (ε^2) c M U (sq_pos_of_pos hε) hc hM hU hN hp hweight hgram hR hO
  have hβeq (a : Bool) : information p O *ᵥ beta p R O a = T2_beta_pop p R O a := by
    change information p O *ᵥ ((information p O)⁻¹ *ᵥ T2_beta_pop p R O a) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hγeq : information p O *ᵥ scoreGamma p R O = T2_population_gradient p R O := by
    change information p O *ᵥ ((information p O)⁻¹ *ᵥ T2_population_gradient p R O) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hβerr (a : Bool) : ‖fittedBeta q R O a z-beta p R O a‖ ≤ Cβ*s := by
    have h := T2_projection_error p q O (beta p R O a) (T2_beta_num q R O a z)
      (T2_beta_num p R O a z) (T2_beta_pop p R O a) ε c U (M*U) B s hε hc hU
      (mul_nonneg hM hU) hB hs hp hq hθ hN hO hgram (hβeq a) (hβbound a)
      (T2_beta_num_difference p q R O a z M U s hM hU hs hN (fun i => hR i z) hO hpq) hpq
    change ‖fittedBeta q R O a z-beta p R O a‖ ≤ _ at h
    apply h.trans
    change L*(‖T2_beta_num p R O a z-T2_beta_pop p R O a‖+(M*U+(k : ℝ)*U^2*B)*s) ≤ Cβ*s
    calc
      _ ≤ L*(s+(M*U+(k : ℝ)*U^2*B)*s) :=
        mul_le_mul_of_nonneg_left (add_le_add (hβmom a) le_rfl) hL
      _ = _ := by dsimp [Cβ]; ring
  have hγerr : ‖fittedGamma q R O z-scoreGamma p R O‖ ≤ Cγ*s := by
    have hnum : ‖T2_ht_gradient q R O z-T2_ht_gradient p R O z‖ ≤ (M*U/ε^2)*s := by
      convert T2_gradient_difference p q R O z ε M U s hε hπ hθ hM hU hs hN
        (fun i => hR i z) hO hpq using 1 <;> ring
    have h := T2_projection_error p q O (scoreGamma p R O) (T2_ht_gradient q R O z)
      (T2_ht_gradient p R O z) (T2_population_gradient p R O) ε c U (M*U/ε^2) B s hε hc hU
      (by positivity) hB hs hp hq hθ hN hO hgram hγeq hγbound hnum hpq
    change ‖fittedGamma q R O z-scoreGamma p R O‖ ≤ _ at h
    apply h.trans
    change L*(‖T2_ht_gradient p R O z-T2_population_gradient p R O‖+
      (M*U/ε^2+(k : ℝ)*U^2*B)*s) ≤ Cγ*s
    calc
      _ ≤ L*(s+(M*U/ε^2+(k : ℝ)*U^2*B)*s) :=
        mul_le_mul_of_nonneg_left (add_le_add hγmom le_rfl) hL
      _ = _ := by dsimp [Cγ]; ring
  change ∀ (i : Fin N) (a : Bool), |fittedScoreFits q R O z i a-scoreFits p R O i a| ≤
    ((k : ℝ)*U*(2*Cβ+Cγ)+3*((k : ℝ)*U)*B)*s
  intro i a
  have hdot (v : Fin k → ℝ) : |dot (O i) v| ≤ (k : ℝ)*U*‖v‖ :=
    T2_dot_bound (O i) v U ‖v‖ hU (hO i)
      (fun j => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j)
  let δ := printedFits p R O i true-printedFits p R O i false
  let δhat := dot (O i) (fittedBeta q R O true z)-dot (O i) (fittedBeta q R O false z)
  let G := dot (O i) (scoreGamma p R O)
  let Ghat := dot (O i) (fittedGamma q R O z)
  have hdtrue : |δ| ≤ 2*((k : ℝ)*U*B) := by
    have hb (a : Bool) : |printedFits p R O i a| ≤ (k : ℝ)*U*B :=
      (hdot _).trans (mul_le_mul_of_nonneg_left (hβbound a) (by positivity))
    exact (abs_sub _ _).trans (by linarith [hb true, hb false])
  have hGtrue : |G| ≤ (k : ℝ)*U*B :=
    (hdot _).trans (mul_le_mul_of_nonneg_left hγbound (by positivity))
  have hdchange : |δhat-δ| ≤ 2*((k : ℝ)*U*Cβ*s) := by
    have heq : δhat-δ = dot (O i) (fittedBeta q R O true z-beta p R O true)-
      dot (O i) (fittedBeta q R O false z-beta p R O false) := by
      simp only [T2_dot_sub, δhat, δ, printedFits]
      ring
    rw [heq]
    have hb (a : Bool) : |dot (O i) (fittedBeta q R O a z-beta p R O a)| ≤ (k : ℝ)*U*Cβ*s :=
      (hdot _).trans (by convert mul_le_mul_of_nonneg_left (hβerr a) (by positivity : 0 ≤ (k : ℝ)*U) using 1 <;> ring)
    exact (abs_sub _ _).trans (by linarith [hb true, hb false])
  have hGchange : |Ghat-G| ≤ (k : ℝ)*U*Cγ*s := by
    rw [show Ghat-G = dot (O i) (fittedGamma q R O z-scoreGamma p R O) from (T2_dot_sub _ _ _).symm]
    exact (hdot _).trans (by convert mul_le_mul_of_nonneg_left hγerr (by positivity : 0 ≤ (k : ℝ)*U) using 1 <;> ring)
  have heq : fittedScoreFits q R O z i a-scoreFits p R O i a =
      T2_scalar_fit (q i) δhat Ghat a-T2_scalar_fit (p i) δ G a := by
    cases a <;> simp only [fittedScoreFits, scoreFits, T2_scalar_fit, δhat, δ, G, Ghat,
      Bool.false_eq_true, if_false, if_true] <;> ring
  rw [heq]
  calc
    _ ≤ |δhat-δ|+|Ghat-G|+|q i-p i| * (|δ|+|G|) :=
      T2_scalar_fit_difference (p i) (q i) δ δhat G Ghat a (hp i) (hq i)
    _ ≤ 2*((k : ℝ)*U*Cβ*s)+(k : ℝ)*U*Cγ*s+s*(2*((k : ℝ)*U*B)+(k : ℝ)*U*B) :=
      add_le_add (add_le_add hdchange hGchange)
        (mul_le_mul (hpq i) (add_le_add hdtrue hGtrue) (by positivity) hs)
    _ = _ := by ring

lemma T2_ratio_residual_difference (r f g p q ε A B s : ℝ)
    (hε : 0 < ε) (hp : ε ≤ p) (hq : ε ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hfg : |f-g| ≤ A) (hrg : |r-g| ≤ B) (hpq : |q-p| ≤ s) :
    |(r-f)/q-(r-g)/p| ≤ A/ε+B*s/ε^2 := by
  have hp0 : 0 < p := hε.trans_le hp
  have hq0 : 0 < q := hε.trans_le hq
  have heq : (r-f)/q-(r-g)/p = (g-f)/q+(r-g)*(q⁻¹-p⁻¹) := by ring
  rw [heq]
  calc
    _ ≤ |(g-f)/q|+|(r-g)*(q⁻¹-p⁻¹)| := abs_add_le _ _
    _ ≤ A/ε+B*(s/ε^2) := by
      rw [abs_div, abs_of_pos hq0, abs_mul]
      exact add_le_add
        ((div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hfg) hq0.le).trans
          (div_le_div_of_nonneg_left hA hε hq))
        (mul_le_mul hrg (T2_inverse_scalar_difference p q ε s hε hp hq hs hpq) (abs_nonneg _) hB)
    _ = _ := by ring

lemma T2_contrast_difference {N : ℕ} (p q : Fin N → ℝ) (R : CircleTable N)
    (g f : Fin N → Bool → ℝ) (z : Assignment N) (ε M F A s : ℝ)
    (hε : 0 < ε) (hM : 0 ≤ M) (hF : 0 ≤ F) (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hπ : ∀ i, ε ≤ p i ∧ ε ≤ 1-p i) (hθ : ∀ i, ε ≤ q i ∧ ε ≤ 1-q i)
    (hR : ∀ i, |R i z| ≤ M) (hg : ∀ i a, |g i a| ≤ F)
    (hf : ∀ i a, |f i a-g i a| ≤ A*s) (hpq : ∀ i, |q i-p i| ≤ s) (i : Fin N) :
    |residualContrast q R f i z-residualContrast p R g i z| ≤
      (A/ε+(M+F)/ε^2)*s := by
  have hratio (a : Bool) (u v : ℝ) (hu : ε ≤ u) (hv : ε ≤ v) (huv : |v-u| ≤ s) :
      |(R i z-f i a)/v-(R i z-g i a)/u| ≤ (A/ε+(M+F)/ε^2)*s := by
    have h := T2_ratio_residual_difference (R i z) (f i a) (g i a) u v ε (A*s) (M+F) s
      hε hu hv (mul_nonneg hA hs) (add_nonneg hM hF) hs (hf i a)
      ((abs_sub _ _).trans (add_le_add (hR i) (hg i a))) huv
    convert h using 1 <;> ring
  cases hz : z i
  · have h := hratio false (1-p i) (1-q i) (hπ i).2 (hθ i).2
      (by simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hpq i)
    simp only [residualContrast, bit, hz, Bool.false_eq_true, if_false, zero_mul,
      zero_div, sub_zero, one_mul, zero_sub]
    rw [show -( (R i z-f i false)/(1-q i)) - (-( (R i z-g i false)/(1-p i))) =
      -((R i z-f i false)/(1-q i)-(R i z-g i false)/(1-p i)) by ring, abs_neg]
    exact h
  · simpa [residualContrast, bit, hz] using hratio true (p i) (q i) (hπ i).1 (hθ i).1 (hpq i)

lemma T2_abs_average_bound {N : ℕ} (X : Fin N → ℝ) (C : ℝ)
    (hN : 0 < N) (hX : ∀ i, |X i| ≤ C) : |(∑ i, X i)/N| ≤ C := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |X i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hX i)
    _ = _ := by simp [mul_comm]

lemma T2_quadratic_plugin_bound {N : ℕ} (p q : Fin N → ℝ) (R : CircleTable N)
    (g f : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N)) (z : Assignment N)
    (D C A s : ℝ) (hN : 0 < N) (hD : 0 ≤ D) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hcount : ∀ i, ((B i).card : ℝ) ≤ D)
    (hbound : ∀ i, |residualContrast p R g i z| ≤ C)
    (hchange : ∀ i, |residualContrast q R f i z-residualContrast p R g i z| ≤ A*s) :
    |(N : ℝ)*(rawSAH q R B f z-rawSAH p R B g z)| ≤ D*(2*C+A)*A*s ∧
    |(N : ℝ)*(oracleHAC q R B f z-oracleHAC p R B g z)| ≤ D*(2*C+A)*A*s := by
  let T := fun i => residualContrast p R g i z
  let T' := fun i => residualContrast q R f i z
  have hT' (i : Fin N) : |T' i| ≤ C+A := by
    calc
      _ = |T i+(T' i-T i)| := by congr 1; ring
      _ ≤ |T i|+|T' i-T i| := abs_add_le _ _
      _ ≤ C+A*s := add_le_add (hbound i) (hchange i)
      _ ≤ _ := by nlinarith
  have hprod (i j : Fin N) : |T' i*T' j-T i*T j| ≤ (2*C+A)*A*s := by
    rw [show T' i*T' j-T i*T j = T' i*(T' j-T j)+(T' i-T i)*T j by ring]
    calc
      _ ≤ |T' i*(T' j-T j)|+|(T' i-T i)*T j| := abs_add_le _ _
      _ ≤ (C+A)*(A*s)+(A*s)*C := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hT' i) (hchange j) (abs_nonneg _) (add_nonneg hC hA))
          (mul_le_mul (hchange i) (hbound j) (abs_nonneg _) (mul_nonneg hA hs))
      _ = _ := by ring
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  constructor
  · have heq : (N : ℝ)*(rawSAH q R B f z-rawSAH p R B g z) =
        (∑ i, (B i).card*((T' i)^2-(T i)^2))/N := by
      rw [T2_sah_row_identity, T2_sah_row_identity]
      dsimp only [T2_Srow, T, T']
      simp only [mul_sub, Finset.sum_sub_distrib]
      field_simp
    rw [heq]
    apply T2_abs_average_bound _ _ hN
    intro i
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hsq : |(T' i)^2-(T i)^2| ≤ (2*C+A)*A*s := by simpa only [pow_two] using hprod i i
    convert mul_le_mul (hcount i) hsq (abs_nonneg _) hD using 1 <;> ring
  · have heq : (N : ℝ)*(oracleHAC q R B f z-oracleHAC p R B g z) =
        (∑ i, ∑ j ∈ B i, (T' i*T' j-T i*T j))/N := by
      dsimp only [oracleHAC, T, T']
      simp only [Finset.sum_sub_distrib]
      field_simp
    rw [heq]
    apply T2_abs_average_bound _ _ hN
    intro i
    calc
      _ ≤ ∑ j ∈ B i, |T' i*T' j-T i*T j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ B i, (2*C+A)*A*s := Finset.sum_le_sum (fun j _ => hprod i j)
      _ = ((B i).card : ℝ)*((2*C+A)*A*s) := by simp
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right (hcount i) (by positivity : 0 ≤ (2*C+A)*A*s) using 1 <;> ring

lemma T2_inprob_good_bound (p : ∀ N, Fin N → ℝ) (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (S V : ∀ N, Assignment N → ℝ) (hS : InProb p S) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ N in atTop, ∀ z, |S N z| ≤ 1 → |V N z| ≤ C*|S N z|) : InProb p V := by
  intro ε hε
  let δ := min (1/2) (ε/(2*(C+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hCδ : C*δ < ε := by
    have hd := mul_le_mul_of_nonneg_left (min_le_right (1/2 : ℝ) (ε/(2*(C+1)))) hC
    have hcp : 0 < 2*(C+1) := by positivity
    have he : C*(ε/(2*(C+1))) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hcp]
      nlinarith
    exact hd.trans_lt he
  have hcomp : ∀ᶠ N in atTop, prob (p N) (fun z => ε < |V N z|) ≤
      prob (p N) (fun z => δ < |S N z|) := by
    filter_upwards [hbound] with N hN
    apply T2_prob_mono _ (hp N)
    intro z hz
    by_contra hn
    have hs : |S N z| ≤ δ := le_of_not_gt hn
    have hb := hN z (hs.trans hδ1)
    have hm := mul_le_mul_of_nonneg_left hs hC
    linarith
  exact squeeze_zero' (Eventually.of_forall (fun N => T2_prob_nonneg _ (hp N) _)) hcomp (hS δ hδ)

lemma T2_inprob_add (p : ∀ N, Fin N → ℝ) (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (U V : ∀ N, Assignment N → ℝ) (hU : InProb p U) (hV : InProb p V) :
    InProb p (fun N z => U N z+V N z) := by
  intro ε hε
  have hbound : ∀ᶠ N in atTop, prob (p N) (fun z => ε < |U N z+V N z|) ≤
      prob (p N) (fun z => ε/2 < |U N z|)+prob (p N) (fun z => ε/2 < |V N z|) := by
    filter_upwards [] with N
    apply (T2_prob_mono _ (hp N) _ _ ?_).trans (T2_prob_union _ (hp N) _ _)
    intro z hz
    by_contra hn
    push_neg at hn
    linarith [abs_add_le (U N z) (V N z)]
  exact squeeze_zero' (Eventually.of_forall (fun N => T2_prob_nonneg _ (hp N) _)) hbound
    (by simpa using (hU (ε/2) (by positivity)).add (hV (ε/2) (by positivity)))

lemma T2_sum4_sq (a b c d : ℝ) : (a+b+c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

lemma T2_plugin_variances {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    let B := spatialNeighborhoods P h
    InProb p (fun N z => (N : ℝ)*(
      rawSAH (propensities (O N) (θhat N z)) (R N) (B N)
        (fittedScoreFits (propensities (O N) (θhat N z)) (R N) (O N) z) z-
      rawSAH (p N) (R N) (B N) (scoreFits (p N) (R N) (O N)) z)) ∧
    InProb p (fun N z => (N : ℝ)*(
      oracleHAC (propensities (O N) (θhat N z)) (R N) (B N)
        (fittedScoreFits (propensities (O N) (θhat N z)) (R N) (O N) z) z-
      oracleHAC (p N) (R N) (B N) (scoreFits (p N) (R N) (O N)) z)) := by
  let p := fun N => propensities (O N) θ₀
  let R := circleSequence P d
  let B := spatialNeighborhoods P h
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  obtain ⟨U₀, hO₀⟩ := hlog.2.2.1
  let U := max U₀ 0
  have hU : 0 ≤ U := le_max_right _ _
  have hO (N : ℕ) (i : Fin N) (j : Fin k) : |O N i j| ≤ U :=
    (hO₀ N i j).trans (le_max_left _ _)
  obtain ⟨ε, hε, hprop⟩ := T2_uniform_propensities O Θ hlog.1 U hU hO
  have hπ (N : ℕ) := hprop N θ₀ hlog.2.1
  have hθ (N : ℕ) (z : Assignment N) := hprop N (θhat N z) (hlog.2.2.2.2 N z).1
  obtain ⟨c, hc, hgram⟩ := hlog.2.2.2.1
  obtain ⟨M, D, hM, hD, hspatial⟩ := T2_spatial_tail P d h hh hP hWD hloc
  obtain ⟨K₀, hK₀, hmle⟩ := T2_mle_second O θ₀ Θ θhat hlog hp
  let S : ∀ N, Assignment N → ℝ := fun N z => (k : ℝ)*U*‖θhat N z-θ₀‖+
    ‖T2_beta_num (p N) (R N) (O N) false z-T2_beta_pop (p N) (R N) (O N) false‖+
    ‖T2_beta_num (p N) (R N) (O N) true z-T2_beta_pop (p N) (R N) (O N) true‖+
    ‖T2_ht_gradient (p N) (R N) (O N) z-T2_population_gradient (p N) (R N) (O N)‖
  have hS0 (N : ℕ) (z : Assignment N) : 0 ≤ S N z := by dsimp [S]; positivity
  let Kβ := (k : ℝ)*D*(M*U)^2
  let Kγ := (k : ℝ)*D*(M*U/ε)^2
  let K := 4*(((k : ℝ)*U)^2*K₀+2*Kβ+Kγ)+1
  have hK : 0 < K := by dsimp [K, Kβ, Kγ]; positivity
  have hSmoment : ∀ᶠ N in atTop, expect (p N) (fun z => (S N z)^2) ≤ K/N := by
    filter_upwards [hmle, hspatial, eventually_gt_atTop 0] with N hmn hs hN
    have hb (a : Bool) := T2_beta_num_second (p N) (R N) (O N) (B N) D M U (hp N) hN
      hM.le hU hs.1 (hO N) hs.2.2.2.1 hs.2.2.1 hs.2.2.2.2 a
    have hg := T2_gradient_second (p N) (R N) (O N) (B N) D M U ε (hp N) hε (hπ N) hN
      hM.le hU hs.1 (hO N) hs.2.2.2.1 hs.2.2.1 hs.2.2.2.2
    have hpoint := expect_mono (p N) (hp N) (fun z => (S N z)^2) (fun z =>
      4*((((k : ℝ)*U)*‖θhat N z-θ₀‖)^2+
        ‖T2_beta_num (p N) (R N) (O N) false z-T2_beta_pop (p N) (R N) (O N) false‖^2+
        ‖T2_beta_num (p N) (R N) (O N) true z-T2_beta_pop (p N) (R N) (O N) true‖^2+
        ‖T2_ht_gradient (p N) (R N) (O N) z-T2_population_gradient (p N) (R N) (O N)‖^2))
      (fun z => T2_sum4_sq _ _ _ _)
    simp only [mul_pow, expect_mul, expect_add] at hpoint
    have hm := mul_le_mul_of_nonneg_left hmn (sq_nonneg ((k : ℝ)*U))
    have hsum := add_le_add (add_le_add (add_le_add hm (hb false)) (hb true)) hg
    have hfour := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
    simp only [mul_pow] at hfour
    apply hpoint.trans (hfour.trans _)
    dsimp only [K, Kβ, Kγ]
    rw [← mul_div_assoc, ← add_div, ← add_div, ← add_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by ring_nf; linarith) (Nat.cast_nonneg N)
  have hSprob : InProb p S := T2_inprob_of_bigop p hp S _
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
    (T2_bigop_of_second p hp S K hK hSmoment)
  let L := (k : ℝ)/(ε^2*c)
  let Bβ := L*(M*U)
  let Cβ := L*(1+M*U+(k : ℝ)*U^2*Bβ)
  let Cγ := L*(1+M*U/ε^2+(k : ℝ)*U^2*Bβ)
  let F := 3*((k : ℝ)*U*Bβ)
  let Afit := (k : ℝ)*U*(2*Cβ+Cγ)+3*((k : ℝ)*U)*Bβ
  let C := (M+F)/ε
  let A := Afit/ε+(M+F)/ε^2
  let Q := D*(2*C+A)*A
  have hF : 0 ≤ F := by dsimp [F, Bβ, L]; positivity
  have hAfit : 0 ≤ Afit := by dsimp [Afit, Cβ, Cγ, Bβ, L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hboth : ∀ᶠ N in atTop, ∀ z, |S N z| ≤ 1 →
      |(N : ℝ)*(rawSAH (propensities (O N) (θhat N z)) (R N) (B N)
        (fittedScoreFits (propensities (O N) (θhat N z)) (R N) (O N) z) z-
        rawSAH (p N) (R N) (B N) (scoreFits (p N) (R N) (O N)) z)| ≤ Q*|S N z| ∧
      |(N : ℝ)*(oracleHAC (propensities (O N) (θhat N z)) (R N) (B N)
        (fittedScoreFits (propensities (O N) (θhat N z)) (R N) (O N) z) z-
        oracleHAC (p N) (R N) (B N) (scoreFits (p N) (R N) (O N)) z)| ≤ Q*|S N z| := by
    filter_upwards [hspatial, hgram, eventually_gt_atTop 0] with N hs hg hN z hz
    let q := propensities (O N) (θhat N z)
    have hq (i : Fin N) : 0 < q i ∧ q i < 1 := ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
    have hbase : 0 ≤ (k : ℝ)*U*‖θhat N z-θ₀‖ := by positivity
    have hb0 := norm_nonneg (T2_beta_num (p N) (R N) (O N) false z-T2_beta_pop (p N) (R N) (O N) false)
    have hb1 := norm_nonneg (T2_beta_num (p N) (R N) (O N) true z-T2_beta_pop (p N) (R N) (O N) true)
    have hg0 := norm_nonneg (T2_ht_gradient (p N) (R N) (O N) z-T2_population_gradient (p N) (R N) (O N))
    have hpq (i : Fin N) : |q i-p N i| ≤ S N z :=
      (T2_propensity_difference (O N) θ₀ (θhat N z) U hU (hO N) i).trans
        (by dsimp [S]; linarith)
    have hβmom (a : Bool) : ‖T2_beta_num (p N) (R N) (O N) a z-T2_beta_pop (p N) (R N) (O N) a‖ ≤ S N z := by
      cases a <;> dsimp [S] <;> linarith
    have hγmom : ‖T2_ht_gradient (p N) (R N) (O N) z-T2_population_gradient (p N) (R N) (O N)‖ ≤ S N z := by
      dsimp [S]; linarith
    have hf := T2_fittedscore_difference (p N) q (R N) (O N) z ε c M U (S N z) hε hc hM.le hU
      (hS0 N z) hN (hp N) hq (hπ N) (hθ N z) hs.1 (hO N) hg hpq hβmom hγmom
    have hweight (i : Fin N) : ε^2 ≤ p N i*(1-p N i) := by
      simpa only [pow_two] using mul_le_mul (hπ N i).1 (hπ N i).2 hε.le (hp N i).1.le
    have hfits (i : Fin N) (a : Bool) : |scoreFits (p N) (R N) (O N) i a| ≤ F :=
      T2_scorefits_bound (p N) (R N) (O N) (ε^2) c M U (sq_pos_of_pos hε) hc hM.le hU hN
        (hp N) hweight hg hs.1 (hO N) i a
    have htrue (i : Fin N) : |residualContrast (p N) (R N) (scoreFits (p N) (R N) (O N)) i z| ≤ C :=
      T2_residual_bound _ _ _ ε M F hε hM.le hF (hπ N) hs.1 hfits i z
    have hchange (i : Fin N) : |residualContrast q (R N) (fittedScoreFits q (R N) (O N) z) i z-
        residualContrast (p N) (R N) (scoreFits (p N) (R N) (O N)) i z| ≤ A*S N z :=
      T2_contrast_difference (p N) q (R N) _ _ z ε M F Afit (S N z) hε hM.le hF hAfit
        (hS0 N z) (hπ N) (hθ N z) (fun i => hs.1 i z) hfits hf hpq i
    have hb := T2_quadratic_plugin_bound (p N) q (R N) _ _ (B N) z D C A (S N z) hN hD.le hC hA
      (hS0 N z) (by simpa only [abs_of_nonneg (hS0 N z)] using hz) hs.2.2.2.1 htrue hchange
    simpa only [abs_of_nonneg (hS0 N z)] using hb
  constructor
  · apply T2_inprob_good_bound p hp S _ hSprob Q hQ
    filter_upwards [hboth] with N hN z hz
    exact (hN z hz).1
  · apply T2_inprob_good_bound p hp S _ hSprob Q hQ
    filter_upwards [hboth] with N hN z hz
    exact (hN z hz).2

lemma T2_fitted_intervals {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) (hinterior : θ₀ ∈ interior Θ)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀))
    (hv : Nondegenerate (fun N => variance (propensities (O N) θ₀)
      (augmented (propensities (O N) θ₀) (circleSequence P d N)
        (scoreFits (propensities (O N) θ₀) (circleSequence P d N) (O N))))) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    let B := spatialNeighborhoods P h
    ∀ α : ℝ, 0 < α → α < 1 →
      Conservative (fun N => prob (p N) (fun z =>
        let phat := propensities (O N) (θhat N z)
        |fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)| ≤ normalQuantile (1-α/2)*
          Real.sqrt (rawSAH phat (R N) (B N) (fittedScoreFits phat (R N) (O N) z) z))) α ∧
      ((∀ N, 0 ≤ homophilyQ (p N) (R N) (B N) (printedFits (p N) (R N) (O N))) →
        Conservative (fun N => prob (p N) (fun z =>
          let phat := propensities (O N) (θhat N z)
          |fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)| ≤ normalQuantile (1-α/2)*
            Real.sqrt (max (oracleHAC phat (R N) (B N) (fittedScoreFits phat (R N) (O N) z) z) 0))) α) := by
  let p := fun N => propensities (O N) θ₀
  let R := circleSequence P d
  let B := spatialNeighborhoods P h
  let g := fun N => scoreFits (p N) (R N) (O N)
  let V := fun N => variance (p N) (augmented (p N) (R N) (g N))
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨T2_logistic_pos _, T2_logistic_lt_one _⟩
  obtain ⟨ε, hε, hε1, hπ⟩ := hoverlap
  have hπ' (N : ℕ) (i : Fin N) : ε ≤ p N i ∧ ε ≤ 1-p N i :=
    ⟨(hπ N i).1.le, by linarith [(hπ N i).2]⟩
  obtain ⟨U₀, hO₀⟩ := hlog.2.2.1
  let U := max U₀ 0
  have hU : 0 ≤ U := le_max_right _ _
  have hO (N : ℕ) (i : Fin N) (j : Fin k) : |O N i j| ≤ U :=
    (hO₀ N i j).trans (le_max_left _ _)
  obtain ⟨c, hc, hgram⟩ := hlog.2.2.2.1
  obtain ⟨M, D, hM, hD, hspatial⟩ := T2_spatial_tail P d h hh hP hWD hloc
  let F := 3*((k : ℝ)*U*((k : ℝ)/(ε^2*c)*(M*U)))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let C := (M+F)/ε
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hregular : ∀ᶠ N in atTop, (∀ i z, |residualContrast (p N) (R N) (g N) i z| ≤ C) ∧
      (∀ i, (B N i).card ≤ Nat.ceil D) ∧ (∀ i, i ∈ B N i) ∧
      (∀ i j, j ∈ B N i ↔ i ∈ B N j) ∧
      (∀ i j, j ∉ B N i → ¬ sharesSource (R N) i j) := by
    filter_upwards [hspatial, hgram, eventually_gt_atTop 0] with N hs hg hN
    have hweight (i : Fin N) : ε^2 ≤ p N i*(1-p N i) := by
      simpa only [pow_two] using mul_le_mul (hπ' N i).1 (hπ' N i).2 hε.le (hp N i).1.le
    have hfits (i : Fin N) (a : Bool) : |g N i a| ≤ F :=
      T2_scorefits_bound (p N) (R N) (O N) (ε^2) c M U (sq_pos_of_pos hε) hc hM.le hU hN
        (hp N) hweight hg hs.1 (hO N) i a
    refine ⟨T2_residual_bound _ _ _ ε M F hε hM.le hF (hπ' N) hs.1 hfits, ?_,
      hs.2.1, hs.2.2.1, hs.2.2.2.2⟩
    intro i
    exact_mod_cast (hs.2.2.2.1 i).trans (Nat.le_ceil D)
  have horacles := T2_oracles_concentrate p R g B hp (Nat.ceil D) C hC hregular
  have hplugin := T2_plugin_variances P O θ₀ Θ θhat d h hh hP hWD hloc hlog
  let WS := fun N => rawSAH (p N) (R N) (B N) (g N)
  let WH := fun N => oracleHAC (p N) (R N) (B N) (g N)
  let WShat := fun N z => rawSAH (propensities (O N) (θhat N z)) (R N) (B N)
    (fittedScoreFits (propensities (O N) (θhat N z)) (R N) (O N) z) z
  let WHhat := fun N z => oracleHAC (propensities (O N) (θhat N z)) (R N) (B N)
    (fittedScoreFits (propensities (O N) (θhat N z)) (R N) (O N) z) z
  have hS : InProb p (fun N z => (N : ℝ)*(WShat N z-expect (p N) (WS N))) := by
    convert T2_inprob_add p hp _ _ hplugin.1 horacles.1 using 1
    funext N z
    ring
  have hH : InProb p (fun N z => (N : ℝ)*(WHhat N z-expect (p N) (WH N))) := by
    convert T2_inprob_add p hp _ _ hplugin.2 horacles.2 using 1
    funext N z
    ring
  have hE : ∀ᶠ N in atTop, expect (p N) (WH N) = V N+
      homophilyQ (p N) (R N) (B N) (printedFits (p N) (R N) (O N))/N ∧
      V N ≤ expect (p N) (WS N) := by
    filter_upwards [hregular, eventually_gt_atTop 0] with N hr hN
    exact corrected_ipw_oracle (p N) (R N) (O N) (B N) hN (hp N)
      hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
  have hnormal := T2_fitted_normal P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior
    ⟨ε, hε, hε1, hπ⟩ hv
  dsimp only
  intro α hα hα1
  constructor
  · exact T2_wald_conservative p hp (fun N z => fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N))
      WShat V (fun N => expect (p N) (WS N)) hv (hE.mono (fun N hN => hN.2)) hS hnormal α hα hα1
  · intro hhom
    have hEH : ∀ᶠ N in atTop, V N ≤ expect (p N) (WH N) := by
      filter_upwards [hE] with N hN
      rw [hN.1]
      exact le_add_of_nonneg_right (div_nonneg (hhom N) (Nat.cast_nonneg N))
    have hWald := T2_wald_conservative p hp (fun N z => fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N))
      WHhat V (fun N => expect (p N) (WH N)) hv hEH hH hnormal α hα hα1
    intro η hη
    filter_upwards [hWald η hη] with N hN
    apply hN.trans
    apply T2_prob_mono (p N) (hp N)
    intro z hz
    exact hz.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_left (WHhat N z) 0))
      (T2_quantile_pos α hα hα1).le)

theorem corrected_ipw_asymptotics_proof {k : ℕ} (P : PopulationSequence Space)
    (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ)
    (hd : 0 ≤ d) (hh : 0 ≤ h) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hlog : LogisticConditions O θ₀ Θ θhat) (hinterior : θ₀ ∈ interior Θ)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀)) :
    let p := fun N => propensities (O N) θ₀
    let R := circleSequence P d
    let B := spatialNeighborhoods P h
    let V := fun N => variance (p N) (augmented (p N) (R N) (scoreFits (p N) (R N) (O N)))
    BigOp p (fun N z => fittedIPW (R N) (O N) (θhat N) z -
      (ht (p N) (R N) z - (∑ i, (bit (z i)-p N i)*dot (O N i) (scoreGamma (p N) (R N) (O N)))/N))
      (fun N => (N : ℝ)⁻¹) ∧
    LittleOp p (fun N z => augmented (p N) (R N) (scoreFits (p N) (R N) (O N)) z -
      fittedIPW (R N) (O N) (θhat N) z) (fun N => (Real.sqrt N)⁻¹) ∧
    (Nondegenerate V →
      NormalLimit p (fun N z => (fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N))/Real.sqrt (V N)) ∧
      ∀ α : ℝ, 0 < α → α < 1 →
        Conservative (fun N => prob (p N) (fun z =>
          let phat := propensities (O N) (θhat N z)
          |fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)| ≤ normalQuantile (1-α/2) *
            Real.sqrt (rawSAH phat (R N) (B N) (fittedScoreFits phat (R N) (O N) z) z))) α ∧
        ((∀ N, 0 ≤ homophilyQ (p N) (R N) (B N) (printedFits (p N) (R N) (O N))) →
          Conservative (fun N => prob (p N) (fun z =>
            let phat := propensities (O N) (θhat N z)
            |fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)| ≤ normalQuantile (1-α/2) *
              Real.sqrt (max (oracleHAC phat (R N) (B N) (fittedScoreFits phat (R N) (O N) z) z) 0))) α)) := by
  dsimp only
  refine ⟨T2_ipw_expansion P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior hoverlap,
    T2_ipw_little P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior hoverlap, ?_⟩
  intro hv
  exact ⟨T2_fitted_normal P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior hoverlap hv,
    T2_fitted_intervals P O θ₀ Θ θhat d h hh hP hWD hloc hlog hinterior hoverlap hv⟩

end
end AronowAudit.P004.Wave1
