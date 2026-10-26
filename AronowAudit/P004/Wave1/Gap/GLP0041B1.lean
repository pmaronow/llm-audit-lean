import AronowAudit.P004.Wave1.Gap.GP0041B3
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Fixed-design, compact-constrained logistic maximum likelihood. -/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical Topology
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private lemma mle_logistic_eq (x : ℝ) : logistic x = Real.sigmoid x := by
  unfold logistic Real.sigmoid
  rw [Real.exp_neg]
  field_simp
  ring

private lemma mle_logistic_pos (x : ℝ) : 0 < logistic x := by
  rw [mle_logistic_eq]; exact Real.sigmoid_pos x

private lemma mle_logistic_lt (x : ℝ) : logistic x < 1 := by
  rw [mle_logistic_eq]; exact Real.sigmoid_lt_one x

private lemma mle_logistic_deriv (x : ℝ) :
    HasDerivAt logistic (logistic x * (1-logistic x)) x := by
  rw [show logistic = Real.sigmoid from funext mle_logistic_eq]
  exact Real.hasDerivAt_sigmoid x

private def mle_weight (x : ℝ) : ℝ := logistic x * (1-logistic x)

private lemma mle_weight_pos (x : ℝ) : 0 < mle_weight x :=
  mul_pos (mle_logistic_pos x) (sub_pos.mpr (mle_logistic_lt x))

private lemma mle_weight_deriv (x : ℝ) :
    HasDerivAt mle_weight (mle_weight x * (1-2*logistic x)) x := by
  convert (mle_logistic_deriv x).mul ((mle_logistic_deriv x).const_sub 1) using 1 <;> first | rfl | (simp only [mle_weight] <;> ring)

private lemma mle_weight_deriv_bound (x : ℝ) :
    |mle_weight x * (1-2*logistic x)| ≤ 1 := by
  have hp := mle_logistic_pos x
  have hq := mle_logistic_lt x
  have hw := (mle_weight_pos x).le
  have hw1 : mle_weight x ≤ 1 := by dsimp [mle_weight]; nlinarith
  have hs : |1-2*logistic x| ≤ 1 := abs_le.mpr (by constructor <;> linarith)
  rw [abs_mul, abs_of_nonneg hw]
  exact (mul_le_mul_of_nonneg_left hs hw).trans
    (by simpa using hw1)

private def mle_softplus (x : ℝ) : ℝ := Real.log (1+Real.exp x)

private lemma mle_softplus_deriv (x : ℝ) : HasDerivAt mle_softplus (logistic x) x := by
  exact ((Real.hasDerivAt_exp x).const_add 1).log (by positivity : 1+Real.exp x ≠ 0)

/-- A second-order lower bound on a unit segment, from monotonicity twice. -/
private lemma mle_taylor_lower (f f' f'' : ℝ → ℝ) (a : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt f' (f'' t) t)
    (ha : ∀ t ∈ Set.Icc (0:ℝ) 1, a ≤ f'' t) :
    f 0 + f' 0 + a/2 ≤ f 1 := by
  have hd (t : ℝ) : HasDerivAt (fun t => f' t-a*t) (f'' t-a) t := by
    convert (hg t).sub ((hasDerivAt_id' t).const_mul a) using 1 <;> first | rfl | (simp <;> ring)
  have hm : MonotoneOn (fun t => f' t-a*t) (Set.Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t).deriv]
    exact sub_nonneg.mpr (ha t (interior_subset ht))
  have hlin (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : f' 0+a*t ≤ f' t := by
    have h := hm (by norm_num) ht ht.1
    dsimp at h
    linarith
  have hd2 (t : ℝ) : HasDerivAt (fun t => f t-f' 0*t-a/2*t^2)
      (f' t-f' 0-a*t) t := by
    convert ((hf t).sub ((hasDerivAt_id' t).const_mul (f' 0))).sub
      (((hasDerivAt_id' t).pow 2).const_mul (a/2)) using 1 <;> ring
  have hm2 : MonotoneOn (fun t => f t-f' 0*t-a/2*t^2) (Set.Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun t => (hd2 t).continuousAt)).continuousOn
      (fun t _ => (hd2 t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd2 t).deriv]
    linarith [hlin t (interior_subset ht)]
  have h := hm2 (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  dsimp at h
  linarith

private lemma mle_softplus_lower (x h m : ℝ)
    (hm : ∀ t ∈ Set.Icc (0:ℝ) 1, m ≤ mle_weight (x+t*h)) :
    mle_softplus x + logistic x*h + m/2*h^2 ≤ mle_softplus (x+h) := by
  have hf (t : ℝ) : HasDerivAt (fun t => mle_softplus (x+t*h))
      (logistic (x+t*h)*h) t := by
    convert (mle_softplus_deriv _).comp t
      (((hasDerivAt_id' t).mul_const h).const_add x) using 1 <;> first | rfl | (simp <;> ring)
  have hg (t : ℝ) : HasDerivAt (fun t => logistic (x+t*h)*h)
      (mle_weight (x+t*h)*h^2) t := by
    convert ((mle_logistic_deriv _).comp t
      (((hasDerivAt_id' t).mul_const h).const_add x)).mul_const h using 1 <;> first | rfl | (simp only [mle_weight] <;> ring)
  have hh := mle_taylor_lower _ _ _ (m*h^2) hf hg
    (fun t ht => mul_le_mul_of_nonneg_right (hm t ht) (sq_nonneg h))
  simpa only [zero_mul, add_zero, one_mul, mul_div_right_comm] using hh

private lemma mle_logistic_remainder (x h : ℝ) :
    |logistic (x+h)-logistic x-mle_weight x*h| ≤ h^2 := by
  let f : ℝ → ℝ := fun t => logistic (x+t*h)
  let f' : ℝ → ℝ := fun t => mle_weight (x+t*h)*h
  let f'' : ℝ → ℝ := fun t =>
    mle_weight (x+t*h)*(1-2*logistic (x+t*h))*h^2
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    convert (mle_logistic_deriv _).comp t
      (((hasDerivAt_id' t).mul_const h).const_add x) using 1 <;> first | rfl | (simp only [f, f', mle_weight, Function.comp_def] <;> ring)
  have hg (t : ℝ) : HasDerivAt f' (f'' t) t := by
    convert ((mle_weight_deriv _).comp t
      (((hasDerivAt_id' t).mul_const h).const_add x)).mul_const h using 1 <;> first | rfl | (simp only [f', f'', Function.comp_def] <;> ring)
  have hb (t : ℝ) : |f'' t| ≤ h^2 := by
    dsimp [f'']
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    simpa using mul_le_mul_of_nonneg_right (mle_weight_deriv_bound (x+t*h)) (sq_nonneg h)
  have hl := mle_taylor_lower f f' f'' (-h^2) hf hg
    (fun t _ => (abs_le.mp (hb t)).1)
  have hu := mle_taylor_lower (fun t => -f t) (fun t => -f' t) (fun t => -f'' t)
    (-h^2) (fun t => (hf t).neg) (fun t => (hg t).neg)
    (fun t _ => by linarith [(abs_le.mp (hb t)).2])
  dsimp [f, f'] at hl hu
  simp only [zero_mul, add_zero, one_mul] at hl hu
  exact abs_le.mpr (by constructor <;> nlinarith [sq_nonneg h])

private def mle_energy {k : ℕ} (v : Fin k → ℝ) : ℝ := ∑ j, (v j)^2

private lemma mle_norm_sq {k : ℕ} (v : Fin k → ℝ) : ‖v‖^2 ≤ mle_energy v := by
  have hn : 0 ≤ mle_energy v := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  apply (Real.le_sqrt (norm_nonneg v) hn).mp
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ j))

private lemma mle_dot_abs {k : ℕ} (u v : Fin k → ℝ) :
    |dot u v| ≤ (k:ℝ)*‖u‖*‖v‖ := by
  calc
    _ ≤ ∑ j, |u j*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, ‖u‖*‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_le_pi_norm u j)
        (by simpa using norm_le_pi_norm v j) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

private lemma mle_dot_path {k : ℕ} (o x v : Fin k → ℝ) (t : ℝ) :
    dot o (x+t • v) = dot o x+t*dot o v := by
  simp [dot, mul_add, mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum]

private lemma mle_dot_sub {k : ℕ} (o x y : Fin k → ℝ) :
    dot o (x-y) = dot o x-dot o y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

private lemma mle_information_mul {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (v : Fin k → ℝ) (j : Fin k) :
    (information p O *ᵥ v) j =
      (∑ i, p i*(1-p i)*O i j*dot (O i) v)/N := by
  simp only [Matrix.mulVec, dotProduct, information, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma mle_information_quad {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (v : Fin k → ℝ) :
    dot v (information p O *ᵥ v) =
      (∑ i, p i*(1-p i)*(dot (O i) v)^2)/N := by
  change (∑ a, v a*(information p O *ᵥ v) a) = _
  simp_rw [mle_information_mul, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (p i*(1-p i)*dot (O i) v)*(∑ a, O i a*v a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [← dot]; ring

/-- Coercivity controls the ordinary nonsingular inverse, also in dimension zero. -/
private lemma mle_inverse {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) (a : ℝ)
    (ha : 0 < a) (hH : ∀ v, a*mle_energy v ≤ dot v (H *ᵥ v)) :
    (∀ u, H *ᵥ (H⁻¹ *ᵥ u) = u) ∧
    (∀ u, ‖H⁻¹ *ᵥ u‖ ≤ ((k:ℝ)+1)/a*‖u‖) := by
  have hbound (v : Fin k → ℝ) : ‖v‖ ≤ ((k:ℝ)+1)/a*‖H *ᵥ v‖ := by
    have h1 := (mul_le_mul_of_nonneg_left (mle_norm_sq v) ha.le).trans (hH v)
    have h2 := (le_abs_self (dot v (H *ᵥ v))).trans (mle_dot_abs v (H *ᵥ v))
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    by_cases hv : ‖v‖ = 0
    · simp [hv]; positivity
    · have hvp := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
      have hsmall : a*‖v‖ ≤ (k:ℝ)*‖H *ᵥ v‖ := by
        nlinarith
      nlinarith [norm_nonneg (H *ᵥ v)]
  have hinj : Function.Injective (fun v => H *ᵥ v) := by
    intro v w he
    change H *ᵥ v = H *ᵥ w at he
    have hz : H *ᵥ (v-w) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
    have hh := hbound (v-w)
    rw [hz, norm_zero, mul_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hu : IsUnit H.det := H.isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hright (u : Fin k → ℝ) : H *ᵥ (H⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, H.mul_nonsing_inv hu, Matrix.one_mulVec]
  exact ⟨hright, fun u => by simpa only [hright] using hbound (H⁻¹ *ᵥ u)⟩

/-- The score energy has an explicit second-moment bound under the finite product law. -/
private lemma mle_score_moment {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (U : ℝ) (hN : 0 < N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hU : 0 ≤ U) (hO : ∀ i j, |O i j| ≤ U) :
    expect p (fun z => mle_energy (logisticScore p O z)) ≤ (k:ℝ)*U^2/N := by
  have hcoord (j : Fin k) :
      expect p (fun z => (logisticScore p O z j)^2) ≤ U^2/N := by
    let X : Fin N → Assignment N → ℝ := fun i z => (bit (z i)-p i)*O i j
    have hm (i : Fin N) : expect p (X i) = 0 := by
      rw [show X i = fun z => (bit (z i)-p i)*O i j from rfl,
        t18_expect_coordinate p i (fun b => (bit b-p i)*O i j)]
      simp only [bit, ite_true, Bool.false_eq_true, ite_false]
      ring
    have hv (i : Fin N) : variance p (X i) ≤ U^2 := by
      unfold variance cov
      rw [hm]
      simp only [mul_zero, sub_zero]
      have he : expect p (fun z => X i z*X i z) = p i*(1-p i)*(O i j)^2 := by
        rw [show (fun z => X i z*X i z) =
          (fun z => ((bit (z i)-p i)*O i j)^2) by funext z; dsimp [X]; ring,
          t18_expect_coordinate p i (fun b => ((bit b-p i)*O i j)^2)]
        simp only [bit, ite_true, Bool.false_eq_true, ite_false]
        ring
      rw [he]
      have ho : (O i j)^2 ≤ U^2  := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hU).mpr (hO i j)
      have hp0 := (hp i).1
      have hp1 := (hp i).2
      have hw : 0 ≤ p i*(1-p i) := mul_nonneg hp0.le (sub_nonneg.mpr hp1.le)
      have hw1 : p i*(1-p i) ≤ 1 := by nlinarith
      exact (mul_le_mul_of_nonneg_left ho hw).trans (mul_le_of_le_one_left (sq_nonneg U) hw1)
    have hcov (i l : Fin N) (hil : i ≠ l) : cov p (X i) (X l) = 0 := by
      unfold cov
      rw [GraphCompletion.expect_mul_of_disjoint_depends p ({i} : Set (Fin N)) (X i) (X l)]
      · ring
      · intro x y hxy
        exact congrArg (fun b => (bit b-p i)*O i j) (hxy i (by simp))
      · intro x y hxy
        exact congrArg (fun b => (bit b-p l)*O l j) (hxy l (by simpa using hil.symm))
    have hs : expect p (fun z => logisticScore p O z j) = 0 := by
      change expect p (fun z => (∑ i, X i z)/N) = 0
      rw [expect_div, expect_sum]
      simp [hm]
    have he : expect p (fun z => (logisticScore p O z j)^2) =
        variance p (fun z => logisticScore p O z j) := by
      unfold variance cov
      rw [hs]
      simp [pow_two]
    rw [he]
    change variance p (fun z => (∑ i, X i z)/N) ≤ _
    rw [variance_div, variance_sum]
    have hdiag : (∑ i, ∑ l, cov p (X i) (X l)) = ∑ i, variance p (X i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rfl
      · intro l _ hli; exact hcov i l hli.symm
      · simp
    rw [hdiag]
    have hsum : (∑ i, variance p (X i)) ≤ (N:ℝ)*U^2 := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hv i)
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    apply (div_le_div_of_nonneg_right hsum (sq_nonneg (N:ℝ))).trans_eq
    field_simp
  unfold mle_energy
  rw [expect_sum]
  simpa [Finset.sum_div, mul_div_assoc] using
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcoord j)

private lemma mle_segment_abs (x y B t : ℝ) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : |x+t*(y-x)| ≤ B := by
  calc
    _ = |(1-t)*x+t*y| := by congr 1; ring
    _ ≤ |(1-t)*x|+|t*y| := abs_add_le _ _
    _ = (1-t)*|x|+t*|y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1-t)*B+t*B := add_le_add
      (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hy ht.1)
    _ = B := by ring

private lemma mle_constants {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) (hlog : LogisticConditions O θ₀ Θ θhat) :
    ∃ U m c : ℝ, 0 < U ∧ 0 < m ∧ 0 < c ∧
      (∀ N i j, |O N i j| ≤ U) ∧
      (∀ N i θ, θ ∈ Θ → ∀ t ∈ Set.Icc (0:ℝ) 1,
        m ≤ mle_weight (dot (O N i) θ₀+t*dot (O N i) (θ-θ₀))) ∧
      ∀ᶠ N in atTop, ∀ v : Fin k → ℝ,
        c*mle_energy v ≤ (∑ i, (dot (O N i) v)^2)/N := by
  obtain ⟨hcpt, hθ, ⟨U₀, hU₀⟩, ⟨c, hc, hgram⟩, _⟩ := hlog
  obtain ⟨T, hT, hΘ⟩ := hcpt.isBounded.exists_pos_norm_le
  let U := |U₀|+1
  have hU : 0 < U := by dsimp [U]; positivity
  have hO (N : ℕ) (i : Fin N) (j : Fin k) : |O N i j| ≤ U :=
    (hU₀ N i j).trans (by dsimp [U]; linarith [le_abs_self U₀])
  have hOn (N : ℕ) (i : Fin N) : ‖O N i‖ ≤ U := by
    exact (pi_norm_le_iff_of_nonneg hU.le).mpr (fun j => by simpa using hO N i j)
  let B : ℝ := (k:ℝ)*U*T
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd (N : ℕ) (i : Fin N) (θ : Fin k → ℝ) (h : θ ∈ Θ) :
      |dot (O N i) θ| ≤ B :=
    (mle_dot_abs _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hOn N i) (Nat.cast_nonneg k)) (hΘ θ h)
      (norm_nonneg _) (by positivity))
  have hw : Continuous mle_weight := by
    have hs : Continuous logistic := by
      rw [show logistic = Real.sigmoid from funext mle_logistic_eq]
      exact continuous_sigmoid
    exact hs.mul (continuous_const.sub hs)
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith : -B ≤ B)) hw.continuousOn
  refine ⟨U, mle_weight b, c, hU, mle_weight_pos b, hc, hO, ?_, hgram⟩
  intro N i θ hθ' t ht
  apply hmin
  rw [Set.mem_Icc, ← abs_le]
  rw [mle_dot_sub]
  exact mle_segment_abs _ _ _ _ (hd N i θ₀ hθ) (hd N i θ hθ') ht

private lemma mle_score_dot {N k : ℕ} (p : Fin N → ℝ)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) (v : Fin k → ℝ) :
    dot (logisticScore p O z) v = (∑ i, (bit (z i)-p i)*dot (O i) v)/N := by
  simp only [dot, logisticScore, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma mle_norm_of_quad {k : ℕ} (v g : Fin k → ℝ) (a : ℝ)
    (ha : 0 < a) (hq : a*mle_energy v ≤ dot g v) :
    ‖v‖ ≤ ((k:ℝ)+1)/a*‖g‖ := by
  have h1 := (mul_le_mul_of_nonneg_left (mle_norm_sq v) ha.le).trans hq
  have h2 := (le_abs_self (dot g v)).trans (mle_dot_abs g v)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  by_cases hv : ‖v‖ = 0
  · simp [hv]; positivity
  · have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hh : a*‖v‖ ≤ (k:ℝ)*‖g‖ := by nlinarith
    nlinarith [norm_nonneg g]

private lemma mle_mle_bound {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) (m c : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hc : 0 < c)
    (hweight : ∀ i t, t ∈ Set.Icc (0:ℝ) 1 →
      m ≤ mle_weight (dot (O i) θ₀+t*dot (O i) (θ-θ₀)))
    (hgram : ∀ v : Fin k → ℝ, c*mle_energy v ≤ (∑ i, (dot (O i) v)^2)/N)
    (hmax : (∑ i : Fin N, (bit (z i)*dot (O i) θ₀-mle_softplus (dot (O i) θ₀))) ≤
      ∑ i : Fin N, (bit (z i)*dot (O i) θ-mle_softplus (dot (O i) θ))) :
    ‖θ-θ₀‖ ≤ ((k:ℝ)+1)/(m*c/2)*‖logisticScore (propensities O θ₀) O z‖ := by
  have hi (i : Fin N) : m/2*(dot (O i) (θ-θ₀))^2 ≤
      (bit (z i)*dot (O i) θ₀-mle_softplus (dot (O i) θ₀)) -
      (bit (z i)*dot (O i) θ-mle_softplus (dot (O i) θ)) +
      (bit (z i)-propensities O θ₀ i)*dot (O i) (θ-θ₀) := by
    have ht := mle_softplus_lower (dot (O i) θ₀) (dot (O i) (θ-θ₀)) m (hweight i)
    rw [mle_dot_sub] at ht ⊢
    simp only [add_sub_cancel] at ht
    change _ ≤ _ + (bit (z i)-logistic (dot (O i) θ₀))*(dot (O i) θ-dot (O i) θ₀)
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_sub_distrib] at hmax
  have hs' : m/2*(∑ i, (dot (O i) (θ-θ₀))^2) ≤
      ∑ i, (bit (z i)-propensities O θ₀ i)*dot (O i) (θ-θ₀) := by linarith
  apply mle_norm_of_quad _ _ (m*c/2) (by positivity)
  rw [mle_score_dot]
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hh := mul_le_mul_of_nonneg_left (hgram (θ-θ₀)) (by positivity : 0 ≤ m/2)
  have hs'' := div_le_div_of_nonneg_right hs' hn.le
  calc
    _ = m/2*(c*mle_energy (θ-θ₀)) := by ring
    _ ≤ m/2*((∑ i, (dot (O i) (θ-θ₀))^2)/N) := hh
    _ ≤ _ := by simpa only [mul_div_assoc] using hs''

private def mle_likelihood {N k : ℕ} (O : Fin N → Fin k → ℝ) (z : Assignment N)
    (θ : Fin k → ℝ) : ℝ :=
  ∑ i, (bit (z i)*dot (O i) θ-mle_softplus (dot (O i) θ))

private lemma mle_likelihood_deriv {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (z : Assignment N) (θ v : Fin k → ℝ) :
    HasDerivAt (fun t : ℝ => mle_likelihood O z (θ+t • v))
      (∑ i, (bit (z i)-logistic (dot (O i) θ))*dot (O i) v) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have hd : HasDerivAt (fun t : ℝ => dot (O i) (θ+t • v)) (dot (O i) v) 0 := by
    simp_rw [mle_dot_path]
    convert ((hasDerivAt_id' (0:ℝ)).mul_const (dot (O i) v)).const_add (dot (O i) θ)
      using 1 <;> first | rfl | simp
  convert (hd.const_mul (bit (z i))).sub
    ((mle_softplus_deriv (dot (O i) (θ+(0:ℝ) • v))).comp 0 hd) using 1 <;>
    first | rfl | (simp only [zero_smul, add_zero] <;> ring)

private lemma mle_score_zero {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (z : Assignment N) (θ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (hθ : θ ∈ interior Θ) (hmax : ∀ x ∈ Θ, mle_likelihood O z x ≤ mle_likelihood O z θ) :
    logisticScore (propensities O θ) O z = 0 := by
  let g := logisticScore (propensities O θ) O z
  have hloc : IsLocalMax (mle_likelihood O z) θ :=
    (show IsMaxOn (mle_likelihood O z) Θ θ from hmax).isLocalMax
      (mem_interior_iff_mem_nhds.mp hθ)
  have hpath : IsLocalMax (fun t : ℝ => mle_likelihood O z (θ+t • g)) 0 := by
    have hp : IsLocalMax (mle_likelihood O z) ((fun t : ℝ => θ+t • g) 0) := by
      simpa only [zero_smul, add_zero] using hloc
    exact hp.comp_continuous (g := fun t : ℝ => θ+t • g) (by fun_prop)
  have hz := hpath.hasDerivAt_eq_zero (mle_likelihood_deriv O z θ g)
  have hgg : dot g g = 0 := by
    rw [mle_score_dot]
    change (∑ i, (bit (z i)-logistic (dot (O i) θ))*dot (O i) g)/N = 0
    rw [hz, zero_div]
  have he : mle_energy g = 0 := by simpa only [dot, mle_energy, pow_two] using hgg
  have hn := mle_norm_sq g
  rw [he] at hn
  have hnorm : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
  exact norm_eq_zero.mp hnorm

private lemma mle_information_coercive {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (m c : ℝ) (hN : 0 < N) (hm : 0 < m)
    (hw : ∀ i, m ≤ mle_weight (dot (O i) θ₀))
    (hg : ∀ v : Fin k → ℝ, c*mle_energy v ≤ (∑ i, (dot (O i) v)^2)/N)
    (v : Fin k → ℝ) :
    (m*c)*mle_energy v ≤ dot v (information (propensities O θ₀) O *ᵥ v) := by
  rw [mle_information_quad]
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  calc
    _ = m*(c*mle_energy v) := by ring
    _ ≤ m*((∑ i, (dot (O i) v)^2)/N) := mul_le_mul_of_nonneg_left (hg v) hm.le
    _ = (∑ i, m*(dot (O i) v)^2)/N := by rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hn
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)

private lemma mle_score_remainder {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) (U : ℝ) (hN : 0 < N)
    (hU : 0 ≤ U) (hO : ∀ i j, |O i j| ≤ U)
    (hz : logisticScore (propensities O θ) O z = 0) :
    ‖information (propensities O θ₀) O *ᵥ (θ-θ₀)-logisticScore (propensities O θ₀) O z‖ ≤
      ((k:ℝ)*U)^2*U*‖θ-θ₀‖^2 := by
  let e : Fin N → ℝ := fun i => logistic (dot (O i) θ)-logistic (dot (O i) θ₀)-
    mle_weight (dot (O i) θ₀)*dot (O i) (θ-θ₀)
  have hOn (i : Fin N) : ‖O i‖ ≤ U :=
    (pi_norm_le_iff_of_nonneg hU).mpr (fun j => by simpa using hO i j)
  have he (i : Fin N) : |e i| ≤ ((k:ℝ)*U)^2*‖θ-θ₀‖^2 := by
    have hs := mle_logistic_remainder (dot (O i) θ₀) (dot (O i) (θ-θ₀))
    rw [mle_dot_sub, add_sub_cancel] at hs
    have hd : |dot (O i) (θ-θ₀)| ≤ (k:ℝ)*U*‖θ-θ₀‖ :=
      (mle_dot_abs _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hOn i) (Nat.cast_nonneg k)) (norm_nonneg _))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (k:ℝ)*U*‖θ-θ₀‖)).mpr hd
    simp only [sq_abs, mle_dot_sub, mul_pow] at hsq
    dsimp [e]
    rw [mle_dot_sub]
    exact hs.trans (by nlinarith [hsq])
  have hcoord (j : Fin k) :
      (information (propensities O θ₀) O *ᵥ (θ-θ₀)-logisticScore (propensities O θ₀) O z) j =
        -(∑ i, e i*O i j)/N := by
    have hs := congrFun hz j
    change (∑ i, (bit (z i)-logistic (dot (O i) θ))*O i j)/N = 0 at hs
    change (information (propensities O θ₀) O *ᵥ (θ-θ₀)) j-
      logisticScore (propensities O θ₀) O z j = _
    rw [mle_information_mul]
    unfold logisticScore
    change (∑ i, mle_weight (dot (O i) θ₀)*O i j*dot (O i) (θ-θ₀))/N-
      (∑ i, (bit (z i)-logistic (dot (O i) θ₀))*O i j)/N = _
    have hid : (∑ i, mle_weight (dot (O i) θ₀)*O i j*dot (O i) (θ-θ₀))/N-
        (∑ i, (bit (z i)-logistic (dot (O i) θ₀))*O i j)/N +
        (∑ i, (bit (z i)-logistic (dot (O i) θ))*O i j)/N = -(∑ i, e i*O i j)/N := by
      rw [← sub_div, ← add_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [e]
      ring
    simpa only [hs, add_zero] using hid
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [hcoord, Real.norm_eq_abs, abs_div, abs_neg,
    show |(N:ℝ)| = (N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |e i*O i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ((k:ℝ)*U)^2*U*‖θ-θ₀‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hh := mul_le_mul (he i) (hO i j) (abs_nonneg _) (by positivity)
      convert hh using 1 <;> ring
    _ = _ := by simp; ring

private lemma mle_expansion_bound {N k : ℕ} (O : Fin N → Fin k → ℝ)
    (θ₀ θ : Fin k → ℝ) (z : Assignment N) (U m c : ℝ)
    (hN : 0 < N) (hU : 0 ≤ U) (hm : 0 < m) (hc : 0 < c)
    (hO : ∀ i j, |O i j| ≤ U) (hw : ∀ i, m ≤ mle_weight (dot (O i) θ₀))
    (hg : ∀ v : Fin k → ℝ, c*mle_energy v ≤ (∑ i, (dot (O i) v)^2)/N)
    (hz : logisticScore (propensities O θ) O z = 0) :
    ‖θ-θ₀-(information (propensities O θ₀) O)⁻¹ *ᵥ logisticScore (propensities O θ₀) O z‖ ≤
      (((k:ℝ)+1)/(m*c))*(((k:ℝ)*U)^2*U)*‖θ-θ₀‖^2 := by
  let H := information (propensities O θ₀) O
  let g := logisticScore (propensities O θ₀) O z
  let v := θ-θ₀-H⁻¹ *ᵥ g
  have hH := mle_information_coercive O θ₀ m c hN hm hw hg
  have hi := mle_inverse H (m*c) (mul_pos hm hc) hH
  have hv : H *ᵥ v = H *ᵥ (θ-θ₀)-g := by
    dsimp [v]
    rw [Matrix.mulVec_sub, hi.1]
  have hq : (m*c)*mle_energy v ≤ dot (H *ᵥ v) v := by
    simpa only [dot, mul_comm] using hH v
  have hb := mle_norm_of_quad v (H *ᵥ v) (m*c) (mul_pos hm hc) hq
  rw [hv] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (mle_score_remainder O θ₀ θ z U hN hU hO hz)
      (by positivity : 0 ≤ ((k:ℝ)+1)/(m*c))
    convert hh using 1 <;> ring)

private lemma mle_square_tail {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (X : Assignment N → ℝ) (t : ℝ) (ht : 0 < t) :
    prob p (fun z => t < |X z|) ≤ expect p (fun z => (X z)^2)/t^2 := by
  apply (t18_prob_mono p hp _ (fun z => t^2 < (X z)^2) ?_).trans
    (t18_markov p hp _ (fun z => sq_nonneg _) _ (sq_pos_of_pos ht))
  intro z hz
  simpa only [sq_abs] using (sq_lt_sq₀ ht.le (abs_nonneg _)).mpr hz

private lemma mle_moment_rates (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (X : ∀ N, Assignment N → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ᶠ N in atTop, expect (p N) (fun z => (X N z)^2) ≤ K/N) :
    InProb p X ∧ BigOp p X (fun N => (Real.sqrt N)⁻¹) := by
  have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  constructor
  · intro ε hε
    have hlim : Tendsto (fun N : ℕ => (K/N)/ε^2) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, zero_mul, mul_zero] using (hi.const_mul K).mul_const (ε^2)⁻¹
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N => t18_prob_nonneg (p N) (hp N) _)) _ hlim
    filter_upwards [hm] with N hN
    exact (mle_square_tail (p N) (hp N) (X N) ε hε).trans
      (div_le_div_of_nonneg_right hN (sq_nonneg ε))
  · intro ε hε
    let C := K/ε+1
    have hC1 : 1 ≤ C := by dsimp [C]; linarith [div_nonneg hK hε.le]
    have hC : 0 < C := by linarith
    have hCe : ε*C = K+ε := by dsimp [C]; field_simp <;> ring
    have hCc : C ≤ C^2 := by nlinarith
    have htail : K/C^2 < ε := by
      apply (div_lt_iff₀ (sq_pos_of_pos hC)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hCc hε.le]
    refine ⟨C, hC, ?_⟩
    filter_upwards [hm, eventually_gt_atTop 0] with N hNm hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
    have ht : 0 < C*(Real.sqrt (N:ℝ))⁻¹ := mul_pos hC (inv_pos.mpr hs)
    rw [abs_of_nonneg (inv_nonneg.mpr hs.le)]
    calc
      _ ≤ expect (p N) (fun z => (X N z)^2)/(C*(Real.sqrt (N:ℝ))⁻¹)^2 :=
        mle_square_tail (p N) (hp N) (X N) _ ht
      _ ≤ (K/N)/(C*(Real.sqrt (N:ℝ))⁻¹)^2 :=
        div_le_div_of_nonneg_right hNm (sq_nonneg _)
      _ = K/C^2 := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hn.le]
        field_simp
      _ < ε := htail

private lemma mle_prob_union {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop) :
    prob p (fun z => A z ∨ B z) ≤ prob p A+prob p B := by
  unfold prob
  rw [← expect_add]
  apply expect_mono p hp
  intro z
  by_cases ha : A z <;> by_cases hb : B z <;> simp [ha, hb]

/-- A quadratic bound on a fixed neighborhood gives the finer stochastic rate. -/
private lemma mle_good_event_rate (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (D E : ∀ N, Assignment N → ℝ) (K B r : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hr : 0 < r)
    (hm : ∀ᶠ N in atTop, expect (p N) (fun z => (D N z)^2) ≤ K/N)
    (hb : ∀ᶠ N in atTop, ∀ z, |D N z| < r → |E N z| ≤ B*(D N z)^2) :
    BigOp p E (fun N => (N:ℝ)⁻¹) := by
  have hD := (mle_moment_rates p hp D K hK hm).1
  intro ε hε
  let C := 2*B*K/ε+1
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB) hK) hε.le]
  have hC : 0 < C := by linarith
  have hCe : ε*C = 2*B*K+ε := by dsimp [C]; field_simp <;> ring
  have htail : B*K/C < ε/2 := by
    apply (div_lt_iff₀ hC).mpr
    nlinarith
  have hbad := (hD (r/2) (by positivity)).eventually (eventually_lt_nhds (show 0 < ε/2 by positivity))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hm, hb, hbad, eventually_gt_atTop 0] with N hNm hNb hbadN hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  rw [abs_of_nonneg (inv_nonneg.mpr hn.le)]
  have hevent : prob (p N) (fun z => C*(N:ℝ)⁻¹ < |E N z|) ≤
      prob (p N) (fun z => r/2 < |D N z|)+
        prob (p N) (fun z => C/N < B*(D N z)^2) := by
    apply (t18_prob_mono (p N) (hp N) _
      (fun z => r/2 < |D N z| ∨ C/N < B*(D N z)^2) ?_).trans
      (mle_prob_union (p N) (hp N) _ _)
    intro z hz
    by_cases hd : r/2 < |D N z|
    · exact Or.inl hd
    · apply Or.inr
      have hlt : |D N z| < r := by linarith [le_of_not_gt hd]
      exact lt_of_lt_of_le hz (hNb z hlt)
  have hmB : expect (p N) (fun z => B*(D N z)^2) ≤ B*K/N := by
    rw [expect_mul]
    convert mul_le_mul_of_nonneg_left hNm hB using 1 <;> ring
  have ht := t18_markov (p N) (hp N) (fun z => B*(D N z)^2)
    (fun z => mul_nonneg hB (sq_nonneg _)) (C/N) (div_pos hC hn)
  have ht' : prob (p N) (fun z => C/N < B*(D N z)^2) ≤ B*K/C := by
    apply (ht.trans (div_le_div_of_nonneg_right hmB (div_nonneg hC.le hn.le))).trans_eq
    field_simp
  linarith

private lemma mle_littleop (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (X : ∀ N, Assignment N → ℝ)
    (hX : BigOp p X (fun N => (N:ℝ)⁻¹)) :
    LittleOp p X (fun N => (Real.sqrt N)⁻¹) := by
  have hh := t18_bigop_rootn p hp X hX
  simpa only [LittleOp, InProb, div_inv_eq_mul, abs_mul, abs_neg, mul_comm] using hh

/-- T10: consistency and the root-N rate need membership; the score expansion
uses interiority of the true parameter. -/
theorem corrected_mle_proof {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ)
    (hlog : LogisticConditions O θ₀ Θ θhat)
    (hoverlap : Overlap (fun N => propensities (O N) θ₀)) :
    let p := fun N => propensities (O N) θ₀
    InProb p (fun N z => ‖θhat N z - θ₀‖) ∧
    BigOp p (fun N z => ‖θhat N z - θ₀‖) (fun N => (Real.sqrt N)⁻¹) ∧
    (θ₀ ∈ interior Θ →
      BigOp p (fun N z => ‖θhat N z-θ₀-(information (p N) (O N))⁻¹ *ᵥ logisticScore (p N) (O N) z‖)
        (fun N => (N : ℝ)⁻¹) ∧
      LittleOp p (fun N z => ‖θhat N z-θ₀-(information (p N) (O N))⁻¹ *ᵥ logisticScore (p N) (O N) z‖)
        (fun N => (Real.sqrt N)⁻¹)) := by
  let p := fun N => propensities (O N) θ₀
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 :=
    ⟨mle_logistic_pos _, mle_logistic_lt _⟩
  obtain ⟨U, m, c, hU, hm, hc, hO, hw, hg⟩ := mle_constants O θ₀ Θ θhat hlog
  let D : ∀ N, Assignment N → ℝ := fun N z => ‖θhat N z-θ₀‖
  let A : ℝ := ((k:ℝ)+1)/(m*c/2)
  let K : ℝ := A^2*(k:ℝ)*U^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsel := hlog.2.2.2.2
  have hbound : ∀ᶠ N in atTop, ∀ z, D N z ≤ A*‖logisticScore (p N) (O N) z‖ := by
    filter_upwards [hg, eventually_gt_atTop 0] with N hgram hN
    intro z
    exact mle_mle_bound (O N) θ₀ (θhat N z) z m c hN hm hc
      (fun i t ht => hw N i (θhat N z) (hsel N z).1 t ht) hgram
      ((hsel N z).2 θ₀ hlog.2.1)
  have hmoment : ∀ᶠ N in atTop, expect (p N) (fun z => (D N z)^2) ≤ K/N := by
    filter_upwards [hbound, eventually_gt_atTop 0] with N hb hN
    calc
      _ ≤ expect (p N) (fun z => A^2*mle_energy (logisticScore (p N) (O N) z)) := by
        apply expect_mono (p N) (hp N)
        intro z
        have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ A*‖logisticScore (p N) (O N) z‖)).mpr (hb z)
        have he := mul_le_mul_of_nonneg_left (mle_norm_sq (logisticScore (p N) (O N) z)) (sq_nonneg A)
        dsimp [D] at hs ⊢
        nlinarith
      _ = A^2*expect (p N) (fun z => mle_energy (logisticScore (p N) (O N) z)) := expect_mul _ _ _
      _ ≤ A^2*((k:ℝ)*U^2/N) := mul_le_mul_of_nonneg_left
        (mle_score_moment (p N) (O N) U hN (hp N) hU.le (hO N)) (sq_nonneg A)
      _ = K/N := by dsimp [K]; ring
  have hrates := mle_moment_rates p hp D K hK hmoment
  refine ⟨hrates.1, hrates.2, ?_⟩
  intro hinterior
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinterior)
  let E : ∀ N, Assignment N → ℝ := fun N z =>
    ‖θhat N z-θ₀-(information (p N) (O N))⁻¹ *ᵥ logisticScore (p N) (O N) z‖
  let B : ℝ := (((k:ℝ)+1)/(m*c))*(((k:ℝ)*U)^2*U)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hexp : ∀ᶠ N in atTop, ∀ z, |D N z| < r → |E N z| ≤ B*(D N z)^2 := by
    filter_upwards [hg, eventually_gt_atTop 0] with N hgram hN
    intro z hz
    have hmem : θhat N z ∈ Metric.ball θ₀ r := by
      simpa only [Metric.mem_ball, dist_eq_norm, D, abs_of_nonneg (norm_nonneg _)] using hz
    have hint : θhat N z ∈ interior Θ := by
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem) hball
    have hs : logisticScore (propensities (O N) (θhat N z)) (O N) z = 0 :=
      mle_score_zero (O N) z (θhat N z) Θ hint (hsel N z).2
    have hw0 (i : Fin N) : m ≤ mle_weight (dot (O N i) θ₀) := by
      simpa only [zero_mul, add_zero] using
        hw N i θ₀ hlog.2.1 0 (by norm_num)
    simpa only [E, D, B, abs_of_nonneg (norm_nonneg _)] using
      mle_expansion_bound (O N) θ₀ (θhat N z) z U m c hN hU.le hm hc (hO N) hw0 hgram hs
  have hE := mle_good_event_rate p hp D E K B r hK hB hr hmoment hexp
  exact ⟨hE, mle_littleop p hp E hE⟩

end
end AronowAudit.P004.Wave1
