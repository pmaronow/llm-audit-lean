import AronowAudit.P029.P029_Audit
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# P029: grouped covariance and finite binomial scores
-/

namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-! ## Fiber centering and covariance -/

private lemma GP029T10_event_pos {L : Type*} [Fintype L]
    (p : L → ℝ) (hp : ∀ i, 0 < p i) (E : L → Prop)
    (hE : ∃ i, E i) : 0 < fP p E := by
  classical
  unfold fP
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact (hp i).le
    · exact le_rfl
  · obtain ⟨i, hi⟩ := hE
    exact ⟨i, Finset.mem_univ i, by simpa only [if_pos hi] using hp i⟩

/-- Multiplication removes the conditional-mean denominator, including an empty event. -/
private lemma GP029T10_mass_mul_ce {L : Type*} [Fintype L]
    (p v : L → ℝ) (hp : ∀ i, 0 < p i) (E : L → Prop) :
    fP p E * fCE p v E = fE p (fun i => if E i then v i else 0) := by
  classical
  by_cases hE : ∃ i, E i
  · have hm := ne_of_gt (GP029T10_event_pos p hp E hE)
    unfold fCE
    field_simp [hm]
  · have he : ∀ i, ¬ E i := by simpa only [not_exists] using hE
    simp [fP, fCE, fE, he]

private lemma GP029T10_centered_fiber {L G : Type*} [Fintype L]
    (p v : L → ℝ) (hp : ∀ i, 0 < p i) (group : L → G) (g : G) :
    (∑ i ∈ Finset.univ.filter (fun i => group i = g),
      p i * (v i - fGroupMean p v group g)) = 0 := by
  classical
  have hn : fE p (fun i => if group i = g then v i else 0) =
      ∑ i ∈ Finset.univ.filter (fun i => group i = g), p i * v i := by
    simp only [fE, Finset.sum_filter, mul_ite, mul_zero]
  have hm : fP p (fun i => group i = g) =
      ∑ i ∈ Finset.univ.filter (fun i => group i = g), p i := by
    simp only [fP, Finset.sum_filter]
  have hc := GP029T10_mass_mul_ce p v hp (fun i => group i = g)
  calc
    _ = (∑ i ∈ Finset.univ.filter (fun i => group i = g), p i * v i) -
        (∑ i ∈ Finset.univ.filter (fun i => group i = g), p i) *
          fGroupMean p v group g := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = 0 := by rw [← hn, ← hm]; exact sub_eq_zero.mpr hc.symm

/-- A centered within-fiber residual is orthogonal to every function of the group. -/
private lemma GP029T10_orthogonal {L G : Type*} [Fintype L] [Fintype G]
    (p v : L → ℝ) (hp : ∀ i, 0 < p i) (group : L → G) (h : G → ℝ) :
    fE p (fun i => (v i - fGroupMean p v group (group i)) * h (group i)) = 0 := by
  classical
  unfold fE
  calc
    _ = ∑ g, ∑ i ∈ Finset.univ.filter (fun i => group i = g),
        p i * ((v i - fGroupMean p v group (group i)) * h (group i)) :=
      (Finset.sum_fiberwise Finset.univ group _).symm
    _ = ∑ g, (∑ i ∈ Finset.univ.filter (fun i => group i = g),
        p i * (v i - fGroupMean p v group g)) * h g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      ring
    _ = 0 := by simp only [GP029T10_centered_fiber p v hp group, zero_mul,
      Finset.sum_const_zero]

/-- The mean of an occupied constant fiber is that constant. -/
private lemma GP029T10_mean_of_constant {L G : Type*} [Fintype L]
    (p v : L → ℝ) (hp : ∀ i, 0 < p i) (group : L → G) (i : L)
    (hv : ∀ j, group j = group i → v j = v i) :
    fGroupMean p v group (group i) = v i := by
  classical
  have hm := GP029T10_event_pos p hp (fun j => group j = group i) ⟨i, rfl⟩
  have hc := GP029T10_mass_mul_ce p v hp (fun j => group j = group i)
  have hn : fE p (fun j => if group j = group i then v j else 0) =
      fP p (fun j => group j = group i) * v i := by
    unfold fE fP
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : group j = group i
    · simp only [if_pos hj, hv j hj]
    · simp only [if_neg hj, mul_zero, zero_mul]
  apply mul_left_cancel₀ (ne_of_gt hm)
  exact hc.trans hn

theorem grouped_covariance_decomposition_proof {n : ℕ} {G : Type*} [Fintype G]
    (s A : Fin (n+1) → ℝ) (group : Fin (n+1) → G) :
    let p : Fin (n+1) → ℝ := fun _ => 1/(n+1)
    fCov p s A =
      fE p (fun i => (s i - fGroupMean p s group (group i)) *
        (A i - fGroupMean p A group (group i))) +
      fE p (fun i => (fGroupMean p s group (group i) - fE p s) *
        (fGroupMean p A group (group i) - fE p A)) ∧
    (∀ g, (∀ i, group i ≠ g → ∀ j, group j = group i → A j = A i) →
      fE p (fun i => (s i - fGroupMean p s group (group i)) *
        (A i - fGroupMean p A group (group i))) =
      ((Finset.univ.filter (fun i => group i = g)).card : ℝ)/(n+1) *
        fCE p (fun i => (s i - fGroupMean p s group g) *
          (A i - fGroupMean p A group g)) (fun i => group i = g)) := by
  classical
  dsimp only
  let p : Fin (n+1) → ℝ := fun _ => 1/(n+1)
  change fCov p s A = _ ∧ _
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hp : ∀ i, 0 < p i := by intro i; exact div_pos zero_lt_one hN
  have hnorm : (∑ i, p i) = 1 := by
    simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hN]
  let ms : G → ℝ := fGroupMean p s group
  let mA : G → ℝ := fGroupMean p A group
  let es : ℝ := fE p s
  let eA : ℝ := fE p A
  have hcross1 : fE p (fun i => (s i - ms (group i)) * (mA (group i) - eA)) = 0 :=
    GP029T10_orthogonal p s hp group (fun g => mA g - eA)
  have hcross2 : fE p (fun i => (A i - mA (group i)) * (ms (group i) - es)) = 0 :=
    GP029T10_orthogonal p A hp group (fun g => ms g - es)
  have hcov : fE p (fun i => (s i - es) * (A i - eA)) = fCov p s A := by
    calc
      _ = ∑ i, (p i * (s i * A i) - (p i * s i) * eA -
          (p i * A i) * es + p i * (es * eA)) := by
        unfold fE
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i * (s i * A i)) - (∑ i, p i * s i) * eA -
          (∑ i, p i * A i) * es + (∑ i, p i) * (es * eA) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = fCov p s A := by
        rw [hnorm]
        dsimp [es, eA, fCov, fE]
        ring
  have hexpand : fE p (fun i => (s i - es) * (A i - eA)) =
      fE p (fun i => (s i - ms (group i)) * (A i - mA (group i))) +
      fE p (fun i => (ms (group i) - es) * (mA (group i) - eA)) +
      fE p (fun i => (s i - ms (group i)) * (mA (group i) - eA)) +
      fE p (fun i => (A i - mA (group i)) * (ms (group i) - es)) := by
    unfold fE
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · rw [hcov, hcross1, hcross2, add_zero, add_zero] at hexpand
    exact hexpand
  · intro g hg
    have hout : ∀ i, group i ≠ g → A i - mA (group i) = 0 := by
      intro i hi
      have hm := GP029T10_mean_of_constant p A hp group i (hg i hi)
      exact sub_eq_zero.mpr hm.symm
    have hrestrict :
        fE p (fun i => (s i - ms (group i)) * (A i - mA (group i))) =
        fE p (fun i => if group i = g then (s i - ms g) * (A i - mA g) else 0) := by
      unfold fE
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : group i = g
      · beta_reduce
        rw [if_pos hi, hi]
      · simp only [if_neg hi, hout i hi, mul_zero]
    have hmass : fP p (fun i => group i = g) =
        ((Finset.univ.filter (fun i => group i = g)).card : ℝ) / (n+1) := by
      unfold fP
      rw [← Finset.sum_filter]
      simp only [p, Finset.sum_const, nsmul_eq_mul]
      ring
    calc
      _ = fE p (fun i => if group i = g then (s i - ms g) * (A i - mA g) else 0) :=
        hrestrict
      _ = fP p (fun i => group i = g) *
          fCE p (fun i => (s i - ms g) * (A i - mA g)) (fun i => group i = g) :=
        (GP029T10_mass_mul_ce p _ hp _).symm
      _ = _ := by rw [hmass]

/-! ## Marginal binomial moments and the zero-control case -/

private lemma GP029T14One_mass_nonneg (n : ℕ) (p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (k : Fin (n+1)) :
    0 ≤ binomialMass n p k := by
  unfold binomialMass
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

private lemma GP029T14One_mass_sum (n : ℕ) (p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    (∑ k : Fin (n+1), binomialMass n p k) = 1 := by
  simpa only [bernstein_apply, binomialMass] using
    bernstein.probability n ⟨p, hp⟩

/-- Evaluate the polynomial first-moment identity before dividing by the arm size.
No division by `p` or `1-p` is used, so both boundary probabilities are included. -/
private lemma GP029T14One_count_mean (n : ℕ) (p : ℝ) :
    (∑ k : Fin (n+1), (k.val : ℝ) * binomialMass n p k) = (n : ℝ) * p := by
  have h := congrArg (fun P : Polynomial ℝ => Polynomial.eval p P)
    (bernsteinPolynomial.sum_smul ℝ n)
  simp only [nsmul_eq_mul, bernsteinPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one] at h
  simpa only [Finset.sum_range, binomialMass] using h

private lemma GP029T14One_rate_mean (n : ℕ) (hn : 0 < n) (p : ℝ) :
    (∑ k : Fin (n+1), binomialMass n p k * ((k.val : ℝ) / n)) = p := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    _ = (∑ k : Fin (n+1), (k.val : ℝ) * binomialMass n p k) / n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = p := by rw [GP029T14One_count_mean]; field_simp [hnr]

/-- The second binomial moment. -/
private lemma GP029T14One_rate_variance (n : ℕ) (hn : 0 < n) (p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    (∑ k : Fin (n+1), binomialMass n p k * (((k.val : ℝ) / n) - p)^2) =
      p * (1-p) / n := by
  have hv := bernstein.variance (Nat.ne_of_gt hn) ⟨p, hp⟩
  simp only [bernstein.z, bernstein_apply] at hv
  calc
    _ = ∑ k : Fin (n+1), (p - (k.val : ℝ) / n)^2 * binomialMass n p k := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := hv

private lemma GP029T14One_zero_mass (n : ℕ) (k : Fin (n+1)) :
    binomialMass n 0 k = if k.val = 0 then 1 else 0 := by
  by_cases hk : k.val = 0
  · simp [binomialMass, hk]
  · simp [binomialMass, hk, zero_pow hk]

private lemma GP029T14One_zero_mass_fin (n : ℕ) (k : Fin (n+1)) :
    binomialMass n 0 k = if k = 0 then 1 else 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [GP029T14One_zero_mass]
  · have hv : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp only [GP029T14One_zero_mass, if_neg hk, if_neg hv]

private lemma GP029T14One_collapse (n1 n0 : ℕ) (p1 : ℝ)
    (F : Fin (n1+1) × Fin (n0+1) → ℝ) :
    fE (binomialArmLaw n1 n0 p1 0) F =
      ∑ k : Fin (n1+1), binomialMass n1 p1 k * F (k, 0) := by
  classical
  unfold fE binomialArmLaw
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp only [GP029T14One_zero_mass_fin]
  simp [mul_ite, ite_mul]

theorem one_sided_saturated_unbiasedness_proof (n1 n0 : ℕ) (hn1 : 0 < n1) (hn0 : 0 < n0)
    (p1 : ℝ) (hp1 : p1 ∈ Icc (0 : ℝ) 1) :
    fP (binomialArmLaw n1 n0 p1 0) (fun k => k.2.val = 0) = 1 ∧
    (∀ k : Fin (n1+1) × Fin (n0+1), k.2.val = 0 →
      armRateScore n1 n0 k = (k.1.val : ℝ)/n1) ∧
    fE (binomialArmLaw n1 n0 p1 0) (armRateScore n1 n0) = p1 := by
  classical
  have hscore : ∀ k : Fin (n1+1) × Fin (n0+1), k.2.val = 0 →
      armRateScore n1 n0 k = (k.1.val : ℝ)/n1 := by
    intro k hk
    unfold armRateScore positiveScore
    simp only [hk, Nat.cast_zero, zero_div, sub_zero]
    exact max_eq_left (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hprob : fP (binomialArmLaw n1 n0 p1 0) (fun k => k.2.val = 0) =
      fE (binomialArmLaw n1 n0 p1 0) (fun _ => 1) := by
    unfold fP fE
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.2.val = 0
    · simp only [if_pos hk, mul_one]
    · have hz : binomialMass n0 0 k.2 = 0 := by
        rw [GP029T14One_zero_mass, if_neg hk]
      simp only [if_neg hk, binomialArmLaw, hz, mul_zero, zero_mul]
  refine ⟨?_, hscore, ?_⟩
  · rw [hprob, GP029T14One_collapse]
    simpa only [mul_one] using GP029T14One_mass_sum n1 p1 hp1
  · rw [GP029T14One_collapse]
    have hs0 : ∀ k : Fin (n1+1), armRateScore n1 n0 (k, 0) = (k.val : ℝ)/n1 :=
      fun k => hscore (k, 0) rfl
    simp only [hs0]
    exact GP029T14One_rate_mean n1 hn1 p1

/-! ## Product moments, strict bias, and a finite square-tail bound -/

private lemma GP029T14Bias_E_add {L : Type*} [Fintype L] (p u v : L → ℝ) :
    fE p (fun i => u i + v i) = fE p u + fE p v := by
  simp only [fE, mul_add, Finset.sum_add_distrib]

private lemma GP029T14Bias_E_sub {L : Type*} [Fintype L] (p u v : L → ℝ) :
    fE p (fun i => u i - v i) = fE p u - fE p v := by
  simp only [fE, mul_sub, Finset.sum_sub_distrib]

private lemma GP029T14Bias_E_scale {L : Type*} [Fintype L]
    (p u : L → ℝ) (a : ℝ) :
    fE p (fun i => a * u i) = a * fE p u := by
  unfold fE
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma GP029T14Bias_product_E {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (q : J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    fE (fun k : I × J => p k.1 * q k.2) (fun k => u k.1 * v k.2) =
      fE p u * fE q v := by
  unfold fE
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma GP029T14Bias_centered_mean (n : ℕ) (hn : 0 < n) (p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    fE (binomialMass n p) (fun k => (k.val : ℝ)/n - p) = 0 := by
  calc
    _ = (∑ k : Fin (n+1), binomialMass n p k * ((k.val : ℝ)/n)) -
        (∑ k : Fin (n+1), binomialMass n p k) * p := by
      simp only [fE, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = 0 := by
      rw [GP029T14One_rate_mean n hn p, GP029T14One_mass_sum n p hp]
      ring

/-- Independence is used only through factorization of these explicit finite sums. -/
private lemma GP029T14Bias_product_moments (n1 n0 : ℕ)
    (hn1 : 0 < n1) (hn0 : 0 < n0) (p1 p0 : ℝ)
    (hp1 : p1 ∈ Icc (0 : ℝ) 1) (hp0 : p0 ∈ Icc (0 : ℝ) 1) :
    ValidLaw (binomialArmLaw n1 n0 p1 p0) ∧
    fE (binomialArmLaw n1 n0 p1 p0)
      (fun k => (k.1.val : ℝ)/n1 - (k.2.val : ℝ)/n0) = p1-p0 ∧
    fE (binomialArmLaw n1 n0 p1 p0)
      (fun k => (((k.1.val : ℝ)/n1 - (k.2.val : ℝ)/n0) - (p1-p0))^2) =
      p1*(1-p1)/n1 + p0*(1-p0)/n0 := by
  let w1 := binomialMass n1 p1
  let w0 := binomialMass n0 p0
  let q := binomialArmLaw n1 n0 p1 p0
  let r1 : Fin (n1+1) → ℝ := fun k => (k.val : ℝ)/n1
  let r0 : Fin (n0+1) → ℝ := fun k => (k.val : ℝ)/n0
  let u1 : Fin (n1+1) → ℝ := fun k => r1 k - p1
  let u0 : Fin (n0+1) → ℝ := fun k => r0 k - p0
  have hnorm1 : fE w1 (fun _ => 1) = 1 := by
    simpa only [fE, mul_one] using GP029T14One_mass_sum n1 p1 hp1
  have hnorm0 : fE w0 (fun _ => 1) = 1 := by
    simpa only [fE, mul_one] using GP029T14One_mass_sum n0 p0 hp0
  have hmean1 : fE w1 r1 = p1 := GP029T14One_rate_mean n1 hn1 p1
  have hmean0 : fE w0 r0 = p0 := GP029T14One_rate_mean n0 hn0 p0
  have hcenter1 : fE w1 u1 = 0 := GP029T14Bias_centered_mean n1 hn1 p1 hp1
  have hcenter0 : fE w0 u0 = 0 := GP029T14Bias_centered_mean n0 hn0 p0 hp0
  have hvar1 : fE w1 (fun k => (u1 k)^2) = p1*(1-p1)/n1 :=
    GP029T14One_rate_variance n1 hn1 p1 hp1
  have hvar0 : fE w0 (fun k => (u0 k)^2) = p0*(1-p0)/n0 :=
    GP029T14One_rate_variance n0 hn0 p0 hp0
  have hprod (f : Fin (n1+1) → ℝ) (g : Fin (n0+1) → ℝ) :
      fE q (fun k => f k.1 * g k.2) = fE w1 f * fE w0 g :=
    GP029T14Bias_product_E w1 w0 f g
  have hnorm : (∑ k, q k) = 1 := by
    have h := hprod (fun _ => 1) (fun _ => 1)
    rw [hnorm1, hnorm0] at h
    simpa only [fE, one_mul, mul_one] using h
  have hleft : fE q (fun k => r1 k.1) = p1 := by
    simpa only [mul_one, hmean1, hnorm0] using hprod r1 (fun _ => 1)
  have hright : fE q (fun k => r0 k.2) = p0 := by
    simpa only [one_mul, hnorm1, hmean0] using hprod (fun _ => 1) r0
  have hleftVar : fE q (fun k => (u1 k.1)^2) = p1*(1-p1)/n1 := by
    have h := hprod (fun k => (u1 k)^2) (fun _ => 1)
    rw [hvar1, hnorm0, mul_one] at h
    simpa only [mul_one] using h
  have hrightVar : fE q (fun k => (u0 k.2)^2) = p0*(1-p0)/n0 := by
    have h := hprod (fun _ => 1) (fun k => (u0 k)^2)
    rw [hvar0, hnorm1, one_mul] at h
    simpa only [one_mul] using h
  have hmixed : fE q (fun k => u1 k.1 * u0 k.2) = 0 := by
    simpa only [hcenter1, hcenter0, mul_zero] using hprod u1 u0
  refine ⟨⟨?_, hnorm⟩, ?_, ?_⟩
  · intro k
    exact mul_nonneg (GP029T14One_mass_nonneg n1 p1 hp1 k.1)
      (GP029T14One_mass_nonneg n0 p0 hp0 k.2)
  · change fE q (fun k => r1 k.1 - r0 k.2) = p1-p0
    rw [GP029T14Bias_E_sub, hleft, hright]
  · change fE q (fun k => ((r1 k.1 - r0 k.2) - (p1-p0))^2) = _
    calc
      _ = fE q (fun k => (u1 k.1)^2 + (u0 k.2)^2 - 2 * (u1 k.1 * u0 k.2)) := by
        apply congrArg (fE q)
        funext k
        dsimp only [u1, u0]
        ring
      _ = _ := by
        rw [GP029T14Bias_E_sub, GP029T14Bias_E_add, GP029T14Bias_E_scale,
          hleftVar, hrightVar, hmixed]
        ring

/-- Direct finite-sum Chebyshev. Normalization is not required. -/
private lemma GP029T14Bias_square_tail {L : Type*} [Fintype L]
    (p T S : L → ℝ) (c δ : ℝ) (hp : ∀ i, 0 ≤ p i) (hδ : 0 < δ)
    (hcontract : ∀ i, |S i - c| ≤ |T i - c|) :
    fP p (fun i => δ < |S i - c|) ≤ fE p (fun i => (T i - c)^2) / δ^2 := by
  classical
  have hsum : δ^2 * fP p (fun i => δ < |S i - c|) ≤
      fE p (fun i => (T i - c)^2) := by
    unfold fP fE
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : δ < |S i - c|
    · rw [if_pos hi]
      have hlt : δ < |T i - c| := lt_of_lt_of_le hi (hcontract i)
      have hprod := mul_nonneg (le_of_lt (sub_pos.mpr hlt))
        (add_nonneg (abs_nonneg (T i - c)) hδ.le)
      have hsquare : δ^2 ≤ (T i - c)^2 := by
        nlinarith only [hprod, sq_abs (T i - c)]
      calc
        δ^2 * p i = p i * δ^2 := mul_comm _ _
        _ ≤ p i * (T i - c)^2 := mul_le_mul_of_nonneg_left hsquare (hp i)
    · rw [if_neg hi, mul_zero]
      exact mul_nonneg (hp i) (sq_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  nlinarith only [hsum]

theorem saturated_binomial_bias_bound_proof (n1 n0 : ℕ) (hn1 : 0 < n1) (hn0 : 0 < n0)
    (p1 p0 : ℝ) (hp0 : 0 ≤ p0) (horder : p0 ≤ p1) (hp1 : p1 ≤ 1) :
    fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0) =
      fE (binomialArmLaw n1 n0 p1 p0)
        (fun k => positiveScore ((k.2.val : ℝ)/n0) ((k.1.val : ℝ)/n1)) ∧
    0 ≤ fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0) ∧
    (0 < p0 → p1 < 1 → 0 < fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0)) ∧
    (∀ δ : ℝ, 0 < δ →
      fP (binomialArmLaw n1 n0 p1 p0) (fun k => δ < |armRateScore n1 n0 k - (p1-p0)|) ≤
        (p1*(1-p1)/n1 + p0*(1-p0)/n0) / δ^2) := by
  classical
  have hp1I : p1 ∈ Icc (0 : ℝ) 1 := ⟨le_trans hp0 horder, hp1⟩
  have hp0I : p0 ∈ Icc (0 : ℝ) 1 := ⟨hp0, le_trans horder hp1⟩
  let q := binomialArmLaw n1 n0 p1 p0
  let T : Fin (n1+1) × Fin (n0+1) → ℝ :=
    fun k => (k.1.val : ℝ)/n1 - (k.2.val : ℝ)/n0
  let R : Fin (n1+1) × Fin (n0+1) → ℝ :=
    fun k => positiveScore ((k.2.val : ℝ)/n0) ((k.1.val : ℝ)/n1)
  let S := armRateScore n1 n0
  let c := p1-p0
  let V := p1*(1-p1)/n1 + p0*(1-p0)/n0
  change fE q S - c = fE q R ∧ 0 ≤ fE q S - c ∧
    (0 < p0 → p1 < 1 → 0 < fE q S - c) ∧
    (∀ δ : ℝ, 0 < δ → fP q (fun k => δ < |S k - c|) ≤ V / δ^2)
  obtain ⟨hvalid, hmean, hvariance⟩ :=
    GP029T14Bias_product_moments n1 n0 hn1 hn0 p1 p0 hp1I hp0I
  change ValidLaw q at hvalid
  change fE q T = c at hmean
  change fE q (fun k => (T k - c)^2) = V at hvariance
  have hscore : (fun k => max (T k) 0) = S := rfl
  have hreverse : (fun k => max (-T k) 0) = R := by
    funext k
    dsimp only [T, R, positiveScore]
    rw [neg_sub]
  have hb := positive_part_bias_identity q T hvalid.1
  rw [hscore, hmean, hreverse] at hb
  refine ⟨hb.1, ?_, ?_, ?_⟩
  · rw [hb.1]
    exact hb.2
  · intro hp0pos hp1lt
    let kstar : Fin (n1+1) × Fin (n0+1) := (0, Fin.last n0)
    have hn0r : (n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
    have hRstar : R kstar = 1 := by
      simp [R, kstar, positiveScore, hn0r]
    have hqstar : q kstar = (1-p1)^n1 * p0^n0 := by
      simp [q, kstar, binomialArmLaw, binomialMass]
    have hstrict : 0 < fE q R := by
      unfold fE
      apply Finset.sum_pos'
      · intro k _
        exact mul_nonneg (hvalid.1 k) (le_max_right _ _)
      · refine ⟨kstar, Finset.mem_univ _, ?_⟩
        rw [hRstar, mul_one, hqstar]
        exact mul_pos (pow_pos (sub_pos.mpr hp1lt) _) (pow_pos hp0pos _)
    rw [hb.1]
    exact hstrict
  · intro δ hδ
    have hcontract : ∀ k, |S k - c| ≤ |T k - c| := by
      intro k
      change |max (T k) 0 - c| ≤ |T k - c|
      exact positive_part_error_bound (T k) c (sub_nonneg.mpr horder)
    have ht := GP029T14Bias_square_tail q T S c δ hvalid.1 hδ hcontract
    rw [hvariance] at ht
    exact ht

end

end AronowAudit.P029.Wave1

