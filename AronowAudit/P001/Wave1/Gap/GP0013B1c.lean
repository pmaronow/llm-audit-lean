import AronowAudit.P001.Wave1.Gap.GP0013B1b
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Uniform polynomial Gram bounds, obtained directly from orthogonality.
The differential operator ((X-X²)p')' is symmetric on the unit interval.
Its leading term and lower-degree orthogonality imply the Legendre equation.
The energy k(k+1)p²+(x-x²)(p')² decreases up to 1/2 and increases thereafter;
integration by parts gives both endpoint squares as 2k+1. This proves the
sharp row bound without an additional analytic Legendre hypothesis.
-/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance GP0013B1c_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

private def GP0013B1c_D (p : Polynomial ℝ) : Polynomial ℝ :=
  ((Polynomial.X - Polynomial.X * Polynomial.X) * p.derivative).derivative

private lemma GP0013B1c_D_coeff (p : Polynomial ℝ) (n : ℕ) :
    (GP0013B1c_D p).coeff n =
      ((n : ℝ)+1)^2 * p.coeff (n+1) - (n : ℝ)*((n : ℝ)+1)*p.coeff n := by
  have he : GP0013B1c_D p =
      (Polynomial.X*p.derivative).derivative -
      (Polynomial.X*(Polynomial.X*p.derivative)).derivative := by
    simp only [GP0013B1c_D, sub_mul, Polynomial.derivative_sub, mul_assoc]
  rw [he, Polynomial.coeff_sub, Polynomial.coeff_derivative,
    Polynomial.coeff_derivative, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]
  cases n with
  | zero => simp [Polynomial.coeff_derivative]
  | succ n =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    push_cast
    ring

private lemma GP0013B1c_D_degree (p : Polynomial ℝ) (k : ℕ)
    (hp : p.degree < k) : (GP0013B1c_D p).degree < k := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  rw [GP0013B1c_D_coeff,
    (Polynomial.degree_lt_iff_coeff_zero _ _).mp hp (n+1) (by omega),
    (Polynomial.degree_lt_iff_coeff_zero _ _).mp hp n hn]
  ring

private lemma GP0013B1c_eigen_degree (p : Polynomial ℝ) (k : ℕ)
    (hp : p.natDegree = k) :
    (GP0013B1c_D p + Polynomial.C ((k : ℝ)*((k : ℝ)+1))*p).degree < k := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, GP0013B1c_D_coeff]
  have hc : p.coeff (n+1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hc]
  by_cases hnk : n=k
  · subst n; ring
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < n by omega)]
    ring

private lemma GP0013B1c_lower_deriv (p : Polynomial ℝ) (k : ℕ)
    (hp : p.natDegree = k) : p.derivative.degree < k := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  rw [Polynomial.coeff_derivative,
    Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < n+1 by omega)]
  simp

private lemma GP0013B1c_lower_xderiv (p : Polynomial ℝ) (k : ℕ)
    (hp : p.natDegree = k) :
    (Polynomial.X*p.derivative - Polynomial.C (k : ℝ)*p).degree < (k : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  cases n with
  | zero =>
    have hk : k=0 := by omega
    simp [hk]
  | succ n =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
      Polynomial.coeff_C_mul]
    by_cases hnk : n+1=k
    · rw [← hnk]; norm_num; ring
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < n+1 by omega)]
      ring

private def GP0013B1c_I (p : Polynomial ℝ) : ℝ := ∫ x in (0 : ℝ)..1, p.eval x

private lemma GP0013B1c_I_add (p q : Polynomial ℝ) :
    GP0013B1c_I (p+q) = GP0013B1c_I p + GP0013B1c_I q := by
  simp only [GP0013B1c_I, Polynomial.eval_add]
  exact intervalIntegral.integral_add (p.continuous.intervalIntegrable 0 1) (q.continuous.intervalIntegrable 0 1)

private lemma GP0013B1c_I_sub (p q : Polynomial ℝ) :
    GP0013B1c_I (p-q) = GP0013B1c_I p - GP0013B1c_I q := by
  simp only [GP0013B1c_I, Polynomial.eval_sub]
  exact intervalIntegral.integral_sub (p.continuous.intervalIntegrable 0 1) (q.continuous.intervalIntegrable 0 1)

private lemma GP0013B1c_I_C_mul (c : ℝ) (p : Polynomial ℝ) :
    GP0013B1c_I (Polynomial.C c*p) = c*GP0013B1c_I p := by
  simp only [GP0013B1c_I, Polynomial.eval_mul, Polynomial.eval_C,
    intervalIntegral.integral_const_mul]

private lemma GP0013B1c_I_derivative (p : Polynomial ℝ) :
    GP0013B1c_I p.derivative = p.eval 1 - p.eval 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt x) (p.derivative.continuous.intervalIntegrable 0 1)

private lemma GP0013B1c_D_symm (p q : Polynomial ℝ) :
    GP0013B1c_I (p * GP0013B1c_D q) = GP0013B1c_I (q * GP0013B1c_D p) := by
  let w : Polynomial ℝ := Polynomial.X-Polynomial.X*Polynomial.X
  have h (p q : Polynomial ℝ) :
      GP0013B1c_I (p*GP0013B1c_D q) = -GP0013B1c_I (p.derivative*(w*q.derivative)) := by
    have hi := GP0013B1c_I_derivative (p*(w*q.derivative))
    rw [Polynomial.derivative_mul, GP0013B1c_I_add] at hi
    have hboundary : (p*(w*q.derivative)).eval 1 - (p*(w*q.derivative)).eval 0 = 0 := by
      simp [w]
    rw [hboundary] at hi
    change GP0013B1c_I (p.derivative*(w*q.derivative)) +
      GP0013B1c_I (p*GP0013B1c_D q) = 0 at hi
    linarith
  rw [h p q, h q p]
  congr 1
  congr 1
  ring

private lemma GP0013B1c_I_sq_zero (p : Polynomial ℝ)
    (hp : GP0013B1c_I (p*p)=0) : ∀ x ∈ Set.Icc (0 : ℝ) 1, p.eval x = 0 := by
  have hi : (∫ x in Set.Icc (0 : ℝ) 1, (p.eval x)^2)=0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    simpa only [GP0013B1c_I, Polynomial.eval_mul, pow_two] using hp
  have hae : (fun x => (p.eval x)^2) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (p.continuous.pow 2).continuousOn.integrableOn_Icc).mp hi
  have he := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ)≠1) hae
    (p.continuous.pow 2).continuousOn continuousOn_const
  intro x hx
  exact sq_eq_zero_iff.mp (he hx)

/-- Orthogonality alone gives the Legendre differential equation on the unit interval. -/
private lemma GP0013B1c_eigen (p : Polynomial ℝ) (k : ℕ)
    (hp : p.natDegree = k)
    (ho : ∀ q : Polynomial ℝ, q.degree < k → GP0013B1c_I (p*q)=0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (GP0013B1c_D p).eval x + ((k : ℝ)*((k : ℝ)+1))*p.eval x = 0 := by
  let q := GP0013B1c_D p + Polynomial.C ((k : ℝ)*((k : ℝ)+1))*p
  have hq : q.degree < k := GP0013B1c_eigen_degree p k hp
  have hzero : GP0013B1c_I (q*q)=0 := by
    have hsym := GP0013B1c_D_symm q p
    have hqp : GP0013B1c_I (q*p)=0 := by
      rw [mul_comm]; exact ho q hq
    have halg : q*q = q*GP0013B1c_D p +
        Polynomial.C ((k : ℝ)*((k : ℝ)+1))*(q*p) := by dsimp [q]; ring
    rw [halg, GP0013B1c_I_add, GP0013B1c_I_C_mul, hqp, mul_zero, add_zero,
      hsym, ho _ (GP0013B1c_D_degree q k hq)]
  simpa only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    GP0013B1c_I_sq_zero q hzero

private lemma GP0013B1c_endpoints (p : Polynomial ℝ) (k : ℕ)
    (hp : p.natDegree = k) (hn : GP0013B1c_I (p*p)=1)
    (ho : ∀ q : Polynomial ℝ, q.degree < k → GP0013B1c_I (p*q)=0) :
    (p.eval 0)^2 = 2*(k : ℝ)+1 ∧ (p.eval 1)^2 = 2*(k : ℝ)+1 := by
  have hx := ho _ (GP0013B1c_lower_xderiv p k hp)
  have he : p*(Polynomial.X*p.derivative-Polynomial.C (k : ℝ)*p) =
      p*(Polynomial.X*p.derivative) - Polynomial.C (k : ℝ)*(p*p) := by ring
  rw [he, GP0013B1c_I_sub, GP0013B1c_I_C_mul, hn, mul_one] at hx
  have hx' : GP0013B1c_I (p*(Polynomial.X*p.derivative)) = k := by linarith
  have hd := GP0013B1c_I_derivative (Polynomial.X*(p*p))
  have halg : (Polynomial.X*(p*p)).derivative =
      p*p + Polynomial.C 2*(p*(Polynomial.X*p.derivative)) := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X]
    rw [Polynomial.C_ofNat]
    ring
  rw [halg, GP0013B1c_I_add, GP0013B1c_I_C_mul, hn, hx'] at hd
  have hb : (p.eval 1)^2 = 2*(k : ℝ)+1 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at hd
    nlinarith [hd]
  have hz := ho _ (GP0013B1c_lower_deriv p k hp)
  have hd0 := GP0013B1c_I_derivative (p*p)
  have halg0 : (p*p).derivative = Polynomial.C 2*(p*p.derivative) := by
    rw [Polynomial.derivative_mul, Polynomial.C_ofNat]; ring
  rw [halg0, GP0013B1c_I_C_mul, hz] at hd0
  simp only [mul_zero, Polynomial.eval_mul] at hd0
  exact ⟨by nlinarith [hb,hd0],hb⟩

/-- The sharp squared evaluation bound, derived without a Legendre input. -/
private lemma GP0013B1c_eval_sq (p : Polynomial ℝ) (k : ℕ)
    (hp : p.natDegree = k) (hn : GP0013B1c_I (p*p)=1)
    (ho : ∀ q : Polynomial ℝ, q.degree < k → GP0013B1c_I (p*q)=0)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (p.eval x)^2 ≤ 2*(k : ℝ)+1 := by
  have hb := GP0013B1c_endpoints p k hp hn ho
  by_cases hk : k=0
  · have hc := Polynomial.eq_C_of_natDegree_eq_zero (hp.trans hk)
    have heval : p.eval x = p.eval 0 := by rw [hc]; simp only [Polynomial.eval_C]
    rw [heval]
    exact hb.1.le
  have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  let l : ℝ := (k : ℝ)*((k : ℝ)+1)
  have hl : 0 < l := mul_pos hkR (by linarith)
  let E : Polynomial ℝ := Polynomial.C l*(p*p) +
    (Polynomial.X-Polynomial.X*Polynomial.X)*(p.derivative*p.derivative)
  have hE (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      E.derivative.eval t = (2*t-1)*(p.derivative.eval t)^2 := by
    have ho' := GP0013B1c_eigen p k hp ho t ht
    have hode : l*p.eval t + (1-2*t)*p.derivative.eval t +
        (t-t*t)*p.derivative.derivative.eval t = 0 := by
      dsimp [GP0013B1c_D] at ho'
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_X] at ho'
      dsimp [l]
      nlinarith [ho']
    dsimp [E]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_X]
    linear_combination 2 * p.derivative.eval t * hode
  have hanti : AntitoneOn E.eval (Set.Icc (0 : ℝ) (1/2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) E.continuous.continuousOn
      E.differentiable.differentiableOn
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      have ht0 := interior_subset ht
      constructor <;> linarith [ht0.1,ht0.2]
    rw [E.deriv, hE t ht']
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have ht0 := interior_subset ht
    linarith [ht0.2]
  have hmono : MonotoneOn E.eval (Set.Icc (1/2 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) E.continuous.continuousOn
      E.differentiable.differentiableOn
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      have ht0 := interior_subset ht
      constructor <;> linarith [ht0.1,ht0.2]
    rw [E.deriv, hE t ht']
    apply mul_nonneg _ (sq_nonneg _)
    have ht0 := interior_subset ht
    linarith [ht0.1]
  have hb0 : p.eval 0*p.eval 0 = 2*(k : ℝ)+1 := by nlinarith [hb.1]
  have hb1 : p.eval 1*p.eval 1 = 2*(k : ℝ)+1 := by nlinarith [hb.2]
  have hbound : E.eval x ≤ l*(2*(k : ℝ)+1) := by
    by_cases hmid : x ≤ 1/2
    · have h := hanti (show (0 : ℝ) ∈ Set.Icc 0 (1/2) by norm_num)
        ⟨hx.1,hmid⟩ hx.1
      simpa only [E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X, zero_mul, sub_self, mul_zero, add_zero,
        hb0] using h
    · have h := hmono (show x ∈ Set.Icc (1/2 : ℝ) 1 from ⟨(not_le.mp hmid).le,hx.2⟩)
        (show (1 : ℝ) ∈ Set.Icc (1/2) 1 by norm_num) hx.2
      simpa only [E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X, one_mul, sub_self, zero_mul, add_zero,
        hb1] using h
  have hw : 0 ≤ (x-x*x)*(p.derivative.eval x)^2 := by
    apply mul_nonneg _ (sq_nonneg _)
    nlinarith [hx.1,hx.2]
  have heval : E.eval x = l*(p.eval x)^2 + (x-x*x)*(p.derivative.eval x)^2 := by
    simp [E,pow_two]
  rw [heval] at hbound
  exact (mul_le_mul_iff_right₀ hl).mp (by nlinarith [hbound,hw])

private def GP0013B1c_inner (p : Polynomial ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun q := GP0013B1c_I (p*q)
  map_add' q r := by rw [mul_add, GP0013B1c_I_add]
  map_smul' c q := by
    change GP0013B1c_I (p*(c • q)) = c*GP0013B1c_I (p*q)
    rw [Polynomial.smul_eq_C_mul]
    have he : p*(Polynomial.C c*q) = Polynomial.C c*(p*q) := by ring
    rw [he,GP0013B1c_I_C_mul]

private lemma GP0013B1c_lower_orthogonal {K : ℕ} (p : Fin K → Polynomial ℝ)
    (hd : ∀ j, (p j).natDegree=j.val)
    (ho : ∀ j k, GP0013B1c_I (p j*p k) = if j=k then 1 else 0)
    (k : Fin K) (q : Polynomial ℝ) (hq : q.degree < (k.val : WithBot ℕ)) :
    GP0013B1c_I (p k*q)=0 := by
  have hne (j : Fin K) : p j ≠ 0 := by
    intro hj
    have h := ho j j
    simp [hj, GP0013B1c_I] at h
  let S : Polynomial.Sequence ℝ := ⟨fun i => if hi : i<K then p ⟨i,hi⟩ else Polynomial.X^i,
    fun i => by
      split_ifs with hi
      · rw [Polynomial.degree_eq_natDegree (hne ⟨i,hi⟩),hd]
      · simp⟩
  have hspan := S.span_degreeLT (m := k.val) (fun i _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (S.ne_zero i)))
  have hle : Submodule.span ℝ (S '' Set.Iio k.val) ≤ (GP0013B1c_inner (p k)).ker := by
    apply Submodule.span_le.mpr
    rintro r ⟨j,hj,rfl⟩
    change GP0013B1c_I (p k*S j)=0
    have hjK : j<K := lt_trans hj k.isLt
    have he : S j = p ⟨j,hjK⟩ := by simp [S,hjK]
    rw [he,ho]
    apply if_neg
    intro heq
    have heq' := congrArg Fin.val heq
    change k.val=j at heq'
    change j<k.val at hj
    omega
  have hmem : q ∈ Submodule.span ℝ (S '' Set.Iio k.val) := by
    rw [hspan,Polynomial.mem_degreeLT]
    exact hq
  exact hle hmem

private lemma GP0013B1c_odd_sum (K : ℕ) :
    (∑ k : Fin K, (2*(k.val : ℝ)+1)) = (K : ℝ)^2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

private lemma GP0013B1c_row_bound {K : ℕ} (p : Fin K → Polynomial ℝ)
    (hd : ∀ j, (p j).natDegree=j.val)
    (ho : ∀ j k, GP0013B1c_I (p j*p k) = if j=k then 1 else 0)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ k, ((p k).eval x)^2) ≤ (K : ℝ)^2 := by
  calc
    (∑ k, ((p k).eval x)^2) ≤ ∑ k : Fin K, (2*(k.val : ℝ)+1) := by
      apply Finset.sum_le_sum
      intro k _
      exact GP0013B1c_eval_sq (p k) k.val (hd k) (by simpa using ho k k)
        (GP0013B1c_lower_orthogonal p hd ho k) x hx
    _ = (K : ℝ)^2 := GP0013B1c_odd_sum K

private lemma GP0013B1c_unit_inner (p q : Polynomial ℝ) :
    mean (uniformLaw 0 1) (fun x => p.eval x*q.eval x) = GP0013B1c_I (p*q) := by
  rw [mean,uniformLaw_zero_one_eq_restrict,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  simp only [GP0013B1c_I, Polynomial.eval_mul]

private def GP0013B1c_general_gram_frob {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  ∑ j, ∑ k, (G j k - if j = k then 1 else 0)^2

private lemma GP0013B1c_general_gram_frob_nonneg {K : ℕ}
    (G : Matrix (Fin K) (Fin K) ℝ) : 0 ≤ GP0013B1c_general_gram_frob G := by
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))

private lemma GP0013B1c_general_gram_product_bound {K : ℕ} (z : Fin K → ℝ)
    (j k : Fin K) : |z j * z k| ≤ ∑ l, (z l)^2 := by
  have hj : (z j)^2 ≤ ∑ l, (z l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ j)
  have hk : (z k)^2 ≤ ∑ l, (z l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ k)
  rw [abs_mul]
  nlinarith [sq_nonneg (|z j| - |z k|), sq_abs (z j), sq_abs (z k)]

private lemma GP0013B1c_general_gram_quadratic_identity {K : ℕ} {Ω : Type*}
    (p : Fin K → Polynomial ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (v : Fin K → ℝ) :
    (∑ j, ∑ k, v j * sampleGram p X n ω j k * v k) =
      (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ) := by
  classical
  simp only [sampleGram, div_eq_mul_inv]
  calc
    (∑ j, ∑ k, v j * ((∑ i ∈ Finset.range n,
        (p j).eval (X i ω) * (p k).eval (X i ω)) * (n : ℝ)⁻¹) * v k) =
      ∑ j, ∑ k, ∑ i ∈ Finset.range n,
        (v j * (p j).eval (X i ω)) *
          (v k * (p k).eval (X i ω)) * (n : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i ∈ Finset.range n, ∑ j, ∑ k,
        (v j * (p j).eval (X i ω)) *
          (v k * (p k).eval (X i ω)) * (n : ℝ)⁻¹ := by
          calc
            _ = ∑ j, ∑ i ∈ Finset.range n, ∑ k,
                (v j * (p j).eval (X i ω)) *
                  (v k * (p k).eval (X i ω)) * (n : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_comm]
            _ = _ := by rw [Finset.sum_comm]
    _ = (∑ i ∈ Finset.range n,
        (∑ k, v k * (p k).eval (X i ω))^2) * (n : ℝ)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          simp only [← Finset.sum_mul, ← Finset.mul_sum, pow_two]

private lemma GP0013B1c_general_gram_frob_controls_quadratic {K : ℕ}
    (G : Matrix (Fin K) (Fin K) ℝ) (hG : GP0013B1c_general_gram_frob G ≤ 1/4)
    (v : Fin K → ℝ) :
    (1/2 : ℝ) * (∑ k, (v k)^2) ≤ ∑ j, ∑ k, v j * G j k * v k := by
  classical
  let A : Matrix (Fin K) (Fin K) ℝ := fun j k => G j k - if j = k then 1 else 0
  let S : ℝ := ∑ k, (v k)^2
  let D : ℝ := ∑ j, ∑ k, A j k * (v j * v k)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hCS : D^2 ≤ GP0013B1c_general_gram_frob G * S^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin K × Fin K))
      (fun jk => A jk.1 jk.2) (fun jk => v jk.1 * v jk.2)
    have hVV : (∑ j, ∑ k, (v j * v k)^2) = S^2 := by
      simp only [S, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simpa only [Fintype.sum_prod_type, D, GP0013B1c_general_gram_frob, A, hVV] using h
  have hD : -(S/2) ≤ D := by
    have hmult := mul_le_mul_of_nonneg_right hG (sq_nonneg S)
    have hDS : D^2 ≤ S^2/4 := by nlinarith
    have habs : |D| ≤ S/2 := by
      apply (sq_le_sq₀ (abs_nonneg D) (div_nonneg hS (by norm_num : (0 : ℝ) ≤ 2))).mp
      nlinarith [sq_abs D]
    exact (abs_le.mp habs).1
  have hdecomp : (∑ j, ∑ k, v j * G j k * v k) = S + D := by
    have he (j k : Fin K) : v j * G j k * v k =
        (if j = k then v j * v k else 0) + A j k * (v j * v k) := by
      dsimp [A]
      split_ifs <;> ring
    simp_rw [he, Finset.sum_add_distrib]
    simp [S, D, pow_two]
  rw [hdecomp]
  change (1/2 : ℝ) * S ≤ S + D
  linarith

private lemma GP0013B1c_general_gram_frob_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ω => GP0013B1c_general_gram_frob (sampleGram p X n ω)) μ ∧
    (∫ ω, GP0013B1c_general_gram_frob (sampleGram p X n ω) ∂μ) ≤ (ζ * (K : ℝ)-K)/(n : ℝ) := by
  classical
  let Y : Fin K → Fin K → ℕ → Ω → ℝ :=
    fun j k i ω => (p j).eval (X i ω) * (p k).eval (X i ω)
  let S : Ω → ℝ := fun ω => ∑ k, ((p k).eval (X 0 ω))^2
  have hYm (j k : Fin K) (i : ℕ) : Measurable (Y j k i) := by
    exact ((p j).continuous.measurable.comp (hiid.1 i)).mul
      ((p k).continuous.measurable.comp (hiid.1 i))
  have hYiid (j k : Fin K) : IID μ (Y j k) := by
    let f : ℝ → ℝ := fun x => (p j).eval x * (p k).eval x
    have hf : Measurable f := (p j).continuous.measurable.mul (p k).continuous.measurable
    exact ⟨hYm j k, hiid.2.1.comp (fun _ => f) (fun _ => hf),
      fun i => (hiid.2.2 i).comp (u := f) hf⟩
  have hY2 (j k : Fin K) : MemLp (Y j k 0) 2 μ := by
    apply (memLp_const ζ).mono' (hYm j k 0).aestronglyMeasurable
    filter_upwards [hrow] with ω hω
    rw [Real.norm_eq_abs]
    exact (GP0013B1c_general_gram_product_bound (fun l => (p l).eval (X 0 ω)) j k).trans hω
  have hYsq (j k : Fin K) : Integrable (fun ω => (Y j k 0 ω)^2) μ :=
    (hY2 j k).integrable_sq
  have hS2 : MemLp S 2 μ := by
    simpa only [S, Y, pow_two] using
      (memLp_finsetSum (Finset.univ : Finset (Fin K)) (fun k _ => hY2 k k))
  have hS1 : Integrable S μ := hS2.integrable one_le_two
  have hES : (∫ ω, S ω ∂μ) = (K : ℝ) := by
    have hd (k : Fin K) : (∫ ω, ((p k).eval (X 0 ω))^2 ∂μ) = 1 := by
      have h := horth k k
      rw [if_pos rfl] at h
      simpa only [mean, pow_two] using h
    dsimp [S]
    rw [integral_finsetSum _ (fun k _ => by
      simpa only [Y, pow_two] using (hY2 k k).integrable one_le_two)]
    simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hESsq : (∫ ω, (S ω)^2 ∂μ) ≤ ζ * (K : ℝ) := by
    calc
      (∫ ω, (S ω)^2 ∂μ) ≤ ∫ ω, ζ * S ω ∂μ := by
        apply integral_mono_ae hS2.integrable_sq (hS1.const_mul ζ)
        filter_upwards [hrow] with ω hω
        have hS0 : 0 ≤ S ω := Finset.sum_nonneg (fun k _ => sq_nonneg _)
        change S ω ≤ ζ at hω
        nlinarith
      _ = ζ * (K : ℝ) := by rw [integral_const_mul, hES]
  have hG2 (j k : Fin K) : MemLp (fun ω => sampleGram p X n ω j k) 2 μ := by
    exact sample_mean_memLp μ (Y j k) (hYiid j k) (hY2 j k) n
  have hcenter (j k : Fin K) : Integrable
      (fun ω => (sampleGram p X n ω j k - if j = k then 1 else 0)^2) μ :=
    ((hG2 j k).sub (memLp_const _)).integrable_sq
  have hcenter_mean (j k : Fin K) :
      (∫ ω, (sampleGram p X n ω j k - if j = k then 1 else 0)^2 ∂μ) =
        var μ (Y j k 0)/(n : ℝ) := by
    have hmom := iid_sample_mean_finite_moments μ (Y j k) (hYiid j k) (hY2 j k) n hn
    have hmean : mean μ (fun ω => sampleGram p X n ω j k) =
        if j = k then 1 else 0 := hmom.1.trans (horth j k)
    rw [← hmean]
    change (∫ ω, (sampleMean (Y j k) n ω - mean μ (sampleMean (Y j k) n))^2 ∂μ) = _
    exact (variance_eq_integral (hG2 j k).aestronglyMeasurable.aemeasurable).symm.trans hmom.2
  have hYvar (j k : Fin K) : var μ (Y j k 0) =
      (∫ ω, (Y j k 0 ω)^2 ∂μ) - if j = k then 1 else 0 := by
    change variance (Y j k 0) μ = _
    rw [variance_eq_sub (hY2 j k)]
    have he : (∫ ω, Y j k 0 ω ∂μ) = if j = k then 1 else 0 := horth j k
    rw [he]
    split_ifs <;> norm_num
  have hFint : Integrable (fun ω => GP0013B1c_general_gram_frob (sampleGram p X n ω)) μ := by
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hcenter j k))
  refine ⟨hFint, ?_⟩
  have hsumY : (∑ j, ∑ k, ∫ ω, (Y j k 0 ω)^2 ∂μ) = ∫ ω, (S ω)^2 ∂μ := by
    calc
      (∑ j, ∑ k, ∫ ω, (Y j k 0 ω)^2 ∂μ) =
          ∫ ω, ∑ j, ∑ k, (Y j k 0 ω)^2 ∂μ := by
        rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hYsq j k))]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum _ (fun k _ => hYsq j k)]
      _ = ∫ ω, (S ω)^2 ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        simp only [Y, S, pow_two, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  calc
    (∫ ω, GP0013B1c_general_gram_frob (sampleGram p X n ω) ∂μ) =
        ∑ j, ∑ k, var μ (Y j k 0)/(n : ℝ) := by
      unfold GP0013B1c_general_gram_frob
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hcenter j k))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun k _ => hcenter j k)]
      simp_rw [hcenter_mean]
    _ = ((∑ j, ∑ k, ∫ ω, (Y j k 0 ω)^2 ∂μ) - (K : ℝ))/(n : ℝ) := by
      simp_rw [← Finset.sum_div, hYvar, Finset.sum_sub_distrib]
      simp
    _ = ((∫ ω, (S ω)^2 ∂μ) - (K : ℝ))/(n : ℝ) := by
      rw [hsumY]
    _ ≤ (ζ * (K : ℝ)-K)/(n : ℝ) :=
      div_le_div_of_nonneg_right (sub_le_sub_right hESsq _) (Nat.cast_nonneg n)

private lemma GP0013B1c_general_gram_deviation_le_half {K : ℕ} (hK : 0 < K)
    (G : Matrix (Fin K) (Fin K) ℝ) (hG : GP0013B1c_general_gram_frob G ≤ 1/4) :
    gramDeviation G ≤ 1/2 := by
  classical
  let H : Matrix (Fin K) (Fin K) ℝ :=
    fun j k => 2 * (if j = k then 1 else 0) - G j k
  have hHF : GP0013B1c_general_gram_frob H = GP0013B1c_general_gram_frob G := by
    unfold GP0013B1c_general_gram_frob
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [H]
    split_ifs <;> ring
  have hunit (v : Fin K → ℝ) (hv : (∑ k, (v k)^2) = 1) :
      |(∑ j, ∑ k, v j * G j k * v k) - 1| ≤ 1/2 := by
    have hlo := GP0013B1c_general_gram_frob_controls_quadratic G hG v
    have hhi := GP0013B1c_general_gram_frob_controls_quadratic H (by rw [hHF]; exact hG) v
    have hHq : (∑ j, ∑ k, v j * H j k * v k) =
        2 - (∑ j, ∑ k, v j * G j k * v k) := by
      have he (j k : Fin K) : v j * H j k * v k =
          (if j = k then 2 * (v j * v k) else 0) - v j * G j k * v k := by
        dsimp [H]
        split_ifs <;> ring
      simp_rw [he, Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.mul_sum]
      have hv' : (∑ k, v k * v k) = 1 := by simpa only [pow_two] using hv
      rw [hv', mul_one]
    rw [hv] at hlo hhi
    rw [hHq] at hhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold gramDeviation
  apply csSup_le
  · let e : Fin K → ℝ := fun k => if k = ⟨0, hK⟩ then 1 else 0
    refine ⟨|(∑ j, ∑ k, e j * G j k * e k) - 1|, e, ?_, rfl⟩
    simp [e]
  · rintro r ⟨v, hv, rfl⟩
    exact hunit v hv

/-- The sharp fixed-n estimate follows from the same elementary moment calculation. -/
private lemma GP0013B1c_general_gram_finite_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ} (hK : 0 < K)
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤
      4 * (ζ * (K : ℝ)-K)/(n : ℝ) := by
  let F : Ω → ℝ := fun ω => GP0013B1c_general_gram_frob (sampleGram p X n ω)
  have hmom := GP0013B1c_general_gram_frob_moment μ X hiid p horth ζ hrow n hn
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => GP0013B1c_general_gram_frob_nonneg (sampleGram p X n ω)))
    hmom.1 (1/4 : ℝ)
  have hbad : prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤
      4 * (ζ * (K : ℝ)-K)/(n : ℝ) := by
    change (1/4 : ℝ) * prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ ∫ ω, F ω ∂μ at hmarkov
    calc
      prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ 4 * ((ζ * (K : ℝ)-K)/(n : ℝ)) := by
        linarith [hmom.2]
      _ = 4 * (ζ * (K : ℝ)-K)/(n : ℝ) := by ring
  have hsub : {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ⊆
      {ω | (1/4 : ℝ) ≤ F ω} := by
    intro ω hω
    by_contra hnot
    have hsmall : GP0013B1c_general_gram_frob (sampleGram p X n ω) ≤ 1/4 :=
      (lt_of_not_ge hnot).le
    exact (not_lt_of_ge (GP0013B1c_general_gram_deviation_le_half hK _ hsmall)) hω
  have hm : prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤
      prob μ {ω | (1/4 : ℝ) ≤ F ω} := measureReal_mono hsub
  exact hm.trans hbad


private lemma GP0013B1c_unit_support {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (hx : μ.map X = uniformLaw 0 1) : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_of_ae_map hX.aemeasurable
  rw [hx, uniformLaw_zero_one_eq_restrict]
  exact ae_restrict_mem measurableSet_Icc

/-- The arbitrary orthonormal polynomial family has the sharp uniform row bound. -/
private lemma GP0013B1c_uniform_row {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hx : μ.map X = uniformLaw 0 1) {K : ℕ} (p : Fin K → Polynomial ℝ)
    (hd : ∀ k, (p k).natDegree=k.val)
    (ho : ∀ j k, mean μ (fun ω => (p j).eval (X ω)*(p k).eval (X ω)) =
      if j=k then 1 else 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, (∑ k, ((p k).eval x)^2) ≤ (K : ℝ)^2 := by
  have hI (j k : Fin K) : GP0013B1c_I (p j*p k) = if j=k then 1 else 0 := by
    have hf : StronglyMeasurable (fun x : ℝ => (p j).eval x*(p k).eval x) := by fun_prop
    rw [← GP0013B1c_unit_inner, mean, ← hx,
      integral_map_of_stronglyMeasurable hX hf]
    exact ho j k
  exact GP0013B1c_row_bound p hd hI

theorem uniform_polynomial_gram_bound_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hx : μ.map (X 0)=uniformLaw 0 1)
   (K n : ℕ) (hK : 0 < K) (hn : 0 < n) (p : Fin K → Polynomial ℝ)
   (hdeg : ∀ k,(p k).natDegree=k.val)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0) :
   (∀ x∈Set.Icc (0 : ℝ) 1,(∑ k,((p k).eval x)^2) ≤ (K : ℝ)^2) ∧
   prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤ 4*((K : ℝ)^3-K)/n := by
  have hr := GP0013B1c_uniform_row μ (X 0) (hiid.1 0) hx p hdeg horth
  refine ⟨hr, ?_⟩
  have hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ (K : ℝ)^2 := by
    filter_upwards [GP0013B1c_unit_support μ (X 0) (hiid.1 0) hx] with ω hω
    exact hr (X 0 ω) hω
  convert GP0013B1c_general_gram_finite_probability_bound μ hK X hiid p horth
    ((K : ℝ)^2) hrow n hn using 1 <;> ring

private lemma GP0013B1c_general_gram_good_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    1 - 4 * (ζ * (K : ℝ)/(n : ℝ)) ≤ prob μ {ω | ∀ v : Fin K → ℝ,
      (1/2 : ℝ) * (∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ)} := by
  let F : Ω → ℝ := fun ω => GP0013B1c_general_gram_frob (sampleGram p X n ω)
  have hXm : ∀ i, Measurable (X i) := hiid.1
  have hFm : Measurable F := by
    dsimp [F, GP0013B1c_general_gram_frob, sampleGram]
    fun_prop
  have hmom := GP0013B1c_general_gram_frob_moment μ X hiid p horth ζ hrow n hn
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => GP0013B1c_general_gram_frob_nonneg (sampleGram p X n ω)))
    hmom.1 (1/4 : ℝ)
  have hbad : prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ 4 * (ζ * (K : ℝ)/(n : ℝ)) := by
    change (1/4 : ℝ) * prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ ∫ ω, F ω ∂μ at hmarkov
    have hweak : (∫ ω, F ω ∂μ) ≤ ζ * (K : ℝ)/(n : ℝ) := by
      exact hmom.2.trans (div_le_div_of_nonneg_right
        (sub_le_self _ (Nat.cast_nonneg K)) (Nat.cast_nonneg n))
    linarith
  have hmeas : MeasurableSet {ω | (1/4 : ℝ) ≤ F ω} :=
    measurableSet_le measurable_const hFm
  have hcomp : prob μ {ω | F ω < (1/4 : ℝ)} =
      1 - prob μ {ω | (1/4 : ℝ) ≤ F ω} := by
    have he : {ω | F ω < (1/4 : ℝ)} = {ω | (1/4 : ℝ) ≤ F ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he]
    exact probReal_compl_eq_one_sub hmeas
  have hsub : {ω | F ω < (1/4 : ℝ)} ⊆ {ω | ∀ v : Fin K → ℝ,
      (1/2 : ℝ) * (∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ)} := by
    intro ω hω v
    rw [← GP0013B1c_general_gram_quadratic_identity p X n ω v]
    exact GP0013B1c_general_gram_frob_controls_quadratic (sampleGram p X n ω) hω.le v
  have hmono : prob μ {ω | F ω < (1/4 : ℝ)} ≤ prob μ {ω | ∀ v : Fin K → ℝ,
      (1/2 : ℝ) * (∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ)} :=
    measureReal_mono hsub
  rw [hcomp] at hmono
  linarith

private lemma GP0013B1c_general_gram_rate_stability_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : ℕ → Polynomial ℝ)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ) (zeta2 : ℕ → ℝ)
   (hrow : ∀ n,∀ᵐ ω ∂μ,(∑ k : Fin (J n+1),((p k).eval (X 0 ω))^2) ≤ zeta2 n)
   (hrate : Tendsto (fun (n : ℕ) => zeta2 n*((J n+1 : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0)) :
   Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1) := by
  have hlo : Tendsto (fun n : ℕ =>
      1 - 4 * (zeta2 n * ((J n+1 : ℕ) : ℝ)/(n : ℝ))) atTop (nhds 1) := by
    have hm := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4)).mul hrate
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hm
    simpa only [mul_zero, sub_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have horth' (j k : Fin (J n+1)) :
        mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω)) =
          if j = k then 1 else 0 := by
      simpa only [mean,Fin.ext_iff] using horth j.val k.val
    exact GP0013B1c_general_gram_good_probability_lower μ X hiid
      (fun k : Fin (J n+1) => p k) horth' (zeta2 n) (hrow n) n hn
  · exact Filter.Eventually.of_forall (fun n => measureReal_le_one)


private lemma GP0013B1c_uniform_restrict (a b : ℝ) :
    uniformLaw a b = ENNReal.ofReal ((b-a)⁻¹) • volume.restrict (Set.Icc a b) := by
  unfold uniformLaw
  have he : (fun x : ℝ => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0)) =
      (Set.Icc a b).indicator (fun _ => ENNReal.ofReal ((b-a)⁻¹)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
  rw [he, withDensity_indicator measurableSet_Icc, withDensity_const]

private lemma GP0013B1c_affine_inner (a b : ℝ) (hab : a<b) (p q : Polynomial ℝ) :
    GP0013B1c_I ((p.comp (Polynomial.C a+Polynomial.C (b-a)*Polynomial.X)) *
      (q.comp (Polynomial.C a+Polynomial.C (b-a)*Polynomial.X))) =
      mean (uniformLaw a b) (fun x => p.eval x*q.eval x) := by
  rw [GP0013B1c_I]
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [intervalIntegral.integral_comp_add_mul (fun x => p.eval x*q.eval x)
    (sub_ne_zero.mpr hab.ne') a]
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel]
  rw [mean, GP0013B1c_uniform_restrict, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr hab.le)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]

private lemma GP0013B1c_interval_row {K : ℕ} (a b : ℝ) (hab : a<b)
    (p : Fin K → Polynomial ℝ) (hd : ∀ k, (p k).natDegree=k.val)
    (ho : ∀ j k, mean (uniformLaw a b) (fun x => (p j).eval x*(p k).eval x) =
      if j=k then 1 else 0)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    (∑ k, ((p k).eval x)^2) ≤ (K : ℝ)^2 := by
  let q : Fin K → Polynomial ℝ := fun k =>
    (p k).comp (Polynomial.C a+Polynomial.C (b-a)*Polynomial.X)
  have hqd (k : Fin K) : (q k).natDegree=k.val := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_add,
      Polynomial.natDegree_C_mul_X _ (sub_ne_zero.mpr hab.ne'), mul_one, hd]
  have hqo (j k : Fin K) : GP0013B1c_I (q j*q k)=if j=k then 1 else 0 := by
    exact (GP0013B1c_affine_inner a b hab (p j) (p k)).trans (ho j k)
  have ht : (x-a)/(b-a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have heval (k : Fin K) : (q k).eval ((x-a)/(b-a)) = (p k).eval x := by
    simp only [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
      Polynomial.eval_X]
    congr 1
    field_simp [sub_ne_zero.mpr hab.ne']
    <;> ring
  simpa only [heval] using GP0013B1c_row_bound q hqd hqo ((x-a)/(b-a)) ht

theorem uniform_cubic_gram_rate_stability_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (a b : ℝ) (hab : a < b)
   (hlaw : μ.map (X 0)=uniformLaw a b) (p : ℕ → Polynomial ℝ)
   (hdeg : ∀ k,(p k).natDegree=k)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ)
   (hrate : Tendsto (fun (n : ℕ) => (((J n+1 : ℕ) : ℝ)^3)/(n : ℝ)) atTop (nhds 0)) :
   Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1) := by
  have hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b := by
    apply ae_of_ae_map (hiid.1 0).aemeasurable
    rw [hlaw,GP0013B1c_uniform_restrict]
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  have hrow (n : ℕ) : ∀ᵐ ω ∂μ,
      (∑ k : Fin (J n+1), ((p k).eval (X 0 ω))^2) ≤ (((J n+1 : ℕ) : ℝ)^2) := by
    have ho (j k : Fin (J n+1)) :
        mean (uniformLaw a b) (fun x => (p j).eval x*(p k).eval x)=if j=k then 1 else 0 := by
      have hf : StronglyMeasurable (fun x : ℝ => (p j).eval x*(p k).eval x) := by fun_prop
      rw [mean,← hlaw,integral_map_of_stronglyMeasurable (hiid.1 0) hf]
      simpa only [mean,Fin.ext_iff] using horth j.val k.val
    filter_upwards [hsupp] with ω hω
    exact GP0013B1c_interval_row a b hab (fun k : Fin (J n+1) => p k)
      (fun k => hdeg k) ho (X 0 ω) hω
  apply GP0013B1c_general_gram_rate_stability_proof μ X hiid p horth J
    (fun n => (((J n+1 : ℕ) : ℝ)^2)) hrow
  convert hrate using 1
  funext n
  ring

end
end AronowAudit.P001.Wave1
