import SAP.P005b.Defs.WholeW1
import SAP.P005b.Bridge
import AronowAudit.P005.Wave1.Gap.FidP005
import AronowAudit.P005.Wave1.Gap.GP005B2
import AronowAudit.P005.Wave1.Gap.GP005B3b
import AronowAudit.P005.Wave1.DebiasedLinearTailC
import AronowAudit.P005.Wave1.Lib.QuadraticSamplingTailC
import AronowAudit.P005.Wave1.Gap.GP005B5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.WH.W1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
open SAP.P005b SAP.P005b.Bridge
set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

/-- Kernel algebra for the p. 1514 term. Prove the zero row/column sums and trace
by finite-sum linearity and covariate centering. For the principal-sum identity,
use corrected_residual_term_identification, corrected_residual_brackets and the
common_residual_normal_equation; then expand dot and the treated mean.
This is finite algebra, including n=2,3 and d=0; no inverse is involved. -/
def T17_L1 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n →
    standardized P →
    let Q := wholeW1Kernel P (wholeW1Delta P m)
    (∀ i, (∑ j, Q i j) = 0) ∧
    (∀ j, (∑ i, Q i j) = 0) ∧
    (∑ i, Q i i) = (n : ℝ) * popMean (fun i => leverage P i * wholeW1Delta P m i) ∧
    (∀ S ∈ design n m,
      wholeW1Star P m S = (∑ i ∈ S, ∑ j ∈ S, Q i j) / (pC n m * m * n))

/-- The two small population sizes excluded by the quadratic-sampling donor.
With zero row and column sums, a principal sum over a complement equals the
principal sum over the set. For n=2,3 each nonempty proper set or its complement
is a singleton. Bound the variance of the uniformly sampled diagonal by its
second moment, then by the sum of all matrix squares. Alternatively fin_cases
n and m and expand the finite sums; n=3 only needs nine matrix entries. -/
def T17_L2 : Prop :=
  ∀ {n m : ℕ}, 2 ≤ n → n < 4 → 0 < m → m < n →
    ∀ Q : Matrix (Fin n) (Fin n) ℝ,
    (∀ i, (∑ j, Q i j) = 0) → (∀ j, (∑ i, Q i j) = 0) →
    variance m (fun S => ∑ i ∈ S, ∑ j ∈ S, Q i j) ≤
      ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) * (∑ i, ∑ j, (Q i j)^2)

/-- The weighted Cauchy–Schwarz estimate is short donor glue. -/
private theorem weighted_moment {n d : ℕ} (P : Population n d)
    (hn : 0 < n) (hG : gram P = 1) (δ : Fin n → ℝ) :
    (popMean (fun i => leverage P i * δ i))^2 ≤
      (n : ℝ) * kappa P * d * popMean (fun i => δ i^2) := by
  have hc : (popMean (fun i => leverage P i*δ i))^2 ≤
      popMean (fun i => leverage P i^2)*popMean (fun i => δ i^2) :=
    AronowAudit.P005.Wave1.GP005B3b_T25_mean_cauchy (leverage P) δ
  have hh : popMean (fun i => leverage P i^2) ≤ (n : ℝ)*kappa P*d := by
    calc
      _ ≤ popMean (fun i => ((n : ℝ)*kappa P)*leverage P i) := by
        apply AronowAudit.P005.mean_mono
        intro i _
        have hb : leverage P i ≤ (n : ℝ)*kappa P :=
          AronowAudit.P005.leverage_le_maximum (toProject P) hn i
        have hnlev : 0 ≤ leverage P i :=
          AronowAudit.P005.leverage_nonneg (toProject P) i
        nlinarith [mul_le_mul_of_nonneg_right hb hnlev]
      _ = ((n : ℝ)*kappa P)*popMean (leverage P) :=
        AronowAudit.P005.mean_mul _ _ _
      _ = _ := by
        rw [show popMean (leverage P) = (d : ℝ) from
          AronowAudit.P005.leverage_population_mean (toProject P) hG]
  exact hc.trans (mul_le_mul_of_nonneg_right hh
    (AronowAudit.P005.mean_nonneg _ _ (fun _ _ => sq_nonneg _)))

/-- From the two finite moment bounds to the uncentered stochastic order.
Use the uniform residual-difference bound 4K and allocation ratios bounded away
from zero. For d>=1 the variance plus squared mean is at most C*kappa*d/n.
Apply t4_variance_eq and finite_markov to F^2. When d=0 (or the rate is zero),
the same second-moment bound forces F=0 on every assignment; prove its tail
probability zero directly. Do not divide by a possibly zero rate. No dimension
or leverage decay and no inverse assumption may be added. -/
def T17_L3 : Prop :=
  ∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)),
    wholeW1Standing d m P →
    (∀ᶠ n in atTop,
      variance (m n) (wholeW1Star (P n) (m n)) ≤
        kappa (P n)/(pT n (m n)*pC n (m n)*(n-1)) *
          popMean (fun i => wholeW1Delta (P n) (m n) i^2)) →
    (∀ᶠ n in atTop,
      (expectation (m n) (wholeW1Star (P n) (m n)))^2 ≤
        ((n : ℝ)*kappa (P n)*d n/(n-1)^2) *
          popMean (fun i => wholeW1Delta (P n) (m n) i^2)) →
    stochasticO m (fun n => wholeW1Star (P n) (m n))
      (fun n => Real.sqrt (kappa (P n)*d n/n))

/-- The actual closed-form coefficients satisfy all normal equations for (1).
Split each sum into T and C, use the complement means, and use
Lhat * betaHat = Nhat from det(Lhat) != 0. The scalar equations give the
intercept and treatment means; Gram normalization gives the covariate equations.
This should be a finite-sum proof, with no determinant of a block matrix needed. -/
def T21_L1 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 0 < m → m < n →
    standardized P → ∀ S ∈ design n m, (Lhat P m S).det ≠ 0 →
    let e := fun i => wholeW1Observed P S i -
      wholeW1Fit P S (wholeW1Intercept P m S) (adjustedATE P m S) (betaHat P m S) i
    (∑ i, e i) = 0 ∧ (∑ i, indicator S i * e i) = 0 ∧
      (∀ k, (∑ i, P.x i k * e i) = 0)

/-- Full rank of the intercept/treatment/covariate design from the paper's
assumptions. If a+t*D+x'b is identically zero, take each arm mean and subtract
it within the arm. The sum of within-arm squared covariate projections is
n*b' Lhat b. Equivalently, the covariate normal equations yield Lhat*b=0.
Invertibility forces b=0, and the two nonempty arm means force a=t=0.
This also covers the empty covariate index type. -/
def T21_L2 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 0 < m → m < n →
    standardized P → ∀ S ∈ design n m, (Lhat P m S).det ≠ 0 →
    ∀ (a t : ℝ) (b : Fin d → ℝ),
    (∀ i, wholeW1Fit P S a t b i = 0) → a = 0 ∧ t = 0 ∧ b = 0

private theorem variance_congr_design {n m : ℕ} (f g : Finset (Fin n) → ℝ)
    (h : ∀ S ∈ design n m, f S = g S) : variance m f = variance m g := by
  have he : expectation m f = expectation m g :=
    AronowAudit.P005.expectation_congr m _ _ h
  unfold variance
  rw [he]
  exact AronowAudit.P005.expectation_congr m _ _ (fun S hS => by rw [h S hS])

/-! Previously proved clauses, assembled directly from project donors. -/

theorem existing_T17 : SAP.P005b.T17Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n d m P hn hm hmn hG δ
    exact AronowAudit.P005.corrected_contraction_chain (toProject P) hn hm hmn hG δ
  · intro n d P hn hG a
    have hmid : (∑ j, a j^2 * dot (P.x j) ((∑ i, Matrix.vecMulVec (P.x i) (P.x i)) *ᵥ P.x j)) =
        (n : ℝ) * ∑ j, a j^2 * leverage P j := by
      rw [sum_outer_eq P hn, hG]
      simp [dot, leverage, Finset.mul_sum, Matrix.smul_mulVec,
        mul_left_comm]
    exact ⟨(AronowAudit.P005.covariate_contraction (toProject P) hn hG a).trans hmid.symm, hmid⟩
  · intro n d m P hn K hT hC
    exact AronowAudit.P005.common_residual_difference_second_moment (toProject P) hn K hT hC
  · intro d m P h
    refine ⟨AronowAudit.P005.Wave1.corrected_contraction_order d m (fun n => toProject (P n)) h, ?_⟩
    obtain ⟨K, hK, hY⟩ := h.2.1
    apply Asymptotics.IsBigO.of_bound (4*K)
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hb := AronowAudit.P005.common_residual_difference_second_moment (m := m n)
      (toProject (P n)) (by omega) K (hY n hn).1 (hY n hn).2.1
    have hp : 0 ≤ popMean (fun i =>
        (commonResidual (P n) (m n) (P n).yT i-commonResidual (P n) (m n) (P n).yC i)^2) :=
      AronowAudit.P005.mean_nonneg _ _ (fun i _ => sq_nonneg _)
    change popMean (fun i =>
      (commonResidual (P n) (m n) (P n).yT i-commonResidual (P n) (m n) (P n).yC i)^2) ≤ 4*K at hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, abs_one, mul_one] using hb

theorem existing_T21 : SAP.P005b.T21Statement := by
  intro n d m P hn hm hmn hP hinv
  have h := AronowAudit.P005.Wave1.noninteracted_exact_unbiasedness_proof
    (toProject P) hn hm hmn hP hinv
  have hd := AronowAudit.P005.Wave1.noninteracted_exact_decomposition_proof
    (toProject P) hn hm hmn hP hinv
  refine ⟨h.1, h.2, ?_, hd.2.1, ?_, ?_⟩
  · intro S hS
    exact (AronowAudit.P005.noninteracted_debiased_expansion (toProject P) m S (N P m)
      hn hm hmn hS (hinv S hS)).1
  · intro S _
    rfl
  · intro ht hc
    have hp := bias_parts_expectation P hn hm hmn ht hc
    have hr : (pT n m/pC n m)*NTTT n m*leverageCov P P.yT -
        (pT n m/pC n m)*NTTC n m*leverageCov P P.yC =
        ((n : ℝ)-2*m)/((n-1 : ℝ)*(n-2 : ℝ)*m)*leverageCov P P.yT -
          (2*(m : ℝ)-n)/((n-1 : ℝ)*(n-2 : ℝ)*(n-m))*leverageCov P P.yC := by
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
      dsimp [pT, pC, NTTT, NTTC]
      field_simp [ne_of_gt hmR, show (n : ℝ) ≠ 0 by linarith,
        show (n : ℝ)-1 ≠ 0 by linarith, show (n : ℝ)-2 ≠ 0 by linarith,
        show (n : ℝ)-m ≠ 0 by linarith]; ring
    refine ⟨hp.1, hp.2, hp.2.trans hr, ?_⟩
    intro S _
    have hg : covarianceCombination m (n-m) (sampleCov S (leverage P) P.yT)
        (sampleCov (control S) (leverage P) P.yC) =
        sampleCov (control S) (leverage P) P.yC / ((m+(n-m) : ℕ)-2 : ℝ) -
          sampleCov S (leverage P) P.yT / ((m+(n-m) : ℕ)-2 : ℝ) :=
      (AronowAudit.P005.collected_covariance_coefficients m (n-m) ht hc _ _).2.2
    dsimp only [covarianceCombination] at hg
    simp only [show m+(n-m) = n by omega, Nat.cast_sub (le_of_lt hmn)] at hg
    dsimp only [biasPart11, biasPart12]
    convert hg using 1; ring


/-- Assemble the full p. 1514 statement from kernel algebra, the small-size
sampling bound, weighted Cauchy–Schwarz and the moment-to-order step. -/
theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) (h3 : T17_L3) :
    T17WholeStatement := by
  have hv : ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n →
      standardized P → variance m (wholeW1Star P m) ≤
        wholeW1VarianceCoefficient n m *
          (∑ i, ∑ j, (wholeW1Kernel P (wholeW1Delta P m) i j)^2) := by
    intro n d m P hn hm hmn hP
    obtain ⟨hr, hc, ht, hid⟩ := h1 P hn hm hmn hP
    let Q := wholeW1Kernel P (wholeW1Delta P m)
    have hb : variance m (fun S => ∑ i ∈ S, ∑ j ∈ S, Q i j) ≤
        ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) * (∑ i, ∑ j, (Q i j)^2) := by
      by_cases hn4 : 4 ≤ n
      · exact AronowAudit.P005.Wave1.principal_sum_variance_tailC hn4
          (le_of_lt hmn) Q hr hc
      · exact h2 hn (by omega) hm hmn Q hr hc
    rw [variance_congr_design _ _ hid]
    change AronowAudit.P005.variance m (fun S =>
      (∑ i ∈ S, ∑ j ∈ S, Q i j)/(pC n m*m*n)) ≤ _
    rw [AronowAudit.P005.Wave1.t4_variance_div]
    calc
      _ ≤ (((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
          (∑ i, ∑ j, (Q i j)^2))/(pC n m*m*n)^2 :=
        div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ = _ := by unfold wholeW1VarianceCoefficient; ring
  have hc : ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n →
      gram P = 1 → wholeW1VarianceCoefficient n m *
        (∑ i, ∑ j, (wholeW1Kernel P (wholeW1Delta P m) i j)^2) ≤
      wholeW1VarianceCoefficient n m *
        (∑ i, ∑ j, (dot (P.x i) (P.x j)*wholeW1Delta P m j)^2) := by
    intro n d m P hn hm hmn hG
    have hcenter := (existing_T17.1 P hn hm hmn hG (wholeW1Delta P m)).1
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hcenter i))
    unfold wholeW1VarianceCoefficient pC
    have hmR : (m : ℝ) < n := by exact_mod_cast hmn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (sq_nonneg _) (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmR.le))
      (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
  refine ⟨existing_T17, ?_, ?_⟩
  · intro n d m P hn hm hmn hP
    exact ⟨hv P hn hm hmn hP, hc P hn hm hmn hP.2⟩
  · intro d m P h
    apply h3 d m P h
    · filter_upwards [h.2.2.1, eventually_ge_atTop 4] with n hP hn
      obtain ⟨hdn, hm, hmn⟩ := h.1 n (by omega)
      have hchain := existing_T17.1 (P n) (by omega) hm hmn hP.2
        (wholeW1Delta (P n) (m n))
      exact ((hv (P n) (by omega) hm hmn hP).trans
        (hc (P n) (by omega) hm hmn hP.2)).trans
          (hchain.2.2.1.trans_le hchain.2.2.2)
    · filter_upwards [h.2.2.1, eventually_ge_atTop 4] with n hP hn
      obtain ⟨hdn, hm, hmn⟩ := h.1 n (by omega)
      obtain ⟨hr, hcol, htrace, hid⟩ := h1 (P n) (by omega) hm hmn hP
      have he := AronowAudit.P005.Wave1.principal_sum_expectation_tailC hn
        (le_of_lt hmn) (wholeW1Kernel (P n) (wholeW1Delta (P n) (m n)))
      have hall : (∑ i, ∑ j, wholeW1Kernel (P n) (wholeW1Delta (P n) (m n)) i j) = 0 := by
        simp only [hr, Finset.sum_const_zero]
      change expectation (m n) (fun S =>
        ∑ i ∈ S, ∑ j ∈ S, wholeW1Kernel (P n) (wholeW1Delta (P n) (m n)) i j) = _ at he
      rw [hall, htrace, mul_zero, add_zero] at he
      have hex : expectation (m n) (wholeW1Star (P n) (m n)) =
          popMean (fun i => leverage (P n) i*wholeW1Delta (P n) (m n) i)/(n-1 : ℝ) := by
        rw [show expectation (m n) (wholeW1Star (P n) (m n)) =
            expectation (m n) (fun S =>
              (∑ i ∈ S, ∑ j ∈ S, wholeW1Kernel (P n) (wholeW1Delta (P n) (m n)) i j) /
                (pC n (m n)*m n*n)) from AronowAudit.P005.expectation_congr (m n) _ _ hid]
        have hdv : expectation (m n) (fun S =>
              (∑ i ∈ S, ∑ j ∈ S, wholeW1Kernel (P n) (wholeW1Delta (P n) (m n)) i j) /
                (pC n (m n)*m n*n)) =
            expectation (m n) (fun S =>
              ∑ i ∈ S, ∑ j ∈ S, wholeW1Kernel (P n) (wholeW1Delta (P n) (m n)) i j) /
                (pC n (m n)*m n*n) := by
          simp only [expectation, ← Finset.sum_div, div_div, mul_comm]
        rw [hdv, he]
        have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
        have hmR : (0 : ℝ) < m n := by exact_mod_cast hm
        have hmnR : (m n : ℝ) < n := by exact_mod_cast hmn
        dsimp [pC]
        field_simp [show (n : ℝ) ≠ 0 by linarith,
          show (n : ℝ)-1 ≠ 0 by linarith, ne_of_gt hmR,
          show (n : ℝ)-m n ≠ 0 by linarith]
      rw [hex, div_pow]
      have hb := div_le_div_of_nonneg_right
        (weighted_moment (P n) (by omega) hP.2 (wholeW1Delta (P n) (m n)))
        (sq_nonneg ((n : ℝ)-1))
      convert hb using 1 <;> ring

private theorem fit_sub {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (a t a₀ t₀ : ℝ) (b b₀ : Fin d → ℝ) (i : Fin n) :
    wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i =
      wholeW1Fit P S a t b i-wholeW1Fit P S a₀ t₀ b₀ i := by
  simp only [wholeW1Fit, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Normal equations give the sum-of-squares decomposition; full rank gives
uniqueness. All probability identities are supplied by the existing finite proofs. -/
theorem T21_assembly (h1 : T21_L1) (h2 : T21_L2) : T21WholeStatement := by
  refine ⟨existing_T21, ?_⟩
  intro n d m P hn hm hmn hP hinv
  have hd := AronowAudit.P005.Wave1.noninteracted_exact_decomposition_proof
    (toProject P) hn hm hmn hP hinv
  refine ⟨?_, hd.2.2.1, ?_⟩
  · intro S hS
    obtain ⟨he, hDe, hxe⟩ := h1 P hn hm hmn hP S hS (hinv S hS)
    let a₀ := wholeW1Intercept P m S
    let t₀ := adjustedATE P m S
    let b₀ := betaHat P m S
    let e := fun i => wholeW1Observed P S i-wholeW1Fit P S a₀ t₀ b₀ i
    change (∑ i, e i) = 0 at he
    change (∑ i, indicator S i * e i) = 0 at hDe
    change (∀ k, (∑ i, P.x i k * e i) = 0) at hxe
    have hortho (a t : ℝ) (b : Fin d → ℝ) :
        (∑ i, e i * wholeW1Fit P S a t b i) = 0 := by
      have hp (i : Fin n) : e i * wholeW1Fit P S a t b i =
          a*e i+t*(indicator S i*e i)+∑ k, b k*(P.x i k*e i) := by
        simp only [wholeW1Fit, dot]
        have hsum : (∑ k, e i*(P.x i k*b k)) = ∑ k, b k*(P.x i k*e i) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [mul_add, mul_add, Finset.mul_sum, hsum]
        ring
      simp_rw [hp]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      change a * (∑ i, e i) + t * (∑ i, indicator S i * e i) +
        (∑ k, b k * (∑ i, P.x i k * e i)) = 0
      simp only [he, hDe, hxe, mul_zero, Finset.sum_const_zero, add_zero]
    intro a t b
    have hdecomp : wholeW1Loss P S a t b =
        wholeW1Loss P S a₀ t₀ b₀ +
          ∑ i, (wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i)^2 := by
      have hz := hortho (a-a₀) (t-t₀) (b-b₀)
      calc
        wholeW1Loss P S a t b = wholeW1Loss P S a₀ t₀ b₀ +
            (∑ i, (wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i)^2) -
            2*(∑ i, e i*wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i) := by
          unfold wholeW1Loss
          rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [fit_sub]
          dsimp [e]
          ring
        _ = _ := by rw [hz]; ring
    have hnon : 0 ≤ ∑ i, (wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i)^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    refine ⟨by rw [hdecomp]; linarith, ?_⟩
    intro heq
    have hz : (∑ i, (wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i)^2) = 0 := by
      linarith [hdecomp]
    have hfit : ∀ i, wholeW1Fit P S (a-a₀) (t-t₀) (b-b₀) i = 0 := by
      intro i
      exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => sq_nonneg _)).mp hz i (mem_univ i))
    obtain ⟨ha, ht, hb⟩ := h2 P hn hm hmn hP S hS (hinv S hS)
      (a-a₀) (t-t₀) (b-b₀) hfit
    exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp ht, sub_eq_zero.mp hb⟩
  · have hr : (pT n m/pC n m)*NTTT n m*leverageCov P P.yT -
        (pT n m/pC n m)*NTTC n m*leverageCov P P.yC =
        ((n : ℝ)-2*m)/((n-1 : ℝ)*(n-2 : ℝ)*m)*leverageCov P P.yT -
          (2*(m : ℝ)-n)/((n-1 : ℝ)*(n-2 : ℝ)*(n-m))*leverageCov P P.yC := by
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
      dsimp [pT, pC, NTTT, NTTC]
      field_simp [ne_of_gt hmR, show (n : ℝ) ≠ 0 by linarith,
        show (n : ℝ)-1 ≠ 0 by linarith, show (n : ℝ)-2 ≠ 0 by linarith,
        show (n : ℝ)-m ≠ 0 by linarith]
      <;> ring
    exact hd.2.2.2.2.1.trans hr.symm

/-- Expose the stronger rate already constructed in the existing expansion
proof, and use finite mean linearity for the p. 1516 identity. -/
theorem T26_assembly : T26WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro d m P h hinv hκ
    exact AronowAudit.P005.Wave1.noninteracted_debiased_linear_expansion_proof
      d m (fun n => toProject (P n)) h hinv hκ
  · intro d m P h hinv
    let PP := fun n => toProject (P n)
    have hp : AronowAudit.P005.standingAssumptions d m PP := h
    obtain ⟨lo, hi, hlo, hlohi, hhi, halloc⟩ := h.2.2.2
    have hB : 0 < 1/lo+1/(1-hi) :=
      add_pos (one_div_pos.2 hlo) (one_div_pos.2 (sub_pos.mpr hhi))
    have hT := AronowAudit.P005.Wave1.tailC_arm_debiased_order d m PP hp .treated
    have hC := AronowAudit.P005.Wave1.tailC_arm_debiased_order d m PP hp .control
    change AronowAudit.P005.stochasticO m
      (fun n S => AronowAudit.P005.Wave1.tailC_arm_remainder (PP n) .treated S)
      (fun n => Real.sqrt (kappa (P n)/n)) at hT
    change AronowAudit.P005.stochasticO m
      (fun n S => AronowAudit.P005.Wave1.tailC_arm_remainder (PP n) .control S)
      (fun n => Real.sqrt (kappa (P n)/n)) at hC
    apply AronowAudit.P005.Wave1.tailC_order_combine m _ _ _ _
      (fun n => pT n (m n)/pC n (m n))
      (fun n => pC n (m n)/pT n (m n)) hT hC _ hB
    filter_upwards [h.2.2.1, hinv, eventually_ge_atTop 3] with n hP hninv hn
    obtain ⟨hd, hdn, hm, hmn⟩ := h.1 n hn
    obtain ⟨hlo', hhi'⟩ := halloc n hn
    have hpq : pT n (m n)+pC n (m n)=1 := by
      dsimp [pT, pC]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp [hn0]
      <;> ring
    have hb := AronowAudit.P005.Wave1.tailC_ratio_bounds lo hi _ _ hlo hhi hlo' hhi' hpq
    intro S hS
    exact ⟨AronowAudit.P005.Wave1.tailC_weighted_remainder
      (PP n) hn hm hmn hP.1 S hS (hninv S hS), hb⟩
  · intro n d m P hn hm hmn _ S hS hinv
    have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
    have hc : (control S).card = n-m := by
      rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp [hs]
    have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
    have hCn : (control S).Nonempty := Finset.card_pos.mp (by omega)
    have hexp := (AronowAudit.P005.noninteracted_debiased_expansion
      (toProject P) m S (N P m) hn hm hmn hS hinv).1
    have hlead : commonLeading P m S =
        mean S P.yT-mean (control S) P.yC-ate P-
          dot (xMean P S-xMean P (control S)) (N P m) := by
      change mean S (fun i => centered P.yT i-dot (P.x i) (N P m))-
        mean (control S) (fun i => centered P.yC i-dot (P.x i) (N P m)) = _
      have hT : mean S (fun i => centered P.yT i-dot (P.x i) (N P m)) =
          mean S P.yT-popMean P.yT-dot (xMean P S) (N P m) :=
        AronowAudit.P005.Wave1.tailC_mean_residual (toProject P) S hSn P.yT (N P m)
      have hC : mean (control S) (fun i => centered P.yC i-dot (P.x i) (N P m)) =
          mean (control S) P.yC-popMean P.yC-dot (xMean P (control S)) (N P m) :=
        AronowAudit.P005.Wave1.tailC_mean_residual (toProject P) (control S) hCn P.yC (N P m)
      rw [hT, hC]
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, ate]
      ring
    change debiasedATE P m S = mean S P.yT-mean (control S) P.yC-
      dot (xMean P S-xMean P (control S)) (Nhat P m S)+
      sampleCov S (leverage P) P.yT/(n-2 : ℝ)-
      sampleCov (control S) (leverage P) P.yC/(n-2 : ℝ) at hexp
    rw [hexp, hlead]
    simp only [wholeW1DebiasedStar, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring

/-- The arm remainder difference and the existing order-combination theorem
already prove the stronger rate without leverage decay. -/
theorem T27_assembly : T27WholeStatement := by
  constructor
  · intro d m P h hinv hκ
    exact AronowAudit.P005.Wave1.interacted_debiased_linear_expansion_proof
      d m (fun n => toProject (P n)) h hinv hκ
  · intro d m P h _
    let PP := fun n => toProject (P n)
    have hp : AronowAudit.P005.standingAssumptions d m PP := h
    have hT := AronowAudit.P005.Wave1.tailC_arm_debiased_order d m PP hp .treated
    have hC := AronowAudit.P005.Wave1.tailC_arm_debiased_order d m PP hp .control
    change AronowAudit.P005.stochasticO m
      (fun n S => AronowAudit.P005.Wave1.tailC_arm_remainder (PP n) .treated S)
      (fun n => Real.sqrt (kappa (P n)/n)) at hT
    change AronowAudit.P005.stochasticO m
      (fun n S => AronowAudit.P005.Wave1.tailC_arm_remainder (PP n) .control S)
      (fun n => Real.sqrt (kappa (P n)/n)) at hC
    apply AronowAudit.P005.Wave1.tailC_order_combine m _ _ _ _
      (fun _ => 1) (fun _ => 1) hT hC 1 (by norm_num)
    filter_upwards [eventually_ge_atTop 3] with n hn
    obtain ⟨hd, hdn, hm, hmn⟩ := h.1 n hn
    intro S hS
    refine ⟨?_, by norm_num, by norm_num⟩
    change AronowAudit.P005.interactedDebiasedATE (PP n) (m n) S-
      AronowAudit.P005.ate (PP n)-AronowAudit.P005.armLeading (PP n) S = _
    simpa only [one_mul] using
      AronowAudit.P005.Wave1.tailC_arm_remainder_difference (PP n) hm hmn S hS

end
end SAP.P005b.WH.W1
