import AronowAudit.P001.Wave1.Lib.TailA.FiniteBootstrap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MeanInequalitiesPow

/-! Exact finite retained-donor void probabilities. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace AronowAudit.P001.TailA
local instance instDecidableReuseProbability (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 1000000

/-- Independent responses with deterministic propensities. -/
def ReuseResponseLaw {n : ℕ} (θ : Fin n → unitInterval) : Measure (Fin n → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (θ i))

instance instProbabilityReuseResponseLaw {n : ℕ} (θ : Fin n → unitInterval) :
    IsProbabilityMeasure (ReuseResponseLaw θ) := by
  unfold ReuseResponseLaw
  infer_instance

/-- The uniform exponential decay constant for retained responding labels. -/
def reuseRho : ℝ := 1-(1-Real.exp (-1))/4

theorem reuse_rho_bounds : 0 < reuseRho ∧ reuseRho < 1 := by
  have he0 := Real.exp_pos (-1)
  have he1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  constructor <;> dsimp [reuseRho] <;> linarith

/-- None of the responding labels in `S` occurs in the resampling map. -/
def reuseNoRetained {n : ℕ} (S : Finset (Fin n)) (r : Fin n → Bool)
    (a : Fin n → Fin n) : Prop := ∀ l ∈ S, r l = true → ∀ t, a t ≠ l

theorem reuse_uniform_avoid {n : ℕ} (hn : 0 < n) (D : Finset (Fin n)) :
    mean (UniformResampling n) (fun a => if ∀ t, a t ∉ D then 1 else 0) =
      (1-(D.card : ℝ)/(n : ℝ))^n := by
  haveI instNonzeroReuseAvoid : NeZero n := ⟨hn.ne'⟩
  rw [mean, uniform_resampling_eq_uniform_pi hn]
  have heq : (fun a : Fin n → Fin n => if ∀ t, a t ∉ D then (1 : ℝ) else 0) =
      fun a => ∏ t, if a t ∉ D then (1 : ℝ) else 0 := by
    funext a
    by_cases ha : ∀ t, a t ∉ D
    · simp only [if_pos ha]
      exact (Finset.prod_eq_one (fun t _ => if_pos (ha t))).symm
    · obtain ⟨t,ht⟩ := not_forall.mp ha
      rw [if_neg ha]
      exact (Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)).symm
  rw [heq, integral_fintype_prod_eq_pow (fun i : Fin n => if i ∉ D then (1 : ℝ) else 0)]
  simp only [Fintype.card_fin]
  congr 1
  rw [uniform_index_integral]
  have hs : (∑ i : Fin n, if i ∉ D then (1 : ℝ) else 0) = n-D.card := by
    have hf : Finset.univ.filter (fun i : Fin n => i ∉ D) = Dᶜ := by ext i; simp
    have hcard : D.card ≤ n := by simpa using Finset.card_le_univ D
    rw [Finset.sum_boole,hf,Finset.card_compl,Fintype.card_fin,Nat.cast_sub hcard]
  rw [hs]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- The actual multinomial sample has the standard exponential avoidance bound. -/
theorem reuse_uniform_avoid_le_exp {n : ℕ} (hn : 0 < n) (D : Finset (Fin n)) :
    mean (UniformResampling n) (fun a => if ∀ t, a t ∉ D then 1 else 0) ≤
      Real.exp (-1) ^ D.card := by
  rw [reuse_uniform_avoid hn D]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hD : (D.card : ℝ) ≤ n := by exact_mod_cast (show D.card ≤ n from by simpa only [Fintype.card_fin] using Finset.card_le_univ D)
  have hbase : 0 ≤ 1-(D.card : ℝ)/(n : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one hnR).mpr hD)
  have hexp : 1-(D.card : ℝ)/(n : ℝ) ≤ Real.exp (-(D.card : ℝ)/(n : ℝ)) := by
    have h := Real.add_one_le_exp (-(D.card : ℝ)/(n : ℝ))
    simpa only [neg_div,sub_eq_add_neg,add_comm] using h
  calc
    _ ≤ (Real.exp (-(D.card : ℝ)/(n : ℝ)))^n := pow_le_pow_left₀ hbase hexp n
    _ = Real.exp (-(D.card : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    _ = Real.exp (-1)^D.card := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem reuse_no_retained_iff {n : ℕ} (S : Finset (Fin n)) (r : Fin n → Bool)
    (a : Fin n → Fin n) :
    reuseNoRetained S r a ↔ ∀ t, a t ∉ S.filter (fun l => r l = true) := by
  constructor
  · intro h t ht
    obtain ⟨hs,hr⟩ := Finset.mem_filter.mp ht
    exact h (a t) hs hr t rfl
  · intro h l hl hr t heq
    exact h t (Finset.mem_filter.mpr ⟨heq ▸ hl, heq ▸ hr⟩)

theorem reuse_filter_exponential {n : ℕ} (S : Finset (Fin n)) (r : Fin n → Bool) :
    Real.exp (-1)^(S.filter (fun l => r l = true)).card =
      ∏ l ∈ S, if r l then Real.exp (-1) else 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert l S hl ih =>
    cases hr : r l <;> simp [Finset.filter_insert,hl,hr,ih,pow_succ,mul_comm]

/-- Exponential response generating function, uniformly in all propensities. -/
theorem reuse_response_exponential_bound {n : ℕ} (θ : Fin n → unitInterval)
    (hθ : ∀ i, (1/4 : ℝ) ≤ θ i) (S : Finset (Fin n)) :
    mean (ReuseResponseLaw θ) (fun r => ∏ l ∈ S, if r l then Real.exp (-1) else 1) ≤
      reuseRho^S.card := by
  change (∫ r, (∏ l ∈ S, if r l then Real.exp (-1) else 1) ∂Measure.pi
    (fun i => bernoulliMeasure true false (θ i))) ≤ _
  have hexpand (r : Fin n → Bool) :
      (∏ l ∈ S, if r l then Real.exp (-1) else 1) =
        ∏ l : Fin n, if l ∈ S then (if r l then Real.exp (-1) else 1) else 1 := by
    simp only [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hexpand]
  rw [integral_fintype_prod_eq_prod (fun i (b : Bool) =>
    if i ∈ S then (if b then Real.exp (-1) else 1) else 1)]
  have hcoord (i : Fin n) : (∫ b, (if i ∈ S then (if b then Real.exp (-1) else 1) else 1)
      ∂bernoulliMeasure true false (θ i)) =
        if i ∈ S then ((θ i : ℝ)*Real.exp (-1)+(1-(θ i : ℝ))) else 1 := by
    rw [integral_bernoulliMeasure]
    by_cases hi : i ∈ S <;> simp [hi,smul_eq_mul] <;> ring
  simp_rw [hcoord]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  calc
    _ ≤ ∏ _l ∈ S, reuseRho := by
      apply Finset.prod_le_prod₀
      · intro i _
        have he := Real.exp_pos (-1)
        have h0 := (θ i).2.1
        have h1 := (θ i).2.2
        positivity
      · intro i _
        have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        have ht := hθ i
        dsimp [reuseRho]
        nlinarith
    _ = reuseRho^S.card := by simp

/-- Geometric void control without independence of the bootstrap occupancies. -/
theorem reuse_retained_void_bound {n : ℕ} (hn : 0 < n)
    (θ : Fin n → unitInterval) (hθ : ∀ i, (1/4 : ℝ) ≤ θ i) (S : Finset (Fin n)) :
    mean (ReuseResponseLaw θ) (fun r => mean (UniformResampling n)
      (fun a => if reuseNoRetained S r a then 1 else 0)) ≤ reuseRho^S.card := by
  have hpoint (r : Fin n → Bool) :
      mean (UniformResampling n) (fun a => if reuseNoRetained S r a then 1 else 0) ≤
        ∏ l ∈ S, if r l then Real.exp (-1) else 1 := by
    simp_rw [reuse_no_retained_iff]
    exact (reuse_uniform_avoid_le_exp hn _).trans_eq (reuse_filter_exponential S r)
  exact (integral_mono (μ := ReuseResponseLaw θ)
    Integrable.of_finite Integrable.of_finite hpoint).trans
      (reuse_response_exponential_bound θ hθ S)

/-- The original sample's response-free intervals obey the same geometric bound. -/
theorem reuse_original_void_bound {n : ℕ} (θ : Fin n → unitInterval)
    (hθ : ∀ i, (1/4 : ℝ) ≤ θ i) (S : Finset (Fin n)) :
    mean (ReuseResponseLaw θ) (fun r => if reuseNoRetained S r id then 1 else 0) ≤
      reuseRho^S.card := by
  apply le_trans (integral_mono (μ := ReuseResponseLaw θ)
    Integrable.of_finite Integrable.of_finite (fun r => ?_))
    (reuse_response_exponential_bound θ hθ S)
  by_cases h : reuseNoRetained S r id
  · rw [if_pos h]
    have hprod : (∏ l ∈ S, if r l then Real.exp (-1) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro l hl
      have hr : r l ≠ true := fun hr => h l hl hr l rfl
      simp [hr]
    rw [hprod]
  · rw [if_neg h]
    exact Finset.prod_nonneg (fun l _ => by split_ifs <;> positivity)

/-- A parameterized square inequality supplies Hölder control of a dependent mask. -/
theorem reuse_masked_moment_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (P : Ω → Prop) (k : ℕ) {B t : ℝ} (ht : 0 < t)
    (hX : (∫ x, X x^(2*k) ∂μ) ≤ B)
    (hP : (∫ x, (if P x then (1 : ℝ) else 0) ∂μ) ≤ t^2) :
    (∫ x, (if P x then X x^k else 0) ∂μ) ≤ (B+1)*t/2 := by
  have hpoint (x : Ω) :
      2*t*(if P x then X x^k else 0) ≤
        t^2*X x^(2*k)+(if P x then 1 else 0) := by
    have hpow : X x^(2*k) = (X x^k)^2 := by rw [← pow_mul]; congr 1; omega
    by_cases hx : P x
    · simp only [if_pos hx,hpow]
      nlinarith [sq_nonneg (t*X x^k-1)]
    · simp only [if_neg hx,hpow,mul_zero,add_zero]
      positivity
  have hi := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hpoint
  simp only [integral_const_mul, integral_add (Integrable.of_finite) (Integrable.of_finite)] at hi
  have hmul := mul_le_mul_of_nonneg_left hX (sq_nonneg t)
  nlinarith

/-- Finite weighted Jensen, packaged as a moment bound for a sum. -/
theorem reuse_weighted_sum_moment {Ω I : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (w : I → ℝ) (k : ℕ) {B : ℝ}
    (hX : ∀ i x, 0 ≤ X i x) (hw : ∀ i, 0 < w i)
    (hS : 0 < ∑ i, w i) (hm : ∀ i, (∫ x, X i x^k ∂μ) ≤ B*(w i)^k) :
    (∫ x, (∑ i, X i x)^k ∂μ) ≤ B*(∑ i, w i)^k := by
  let S : ℝ := ∑ i, w i
  have hS' : 0 < S := hS
  have hnorm : (∑ i, w i/S) = 1 := by rw [← Finset.sum_div]; exact div_self hS'.ne'
  have hpoint (x : Ω) : ((∑ i, X i x)/S)^k ≤
      ∑ i, (w i/S)*((X i x/w i)^k) := by
    have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
      (fun i => w i/S) (fun i => X i x/w i)
      (fun i _ => div_nonneg (hw i).le hS'.le) hnorm
      (fun i _ => div_nonneg (hX i x) (hw i).le) k
    have heq : (∑ i, (w i/S)*(X i x/w i)) = (∑ i, X i x)/S := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hw i).ne']
    rwa [heq] at h
  have hi := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hpoint
  simp only [div_pow, integral_div,
    integral_finsetSum _ (fun _ _ => Integrable.of_finite), integral_const_mul] at hi
  have hb : (∑ i, w i/S*((∫ x, X i x^k ∂μ)/(w i)^k)) ≤ B := by
    calc
      _ ≤ ∑ i, w i/S*B := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (hw i).le hS'.le)
        exact (div_le_iff₀ (pow_pos (hw i) k)).mpr (hm i)
      _ = B := by rw [← Finset.sum_mul,hnorm,one_mul]
  exact (div_le_iff₀ (pow_pos hS' k)).mp (hi.trans hb)

end AronowAudit.P001.TailA
