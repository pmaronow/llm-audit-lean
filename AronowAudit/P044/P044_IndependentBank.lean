import Mathlib.Probability.Distributions.Binomial
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
P044-T8(iv): the independent, with-replacement bank illustration.
The observed exposure and the simulated exposure count are genuine random
variables with Bernoulli and Binomial laws.  This is the illustrative independent
bank, distinct from the chapter package's duplicate-rejecting seed coupling.
-/
namespace AronowAudit.P044.IndependentBank

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

noncomputable section

/-- Actual joint probability law for an independent observed exposure and
an R-draw Binomial exposure count. -/
def jointLaw (R : ℕ) (p : unitInterval) : Measure (Bool × ℕ) :=
  (bernoulliMeasure true false p).prod (binomial R p)

instance (R : ℕ) (p : unitInterval) : IsProbabilityMeasure (jointLaw R p) := by
  unfold jointLaw
  infer_instance

/-- The returned add-one probability q=(C+1)/(R+1). -/
def smoothedWeight (R c : ℕ) : ℝ := ((c : ℝ) + 1) / ((R : ℝ) + 1)

/-- The actual observed inverse-weight term I(D=a)/q. -/
def weightedObservation (R : ℕ) (ω : Bool × ℕ) : ℝ :=
  (if ω.1 then 1 else 0) / smoothedWeight R ω.2


lemma reciprocal_binomial_moment (R : ℕ) (p : unitInterval) :
    (p : ℝ) * ((R : ℝ) + 1) *
        (∫ c : ℕ, 1 / ((c : ℝ) + 1) ∂binomial R p) =
      1 - (1 - (p : ℝ)) ^ (R + 1) := by
  rw [integral_binomial, ← Nat.range_succ_eq_Iic]
  simp only [smul_eq_mul, mul_one_div]
  have hterm (c : ℕ) :
      (p : ℝ) * ((R : ℝ) + 1) *
          ((R.choose c : ℝ) * (p : ℝ) ^ c * (1 - (p : ℝ)) ^ (R - c) /
            ((c : ℝ) + 1)) =
        (p : ℝ) ^ (c + 1) * (1 - (p : ℝ)) ^ ((R + 1) - (c + 1)) *
          ((R + 1).choose (c + 1) : ℝ) := by
    have hne : (c : ℝ) + 1 ≠ 0 := by positivity
    have hc : ((R : ℝ) + 1) * (R.choose c : ℝ) =
        ((R + 1).choose (c + 1) : ℝ) * ((c : ℝ) + 1) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq R c)
    have hcoeff : ((R : ℝ) + 1) * (R.choose c : ℝ) / ((c : ℝ) + 1) =
        ((R + 1).choose (c + 1) : ℝ) := (div_eq_iff hne).mpr hc
    calc
      _ = (((R : ℝ) + 1) * (R.choose c : ℝ) / ((c : ℝ) + 1)) *
          (p : ℝ) ^ c * (p : ℝ) * (1 - (p : ℝ)) ^ (R - c) := by ring
      _ = _ := by rw [hcoeff]; simp [pow_succ, Nat.add_sub_add_right]; ring
  have hs := add_pow (p : ℝ) (1 - (p : ℝ)) (R + 1)
  rw [Finset.sum_range_succ'] at hs
  have hpadd : (p : ℝ) + (1 - (p : ℝ)) = 1 := by ring
  rw [hpadd] at hs
  simp only [one_pow, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    one_mul, Nat.sub_zero] at hs
  rw [Finset.mul_sum]
  simp_rw [hterm]
  linarith

lemma weightedObservation_factor (R : ℕ) (ω : Bool × ℕ) :
    weightedObservation R ω =
      (if ω.1 then (1 : ℝ) else 0) * (((R : ℝ) + 1) / ((ω.2 : ℝ) + 1)) := by
  cases h : ω.1 <;> simp [weightedObservation, smoothedWeight, h]

lemma weightedObservation_integrable (R : ℕ) (p : unitInterval) :
    Integrable (weightedObservation R) (jointLaw R p) := by
  have heq : weightedObservation R = fun ω : Bool × ℕ =>
      (if ω.1 then (1 : ℝ) else 0) * (((R : ℝ) + 1) / ((ω.2 : ℝ) + 1)) :=
    funext (weightedObservation_factor R)
  rw [heq]
  exact (integrable_bernoulliMeasure true false p (fun b => if b then (1 : ℝ) else 0)).mul_prod
    (integrable_binomial (fun c : ℕ => ((R : ℝ) + 1) / ((c : ℝ) + 1)))

lemma weightedObservation_expectation (R : ℕ) (p : unitInterval) :
    (∫ ω, weightedObservation R ω ∂jointLaw R p) =
      1 - (1 - (p : ℝ)) ^ (R + 1) := by
  simp_rw [weightedObservation_factor]
  have hm := integral_prod_mul (μ := bernoulliMeasure true false p) (ν := binomial R p)
    (fun b : Bool => if b then (1 : ℝ) else 0)
    (fun c : ℕ => ((R : ℝ) + 1) / ((c : ℝ) + 1))
  rw [jointLaw, hm, integral_bernoulliMeasure]
  simp only [Bool.false_eq_true, ↓reduceIte, smul_eq_mul, mul_one, mul_zero, add_zero]
  simp_rw [div_eq_mul_inv]
  rw [integral_const_mul]
  have h := reciprocal_binomial_moment R p
  simpa only [one_div, mul_assoc] using h

/-- The complete probability-space statement, for arbitrary independent random
variables with the stipulated Bernoulli/Binomial laws, including integrability. -/
theorem independent_bank_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : ℕ) (p : unitInterval)
    (D : Ω → Bool) (C : Ω → ℕ)
    (hD : HasLaw D (bernoulliMeasure true false p) μ)
    (hC : HasLaw C (binomial R p) μ) (hDC : IndepFun D C μ)
    (_hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Integrable (fun ω => (if D ω then (1 : ℝ) else 0) /
      smoothedWeight R (C ω)) μ ∧
    (∫ ω, (if D ω then (1 : ℝ) else 0) / smoothedWeight R (C ω) ∂μ) =
      1 - (1 - (p : ℝ)) ^ (R + 1) ∧
    1 - (1 - (p : ℝ)) ^ (R + 1) < 1 := by
  have hpair : HasLaw (fun ω => (D ω, C ω)) (jointLaw R p) μ := hDC.hasLaw_prod hD hC
  refine ⟨hpair.integrable_comp (weightedObservation_integrable R p), ?_, ?_⟩
  · have heq := hpair.integral_comp (weightedObservation_integrable R p).aestronglyMeasurable
    exact heq.trans (weightedObservation_expectation R p)
  · have hpos : 0 < (1 - (p : ℝ)) ^ (R + 1) := by positivity
    linarith


end
end AronowAudit.P044.IndependentBank

