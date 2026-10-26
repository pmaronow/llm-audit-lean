import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace AronowAudit.P037
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Tables S6/S7 notes, SI pp. 41--42: "weights to each school drawn
from the standard uniform distribution". One direct multiplier has the
Lebesgue probability law restricted to (0,1), whose length is one. -/
noncomputable def unitUniformLaw : Measure ℝ := volume.restrict (Ioo 0 1)

/-- Normalized school probability weights: p_i=w_i/sum_j w_j.
Raw direct uniform weights are the interpretation of the table notes;
normalized exponential weights implement the correction. -/
noncomputable def normalizeWeights {n : ℕ} (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i / ∑ j, w j

/-- P037-T5(a), Bayesian-bootstrap definition (after Rubin):
the open simplex in n-1 free coordinates, with all masses positive. -/
def openProbabilitySimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i < 1}

/-- Append the last simplex coordinate, 1-sum of the free coordinates.
This uses m coordinates for m+1 school masses; the last is not discarded. -/
noncomputable def completeSimplex (m : ℕ) (p : Fin m → ℝ) : Fin (m+1) → ℝ :=
  fun i => if hi : i.val < m then p ⟨i.val, hi⟩ else 1 - ∑ j, p j

/-- P037-T5(a): Dirichlet(1,...,1) on m+1 school masses is the uniform
simplex law, density m! with respect to its m free coordinates. Unlike a
zero measure, this is the actual Lebesgue simplex measure and density. -/
noncomputable def bayesianBootstrapLaw (m : ℕ) : Measure (Fin (m+1) → ℝ) :=
  Measure.map (completeSimplex m)
    ((m.factorial : ℝ≥0∞) • (volume.restrict (openProbabilitySimplex m)))

/-- P037-T4's full direct-uniform weighting law for n+2 schools. Product
measure gives independent school multipliers; map gives their normalization. -/
noncomputable def normalizedUniformLaw (n : ℕ) : Measure (Fin (n+2) → ℝ) :=
  Measure.map normalizeWeights
    (Measure.pi (fun _ : Fin (n+2) => unitUniformLaw))

/-- P037-T5(b): independently normalized Exp(1) school multipliers.
Mathlib's expMeasure is the nondegenerate standard exponential measure. -/
noncomputable def normalizedExponentialLaw (n : ℕ) : Measure (Fin (n+2) → ℝ) :=
  Measure.map normalizeWeights
    (Measure.pi (fun _ : Fin (n+2) => ProbabilityTheory.expMeasure 1))

/-- P037-T4's witnessing event A={p:p_1/(p_1+p_2)<1/4}, valid for every
school sample size n+2 ≥ 2, including 49 and 56. Indexing starts at zero. -/
def bootstrapWitnessEvent (n : ℕ) : Set (Fin (n+2) → ℝ) :=
  {p | p 0 / (p 0 + p 1) < 1/4}

/-- P037-T4(i),(ii), finite algebra: normalization cancels in the event,
and the unnormalized ratio is <1/4 exactly when the first draw is < the
second / 3. Positive draws ensure every denominator is nonzero. -/
theorem bootstrap_ratio_cancellation (u v total : ℝ)
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < total) :
    (u/total)/(u/total+v/total) = u/(u+v) ∧
    (u/(u+v) < 1/4 ↔ u < v/3) := by
  have hs : 0 < u+v := by linarith
  constructor
  · field_simp
  · rw [div_lt_iff₀ hs]
    constructor <;> intro h <;> linarith

/-- P037-T4(i): the area of {0<u<v/3<1} in the unit square is 1/6.
This theorem evaluates the reduced integral. -/
theorem uniform_witness_integral :
    (∫ v : ℝ in (0:ℝ)..1, ∫ u : ℝ in (0:ℝ)..(v/3), (1:ℝ)) = 1/6 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
  rw [intervalIntegral.integral_div]
  norm_num

/-- P037-T4(ii): the two exponential tail integrals in the event calculation
are exactly 1 and 3/4, hence their difference is 1/4.
No approximation or numerical quadrature enters this certificate. -/
theorem exponential_witness_integrals :
    (∫ v : ℝ in Ioi 0, Real.exp (-v)) = 1 ∧
    (∫ v : ℝ in Ioi 0, Real.exp (-(4/3)*v)) = 3/4 ∧
    (1:ℝ)-3/4 = 1/4 ∧ (1/6:ℝ) ≠ 1/4 ∧ (1/6:ℝ)-1/4 = -1/12 := by
  refine ⟨integral_exp_neg_Ioi_zero, ?_, by norm_num⟩
  rw [integral_exp_mul_Ioi (by norm_num : (-(4/3):ℝ) < 0)]
  norm_num


/-- P037-T5(b): the inverse-CDF construction -log(V) applied to a
uniform draw gives Exp(1); independence is preserved by coordinate maps. -/
theorem uniform_log_gives_exponential :
    Measure.map (fun v : ℝ => -Real.log v) unitUniformLaw =
      ProbabilityTheory.expMeasure 1 := by
  have hm : Measurable (fun v : ℝ => -Real.log v) := Real.measurable_log.neg
  letI : IsProbabilityMeasure unitUniformLaw := ⟨by
    norm_num [unitUniformLaw, Real.volume_Ioo]⟩
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (Measure.map (fun v : ℝ => -Real.log v) unitUniformLaw) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.eq_of_cdf
  ext x
  have hset : (fun v : ℝ => -Real.log v) ⁻¹' Iic x ∩ Ioo 0 1 =
      Ico (Real.exp (-x)) 1 := by
    ext v
    change ((-Real.log v ≤ x) ∧ (0 < v ∧ v < 1)) ↔
      (Real.exp (-x) ≤ v ∧ v < 1)
    constructor
    · rintro ⟨hlog,hv0,hv1⟩
      refine ⟨?_,hv1⟩
      have hh := Real.exp_le_exp.mpr (show -x ≤ Real.log v by linarith)
      simpa only [Real.exp_log hv0] using hh
    · rintro ⟨hev,hv1⟩
      have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hev
      have hlog : -x ≤ Real.log v := Real.exp_le_exp.mp (by
        simpa only [Real.exp_log hv0] using hev)
      exact ⟨by linarith,hv0,hv1⟩
  rw [ProbabilityTheory.cdf_eq_real, Measure.real_def, Measure.map_apply hm measurableSet_Iic,
    unitUniformLaw, Measure.restrict_apply (measurableSet_Iic.preimage hm), hset,
    Real.volume_Ico, ProbabilityTheory.cdf_expMeasure_eq (by norm_num)]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, one_mul, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  · rw [if_neg hx, ENNReal.ofReal_eq_zero.mpr, ENNReal.toReal_zero]
    simpa using (sub_nonpos.mpr (Real.one_le_exp_iff.mpr (by linarith : 0 ≤ -x)))

/-- P037-T5(b): marginalizing t^(n-1)e^(-t) yields the constant density
(n-1)! of the Bayesian bootstrap. Here n=m+1. -/
theorem simplex_gamma_integral (m : ℕ) :
    (∫ t : ℝ in Ioi 0, t^m*Real.exp (-t)) = m.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (m:ℝ)+1) (r := 1) (by positivity) (by norm_num)
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

/-- The weighted least-squares refit in Tables S6/S7, represented by
its exact normal equations. For positive weights and full column rank
the solution is unique and is (X'WX)^(-1)X'Wy. -/
def WeightedLeastSquares {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : I → K → ℝ) (y : I → ℝ) (b : K → ℝ) : Prop :=
  ∀ k, ∑ i, w i * X i k * (y i - ∑ l, X i l*b l) = 0

/-- P037-T4(iv): the weighted Gram matrix X' diag(w) X,
for the school-weighted refits described in SI pp. 41--42. -/
noncomputable def weightedGram {I K : Type*} [Fintype I]
    (w : I → ℝ) (X : Matrix I K ℝ) : Matrix K K ℝ :=
  fun k l => ∑ i, w i * X i k * X i l

/-- P037-T4(iv): X' diag(w) y. -/
noncomputable def weightedRhs {I K : Type*} [Fintype I]
    (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) : K → ℝ :=
  fun k => ∑ i, w i * X i k * y i

/-- P037-T4(iv): “b̂(w) = (X'WX)^(-1)X'Wy”.
This is the actual inverse-formula coefficient; positive weights and
full column rank are hypotheses of its scaling theorem. -/
noncomputable def weightedCoefficient {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) : K → ℝ :=
  (weightedGram w X)⁻¹.mulVec (weightedRhs w X y)

/-- P037-T4(iv), P037-T5(d): for positive school weights and a full
column-rank design matrix, a common positive scaling leaves the actual
inverse-formula WLS coefficient unchanged. It also preserves the normal
equations' solution set. -/
theorem weighted_least_squares_scale {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) (b : K → ℝ)
    (_hw : ∀ i, 0 < w i) (_hX : Function.Injective X.mulVec)
    (c : ℝ) (hc : 0 < c) :
    weightedCoefficient (fun i => c*w i) X y = weightedCoefficient w X y ∧
    (WeightedLeastSquares (fun i => c*w i) X y b ↔ WeightedLeastSquares w X y b) := by
  classical
  have hcancel : c ≠ 0 := ne_of_gt hc
  have hG : weightedGram (fun i => c*w i) X = c • weightedGram w X := by
    ext k l
    simp [weightedGram, Finset.mul_sum, mul_assoc]
  have hh : weightedRhs (fun i => c*w i) X y = c • weightedRhs w X y := by
    funext k
    simp [weightedRhs, Finset.mul_sum, mul_assoc]
  constructor
  · unfold weightedCoefficient
    rw [hG, hh]
    by_cases hdet : IsUnit (weightedGram w X).det
    · letI : Invertible c := invertibleOfNonzero hcancel
      rw [Matrix.inv_smul _ _ hdet, Matrix.smul_mulVec, Matrix.mulVec_smul,
        smul_smul]
      simp
    · have hz : (weightedGram w X).det = 0 := by
        simpa only [isUnit_iff_ne_zero, not_not] using hdet
      have hscaled : ¬ IsUnit (c • weightedGram w X).det := by
        simp [Matrix.det_smul, hz]
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
        Matrix.nonsing_inv_apply_not_isUnit _ hdet]
      simp
  · unfold WeightedLeastSquares
    simp only [mul_assoc, ← Finset.mul_sum, mul_eq_zero, hcancel, false_or]

end AronowAudit.P037

