import SAP.P011a.WH.W1.Leaves
import AronowAudit.P011.P011_HomoskedasticCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W1.P.T12_L1

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix Topology ENNReal
noncomputable section

theorem prove {n : ℕ} (hn : 0 < n) (m : SAP.P011a.Model n) (c d : ℝ)
    (_hc : 0 < c) (hd : 0 < d) (hdep : SAP.P011a.Dependency m)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |SAP.P011a.weighted m y i-SAP.P011a.beta m| ≤ c)
    (hdeg : ∀ i, (SAP.P011a.degree m.G i : ℝ) ≤ d)
    (hs : SAP.P011a.Homoskedastic m) :
    SAP.P011a.WholeHomoskedasticComparison m d := by
  let q := SAP.P011a.Bridge.model m
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdep' : AronowAudit.P011.Dependency q := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.Dependency, AronowAudit.P011.Dependency,
      SAP.P011a.VariableDependency, AronowAudit.P011.VariableDependency] using hdep
  have hs' : AronowAudit.P011.Homoskedastic q := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.Homoskedastic, AronowAudit.P011.Homoskedastic,
      SAP.P011a.covariance, AronowAudit.P011.covariance,
      SAP.P011a.expectation, AronowAudit.P011.expectation,
      SAP.P011a.weighted, AronowAudit.P011.weighted] using hs
  have hb' : ∀ᵐ y ∂q.law, ∀ i,
      |AronowAudit.P011.weighted q y i-AronowAudit.P011.beta q| ≤ c := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.weighted, AronowAudit.P011.weighted,
      SAP.P011a.beta, AronowAudit.P011.beta, SAP.P011a.expectation, AronowAudit.P011.expectation,
      SAP.P011a.betaHat, AronowAudit.P011.betaHat, SAP.P011a.average, AronowAudit.P011.average] using hb
  have hdeg' : ∀ i, (AronowAudit.P011.degree q.G i : ℝ) ≤ d := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.degree, AronowAudit.P011.degree] using hdeg
  have hL2 : ∀ i, MemLp (fun y => AronowAudit.P011.weighted q y i) 2 q.law :=
    fun i => AronowAudit.P011.ProbabilityCompletion.weighted_memLp q c hb' i
  have hcorr := AronowAudit.P011.pairwise_correlation_repair hn q hdep' hs' hL2
  have hσq : 0 ≤ AronowAudit.P011.meanVariance q :=
    AronowAudit.P011.CorrelationCompletion.meanVariance_nonneg hn q hs' hL2
  have hσ : 0 ≤ SAP.P011a.meanVariance m := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.meanVariance, AronowAudit.P011.meanVariance,
      SAP.P011a.covariance, AronowAudit.P011.covariance,
      SAP.P011a.expectation, AronowAudit.P011.expectation,
      SAP.P011a.weighted, AronowAudit.P011.weighted] using hσq
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hspread : 0 ≤ SAP.P011a.meanSpread m := by
    unfold SAP.P011a.meanSpread
    exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hnR.le
  have hadj (i j : Fin n) : 0 ≤ AronowAudit.P011.adjacency q.G i j := by
    unfold AronowAudit.P011.adjacency
    split_ifs <;> norm_num
  have hrhoSum :
      (∑ i, ∑ j, AronowAudit.P011.adjacency q.G i j * AronowAudit.P011.rho q i j) ≤
        ∑ i, ∑ j, AronowAudit.P011.adjacency q.G i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcorr.2.1 i j) (hadj i j)
  have hdegrees :
      (∑ i, ∑ j, AronowAudit.P011.adjacency q.G i j) ≤ (n : ℝ) * d := by
    calc
      _ = ∑ i, (AronowAudit.P011.degree q.G i : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← AronowAudit.P011.degree_row_sum]
      _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => hdeg' i
      _ = (n : ℝ) * d := by simp [mul_comm]
  have hgq : 1 ≤ AronowAudit.P011.gFactor q ∧ AronowAudit.P011.gFactor q ≤ 1+d := by
    constructor
    · unfold AronowAudit.P011.gFactor
      have hnonneg : 0 ≤ ∑ i, ∑ j, AronowAudit.P011.adjacency q.G i j :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hadj i j
      exact le_add_of_nonneg_right (div_nonneg hnonneg hnR.le)
    · unfold AronowAudit.P011.gFactor
      have hdiv := div_le_div_of_nonneg_right hdegrees hnR.le
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
      have heq : ((n : ℝ) * d) / (n : ℝ) = d := by field_simp
      rw [heq] at hdiv
      linarith
  have hg : 1 ≤ SAP.P011a.gFactor m ∧ SAP.P011a.gFactor m ≤ 1+d := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.gFactor, AronowAudit.P011.gFactor,
      SAP.P011a.adjacency, AronowAudit.P011.adjacency] using hgq
  have htrueq :
      (n : ℝ) * AronowAudit.P011.var q (AronowAudit.P011.betaHat q) ≤
        AronowAudit.P011.meanVariance q * AronowAudit.P011.gFactor q := by
    rw [hcorr.1]
    apply mul_le_mul_of_nonneg_left _ hσq
    unfold AronowAudit.P011.gFactor
    linarith [div_le_div_of_nonneg_right hrhoSum hnR.le]
  have htrue :
      (n : ℝ) * SAP.P011a.var m (SAP.P011a.betaHat m) ≤
        SAP.P011a.meanVariance m * SAP.P011a.gFactor m := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.var, AronowAudit.P011.var,
      SAP.P011a.betaHat, AronowAudit.P011.betaHat, SAP.P011a.average, AronowAudit.P011.average,
      SAP.P011a.expectation, AronowAudit.P011.expectation,
      SAP.P011a.meanVariance, AronowAudit.P011.meanVariance,
      SAP.P011a.covariance, AronowAudit.P011.covariance,
      SAP.P011a.weighted, AronowAudit.P011.weighted,
      SAP.P011a.adjacency, AronowAudit.P011.adjacency,
      SAP.P011a.gFactor, AronowAudit.P011.gFactor] using htrueq
  have hcovsumq :
      (n : ℝ) * AronowAudit.P011.var q (AronowAudit.P011.betaHat q) =
        AronowAudit.P011.QuadraticCompletion.total (AronowAudit.P011.covariance q) / (n : ℝ) := by
    rw [AronowAudit.P011.QuadraticCompletion.beta_variance q hL2]
    field_simp
  have hcovsum :
      (n : ℝ) * SAP.P011a.var m (SAP.P011a.betaHat m) =
        (∑ i, ∑ j, SAP.P011a.covariance m i j) / (n : ℝ) := by
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.var, AronowAudit.P011.var,
      SAP.P011a.betaHat, AronowAudit.P011.betaHat, SAP.P011a.average, AronowAudit.P011.average,
      SAP.P011a.expectation, AronowAudit.P011.expectation,
      SAP.P011a.covariance, AronowAudit.P011.covariance,
      SAP.P011a.weighted, AronowAudit.P011.weighted,
      AronowAudit.P011.QuadraticCompletion.total] using hcovsumq
  refine ⟨?_, hspread, hcovsum, htrue, hg.1, hg.2, ?_⟩
  · intro i
    simpa [q, SAP.P011a.Bridge.model, SAP.P011a.meanVariance, AronowAudit.P011.meanVariance,
      SAP.P011a.covariance, AronowAudit.P011.covariance,
      SAP.P011a.expectation, AronowAudit.P011.expectation,
      SAP.P011a.weighted, AronowAudit.P011.weighted] using
      (AronowAudit.P011.CorrelationCompletion.common_variance hn q hs' i)
  · intro y
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold SAP.P011a.V2 SAP.P011a.gFactor
      field_simp
    · rw [show (n : ℝ) * SAP.P011a.V2 m.G (SAP.P011a.weighted m y) =
        SAP.P011a.gFactor m * SAP.P011a.sampleVariance (SAP.P011a.weighted m y) from ?_]
      · nlinarith [htrue]
      · unfold SAP.P011a.V2 SAP.P011a.gFactor
        field_simp
    · unfold SAP.P011a.varianceRemainder
      ring
    · have hg0 : 0 ≤ SAP.P011a.gFactor m := by linarith [hg.1]
      have h1 := mul_nonneg hg0 hspread
      have h2 := mul_le_mul_of_nonneg_left
        (neg_le_abs (SAP.P011a.varianceRemainder m y)) hg0
      have h3 := mul_le_mul_of_nonneg_right hg.2
        (abs_nonneg (SAP.P011a.varianceRemainder m y))
      nlinarith

end
end SAP.P011a.WH.W1.P.T12_L1

theorem SAP.P011a.WH.W1.T12_L1_proof : SAP.P011a.WH.W1.T12_L1 := by
  intro n hn m c d hc hd hdep hb hdeg hs
  exact SAP.P011a.WH.W1.P.T12_L1.prove hn m c d hc hd hdep hb hdeg hs
