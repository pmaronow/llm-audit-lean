import SAP.P011c.WH.W2.Leaves
import AronowAudit.P011.P011_HomoskedasticCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c.WH.W2.P.T36_L1

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

private theorem row_bound_model {n : ℕ} (hn : 0 < n)
    (m : AronowAudit.P011.Model n) (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hdep : AronowAudit.P011.Dependency m)
    (hbound : ∀ᵐ y ∂m.law, ∀ i,
      |AronowAudit.P011.weighted m y i - AronowAudit.P011.beta m| ≤ c1)
    (hdegree : ∀ i, (AronowAudit.P011.degree m.G i : ℝ) ≤ c2)
    (hhom : AronowAudit.P011.Homoskedastic m)
    (ε : ℝ) (hε : 0 < ε) :
    AronowAudit.P011.probability m
      {y | (n : ℝ) *
        (AronowAudit.P011.var m (AronowAudit.P011.betaHat m) -
          AronowAudit.P011.V2 m.G (AronowAudit.P011.weighted m y)) > ε} ≤
      4 * (1 + c2)^3 * c1^4 / ((n : ℝ) * ε^2) := by
  let d : ℝ := 1 + c2
  let : IsProbabilityMeasure m.law := m.probability
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < d := by dsimp [d]; linarith
  have hddegree (i : Fin n) :
      (AronowAudit.P011.degree m.G i : ℝ) + 1 ≤ d := by
    dsimp [d]
    linarith [hdegree i]
  have hL2 := AronowAudit.P011.ProbabilityCompletion.weighted_memLp m c1 hbound
  have hR := AronowAudit.P011.HomoskedasticCompletion.remainder_memLp_two hn m c1 hbound
  have hRsecond := AronowAudit.P011.HomoskedasticCompletion.remainder_second_bound
    hn m c1 d hc1.le hdep hbound hddegree

  have hAdj (i j : Fin n) : 0 ≤ AronowAudit.P011.adjacency m.G i j := by
    unfold AronowAudit.P011.adjacency
    split_ifs <;> norm_num
  have hDegreeSum :
      (∑ i, ∑ j, AronowAudit.P011.adjacency m.G i j) ≤ (n : ℝ) * c2 := by
    calc
      _ ≤ ∑ i : Fin n, c2 := Finset.sum_le_sum (fun i _ => by
        rw [← AronowAudit.P011.degree_row_sum]
        exact hdegree i)
      _ = _ := by simp [nsmul_eq_mul]
  have hAdjSumNonneg :
      0 ≤ ∑ i, ∑ j, AronowAudit.P011.adjacency m.G i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hAdj i j))
  have hGFactor :
      1 ≤ AronowAudit.P011.gFactor m ∧ AronowAudit.P011.gFactor m ≤ d := by
    unfold AronowAudit.P011.gFactor
    constructor
    · have hdiv := div_nonneg hAdjSumNonneg (le_of_lt hnR)
      linarith
    · have hdiv :
        (∑ i, ∑ j, AronowAudit.P011.adjacency m.G i j) / (n : ℝ) ≤ c2 :=
          (div_le_iff₀ hnR).mpr (by simpa [mul_comm] using hDegreeSum)
      dsimp [d]
      linarith

  have hCorr := AronowAudit.P011.pairwise_correlation_repair
    hn m hdep hhom hL2
  have hσ : 0 ≤ AronowAudit.P011.meanVariance m :=
    AronowAudit.P011.CorrelationCompletion.meanVariance_nonneg hn m hhom hL2
  have hCorrSum :
      (∑ i, ∑ j, AronowAudit.P011.adjacency m.G i j *
        AronowAudit.P011.rho m i j) ≤
      ∑ i, ∑ j, AronowAudit.P011.adjacency m.G i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hCorr.2.1 i j) (hAdj i j)
  have hTrue :
      (n : ℝ) * AronowAudit.P011.var m (AronowAudit.P011.betaHat m) ≤
        AronowAudit.P011.meanVariance m * AronowAudit.P011.gFactor m := by
    rw [hCorr.1]
    apply mul_le_mul_of_nonneg_left _ hσ
    unfold AronowAudit.P011.gFactor
    linarith [div_le_div_of_nonneg_right hCorrSum (le_of_lt hnR)]

  have hScaled (y : Fin n → ℝ) :
      (n : ℝ) * AronowAudit.P011.V2 m.G (AronowAudit.P011.weighted m y) =
        AronowAudit.P011.gFactor m *
          AronowAudit.P011.sampleVariance (AronowAudit.P011.weighted m y) := by
    unfold AronowAudit.P011.V2 AronowAudit.P011.gFactor
    field_simp <;> ring
  have hSpread : 0 ≤ AronowAudit.P011.meanSpread m := by
    unfold AronowAudit.P011.meanSpread
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (le_of_lt hnR)
  have hPoint (y : Fin n → ℝ) :
      (n : ℝ) * AronowAudit.P011.var m (AronowAudit.P011.betaHat m) -
        (n : ℝ) * AronowAudit.P011.V2 m.G (AronowAudit.P011.weighted m y) ≤
          d * |AronowAudit.P011.varianceRemainder m y| := by
    rw [hScaled y]
    have hRdef :
        AronowAudit.P011.sampleVariance (AronowAudit.P011.weighted m y) =
          AronowAudit.P011.meanVariance m + AronowAudit.P011.meanSpread m +
            AronowAudit.P011.varianceRemainder m y := by
      unfold AronowAudit.P011.varianceRemainder
      ring
    rw [hRdef]
    have hg0 : 0 ≤ AronowAudit.P011.gFactor m :=
      le_trans (by norm_num) hGFactor.1
    have h1 := mul_nonneg hg0 hSpread
    have h2 := mul_le_mul_of_nonneg_left
      (neg_le_abs (AronowAudit.P011.varianceRemainder m y)) hg0
    have h3 := mul_le_mul_of_nonneg_right hGFactor.2
      (abs_nonneg (AronowAudit.P011.varianceRemainder m y))
    nlinarith [hTrue]

  have hsub :
      {y | (n : ℝ) *
        (AronowAudit.P011.var m (AronowAudit.P011.betaHat m) -
          AronowAudit.P011.V2 m.G (AronowAudit.P011.weighted m y)) > ε} ⊆
      {y | |AronowAudit.P011.varianceRemainder m y| > ε / d} := by
    intro y hy
    change ε < (n : ℝ) *
      (AronowAudit.P011.var m (AronowAudit.P011.betaHat m) -
        AronowAudit.P011.V2 m.G (AronowAudit.P011.weighted m y)) at hy
    change ε / d < |AronowAudit.P011.varianceRemainder m y|
    apply (div_lt_iff₀ hd).mpr
    nlinarith [hPoint y]
  calc
    _ ≤ m.law.real {y | |AronowAudit.P011.varianceRemainder m y| > ε / d} :=
      MeasureTheory.measureReal_mono (μ := m.law) hsub (measure_ne_top _ _)
    _ ≤ (∫ y, (AronowAudit.P011.varianceRemainder m y)^2 ∂m.law) / (ε / d)^2 :=
      AronowAudit.P011.HomoskedasticCompletion.second_moment_tail
        m.law _ hR _ (div_pos hε hd)
    _ ≤ (4 * d * c1^4 / (n : ℝ)) / (ε / d)^2 :=
      div_le_div_of_nonneg_right hRsecond (sq_nonneg _)
    _ = 4 * (1 + c2)^3 * c1^4 / ((n : ℝ) * ε^2) := by
      have hdne : d ≠ 0 := ne_of_gt hd
      have hεne : ε ≠ 0 := ne_of_gt hε
      dsimp [d]
      field_simp <;> ring

private theorem row_bound {n : ℕ} (hn : 0 < n)
    (m : SAP.P011c.Model n) (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hdep : SAP.P011c.Dependency m)
    (hbound : ∀ᵐ y ∂m.law, ∀ i,
      |SAP.P011c.weighted m y i - SAP.P011c.beta m| ≤ c1)
    (hdegree : ∀ i, (SAP.P011c.degree m.G i : ℝ) ≤ c2)
    (hhom : SAP.P011c.Homoskedastic m)
    (ε : ℝ) (hε : 0 < ε) :
    SAP.P011c.probability m
      {y | (n : ℝ) *
        (SAP.P011c.var m (SAP.P011c.betaHat m) -
          SAP.P011c.V2 m.G (SAP.P011c.weighted m y)) > ε} ≤
      4 * (1 + c2)^3 * c1^4 / ((n : ℝ) * ε^2) := by
  let m' := SAP.P011c.Bridge.toModel m
  have hdep' : AronowAudit.P011.Dependency m' := by
    simpa only [m', SAP.P011c.Bridge.toModel,
      SAP.P011c.Dependency, SAP.P011c.VariableDependency,
      AronowAudit.P011.Dependency, AronowAudit.P011.VariableDependency] using hdep
  have hbound' : ∀ᵐ y ∂m'.law, ∀ i,
      |AronowAudit.P011.weighted m' y i - AronowAudit.P011.beta m'| ≤ c1 := by
    filter_upwards [hbound] with y hy
    intro i
    simpa only [m', SAP.P011c.Bridge.weighted_eq, SAP.P011c.Bridge.beta_eq,
      SAP.P011c.Bridge.toModel] using hy i
  have hdegree' : ∀ i, (AronowAudit.P011.degree m'.G i : ℝ) ≤ c2 := by
    simpa only [m', SAP.P011c.Bridge.degree_eq, SAP.P011c.Bridge.toModel] using hdegree
  have hhom' : AronowAudit.P011.Homoskedastic m' :=
    (SAP.P011c.Bridge.homoskedastic_iff m).mp hhom
  have hrow := row_bound_model hn m' c1 c2 hc1 hc2 hdep' hbound' hdegree' hhom' ε hε
  simpa only [m', SAP.P011c.Bridge.toModel,
    SAP.P011c.probability, AronowAudit.P011.probability,
    SAP.P011c.Bridge.variance_eq, SAP.P011c.Bridge.betaHat_eq,
    SAP.P011c.Bridge.V2_eq, SAP.P011c.Bridge.weighted_eq] using hrow

end SAP.P011c.WH.W2.P.T36_L1

theorem SAP.P011c.WH.W2.T36_L1_proof : SAP.P011c.WH.W2.T36_L1 := by
  intro n hn m c1 c2 hc1 hc2 hdep hbound hdegree hhom ε hε
  exact SAP.P011c.WH.W2.P.T36_L1.row_bound
    hn m c1 c2 hc1 hc2 hdep hbound hdegree hhom ε hε
