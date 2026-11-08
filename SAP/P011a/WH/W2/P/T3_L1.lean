import SAP.P011a.WH.W2.Leaves
import AronowAudit.P011.P011_OracleCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset
open SAP.P011a SAP.P011a.WH.W2
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

theorem SAP.P011a.WH.W2.T3_L1_proof : SAP.P011a.WH.W2.T3_L1 := by
  intro F c1 c2 c3 c4 h
  classical
  rcases h with ⟨hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  let F' : AronowAudit.P011.Family := SAP.P011a.Bridge.family F
  have hDep' : ∀ k, AronowAudit.P011.Dependency (F'.model k) := by
    intro k
    change AronowAudit.P011.VariableDependency (F'.model k).law (F'.model k).G
      (fun i y => y i)
    intro S T hST hG
    exact hDep k S T hST hG
  have hBound' : ∀ k, ∀ᵐ y ∂(F'.model k).law, ∀ i,
      |AronowAudit.P011.weighted (F'.model k) y i - AronowAudit.P011.beta (F'.model k)| ≤ c1 := by
    intro k
    simpa [F', SAP.P011a.Bridge.family, SAP.P011a.Bridge.model,
      SAP.P011a.weighted, AronowAudit.P011.weighted,
      SAP.P011a.beta, AronowAudit.P011.beta,
      SAP.P011a.betaHat, AronowAudit.P011.betaHat,
      SAP.P011a.average, AronowAudit.P011.average,
      SAP.P011a.expectation, AronowAudit.P011.expectation] using hBound k
  have hDeg' : ∀ k i, (AronowAudit.P011.degree (F'.model k).G i : ℝ) ≤ c2 := by
    intro k i
    simpa [F', SAP.P011a.Bridge.family, SAP.P011a.Bridge.model,
      SAP.P011a.degree, AronowAudit.P011.degree] using hDeg k i
  have hVar' : Tendsto
      (fun k => (F'.size k : ℝ) * AronowAudit.P011.var (F'.model k)
        (AronowAudit.P011.betaHat (F'.model k))) atTop (𝓝 c3) := by
    change Tendsto (fun k => (F.size k : ℝ) * SAP.P011a.var (F.model k)
      (SAP.P011a.betaHat (F.model k))) atTop (𝓝 c3) at hVar
    change Tendsto (fun k => (F.size k : ℝ) * SAP.P011a.var (F.model k)
      (SAP.P011a.betaHat (F.model k))) atTop (𝓝 c3)
    exact hVar

  let (k : ℕ) : IsProbabilityMeasure (F'.model k).law := (F'.model k).probability
  let μ : ∀ k, Measure (Fin (F'.size k) → ℝ) := fun k => (F'.model k).law
  let D : ℕ := ⌈c2⌉₊ + 1
  have hD (k : ℕ) (i : Fin (F'.size k)) :
      AronowAudit.P011.degree (F'.model k).G i + 1 ≤ D := by
    dsimp [D]
    exact Nat.add_le_add_right
      (by exact_mod_cast (hDeg' k i).trans (Nat.le_ceil c2)) 1
  have hDR (k : ℕ) (i : Fin (F'.size k)) :
      (AronowAudit.P011.degree (F'.model k).G i : ℝ) + 1 ≤ (D : ℝ) := by
    exact_mod_cast hD k i
  have hL2 (k : ℕ) (i : Fin (F'.size k)) :=
    AronowAudit.P011.ProbabilityCompletion.weighted_memLp (F'.model k) c1 (hBound' k) i
  have hN : Tendsto (fun k => (F'.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F'.grows
  have hQ2 (k : ℕ) : MemLp
      (fun y => AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ))
      2 (F'.model k).law := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (AronowAudit.P011.OracleCompletion.Q_memLp2 (F'.model k) c1 (hBound' k)).const_mul
        ((F'.size k : ℝ)⁻¹)
  have hQV : Tendsto
      (fun k => ProbabilityTheory.variance
        (fun y => AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ))
        (F'.model k).law) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => ProbabilityTheory.variance_nonneg _ _)
      (fun k => AronowAudit.P011.OracleCompletion.normalized_Q_variance
        (F'.positive k) (F'.model k) c1 hc1.le (hDep' k) (hBound' k) D (hD k))
    exact hN.const_div_atTop _
  have hQ := AronowAudit.P011.OracleCompletion.rowCP_of_variance μ
    (fun k y => AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ))
    hQ2 hQV
  have hQB : ∀ ε > (0 : ℝ), Tendsto
      (fun k => (F'.model k).law.real {y |
        |AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ) -
          ((F'.size k : ℝ) * AronowAudit.P011.var (F'.model k)
            (AronowAudit.P011.betaHat (F'.model k)) +
            AronowAudit.P011.meanBias (F'.model k))| > ε}) atTop (𝓝 0) := by
    have hE (k : ℕ) :
        (∫ y, AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ)
            ∂(F'.model k).law) =
          (F'.size k : ℝ) * AronowAudit.P011.var (F'.model k)
            (AronowAudit.P011.betaHat (F'.model k)) +
            AronowAudit.P011.meanBias (F'.model k) :=
      AronowAudit.P011.OracleCompletion.normalized_Q_expectation
        (F'.positive k) (F'.model k) (hDep' k) (hL2 k)
    simpa only [μ, probability, hE] using hQ

  have hBV : Tendsto
      (fun k => ProbabilityTheory.variance (AronowAudit.P011.betaHat (F'.model k))
        (F'.model k).law) atTop (𝓝 0) := by
    have hv := hVar'.div_atTop hN
    have he (k : ℕ) :
        ((F'.size k : ℝ) * AronowAudit.P011.var (F'.model k)
          (AronowAudit.P011.betaHat (F'.model k))) / (F'.size k : ℝ) =
          ProbabilityTheory.variance (AronowAudit.P011.betaHat (F'.model k))
            (F'.model k).law := by
      rw [ProbabilityTheory.variance_eq_integral
        (AronowAudit.P011.ProbabilityCompletion.betaHat_measurable _).aemeasurable]
      change _ = AronowAudit.P011.var (F'.model k) (AronowAudit.P011.betaHat (F'.model k))
      have hn0 : (F'.size k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (F'.positive k)
      field_simp
    simpa only [he] using hv
  have hBC : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => AronowAudit.P011.betaHat (F'.model k) y - AronowAudit.P011.beta (F'.model k)) 0 := by
    simpa only [AronowAudit.P011.CoverageCompletion.RowCP, sub_zero,
      AronowAudit.P011.beta, AronowAudit.P011.expectation] using
      AronowAudit.P011.OracleCompletion.rowCP_of_variance μ
        (fun k => AronowAudit.P011.betaHat (F'.model k))
        (fun k => AronowAudit.P011.ProbabilityCompletion.betaHat_memLp _ (hL2 k)) hBV
  let B : ℝ → ℝ := fun a => (D : ℝ) * (2 * c1 * |a| + a ^ 2)
  have hBC' : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => B (AronowAudit.P011.betaHat (F'.model k) y -
        AronowAudit.P011.beta (F'.model k))) 0 := by
    have hh := AronowAudit.P011.CoverageCompletion.rowCP_continuous_pair μ
      (fun k y => AronowAudit.P011.betaHat (F'.model k) y - AronowAudit.P011.beta (F'.model k))
      (fun _ _ => (0 : ℝ)) 0 0 hBC
      (AronowAudit.P011.CoverageCompletion.rowCP_det _ (fun _ => (0 : ℝ)) 0 tendsto_const_nhds)
      (fun p : ℝ × ℝ => B p.1) (by dsimp [B]; fun_prop)
    simpa only [B, abs_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using hh
  have hE : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => (F'.size k : ℝ) * AronowAudit.P011.V1 (F'.model k).G
          (AronowAudit.P011.weighted (F'.model k) y) -
        AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ)) 0 := by
    apply AronowAudit.P011.OracleCompletion.rowCP_dominated μ _
      (fun k y => B (AronowAudit.P011.betaHat (F'.model k) y -
        AronowAudit.P011.beta (F'.model k))) hBC'
    intro k
    filter_upwards [hBound' k] with y hy
    exact AronowAudit.P011.OracleCompletion.sample_centering_bound
      (F'.positive k) (F'.model k) c1 D (hDR k) y hy
  have hFinal := AronowAudit.P011.OracleCompletion.row_moving_add_error
    μ
    (fun k y => AronowAudit.P011.OracleCompletion.Q (F'.model k) y / (F'.size k : ℝ))
    (fun k y => (F'.size k : ℝ) * AronowAudit.P011.V1 (F'.model k).G
      (AronowAudit.P011.weighted (F'.model k) y))
    (fun k => (F'.size k : ℝ) * AronowAudit.P011.var (F'.model k)
      (AronowAudit.P011.betaHat (F'.model k)) + AronowAudit.P011.meanBias (F'.model k))
    hQB hE
  intro ε hε
  have hh := hFinal ε hε
  simpa [μ, AronowAudit.P011.InProbability, AronowAudit.P011.probability,
    SAP.P011a.InProbability, SAP.P011a.probability,
    F', SAP.P011a.Bridge.family, SAP.P011a.Bridge.model,
    SAP.P011a.V1, AronowAudit.P011.V1,
    SAP.P011a.adjacency, AronowAudit.P011.adjacency,
    SAP.P011a.weighted, AronowAudit.P011.weighted,
    SAP.P011a.var, AronowAudit.P011.var,
    SAP.P011a.betaHat, AronowAudit.P011.betaHat,
    SAP.P011a.beta, AronowAudit.P011.beta,
    SAP.P011a.delta, AronowAudit.P011.delta,
    SAP.P011a.average, AronowAudit.P011.average,
    SAP.P011a.meanBias, AronowAudit.P011.meanBias,
    SAP.P011a.quadratic, AronowAudit.P011.quadratic,
    SAP.P011a.oracleMatrix, AronowAudit.P011.oracleMatrix,
    SAP.P011a.centered, AronowAudit.P011.centered,
    SAP.P011a.expectation, AronowAudit.P011.expectation] using hh

end
