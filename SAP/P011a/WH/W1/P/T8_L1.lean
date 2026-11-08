import SAP.P011a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P011a.WH.W1.P.T8_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section

end
end SAP.P011a.WH.W1.P.T8_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section

theorem SAP.P011a.WH.W1.T8_L1_proof : SAP.P011a.WH.W1.T8_L1 := by
  intro hq F c1 c2 c3 c4 h hlim
  classical
  let M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ :=
    fun k => oracleMatrix (F.model k).G
  have hmat (k : ℕ) : M k =
      AronowAudit.P011.oracleMatrix (Bridge.model (F.model k)).G := by
    ext i j
    simp [M, Bridge.model, oracleMatrix, adjacency,
      AronowAudit.P011.oracleMatrix, AronowAudit.P011.adjacency]
  have hdegreeEq (k : ℕ) (i : Fin (F.size k)) :
      AronowAudit.P011.degree (Bridge.model (F.model k)).G i = degree (F.model k).G i := by
    rfl
  have hsym (k : ℕ) (i j : Fin (F.size k)) : M k i j = M k j i := by
    rw [hmat k]
    exact AronowAudit.P011.SpectralConfidence.oracle_symmetric
      (Bridge.model (F.model k)).G i j
  have hnorm (k : ℕ) : operatorNorm (M k) ≤ 1+c2 := by
    have hs : ((Finset.univ.sup (fun i => degree (F.model k).G i) : ℕ) : ℝ) ≤ c2 := by
      obtain ⟨i, hi⟩ := Finset.exists_mem_eq_sup
        (s := (Finset.univ : Finset (Fin (F.size k))))
        (f := fun i => degree (F.model k).G i)
        (by exact ⟨⟨0, F.positive k⟩, Finset.mem_univ _⟩)
      rw [hi.2]
      exact h.degrees k i
    have ho := AronowAudit.P011.SpectralConfidence.oracle_operatorNorm_degree
      (Bridge.model (F.model k)).G
    have ho' : operatorNorm (M k) ≤
        1 + ((Finset.univ.sup (fun i => degree (F.model k).G i) : ℕ) : ℝ) := by
      rw [hmat k]
      change AronowAudit.P011.operatorNorm
          (AronowAudit.P011.oracleMatrix (Bridge.model (F.model k)).G) ≤ _
      simpa only [hdegreeEq] using ho
    linarith
  have hvar := quadratic_variance F c1 c2 c3 c4 (1+c2) h M hsym hnorm
  have hkernel := hq F c1 c2 c3 c4 (1+c2) h M hsym hnorm hvar
  let μ : ∀ k, Measure (Fin (F.size k) → ℝ) := fun k => (F.model k).law
  letI (k : ℕ) : IsProbabilityMeasure (μ k) := by
    dsimp [μ]
    exact (F.model k).probability
  let X : ∀ k, (Fin (F.size k) → ℝ) → ℝ := fun k y =>
    scaledOracle F k y - scaledTrue F k
  let b : ℕ → ℝ := fun k => meanBias (F.model k)
  have hcentre (k : ℕ) :
      (Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)) +
        quadratic (M k) (delta (F.model k))) / (F.size k : ℝ) = b k := by
    simp [M, b, meanBias]
  have hstat (k : ℕ) (y : Fin (F.size k) → ℝ) :
      (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) -
          scaledTrue F k -
        ((Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)) +
          quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)) =
        X k y - b k := by
    rw [hcentre k]
    have hv1 : varianceForm (M k) (weighted (F.model k) y) =
        V1 (F.model k).G (weighted (F.model k) y) := by
      change AronowAudit.P011.varianceForm
          (AronowAudit.P011.oracleMatrix (Bridge.model (F.model k)).G)
          (AronowAudit.P011.weighted (Bridge.model (F.model k)) y) =
        AronowAudit.P011.V1 (Bridge.model (F.model k)).G
          (AronowAudit.P011.weighted (Bridge.model (F.model k)) y)
      exact AronowAudit.P011.variance_form_oracle
        (Bridge.model (F.model k)).G
        (AronowAudit.P011.weighted (Bridge.model (F.model k)) y)
    rw [hv1]
    dsimp [X, scaledOracle, scaledTrue, b]
  have hE : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => X k y - b k) 0 := by
    intro ε hε
    have hk : Tendsto
        (fun k => probability (F.model k)
          {y | abs ((F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) -
            scaledTrue F k -
            ((Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)) +
              quadratic (M k) (delta (F.model k))) / (F.size k : ℝ))) > ε})
        atTop (𝓝 0) := by
      simpa only [InProbability, probability] using hkernel.1 ε hε
    have hsets (k : ℕ) :
        {y | |X k y-b k-0| > ε} =
          {y | abs ((F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) -
            scaledTrue F k -
            ((Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)) +
              quadratic (M k) (delta (F.model k))) / (F.size k : ℝ))) > ε} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [← hstat k y]
      simp
    simpa only [AronowAudit.P011.CoverageCompletion.RowCP, μ, probability, hsets] using hk
  have hbnd (k : ℕ) : |b k| ≤ (1+c2)*c1^2 := by
    simpa [b] using bias_bound F c1 c2 c3 c4 h k
  have hBelow : IsBoundedUnder (· ≥ ·) atTop b := by
    refine ⟨-((1+c2)*c1^2), ?_⟩
    change ∀ᶠ k : ℕ in atTop, -((1+c2)*c1^2) ≤ b k
    exact Filter.Eventually.of_forall fun k : ℕ => (abs_le.mp (hbnd k)).1
  have hAbove : IsBoundedUnder (· ≤ ·) atTop b := by
    refine ⟨(1+c2)*c1^2, ?_⟩
    change ∀ᶠ k : ℕ in atTop, b k ≤ (1+c2)*c1^2
    exact Filter.Eventually.of_forall fun k : ℕ => (abs_le.mp (hbnd k)).2
  have hcentres := AronowAudit.P011.MeanCompletion.conservative_centres
    μ X b hE hBelow hAbove
  have hneg := hcentres.2 hlim
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      (F.size k : ℝ) *
        (var (F.model k) (betaHat (F.model k)) -
          V1 (F.model k).G (weighted (F.model k) y)) = -X k y := by
    dsimp [X, scaledOracle, scaledTrue]
    ring
  intro ε hε
  simpa only [Conservative, probability, μ, he] using hneg ε hε

