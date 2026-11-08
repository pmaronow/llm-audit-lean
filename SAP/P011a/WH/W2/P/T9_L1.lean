import SAP.P011a.WH.W2.Leaves
import AronowAudit.P011.Wave1.Gap.GP011B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2.P.T9_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

end
end SAP.P011a.WH.W2.P.T9_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

theorem SAP.P011a.WH.W2.T9_L1_proof : SAP.P011a.WH.W2.T9_L1 := by
  classical
  intro F c1 c2 c3 c4 h a B hB hb
  let m' : ∀ k, AronowAudit.P011.Model (F.size k) :=
    fun k => SAP.P011a.Bridge.model (F.model k)
  let : ∀ k, IsProbabilityMeasure (m' k).law := fun k => (m' k).probability
  have hparts := h
  rcases hparts with ⟨hc1, hc2, hc3, hc4, hdep, hbound, hdegree, hscaled, htheta⟩
  have hdep' (k : ℕ) : AronowAudit.P011.Dependency (m' k) := by
    convert hdep k using 1; rfl
  have hbound' (k : ℕ) : ∀ᵐ y ∂(m' k).law, ∀ i,
      |AronowAudit.P011.weighted (m' k) y i - a k i| ≤ B := by
    convert hb k using 1 <;> rfl
  let d : ℕ := Nat.ceil c2 + 1
  have hdeg (k : ℕ) (i : Fin (F.size k)) :
      AronowAudit.P011.degree (m' k).G i + 1 ≤ d := by
    dsimp [d]
    have hx := hdegree k i
    change (AronowAudit.P011.degree (m' k).G i : ℝ) ≤ c2 at hx
    exact Nat.add_le_add_right (by exact_mod_cast hx.trans (Nat.le_ceil c2)) 1
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    AronowAudit.P011.ProbabilityCompletion.weighted_memLp
      (m' k) c1 (by convert hbound k using 1 <;> rfl) i
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hQ2 (k : ℕ) : MemLp
      (fun y => AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y /
        (F.size k : ℝ)) 2 (m' k).law := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (AronowAudit.P011.Wave1.msr_Q_memLp2 (m' k) (a k) B
        (hbound' k)).const_mul ((F.size k : ℝ)⁻¹)
  have hv : Tendsto (fun k => ProbabilityTheory.variance
      (fun y => AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y /
        (F.size k : ℝ)) (m' k).law) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => ProbabilityTheory.variance_nonneg _ _)
      (fun k => AronowAudit.P011.Wave1.msr_normalized_variance
        (F.positive k) (m' k) (a k) (hdep' k) B hB (hbound' k) d (hdeg k))
    exact hN.const_div_atTop _
  have hcp := AronowAudit.P011.OracleCompletion.rowCP_of_variance
    (fun k => (m' k).law)
    (fun k y => AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y /
      (F.size k : ℝ)) hQ2 hv
  have he (k : ℕ) : AronowAudit.P011.expectation (m' k)
      (fun y => AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y /
        (F.size k : ℝ)) =
      (F.size k : ℝ) * AronowAudit.P011.var (m' k)
        (AronowAudit.P011.betaHat (m' k)) +
        AronowAudit.P011.quadratic (AronowAudit.P011.oracleMatrix (m' k).G)
          (fun i => AronowAudit.P011.expectation (m' k)
            (fun y => AronowAudit.P011.weighted (m' k) y i) - a k i) /
          (F.size k : ℝ) :=
    AronowAudit.P011.Wave1.msr_normalized_expectation
      (F.positive k) (m' k) (a k) (hdep' k) (hL2 k)
  have hT (k : ℕ) (y : Fin (F.size k) → ℝ) :
      SAP.P011a.quadratic (SAP.P011a.oracleMatrix (F.model k).G)
        (SAP.P011a.weighted (F.model k) y - a k) / (F.size k : ℝ) =
      AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y / (F.size k : ℝ) := by
    rfl
  have hCenter (k : ℕ) :
      SAP.P011a.scaledTrue F k +
        SAP.P011a.quadratic (SAP.P011a.oracleMatrix (F.model k).G)
          (fun i => SAP.P011a.expectation (F.model k)
            (fun y => SAP.P011a.weighted (F.model k) y i) - a k i) /
          (F.size k : ℝ) =
        ∫ y, AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y /
          (F.size k : ℝ) ∂(m' k).law := by
    calc
      _ = (F.size k : ℝ) * AronowAudit.P011.var (m' k)
          (AronowAudit.P011.betaHat (m' k)) +
          AronowAudit.P011.quadratic (AronowAudit.P011.oracleMatrix (m' k).G)
            (fun i => AronowAudit.P011.expectation (m' k)
              (fun y => AronowAudit.P011.weighted (m' k) y i) - a k i) /
            (F.size k : ℝ) := by rfl
      _ = AronowAudit.P011.expectation (m' k)
          (fun y => AronowAudit.P011.Wave1.msr_Q (m' k) (a k) y /
            (F.size k : ℝ)) := (he k).symm
      _ = _ := rfl
  have hgoal := hcp
  intro ε hε
  have hh := hgoal ε hε
  have hEvent (k : ℕ) :
      {y | |SAP.P011a.quadratic (SAP.P011a.oracleMatrix (F.model k).G)
          (SAP.P011a.weighted (F.model k) y - a k) / (F.size k : ℝ) -
        (SAP.P011a.scaledTrue F k +
          SAP.P011a.quadratic (SAP.P011a.oracleMatrix (F.model k).G)
            (fun i => SAP.P011a.expectation (F.model k)
              (fun y => SAP.P011a.weighted (F.model k) y i) - a k i) /
            (F.size k : ℝ))| > ε} =
      {ω | |AronowAudit.P011.Wave1.msr_Q (m' k) (a k) ω /
          (F.size k : ℝ) -
        ∫ z, AronowAudit.P011.Wave1.msr_Q (m' k) (a k) z /
          (F.size k : ℝ) ∂(m' k).law| > ε} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [hT k y, hCenter k]
  have hSeq :
      (fun k => SAP.P011a.probability (F.model k)
        {y | |SAP.P011a.quadratic (SAP.P011a.oracleMatrix (F.model k).G)
            (SAP.P011a.weighted (F.model k) y - a k) / (F.size k : ℝ) -
          (SAP.P011a.scaledTrue F k +
            SAP.P011a.quadratic (SAP.P011a.oracleMatrix (F.model k).G)
              (fun i => SAP.P011a.expectation (F.model k)
                (fun y => SAP.P011a.weighted (F.model k) y i) - a k i) /
              (F.size k : ℝ))| > ε}) =
      (fun k => (m' k).law.real
        {ω | |AronowAudit.P011.Wave1.msr_Q (m' k) (a k) ω /
            (F.size k : ℝ) -
          ∫ z, AronowAudit.P011.Wave1.msr_Q (m' k) (a k) z /
            (F.size k : ℝ) ∂(m' k).law| > ε}) := by
    funext k
    change (F.model k).law.real _ = (m' k).law.real _
    rw [hEvent k]
    rfl
  rw [hSeq]
  exact hh

