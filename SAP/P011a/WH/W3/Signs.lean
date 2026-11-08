import SAP.P011a.Defs.WholeW3
import SAP.P011a.WH.W3.Analytic
import SAP.P011a.Bridge
import AronowAudit.P011.P011_SignCompletion
import AronowAudit.P011.P011_MeanCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W3

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- The coordinate integral donor applied to a singleton indicator gives each
of the two sign probabilities exactly, with no appeal to numerical computation. -/
theorem sign_probability {n : ℕ} (i : Fin n) (t : ℝ) (ht : t = 1 ∨ t = -1) :
    probability (signModel n) {y | y i = t} = 1/2 := by
  let g : ℝ → ℝ := fun z => if z = t then 1 else 0
  have hg : Measurable g :=
    Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const
  have hi : expectation (signModel n) (fun y => g (y i)) =
      probability (signModel n) {y | y i = t} := by
    unfold expectation probability
    convert integral_indicator_one (μ := (signModel n).law)
      (measurableSet_eq_fun (measurable_pi_apply i) measurable_const) using 1
    congr 1
  have he : expectation (signModel n) (fun y => g (y i)) = (g (-1) + g 1)/2 :=
    AronowAudit.P011.DataMatrixCompletion.coord_integral i g hg
  rw [hi] at he
  rcases ht with rfl | rfl <;> norm_num [g] at he ⊢ <;> exact he

/-- Reuse the exact iid-sign moments, then combine the two existing probability
limits to exhibit a residual tending to one. Uniqueness of deterministic centers
rules out convergence of that residual to zero. -/
theorem sign_failure : WholeSignFailure := by
  have hs := Bridge.SignWitnessFacts_proved
  have hw : WholeScaling_W3 signFamily 1 1 1 2 := wholeScaling_of_scaling _ _ _ _ _ hs.1
  have hdep (k : ℕ) : Dependency (signFamily.model k) := hs.1.2.2.2.2.2.1 k
  have hmean {n : ℕ} (i : Fin n) :
      expectation (signModel n) (fun y => weighted (signModel n) y i) = 0 := by
    have he : expectation (signModel n) (fun y => y i) = ((-1 : ℝ) + 1)/2 :=
      AronowAudit.P011.DataMatrixCompletion.coord_integral i (fun z => z) measurable_id
    simpa [weighted, signModel] using he
  have hcov (k : ℕ) : covariance (signFamily.model k) = 1 := by
    ext i j
    exact AronowAudit.P011.DataMatrixCompletion.covariance_formula i j
  have hdelta (k : ℕ) : delta (signFamily.model k) = 0 := by
    ext i
    change expectation (signModel (k+1)) (fun y => weighted (signModel (k+1)) y i) -
      beta (signFamily.model k) = 0
    have hm : expectation (signModel (k+1)) (fun y => weighted (signModel (k+1)) y i) = 0 :=
      hmean i
    rw [hm, (hs.2.2 k).2, sub_zero]
  have hae (k : ℕ) : ∀ᵐ y ∂(signFamily.model k).law,
      Matrix.trace (dataMatrix y - 1) / (signFamily.size k : ℝ) =
        (1 - (signFamily.size k : ℝ)) / (signFamily.size k : ℝ) := by
    filter_upwards [AronowAudit.P011.DataMatrixCompletion.ae_signs (k+1)] with y hy
    have ht : Matrix.trace (dataMatrix y) = 1 :=
      (Bridge.DataDependentFailure_proved.1 (k+1) (Nat.succ_pos k) y hy).2.1
    rw [Matrix.trace_sub, ht, Matrix.trace_one, Fintype.card_fin]
  have hsize (k : ℕ) : (signFamily.size k : ℝ) = (k+1 : ℝ) := by simp [signFamily]
  have htrue (k : ℕ) : scaledTrue signFamily k = 1 := (hs.2.2 k).1
  have hdata := Bridge.DataDependentFailure_proved
  have hV : InProbability signFamily
      (fun k y => (signFamily.size k : ℝ)*varianceForm (dataMatrix y) y) (fun _ => 1) := by
    simpa only [InProbability, hsize, sub_zero] using hdata.2.1
  have hdiff : InProbability signFamily
      (fun k y => (signFamily.size k : ℝ)*varianceForm (dataMatrix y) y - scaledTrue signFamily k)
      (fun _ => 0) := by
    simpa only [InProbability, hsize, htrue] using hdata.2.1
  have hN : Tendsto (fun k => (signFamily.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp signFamily.grows
  have hbracket : Tendsto (fun k => (1 - (signFamily.size k : ℝ)) / (signFamily.size k : ℝ))
      atTop (𝓝 (-1)) := by
    have he (k : ℕ) : (1 - (signFamily.size k : ℝ)) / (signFamily.size k : ℝ) =
        (-1 : ℝ) + 1/(signFamily.size k : ℝ) := by
      have hn : (signFamily.size k : ℝ) ≠ 0 := by exact_mod_cast (signFamily.positive k).ne'
      field_simp; ring
    simp_rw [he]
    simpa using tendsto_const_nhds.add (hN.const_div_atTop 1)
  let μ := fun k => (signFamily.model k).law
  let (k : ℕ) : IsProbabilityMeasure (μ k) := (signFamily.model k).probability
  have hX : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => (signFamily.size k : ℝ)*varianceForm (dataMatrix y) y - 1) 0 := by
    simpa only [AronowAudit.P011.CoverageCompletion.RowCP, μ, InProbability, probability, hsize]
      using hdata.2.1
  have hY : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => Matrix.trace (dataMatrix y - 1)/(signFamily.size k : ℝ)) (-1) := by
    simpa only [AronowAudit.P011.CoverageCompletion.RowCP, μ, InProbability, probability, hsize]
      using hdata.2.2
  have hR : InProbability signFamily signExpansionResidual (fun _ => 1) := by
    have he := AronowAudit.P011.CoverageCompletion.rowCP_continuous_pair μ _ _ 0 (-1) hX hY
      (fun p : ℝ × ℝ => p.1 - p.2) (by fun_prop)
    simpa only [AronowAudit.P011.CoverageCompletion.RowCP, μ, InProbability, probability,
      signExpansionResidual, htrue, Prod.fst, Prod.snd, sub_neg_eq_add, zero_add] using he
  have hnot : ¬ InProbability signFamily signExpansionResidual (fun _ => 0) := by
    intro hzero
    have hz : AronowAudit.P011.CoverageCompletion.RowCP μ signExpansionResidual 0 := hzero
    have ho : AronowAudit.P011.CoverageCompletion.RowCP μ
        (fun k y => signExpansionResidual k y - 1) 0 := by
      simpa only [AronowAudit.P011.CoverageCompletion.RowCP, InProbability, probability, μ, sub_zero]
        using hR
    have hc := AronowAudit.P011.MeanCompletion.deterministic_centres μ signExpansionResidual
      (fun _ => 1) hz ho
    have hf : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hc
    norm_num at hf
  refine ⟨hw, hs.2.1, ?_, hV, hdiff, hbracket, hR, hnot⟩
  intro k
  exact ⟨htrue k, (hs.2.2 k).2, hdep k, hcov k, hdelta k,
    (fun i => ⟨sign_probability i 1 (Or.inl rfl), sign_probability i (-1) (Or.inr rfl)⟩), hae k⟩

end
end SAP.P011a.WH.W3
