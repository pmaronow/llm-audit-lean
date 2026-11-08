import SAP.P011b.WH.W2.Witness
import SAP.P011b.WH.W2.Residual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

/-- Root-n OLS rate for a deterministic sequence b_n, at fixed positive dimension.
Adapt Wave1.olsr_root_n_rate row by row: apply olsr_score_norm_moment with b k;
the resulting uniform moment constant is p*(c2+1)*(2*Bx*By)^2. Apply
olsr_tight_of_moment to the score divided by sqrt(n), then olsr_error_bound and
rrn_tight_dominated with constant 1/lam. All constants are independent of b k.
No coefficient-weight identity is needed for this rate. This is about 100 lines
of adaptation of the existing rate proof, not a new probability limit theorem. -/
def T16_L1 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
  ∀ (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : ℕ → Fin p → ℝ),
    0 < p → (∀ k, p ≤ F.size k) →
    (∀ k, ((D k)ᵀ * D k).det ≠ 0) →
    (∀ k, MeanModel (F.model k) (D k) (b k)) →
    DesignRegularW2 F p D →
    Tight F (fun k y => Real.sqrt (F.size k : ℝ) * l2 (ols (D k) y - b k))

/-- Convergence of the precise displayed perturbation bound, allowing b=b_n.
From rrn_error_norm_bounds and the root-n premise, l2(Delta) is Tight, since
Delta is the negative fitted-minus-true error. rrn_tight_div_sqrt therefore gives
d_n=l2(Delta)/sqrt(n) -> 0 in probability. true_error_boundW2 and
rrn_l2_div_bound give l2(e*)/sqrt(n) <= 2*c1 almost surely. Rewrite
l2(Delta)^2/n=d_n^2 at the positive sample sizes. Bound the RHS by
(1+c2)*(4*c1*d_n+d_n^2), use rowCP_continuous_pair for this polynomial at zero,
and rowCP_dominated. This needs only the row bound and the supplied root-n rate;
it does not assume the desired residual consistency. About 100–150 lines. -/
def T16_L2 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
  ∀ (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : ℕ → Fin p → ℝ),
    (∀ k, MeanModel (F.model k) (D k) (b k)) →
    (∃ Bx : ℝ, 0 ≤ Bx ∧ ∀ k i, l2 (D k i) ≤ Bx) →
    Tight F (fun k y => Real.sqrt (F.size k : ℝ) * l2 (ols (D k) y - b k)) →
    InProbability F (fun k y => perturbationRHSW2 c2
      (trueResidual (F.model k) (D k) (b k) y) (olsDeltaW2 (F.model k) (D k) (b k) y))
      (fun _ => 0)

/-- Assemble the residual conclusions from the two new steps. True-error oracle
concentration already permits row-dependent deterministic centring; the final
perturbation transfer and maximum domination are existing elementary glue. -/
theorem residual_conclusionsW2 (h1 : T16_L1) (h2 : T16_L2) : ResidualOLSConclusionsW2 := by
  intro F c1 c2 c3 c4 h p j D b hp hpn hr hm _ hreg
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hrate := h1 F c1 c2 c3 c4 h p D b hp hpn hr hm hreg
  obtain ⟨Bx, By, lam, hBx, _, _, hx, _, _⟩ := hreg
  have hRHS := h2 F c1 c2 c3 c4 h p D b hm ⟨Bx, hBx, hx⟩ hrate
  have hdeg : ∀ k i, (degree (F.model k).G i : ℝ) ≤ c2 := h.2.2.2.2.2.2.2.1
  have hc2 : 0 ≤ c2 := h.2.2.1.le
  have hbound (k : ℕ) (y : Fin (F.size k) → ℝ) :
      perturbationErrorW2 (F.model k).G (trueResidual (F.model k) (D k) (b k) y)
        (olsDeltaW2 (F.model k) (D k) (b k) y) ≤
      perturbationRHSW2 c2 (trueResidual (F.model k) (D k) (b k) y)
        (olsDeltaW2 (F.model k) (D k) (b k) y) :=
    perturbation_boundW2 (F.positive k) (F.model k).G c2 hc2 (hdeg k) _ _
  have herr : InProbability F (fun k y => perturbationErrorW2 (F.model k).G
      (trueResidual (F.model k) (D k) (b k) y) (olsDeltaW2 (F.model k) (D k) (b k) y))
      (fun _ => 0) := by
    apply AronowAudit.P011.OracleCompletion.rowCP_dominated
      (fun k => (F.model k).law) _ _ hRHS
    intro k
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))]
      exact hbound k y
  have htransfer : AronowAudit.P011.CoverageCompletion.RowCP (fun k => (F.model k).law)
      (fun k y => (F.size k : ℝ) * VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (ols (D k)) y) -
        quadratic (oracleMatrix (F.model k).G) (trueResidual (F.model k) (D k) (b k) y) /
          (F.size k : ℝ)) 0 := by
    apply AronowAudit.P011.OracleCompletion.rowCP_dominated
      (fun k => (F.model k).law) _ _ herr
    intro k
    exact Eventually.of_forall fun y => by
      have hn0 : (F.size k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (F.positive k)
      have he : (F.size k : ℝ) * VResidual (F.model k).G
          (fittedResidual (F.model k) (D k) (ols (D k)) y) -
          quadratic (oracleMatrix (F.model k).G) (trueResidual (F.model k) (D k) (b k) y) /
            (F.size k : ℝ) =
          (quadratic (oracleMatrix (F.model k).G)
            (trueResidual (F.model k) (D k) (b k) y - olsDeltaW2 (F.model k) (D k) (b k) y) -
            quadratic (oracleMatrix (F.model k).G) (trueResidual (F.model k) (D k) (b k) y)) /
              (F.size k : ℝ) := by
        rw [fitted_eqW2]
        unfold VResidual
        field_simp
        <;> ring
      rw [he, abs_div, abs_of_pos (show (0 : ℝ) < F.size k by exact_mod_cast F.positive k)]
      exact le_rfl
  have ho : InProbability F (fun k y => (F.size k : ℝ) * VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (ols (D k)) y)) (scaledTrue F) :=
    AronowAudit.P011.OracleCompletion.row_moving_add_error (fun k => (F.model k).law)
      _ _ (scaledTrue F) (true_oracleW2 F c1 c2 c3 c4 h p D b hm) htransfer
  refine ⟨hrate, fun k y => fitted_eqW2 _ _ _ _, hbound, hRHS, herr, ho, ?_⟩
  intro hv
  refine ⟨selection_existsW2 F hv
    (fun k y B => VResidual B (fittedResidual (F.model k) (D k) (ols (D k)) y)), ?_⟩
  intro A hA
  exact AronowAudit.P011.Wave1.rps_maximum_conservative (Bridge.toFamily F)
    (fun k y => fittedResidual (F.model k) (D k) (ols (D k)) y) A hv hA ho

/-- The corrected full claim. Only the varying-coefficient rate and the convergence
of the displayed bound remain as leaves; every finite and oracle/maximization
argument and both existential examples are proved in the imported support files. -/
theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2) : T16WholeStatement_W2 := by
  exact ⟨finite_identitiesW2, shift_identitiesW2, intercept_identitiesW2,
    raw_conclusionsW2, raw_maximum_witnessW2, slope_shift_witnessW2,
    residual_conclusionsW2 h1 h2, maximum_measurableW2⟩

end
end SAP.P011b.WH.W2
