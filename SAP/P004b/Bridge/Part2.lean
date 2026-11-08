import SAP.P004b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

/-- Restricting a tail event to assignments with nonempty arms only decreases its probability. -/
theorem inProb_armRestricted (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U : ∀ N, Assignment N → ℝ)
    (h : InProb p U) : InProb p (fun N => armRestricted (U N)) := by
  intro ε hε
  apply squeeze_zero (fun N => AronowAudit.P004.Wave1.t18_prob_nonneg (p N) (hp N) _)
    (fun N => AronowAudit.P004.Wave1.t18_prob_mono (p N) (hp N) _ _ ?_) (h ε hε)
  intro z hz
  by_cases ha : ValidArms z
  · simpa only [armRestricted, if_pos ha] using hz
  · simp only [armRestricted, if_neg ha, abs_zero] at hz
    exact (not_lt_of_ge hε.le hz).elim

theorem bigOp_armRestricted (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (U : ∀ N, Assignment N → ℝ)
    (r : ℕ → ℝ) (h : BigOp p U r) : BigOp p (fun N => armRestricted (U N)) r := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ := h ε hε
  refine ⟨C, hC, htail.mono (fun N hN => ?_)⟩
  apply lt_of_le_of_lt (AronowAudit.P004.Wave1.t18_prob_mono (p N) (hp N) _ _ ?_) hN
  intro z hz
  by_cases ha : ValidArms z
  · simpa only [armRestricted, if_pos ha] using hz
  · simp only [armRestricted, if_neg ha, abs_zero] at hz
    exact (not_lt_of_ge (mul_nonneg hC.le (abs_nonneg _)) hz).elim

/-- A valid-interval guard weakens the coverage event by logical implication alone. -/
theorem conservative_guarded (p : ℝ) (R : ∀ N, CircleTable N)
    (Q : ∀ N, Matrix (Fin N) (Fin N) ℝ) (lo hi α : ℝ) (hp : 0 < p ∧ p < 1)
    (h : Conservative (fun N => prob (fun _ => p) (fun z =>
      lo ≤ (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt (kernelVariance z (residual (R N) z) (Q N)) ∧
      (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt (kernelVariance z (residual (R N) z) (Q N)) ≤ hi)) α) :
    Conservative (fun N => prob (fun _ => p) (GuardedInterval p (R N) (Q N) lo hi)) α := by
  intro ε hε
  exact (h ε hε).mono (fun N hN => hN.trans
    (AronowAudit.P004.Wave1.t18_prob_mono _ (fun _ => hp) _ _ (fun _ hz _ => hz)))

/-- All the exported thin polygons lie in the radius-two neighborhood. -/
theorem thin_count : ThinCountFailure := by
  intro n hn
  have hnear : ∀ i : Fin (n+1),
      sInf {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i, dist x y = r} < 2 :=
    (AronowAudit.P004.Wave1.polygon_spacing_counterexample_proof.1 n hn).2.2
  rw [Finset.filter_eq_self.mpr (fun i _ => (hnear i).le)]
  simp

/-- Positivity here is just arithmetic on the exported sparse-witness variance formula. -/
theorem sparse_validInterval {N : ℕ} (hN : 10 ≤ N) (z : Assignment N)
    (hg : SparseGood z) :
    ValidInterval (circleAverage (sparsePopulation N) 1)
      (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N)) z := by
  have hn : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : armCount z true + armCount z false = (N : ℝ) :=
    AronowAudit.P004.Wave1.T27_count_complement z
  have h1 : 0 < armCount z true := by rcases hg with ⟨hl, hu⟩; linarith
  have h0 : 0 < armCount z false := by rcases hg with ⟨hl, hu⟩; linarith
  have hq1 : 1 < armCount z true := by rcases hg with ⟨hl, hu⟩; linarith
  have hq0 : 1 < armCount z false := by rcases hg with ⟨hl, hu⟩; linarith
  refine ⟨⟨h1, h0⟩, ?_⟩
  rw [show circleAverage (sparsePopulation N) 1 = sparseTable N from AronowAudit.P004.Wave1.T27_circle N]
  rw [show kernelVariance z (residual (sparseTable N) z)
      (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N)) =
      (1/4+3/4*bit (z ⟨0, by omega⟩))^2 * (armCount z (z ⟨0, by omega⟩)-1) /
        (armCount z (z ⟨0, by omega⟩))^3 from
      AronowAudit.P004.Wave1.T27_spike_variance (by omega) z h1 h0]
  cases hz : z (⟨0, by omega⟩ : Fin N) <;> simp only [bit, hz, Bool.false_eq_true, if_false, if_true]
  · exact div_pos (mul_pos (sq_pos_of_pos (by norm_num)) (sub_pos.mpr hq0)) (pow_pos h0 _)
  · exact div_pos (mul_pos (sq_pos_of_pos (by norm_num)) (sub_pos.mpr hq1)) (pow_pos h1 _)

end
end SAP.P004b.Bridge
