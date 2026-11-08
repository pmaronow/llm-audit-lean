import SAP.P045b.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P045b.Bridge
open SAP.P045b Finset
open scoped BigOperators
noncomputable section

/-- The four exposure labels, in the order 11, 10, 01, 00. -/
def cliqueLabels : Fin 4 ≃ AronowAudit.P045.ExposureVariance.Exposure where
  toFun := ![.d11, .d10, .d01, .d00]
  invFun a := match a with
    | .d11 => 0 | .d10 => 1 | .d01 => 2 | .d00 => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv a := by cases a <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem T32_glue : T32Statement := by
  refine ⟨AronowAudit.P045.ExposureVariance.Exposure, inferInstance,
    cliqueLabels, AronowAudit.P045.ExposureVariance.cliqueF,
    AronowAudit.P045.ExposureVariance.cliqueWeights,
    AronowAudit.P045.ExposureVariance.cliqueJoints, ?_⟩
  rcases AronowAudit.P045.ExposureVariance.clique_variance_counterexample with
    ⟨hmap, hsupp, hsymm, hinj, _, hnoloop, hprob, hbank, hpos, htau,
      hexact, hM0, hvar0, hV0, hdiff0, hM1, hvar1, hV1, hdiff1, hbelow, _⟩
  rcases AronowAudit.P045.ExposureVariance.clique_structure with
    ⟨_, _, _, _, nk, nl, ns, nd⟩
  refine ⟨hmap, hsupp, hinj, hsymm, hnoloop, hbank,
    AronowAudit.P045.ExposureVariance.clique_retained_weights.1,
    AronowAudit.P045.ExposureVariance.clique_retained_weights.2,
    ?_, htau, ?_, ?_, ?_, ns, nd, ?_,
    AronowAudit.P045.ExposureVariance.clique_probability_laws.1,
    AronowAudit.P045.ExposureVariance.clique_probability_laws.2.1,
    hM0, hvar0, hV0, hdiff0, hM1, hvar1, hV1, hdiff1, hbelow,
    AronowAudit.P045.ExposureVariance.clique_all_fixed_table_counterexamples,
    ?_, ?_⟩
  · intro t i
    change 0 < AronowAudit.P045.ExposureVariance.cliqueWeights t i .d01 ∧
      0 < AronowAudit.P045.ExposureVariance.cliqueWeights t i .d00
    rw [AronowAudit.P045.ExposureVariance.clique_retained_weights.1,
      AronowAudit.P045.ExposureVariance.clique_retained_weights.1]
    exact hpos t i
  · intro i
    have h := hprob i
    refine ⟨AronowAudit.P045.ExposureVariance.clique_full_counts.1 i .d01,
      AronowAudit.P045.ExposureVariance.clique_full_counts.1 i .d00,
      h.1, h.2, ?_, ?_⟩
    · change 0 < AronowAudit.P045.ExposureVariance.marginal
        (fun _ : Fin 66 => (1/66 : ℚ)) AronowAudit.P045.ExposureVariance.cliqueF i .d01
      rw [h.1]
      norm_num
    · change 0 < AronowAudit.P045.ExposureVariance.marginal
        (fun _ : Fin 66 => (1/66 : ℚ)) AronowAudit.P045.ExposureVariance.cliqueF i .d00
      rw [h.2]
      norm_num
  · intro i j hij
    have hkk := AronowAudit.P045.ExposureVariance.clique_full_counts.2
      i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
    have hll := AronowAudit.P045.ExposureVariance.clique_full_counts.2
      i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
    have hkl := AronowAudit.P045.ExposureVariance.clique_full_counts.2
      i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
    simp only [AronowAudit.P045.ExposureVariance.cliqueFullJoint, ite_eq_right hij] at hkk hll hkl
    exact ⟨hkk, hll, hkl⟩
  · intro r
    exact ⟨nk r, nl r⟩
  · refine ⟨?_, hexact⟩
    have hm : AronowAudit.P045.ExposureVariance.marginal
        (fun _ : Fin 66 => (1/66 : ℚ)) AronowAudit.P045.ExposureVariance.cliqueF =
        AronowAudit.P045.ExposureVariance.cliqueObservationMarginal 0 false := by
      funext i a
      simpa only [AronowAudit.P045.ExposureVariance.clique_observation_independent_mass] using
        AronowAudit.P045.ExposureVariance.clique_observation_marginal 0 false i a
    change ∀ r, AronowAudit.P045.ExposureVariance.htContrast
      AronowAudit.P045.ExposureVariance.cliqueF AronowAudit.P045.ExposureVariance.cliqueY
      (AronowAudit.P045.ExposureVariance.marginal (fun _ : Fin 66 => (1/66 : ℚ))
        AronowAudit.P045.ExposureVariance.cliqueF) .d01 .d00 r = _
    rw [hm]
    exact AronowAudit.P045.ExposureVariance.clique_exact_profile_estimates
  · intro t
    have h := AronowAudit.P045.ExposureVariance.clique_relabeling_verified t
    exact ⟨AronowAudit.P045.ExposureVariance.cliqueRelabeling t, h.1, h.2.1⟩
  · intro included
    have h := AronowAudit.P045.ExposureVariance.clique_real_variance_shortfall included
    simp only [AronowAudit.P045.ExposureVariance.cliqueY, Rat.cast_one] at h
    exact h

end
end SAP.P045b.Bridge
