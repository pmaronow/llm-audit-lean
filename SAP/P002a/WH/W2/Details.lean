import SAP.P002a.WH.W2.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SAP.P002a.WH.W2
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

private theorem groupMean_constant {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (c : ℝ) :
    groupMean S (fun _ => c) = c := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [groupMean, hc]

private theorem sigma_constant {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (c : ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawSigma2 P (fun _ => c) S = 0 := by
  have hsz : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
  have hsne : S.Nonempty := Finset.card_pos.mp (hsz ▸ hP.2.1)
  have hcne : Sᶜ.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_compl, Fintype.card_fin, hsz]
    exact Nat.sub_pos_of_lt hP.2.2)
  simp [rawSigma2, armMean, groupMean_constant S hsne c, groupMean_constant Sᶜ hcne c]

private theorem quantile_zero {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (g : Finset (Fin n) → ℝ≥0∞) (hg : ∀ S ∈ assignments P, g S = 0)
    (α : ℝ) (hα : 0 < α) : quantile P g α = 0 := by
  have hne : (assignments P).Nonempty := Finset.powersetCard_nonempty.mpr (by
    simpa using hP.2.2.le)
  have hprob : probability P (fun S => g S ≤ 0) = 1 := by
    unfold probability
    rw [Finset.filter_eq_self.mpr (fun S hS => by rw [hg S hS])]
    have hc : ((assignments P).card : ℝ) ≠ 0 := by exact_mod_cast hne.card_ne_zero
    exact div_self hc
  let C := ((assignments P).image g).filter fun t => 1-α ≤ probability P (fun S => g S ≤ t)
  have hzero : (0 : ℝ≥0∞) ∈ C := by
    obtain ⟨S, hS⟩ := hne
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨S, hS, hg S hS⟩, ?_⟩
    rw [hprob]; linarith
  change (if h : C.Nonempty then C.min' h else ⊤) = 0
  rw [dite_eq_left ⟨0, hzero⟩]
  exact le_antisymm (Finset.min'_le C 0 hzero) bot_le

theorem t4_raw_zeros : W2T4RawZeros := by
  intro n P hP α hα
  obtain ⟨c, hc⟩ := restrictedT4.2.1 P hP
  have hobs (O : Finset (Fin n)) : observedW P (late P) O = fun _ => c :=
    AronowAudit.P002.observedW_constant (toPopulation P) (late P) c hc O
  have ht (T : Finset (Fin n)) (hT : T ∈ assignments P) : rawTau P (fun _ => c) T = 0 :=
    AronowAudit.P002.rawTau_constant (toPopulation P) hP.1 c T hT
  have hs (T : Finset (Fin n)) (hT : T ∈ assignments P) : rawSigma2 P (fun _ => c) T = 0 :=
    sigma_constant P hP.1 c T hT
  have har (T : Finset (Fin n)) (hT : T ∈ assignments P) : rawAR P (fun _ => c) T = 0 := by
    simp [rawAR, ht T hT, hs T hT, absStudent]
  have hq : quantile P (rawAR P (fun _ => c)) α = 0 := quantile_zero P hP.1 _ har α hα.1
  refine ⟨c, hc, ?_⟩
  intro O hO
  refine ⟨hobs O, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change rawTau P (observedW P (late P) O) O = 0
    rw [hobs O]; exact ht O hO
  · rw [hobs O]; exact hs O hO
  · rw [hobs O]; exact har O hO
  · intro T hT; rw [hobs O]; exact ⟨ht T hT, hs T hT, har T hT⟩
  · rw [hobs O]; exact hq
  · unfold accepted; rw [hobs O, har O hO]; exact bot_le

/-- Direct reconstruction of the unchanged parameter-space clauses. -/
theorem t2_inclusions : W2T2Inclusions := by
  constructor
  · intro n P δ r A hδ hP
    rcases hP with ⟨hD, hm, hc, hl, hu, hv, hf⟩
    refine ⟨hD, hm, hc, hl, hu, ?_, hf⟩
    simp only [neg_zero, zero_mul]
    exact (mul_nonneg (mul_nonneg (by linarith : 0 ≤ -δ) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).trans hv
  · intro n k P δ e A B r hδ hP
    rcases hP with ⟨hD, hm, hc, hl, hu, hv, hf, hx, h4, he⟩
    refine ⟨hD, hm, hc, hl, hu, ?_, hf, hx, h4, he⟩
    simp only [neg_zero, zero_mul]
    exact (mul_nonneg (mul_nonneg (by linarith : 0 ≤ -δ) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).trans hv

end
end SAP.P002a.WH.W2
