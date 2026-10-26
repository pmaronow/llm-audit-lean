import AronowAudit.P005.Wave1.InteractedExpansionBlueprint

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- It is enough to bound the rate by 1: the deterministic remainder diverges. -/
theorem n11_proof : N11 := by
  intro hR hk hO
  obtain ⟨M, hM, n₀, htail⟩ := hO (1/2) (by norm_num)
  obtain ⟨q, hq⟩ := exists_nat_gt (M + 6)
  let n : ℕ := 2 * (q + n₀ + 6)
  have hn6 : 6 ≤ n := by dsimp [n]; omega
  have hnn₀ : n₀ ≤ n := by dsimp [n]; omega
  have hneven : Even n := ⟨q + n₀ + 6, by dsimp [n]; omega⟩
  have hnq : q ≤ n := by dsimp [n]; omega
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have hnpos : (0 : ℝ) < n := by linarith
  have hbig : M < (n : ℝ) - 6 := by
    have hqn : (q : ℝ) ≤ n := by exact_mod_cast hnq
    linarith
  have harg : kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n ≤ 1 := by
    apply (div_le_iff₀ hnpos).2
    simpa using (show kappa (spikePopulation n) ≤ (n : ℝ) by
      linarith [hk n hn6])
  have hrate : Real.sqrt (kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n) ≤ 1 :=
    Real.sqrt_le_one.mpr harg
  have hevent : ∀ S ∈ design n (n / 2),
      |R n S| > M * Real.sqrt (kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n) := by
    intro S hS
    have hr := hR n hn6 hneven S hS
    have hm := mul_le_mul_of_nonneg_left hrate hM.le
    linarith
  have hdesign : 0 < (design n (n / 2)).card := by
    simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact Nat.choose_pos (by omega)
  have hp : probability (n / 2) (fun S => |R n S| >
      M * Real.sqrt (kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n)) = 1 := by
    unfold probability
    rw [Finset.filter_true_of_mem hevent]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hdesign))
  have ht := htail n hnn₀
  rw [hp] at ht
  norm_num at ht

end
end AronowAudit.P005.Wave1.InteractedExpansion
