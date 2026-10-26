import AronowAudit.P005.Wave1.InteractedExpansionBlueprint

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem n3_proof : N3 := by
  intro h1 h2
  refine ⟨?_, ⟨1, by norm_num, ?_⟩, ?_, ⟨1/4, 3/4, by norm_num,
    by norm_num, by norm_num, ?_⟩⟩
  · intro n hn
    dsimp only
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro n hn
    have hnon : (univ : Finset (Fin n)).Nonempty :=
      Finset.card_pos.mp (by simpa using (show 0 < n by omega))
    have hy : popMean (fun i => spikeV n i ^ 2) ≤ 1 := by
      calc
        _ ≤ mean univ (fun _ => (1 : ℝ)) := by
          apply mean_mono
          intro i hi
          have h := (abs_le.mp ((h1 n hn).2.2.1 i))
          nlinarith [h.1, h.2]
        _ = 1 := mean_const univ hnon 1
    refine ⟨hy, hy, ?_⟩
    intro k
    have hg := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M k k) (h2 n hn).2
    have hsq : popMean (fun i => (spikePopulation n).x i k ^ 2) = 1 := by
      simpa [gram, pow_two] using hg
    exact hsq.le
  · exact Filter.eventually_atTop.2 ⟨3, fun n hn => h2 n hn⟩
  · intro n hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : (0 : ℝ) < n := by linarith
    have hlow : n ≤ 3 * (n / 2) := by omega
    have hhigh : (n / 2) * 2 ≤ n := Nat.div_mul_le_self n 2
    have hl : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hlow
    have hh : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast hhigh
    constructor
    · exact (lt_div_iff₀ hd).2 (by nlinarith)
    · exact (div_lt_iff₀ hd).2 (by nlinarith)

end
end AronowAudit.P005.Wave1.InteractedExpansion
