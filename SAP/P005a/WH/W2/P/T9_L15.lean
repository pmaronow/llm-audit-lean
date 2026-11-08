import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L15

open Filter

end SAP.P005a.WH.W2.P.T9_L15

open Filter
open scoped Topology

theorem SAP.P005a.WH.W2.T9_L15_proof : SAP.P005a.WH.W2.T9_L15 := by
  unfold SAP.P005a.WH.W2.T9_L15 SAP.P005a.mixedLogEquivalence
  intro d κ hd hk
  let B : ℕ → ℝ := fun n => κ n * Real.log (2 * d n : ℕ)
  let L : ℕ → ℝ := fun n => κ n * Real.log (d n)
  let I : ℕ → ℝ := fun n => if d n = 1 then κ n else 0
  have hcond := AronowAudit.P005.repaired_log_conditions d κ hd hk
  constructor
  · intro hB
    constructor
    · exact (hcond.2.1 hB).2
    · have hκ0 : Tendsto κ atTop (nhds 0) := (hcond.2.1 hB).1
      have hInonneg : ∀ᶠ n in atTop, 0 ≤ I n := by
        filter_upwards [hk] with n hn
        dsimp [I]
        split_ifs <;> linarith
      have hIle : ∀ᶠ n in atTop, I n ≤ κ n := by
        filter_upwards [hk] with n hn
        dsimp [I]
        split_ifs <;> linarith
      exact squeeze_zero' hInonneg hIle hκ0
  · rintro ⟨hL, hI⟩
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hκnonneg : ∀ᶠ n in atTop, 0 ≤ κ n := hk
    have hLnonneg : ∀ᶠ n in atTop, 0 ≤ L n := by
      filter_upwards [hd, hk] with n hdn hkn
      dsimp [L]
      apply mul_nonneg hkn
      apply Real.log_nonneg
      exact_mod_cast hdn
    have hInonneg : ∀ᶠ n in atTop, 0 ≤ I n := by
      filter_upwards [hk] with n hn
      dsimp [I]
      split_ifs <;> linarith
    have hbound : ∀ᶠ n in atTop, κ n ≤ I n + L n / Real.log 2 := by
      filter_upwards [hd, hk] with n hdn hkn
      have hdreal : (1 : ℝ) ≤ (d n : ℝ) := by exact_mod_cast hdn
      by_cases h1 : d n = 1
      · simp [I, L, h1]
      · have hdn2 : 2 ≤ d n := by omega
        have hlog : Real.log 2 ≤ Real.log (d n : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hdn2)
        have hmul : κ n * Real.log 2 ≤ κ n * Real.log (d n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog hkn
        have hdiv : κ n ≤ (κ n * Real.log (d n : ℝ)) / Real.log 2 :=
          (le_div_iff₀ hlog2).2 (by simpa [mul_comm] using hmul)
        simpa [I, L, h1] using hdiv
    have hsum : Tendsto (fun n => I n + L n / Real.log 2) atTop (nhds 0) := by
      have hLdiv : Tendsto (fun n => L n / Real.log 2) atTop (nhds 0) := by
        simpa using hL.div_const (Real.log 2)
      simpa using hI.add hLdiv
    have hκ0 : Tendsto κ atTop (nhds 0) := squeeze_zero' hκnonneg hbound hsum
    have hκlog2 : Tendsto (fun n => κ n * Real.log 2) atTop (nhds 0) := by
      simpa using hκ0.mul_const (Real.log 2)
    have hBsum : Tendsto (fun n => L n + κ n * Real.log 2) atTop (nhds 0) := by
      simpa using hL.add hκlog2
    have heq : ∀ᶠ n in atTop, L n + κ n * Real.log 2 = B n := by
      filter_upwards [hd] with n hdn
      have hdpos : (0 : ℝ) < (d n : ℝ) := by
        have : (0 : ℝ) < (1 : ℝ) := by norm_num
        exact lt_of_lt_of_le this (by exact_mod_cast hdn)
      dsimp [L, B]
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (ne_of_gt hdpos)]
      ring
    have hB' : Tendsto B atTop (nhds 0) := hBsum.congr' heq
    simpa [B] using hB'
