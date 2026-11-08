import SAP.P005a.Defs.WholeW2
import SAP.P005a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2
noncomputable section
open Finset Filter SAP.P005a.Bridge AronowAudit.P005.Wave1
open scoped BigOperators Matrix Topology
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

/-- The existing finite-moment/Markov argument works after any common threshold. -/
theorem wholeArmOrder_proof : wholeArmOrder := by
  intro n₀ hn₀ d m P h t
  classical
  rcases h with ⟨hsize, ⟨K, hK, hym⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
  let a : ℝ := min lo (1-hi)
  have ha : 0 < a := lt_min hlo (sub_pos.mpr hhi)
  let L : ℝ := 1+1/a
  have hL : 1 ≤ L := by
    have ha0 : 0 ≤ 1/a := (one_div_pos.mpr ha).le
    dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  let B : ℝ := ((17*L^4*K+1) + 2*(2*L*K*(17*L^4+4*L^2)+1) + (72*L^3*K+1))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨n₁, hstd⟩ := Filter.eventually_atTop.mp hstd
  intro ε hε
  let M : ℝ := (B+1)/ε+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hBM : B < ε*M := by
    have he : ε*((B+1)/ε) = B+1 := by field_simp <;> ring
    dsimp only [M]; nlinarith only [he, hε]
  refine ⟨M, hM, max (max 3 n₀) n₁, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := le_trans (le_trans (le_max_left 3 n₀) (le_max_left (max 3 n₀) n₁)) hn
  have hnstart : n₀ ≤ n := le_trans (le_trans (le_max_right 3 n₀) (le_max_left (max 3 n₀) n₁)) hn
  have hn0 : 0 < n := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn0
  have hPn : standardized (P n) := hstd n ((le_max_right (max 3 n₀) n₁).trans hn)
  have hsz := hsize n hnstart
  have hp := halloc n hnstart
  let s := armSize n (m n) t
  let y := if t = .treated then (P n).yT else (P n).yC
  let F := fun (S : Finset (Fin n)) => armDebiased (P n) (armSet t S) y -
      (mean (armSet t S) y-dot (xMean (P n) (armSet t S)) (populationSlope (P n) y))
  have hs : 0 < s := by cases t <;> simp only [s, armSize] <;> omega
  have hsn : s < n := by cases t <;> simp only [s, armSize] <;> omega
  have hslo : a*(n : ℝ) ≤ s := by
    cases t with
    | treated =>
      change a*(n : ℝ) ≤ (m n : ℝ)
      have hlow : lo*(n : ℝ) < m n := (lt_div_iff₀ hnp).mp hp.1
      exact (mul_le_mul_of_nonneg_right (min_le_left lo (1-hi)) hnp.le).trans hlow.le
    | control =>
      change a*(n : ℝ) ≤ ((n-m n : ℕ) : ℝ)
      rw [Nat.cast_sub hsz.2.2.2.le]
      have hupp : (m n : ℝ) < hi*n := (div_lt_iff₀ hnp).mp hp.2
      have hmul := mul_le_mul_of_nonneg_right (min_le_right lo (1-hi)) hnp.le
      nlinarith
  have hNs : (n : ℝ)/s ≤ L := by
    have hsp : (0 : ℝ) < s := by exact_mod_cast hs
    have hb : (n : ℝ)/s ≤ 1/a := (div_le_div_iff₀ hsp ha).mpr (by nlinarith only [hslo])
    exact hb.trans (by dsimp [L]; linarith)
  have hY : popMean (fun i => y i^2) ≤ K := by
    cases t with
    | treated => exact (hym n hnstart).1
    | control => exact (hym n hnstart).2.1
  have hfirst : expectation (m n) (fun S => |F S|) ≤ B*Real.sqrt (kappa (P n)/n) := by
    have hh := GP005B1b_remainder_first (toPopulation (P n)) hn3 hsz.1 hs hsn hPn y K L hK hL hY hNs
    cases t with
    | treated => exact hh
    | control =>
      change expectation (m n) (fun S => |armDebiased (P n) (control S) y -
        (mean (control S) y-dot (xMean (P n) (control S)) (populationSlope (P n) y))|) ≤ _
      rw [expectation_control hsz.2.2.2.le
        (fun S => |armDebiased (P n) S y-(mean S y-dot (xMean (P n) S) (populationSlope (P n) y))|)]
      exact hh
  have hκ : 0 < kappa (P n) := lt_of_lt_of_le
    (div_pos (by exact_mod_cast (by omega : 0 < d n)) hnp) (AronowAudit.P005.kappa_bounds (toPopulation (P n)) hn0 hPn.2).1
  have hr : 0 < Real.sqrt (kappa (P n)/n) := Real.sqrt_pos.2 (div_pos hκ hnp)
  change probability (m n) (fun S => M*Real.sqrt (kappa (P n)/n) < |F S|) < ε
  calc
    _ ≤ expectation (m n) (fun S => |F S|)/(M*Real.sqrt (kappa (P n)/n)) :=
      GP005B1b_markov (m n) (fun S => |F S|) (fun _ _ => abs_nonneg _) _ (mul_pos hM hr)
    _ ≤ (B*Real.sqrt (kappa (P n)/n))/(M*Real.sqrt (kappa (P n)/n)) :=
      div_le_div_of_nonneg_right hfirst (mul_pos hM hr).le
    _ < ε := (div_lt_iff₀ (mul_pos hM hr)).mpr (by
      have hh := mul_lt_mul_of_pos_right hBM hr
      nlinarith only [hh])


end
end SAP.P005a.WH.W2
