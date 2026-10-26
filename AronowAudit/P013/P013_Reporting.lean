import Mathlib

namespace AronowAudit.P013

open scoped BigOperators
open Finset
noncomputable section

/-- A value "displays as" the three-decimal entry p when it belongs to
[p-1/2000,p+1/2000]. Closed bins allow every rounding tie rule.
Table 2, p. 1936; correction P013-E008. -/
def Displays3 (x p : ℝ) : Prop := p - 1/2000 ≤ x ∧ x ≤ p + 1/2000

/-- The two endpoints of a symmetric normal approximation interval sum to
twice its estimate (Table 2 note, p. 1936; P013-T10(a)). -/
theorem wald_center (e s z : ℝ) : (e - z*s) + (e + z*s) = 2*e := by ring

/-- The WLS d101 versus d000 estimate and CI in Table 2 cannot all result
from rounding a symmetric interval, including ties (P013-T10(b), p. 1936). -/
theorem wls_d101_impossible (e L U : ℝ)
    (he : Displays3 e (295/1000)) (hL : Displays3 L (50/1000))
    (hU : Displays3 U (536/1000)) (hmid : L + U = 2*e) : False := by
  unfold Displays3 at *
  linarith [he.1, hL.2, hU.2]

/-- The WLS d111 versus d000 estimate and CI in Table 2 cannot all result
from rounding a symmetric interval, including ties (P013-T10(c), p. 1936). -/
theorem wls_d111_impossible (e L U : ℝ)
    (he : Displays3 e (306/1000)) (hL : Displays3 L (212/1000))
    (hU : Displays3 U (404/1000)) (hmid : L + U = 2*e) : False := by
  unfold Displays3 at *
  linarith [he.2, hL.1, hU.1]

/-- Neither disputed Table 2 row can be a rounded e ± zs interval for any
real estimate, standard error or critical value (P013-T10). -/
theorem table2_two_rows (e s z : ℝ) :
    ¬ (Displays3 e (295/1000) ∧ Displays3 (e-z*s) (50/1000) ∧
       Displays3 (e+z*s) (536/1000)) ∧
    ¬ (Displays3 e (306/1000) ∧ Displays3 (e-z*s) (212/1000) ∧
       Displays3 (e+z*s) (404/1000)) := by
  constructor
  · rintro ⟨he, hL, hU⟩
    exact wls_d101_impossible e _ _ he hL hU (wald_center e s z)
  · rintro ⟨he, hL, hU⟩
    exact wls_d111_impossible e _ _ he hL hU (wald_center e s z)

/-- Section 9's "randomly assigned without replacement and with uniform
probability to 1/10 of individuals" (p. 1930): every size-n subset of a
school U is equiprobable. The probability of A is its count divided by C(N,n). -/
def completeProbability (U : Finset ℕ) (n : ℕ) (A : Finset ℕ → Prop) : ℝ :=
  by classical exact ((U.powersetCard n).filter A).card / (Nat.choose U.card n : ℝ)

/-- "Isolated Direct Exposure" d10: focal i treated and all its neighbours
untreated (Section 9, exposure mapping, p. 1930). -/
def isolatedExposure (i : ℕ) (neighbors : Finset ℕ) (S : Finset ℕ) : Prop :=
  i ∈ S ∧ Disjoint S neighbors

/-- "No Exposure" d00: neither focal i nor any neighbour treated
(Section 9, exposure mapping, p. 1930). -/
def noExposure (i : ℕ) (neighbors : Finset ℕ) (S : Finset ℕ) : Prop :=
  i ∉ S ∧ Disjoint S neighbors

/-- The degree-39 student's two exposure probabilities are the ratios of
binomial counts in correction P013-N004, P013-T11(a). This is a counting
statement for the actual uniform size-n randomization space, not an assumed
formula for its probabilities. -/
theorem complete_randomization_degree39_counts (U neighbors : Finset ℕ) (i n : ℕ)
    (hi : i ∈ U) (hsub : neighbors ⊆ U) (hex : i ∉ neighbors)
    (hdeg : neighbors.card = 39) (hn : 1 ≤ n) (hmax : n ≤ U.card - 39) :
    completeProbability U n (isolatedExposure i neighbors) =
      (Nat.choose (U.card - 40) (n - 1) : ℝ) / Nat.choose U.card n ∧
    completeProbability U n (noExposure i neighbors) =
      (Nat.choose (U.card - 40) n : ℝ) / Nat.choose U.card n := by
  classical
  have hisub : ({i} : Finset ℕ) ⊆ U \ neighbors := by
    simpa using mem_sdiff.mpr ⟨hi, hex⟩
  have hboth : insert i neighbors ⊆ U := insert_subset hi hsub
  have hp : (U.powersetCard n).filter (isolatedExposure i neighbors) =
      ((U \ neighbors).powersetCard n).filter (({i} : Finset ℕ) ⊆ ·) := by
    ext S
    simp only [mem_filter, mem_powersetCard, isolatedExposure, singleton_subset_iff, subset_sdiff]
    tauto
  have hq : (U.powersetCard n).filter (noExposure i neighbors) =
      (U \ insert i neighbors).powersetCard n := by
    ext S
    simp only [mem_filter, mem_powersetCard, noExposure, subset_sdiff,
      disjoint_insert_right]
    tauto
  have hpcard : ((U.powersetCard n).filter (isolatedExposure i neighbors)).card =
      Nat.choose (U.card - 40) (n-1) := by
    rw [hp, card_filter_powersetCard_subset {i} (U \ neighbors) n hisub (by simpa using hn),
      card_sdiff_of_subset hsub, hdeg]
    simp only [card_singleton]
    congr 1
  have hqcard : ((U.powersetCard n).filter (noExposure i neighbors)).card =
      Nat.choose (U.card - 40) n := by
    rw [hq, card_powersetCard, card_sdiff_of_subset hboth, card_insert_of_notMem hex, hdeg]
  unfold completeProbability
  rw [hpcard, hqcard]
  exact ⟨rfl, rfl⟩

/-- Algebraic binomial-count ratio, including the endpoint n = N-39
where q = 0 (P013-T11(b), Section 9 correction). -/
theorem degree39_choose_ratio (N n : ℕ) (hN : 40 ≤ N) (hn : 1 ≤ n)
    (hmax : n ≤ N - 39) :
    (Nat.choose (N - 40) n : ℝ) / Nat.choose N n =
      ((N : ℝ) - 39 - n) / n *
        ((Nat.choose (N - 40) (n - 1) : ℝ) / Nat.choose N n) := by
  have hk : n - 1 + 1 = n := by omega
  have hrec := Nat.choose_succ_right_eq (N - 40) (n - 1)
  rw [hk] at hrec
  have hsub : N - 40 - (n - 1) = N - 39 - n := by omega
  rw [hsub] at hrec
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcast : ((N - 39 - n : ℕ) : ℝ) = (N : ℝ) - 39 - n := by
    rw [Nat.cast_sub hmax, Nat.cast_sub (by omega : 39 ≤ N)]
    norm_num
  have hreal : (Nat.choose (N - 40) n : ℝ) * n =
      (Nat.choose (N - 40) (n - 1) : ℝ) * ((N : ℝ) - 39 - n) := by
    rw [← hcast]
    exact_mod_cast hrec
  have heq : (Nat.choose (N - 40) n : ℝ) =
      ((N : ℝ) - 39 - n) / n * Nat.choose (N - 40) (n - 1) := by
    apply (eq_div_iff hn0).2 at hreal
    convert hreal using 1 <;> ring
  rw [heq]
  ring

/-- A school treated at one tenth (allowing nearest-integer rounding) has
q ≤ 9p for the degree-39 unit; uses the exact ratio (P013-T11(c)). -/
theorem degree39_ratio_bound (N n p q : ℝ) (hn : 0 < n) (hN : N ≤ 10*n + 5)
    (hp : 0 ≤ p) (hformula : q = ((N-39-n)/n)*p) : q ≤ 9*p := by
  have hratio : (N-39-n)/n ≤ 9 := (div_le_iff₀ hn).2 (by linarith)
  rw [hformula]
  exact mul_le_mul_of_nonneg_right hratio hp

/-- Allowing all rounding ties for 0.00067, its exact design probability
implies q ≤ 0.006075 < 0.01 (P013-T11(d), p. 1931). -/
theorem degree39_small_p (N n p q : ℝ) (hn : 0 < n) (hN : N ≤ 10*n + 5)
    (hp : 0 ≤ p) (hformula : q = ((N-39-n)/n)*p) (hround : p ≤ 27/40000) :
    q ≤ 243/40000 ∧ q < 1/100 := by
  have h := degree39_ratio_bound N n p q hn hN hp hformula
  constructor <;> linarith

/-- Conversely no-exposure probability at least 0.01 requires p ≥ 1/900,
which cannot display as 0.00067 (P013-T11(d), p. 1931). -/
theorem degree39_large_q (N n p q : ℝ) (hn : 0 < n) (hN : N ≤ 10*n + 5)
    (hp : 0 ≤ p) (hformula : q = ((N-39-n)/n)*p) (hq : 1/100 ≤ q) :
    1/900 ≤ p ∧ 27/40000 < p := by
  have h := degree39_ratio_bound N n p q hn hN hp hformula
  constructor <;> linarith

/-- Full corrected Section 9 claim on its finite uniform assignment space:
if the degree-39 isolated-direct probability displays as 0.00067, the
no-exposure probability is below 0.01 (P013-T11). No school size or corrected
decimal is invented. -/
theorem degree39_design_incompatibility (U neighbors : Finset ℕ) (i n : ℕ)
    (hi : i ∈ U) (hsub : neighbors ⊆ U) (hex : i ∉ neighbors)
    (hdeg : neighbors.card = 39) (hn : 1 ≤ n) (hmax : n ≤ U.card - 39)
    (hroundN : U.card ≤ 10*n+5)
    (hp : completeProbability U n (isolatedExposure i neighbors) ≤ 27/40000) :
    completeProbability U n (noExposure i neighbors) ≤ 243/40000 ∧
      completeProbability U n (noExposure i neighbors) < 1/100 := by
  have hcounts := complete_randomization_degree39_counts U neighbors i n hi hsub hex hdeg hn hmax
  have hN : 40 ≤ U.card := by
    have hx := card_le_card (insert_subset hi hsub)
    simpa [card_insert_of_notMem hex, hdeg] using hx
  have hratio := degree39_choose_ratio U.card n hN hn hmax
  have hformula : completeProbability U n (noExposure i neighbors) =
      ((U.card : ℝ)-39-n)/n * completeProbability U n (isolatedExposure i neighbors) := by
    rw [hcounts.1, hcounts.2]
    exact hratio
  have hpnonneg : 0 ≤ completeProbability U n (isolatedExposure i neighbors) := by
    rw [hcounts.1]
    positivity
  apply degree39_small_p U.card n _ _ (by exact_mod_cast (by omega : 0 < n))
    (by exact_mod_cast hroundN) hpnonneg hformula hp

end
end AronowAudit.P013

