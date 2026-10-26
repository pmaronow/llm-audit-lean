import AronowAudit.P045.Wave1.ClusterSamplerBlueprint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Summability and evaluation of the three net masses. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

theorem n8_proof : N8 := by
  classical
  intro hs hp
  have hsingle : HasSum (fun t : ℕ => if t = 1 then (1 / 4 : ℝ) else 0) (1 / 4) :=
    hasSum_ite_eq 1 (1 / 4 : ℝ)
  have hexception : HasSum (fun t : ℕ => if t = 2 then (1 / 4 : ℝ) else 0) (1 / 4) :=
    hasSum_ite_eq 2 (1 / 4 : ℝ)
  have hgeo : Summable (fun t : ℕ => (1 / 4 : ℝ) ^ t) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let g : ℕ → ℝ := fun t => if 2 ≤ t then (1 / 4 : ℝ) ^ t else 0
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (f := fun t : ℕ => (1 / 4 : ℝ) ^ t) _ _ hgeo
    · intro t
      dsimp only [g]
      split_ifs <;> positivity
    · intro t
      dsimp only [g]
      by_cases ht : 2 ≤ t
      · rw [if_pos ht]
      · rw [if_neg ht]
        exact pow_nonneg (by norm_num) t
  have hshift_summable : Summable (fun t : ℕ => g (t + 2)) :=
    (summable_nat_add_iff 2).2 hg
  have hshift : (∑' t : ℕ, g (t + 2)) = 1 / 12 := by
    calc
      (∑' t : ℕ, g (t + 2)) = ∑' t : ℕ, (1 / 4 : ℝ) ^ t * (1 / 4 : ℝ) ^ 2 := by
        apply tsum_congr
        intro t
        dsimp only [g]
        rw [if_pos (by omega), pow_add]
      _ = (∑' t : ℕ, (1 / 4 : ℝ) ^ t) * (1 / 4 : ℝ) ^ 2 := tsum_mul_right
      _ = 1 / 12 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
  have htail : (∑' t : ℕ, g t) = 1 / 12 := by
    have hsplit := hg.sum_add_tsum_nat_add 2
    have hhead : (∑ t ∈ Finset.range 2, g t) = 0 := by
      norm_num [g, Finset.sum_range_succ]
    rw [hhead, hshift, zero_add] at hsplit
    exact hsplit.symm
  have hpair_summable : Summable (fun t : ℕ =>
      (if t = 2 then (1 / 4 : ℝ) else 0) + g t) :=
    hexception.summable.add hg
  -- These are the actual inner-sum functions defining the three terminal masses.
  have hmass1_summable : Summable (fun t : ℕ =>
      ∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({1} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) := by
    simpa only [(hs _).1] using hsingle.summable
  have hmass2_summable : Summable (fun t : ℕ =>
      ∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({2} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) := by
    simpa only [(hs _).2] using hsingle.summable
  have hmass03_summable : Summable (fun t : ℕ =>
      ∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) := by
    simpa only [hp _, g] using hpair_summable
  refine ⟨?_, ?_, ?_⟩
  · unfold terminalCentres
    simp_rw [(hs _).1]
    exact hsingle.tsum_eq
  · unfold terminalCentres
    simp_rw [(hs _).2]
    exact hsingle.tsum_eq
  · unfold terminalCentres
    simp_rw [hp _]
    change tsum (fun t : ℕ => (if t = 2 then (1 / 4 : ℝ) else 0) + g t) = 1 / 3
    rw [hexception.summable.tsum_add hg, hexception.tsum_eq, htail]
    norm_num

end

end AronowAudit.P045.Wave1.ClusterSampler
