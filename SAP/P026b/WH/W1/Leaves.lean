import SAP.P026b.Defs.WholeW1
import SAP.P026b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b.WH.W1
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

/-- Count-free equal-marginal HT rescaling, the new step in equation [12].
Factor each common marginal out of `htTotal` using `Finset.sum_div` and
`AronowAudit.P026.observed_mask` through `SAP.P026b.Bridge.toDesign`.
Substitute m/M and (M-m)/M, then use `field_simp` and `ring` with the
positive natural denominators. The proof of `AronowAudit.P026.complete_clusters`
does exactly this; its fixed-count premise is unused. This is a pointwise
algebraic identity, so neither a probability law nor a realized count is needed. -/
def T21_L1 : Prop :=
  ∀ (Ω I : Type) [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ) (N M m : ℕ), 0 < N → 0 < m → m < M →
    (∀ i, marginal D true i = (m : ℝ) / M ∧
      marginal D false i = ((M - m : ℕ) : ℝ) / M) →
    ∀ (x z : I → ℝ) (w : Ω),
      ht D N x z w = T21ClusterContrast D N M m x z w

/-- Evaluate expectations for the three-point law inside the allocation cube. -/
theorem T21_witness_sum (f : (Fin 3 → Bool) → ℝ) :
    (∑ w, T21WitnessWeight w * f w) = (∑ j : Fin 3, f (T21OneHot j)) / 3 := by
  unfold T21WitnessWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp [div_eq_mul_inv, mul_comm]

/-- The explicit real probability law for clause (c), with positive marginals. -/
def T21_witnessAssignment : UnitExperiment (Fin 3) where
  weight := T21WitnessWeight
  nonnegative := by
    intro w
    unfold T21WitnessWeight
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> norm_num
  normalized := by
    simpa [Fin.sum_univ_succ] using T21_witness_sum (fun _ => 1)
  positive := by
    intro c
    rw [T21_witness_sum, T21_witness_sum]
    fin_cases c <;> norm_num [Fin.sum_univ_succ, T21OneHot]

/-- The actual partition and assignment law for the biased difference in means. -/
def T21_witnessExperiment : ClusterExperiment (Fin 4) (Fin 3) where
  cluster := T21WitnessCluster
  covers := by
    intro c
    fin_cases c
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  assignment := T21_witnessAssignment

/-- Only allocations treating exactly one cluster have positive mass. -/
theorem T21_witness_support (w : Fin 3 → Bool) (hw : 0 < T21WitnessWeight w) :
    w = T21OneHot 0 ∨ w = T21OneHot 1 ∨ w = T21OneHot 2 := by
  by_contra h
  simp only [not_or] at h
  norm_num [T21WitnessWeight, Fin.sum_univ_succ, h.1, h.2.1, h.2.2] at hw

/-- Assemble the three clauses from equal-marginal rescaling, existing HT
unbiasedness and complete-unit results, and direct finite witness arithmetic. -/
theorem T21_assembly (h1 : T21_L1) : T21WholeStatement := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Ω I _ _ _ D hD n hn hnN hm hc x z
    have hu := AronowAudit.P026.complete_units (Bridge.toDesign D) hD
      (Fintype.card I) n rfl hn hnN hm hc x z
    have hfalse (w : Ω) (hw : 0 < D.weight w) :
        (∑ i, indicator D false w i) = (Fintype.card I - n : ℕ) := by
      have hi (i : I) : indicator D false w i = 1 - indicator D true w i :=
        AronowAudit.P026.indicator_complement (Bridge.toDesign D) w i
      simp_rw [hi]
      rw [Finset.sum_sub_distrib, hc w hw, Nat.cast_sub hnN.le]
      simp
    have hdm (w : Ω) (hw : 0 < D.weight w) :
        differenceInMeans D x z w = observedArmSum D true x z w / n -
          observedArmSum D false x z w / (Fintype.card I - n : ℕ) := by
      unfold differenceInMeans
      rw [hc w hw, hfalse w hw]
    refine ⟨fun w hw => ⟨hfalse w hw, hu.1 w hw, hdm w hw⟩, hu.2, ?_⟩
    calc
      expectation D (differenceInMeans D x z) =
          expectation D (fun w => observedArmSum D true x z w / n -
            observedArmSum D false x z w / (Fintype.card I - n : ℕ)) := by
        unfold expectation
        apply Finset.sum_congr rfl
        intro w _
        by_cases hz : D.weight w = 0
        · simp [hz]
        · rw [hdm w (lt_of_le_of_ne (hD.1 w) (Ne.symm hz))]
      _ = ate (Fintype.card I) x z := hu.2
  · intro U _ _ _ M m hm hmM E _hseparated hmarg x z
    have hid := h1 (Fin M → Bool) U E.unitDesign (Fintype.card U) M m
      Fintype.card_pos hm hmM (fun i => hmarg (E.cluster i)) x z
    have hub := (AronowAudit.P026.ht_unbiased (Bridge.toDesign E.unitDesign)
      (Bridge.toCluster E).unit_probability (Bridge.toCluster E).unit_marginals
      (Fintype.card U) Fintype.card_pos x z).2.2
    refine ⟨hid, ?_, hub⟩
    have hf : T21ClusterContrast E.unitDesign (Fintype.card U) M m x z =
        ht E.unitDesign (Fintype.card U) x z := funext (fun w => (hid w).symm)
    rw [hf]
    exact hub
  · let E := T21_witnessExperiment
    have hmarg : ∀ c, marginal E.clusterDesign true c = 1 / 3 ∧
        marginal E.clusterDesign false c = 2 / 3 := by
      intro c
      change (∑ w, T21WitnessWeight w * (if w c = true then 1 else 0)) = 1 / 3 ∧
        (∑ w, T21WitnessWeight w * (if w c = false then 1 else 0)) = 2 / 3
      rw [T21_witness_sum, T21_witness_sum]
      fin_cases c <;> norm_num [Fin.sum_univ_succ, T21OneHot]
    have hunit : ∀ i, marginal E.unitDesign true i = 1 / 3 ∧
        marginal E.unitDesign false i = 2 / 3 := fun i => hmarg (E.cluster i)
    have hmean : expectation E.unitDesign
        (differenceInMeans E.unitDesign (![1, 1, 0, 0]) (![1, 1, 0, 0])) = 1 / 9 := by
      change (∑ w, T21WitnessWeight w *
        differenceInMeans E.unitDesign (![1, 1, 0, 0]) (![1, 1, 0, 0]) w) = 1 / 9
      rw [T21_witness_sum]
      simp only [Fin.sum_univ_succ, differenceInMeans, observedArmSum, indicator, observed,
        E, T21_witnessExperiment, ClusterExperiment.unitDesign, T21WitnessCluster, T21OneHot]
      norm_num
    have hate : ate 4 (![1, 1, 0, 0] : Fin 4 → ℝ) (![1, 1, 0, 0]) = 0 := by
      simp only [ate, sub_self, zero_div]
    have hht : expectation E.unitDesign
        (ht E.unitDesign 4 (![1, 1, 0, 0]) (![1, 1, 0, 0])) = 0 := by
      have h := (AronowAudit.P026.ht_unbiased (Bridge.toDesign E.unitDesign)
        (Bridge.toCluster E).unit_probability (Bridge.toCluster E).unit_marginals
        4 (by norm_num) (![1, 1, 0, 0]) (![1, 1, 0, 0])).2.2
      exact h.trans hate
    refine ⟨E, rfl, rfl, hmarg, hunit, ?_, ?_, ?_, hmean, hht, hate, ?_⟩
    · intro c d hcd
      change (∑ w, T21WitnessWeight w * (if w c ≠ w d then 1 else 0)) = 2 / 3
      rw [T21_witness_sum]
      fin_cases c <;> fin_cases d <;> try exact (hcd rfl).elim
      all_goals
        simp only [Fin.sum_univ_succ, T21OneHot]
        norm_num
    · intro w hw
      rcases T21_witness_support w hw with rfl | rfl | rfl <;>
        simp only [Fin.sum_univ_succ, indicator, E, T21_witnessExperiment,
          ClusterExperiment.clusterDesign, UnitExperiment.design,
          ClusterExperiment.unitDesign, T21WitnessCluster, T21OneHot] <;> norm_num
    · intro w hw
      rcases T21_witness_support w hw with rfl | rfl | rfl <;>
        simp only [Fin.sum_univ_succ, indicator, E, T21_witnessExperiment,
          ClusterExperiment.unitDesign, T21WitnessCluster, T21OneHot] <;> norm_num
    · rw [hmean, hate]
      norm_num

end
end SAP.P026b.WH.W1
