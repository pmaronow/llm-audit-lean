import SAP.P020.Defs.WholeW3
import SAP.P020.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020.WH.W3

open scoped BigOperators
open SAP.P020.Bridge

noncomputable section

/-- The whole T13 needs no unproved leaves. Existing complete-randomization
first moments prove the arm-mean centering calculation by finite linearity;
the two existing Des Raj unbiasedness theorems give all six original identities.
No independence of cluster indicators or variance/rank condition is used. -/
theorem T13_assembly : T13WholeStatement_W3 := by
  have hsize (P : ClusterPopulation) (a : Bool) :
      expectation (clusterLaw P)
        (fun s => armMeanSize P a s - (populationSize P : ℝ) / P.M) = 0 := by
    have hsub : expectation (clusterLaw P)
          (fun s => armMeanSize P a s - (populationSize P : ℝ) / P.M) =
        expectation (clusterLaw P) (armMeanSize P a) -
          expectation (clusterLaw P) (fun _ => (populationSize P : ℝ) / P.M) :=
      AronowAudit.P020.expectation_sub (toLaw (clusterLaw P)) _ _
    have he : expectation (clusterLaw P) (armMeanSize P a) =
        (populationSize P : ℝ) / P.M :=
      AronowAudit.P020.expected_arm_mean_size (toPopulation P) a
    have hc : expectation (clusterLaw P) (fun _ => (populationSize P : ℝ) / P.M) =
        (populationSize P : ℝ) / P.M :=
      AronowAudit.P020.expectation_const (toLaw (clusterLaw P)) _
    rw [hsub, he, hc, sub_self]
  have hmean (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) :
      expectation (clusterLaw P)
        (fun s => armSum P a v s / (if a then P.mt else controlCount P)) =
      clusterMean v := by
    have hmul (c : ℝ) : expectation (clusterLaw P) (fun s => armSum P a v s * c) =
        expectation (clusterLaw P) (armSum P a v) * c :=
      AronowAudit.P020.expectation_mul_const (toLaw (clusterLaw P)) _ c
    have hsum : expectation (clusterLaw P) (armSum P a v) =
        ((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j :=
      AronowAudit.P020.expected_arm_sum (toPopulation P) a v
    simp_rw [div_eq_mul_inv]
    rw [hmul, hsum]
    have ha : ((if a then P.mt else controlCount P) : ℝ) ≠ 0 := by
      cases a
      · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
      · exact_mod_cast (Nat.ne_of_gt P.mt_pos)
    have hM : (P.M : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
      unfold clusterMean <;> field_simp
  have hcenter (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) :
      expectation (clusterLaw P) (centeredArmMeanW3 P a v) = 0 := by
    have hsub := AronowAudit.P020.expectation_sub (toLaw (clusterLaw P))
      (fun s => armSum P a v s / (if a then P.mt else controlCount P))
      (fun _ => clusterMean v)
    change expectation (clusterLaw P) (centeredArmMeanW3 P a v) =
      expectation (clusterLaw P)
          (fun s => armSum P a v s / (if a then P.mt else controlCount P)) -
        expectation (clusterLaw P) (fun _ => clusterMean v) at hsub
    rw [hsub, hmean]
    have hc : expectation (clusterLaw P) (fun _ => clusterMean v) = clusterMean v :=
      AronowAudit.P020.expectation_const (toLaw (clusterLaw P)) (clusterMean v)
    rw [hc, sub_self]
  have hmultiple (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) (k : ℝ) :
      expectation (clusterLaw P) (fun s => k * centeredArmMeanW3 P a v s) = 0 := by
    have hm : expectation (clusterLaw P) (fun s => k * centeredArmMeanW3 P a v s) =
        k * expectation (clusterLaw P) (centeredArmMeanW3 P a v) :=
      AronowAudit.P020.expectation_const_mul (toLaw (clusterLaw P))
        (centeredArmMeanW3 P a v) k
    rw [hm, hcenter, mul_zero]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro P k
    exact AronowAudit.P020.des_raj_unbiased (toPopulation P) k
  · intro P A X ks ka
    exact AronowAudit.P020.des_raj_covariates_unbiased (toPopulation P) X ks ka
  · intro P a k
    have hm : expectation (clusterLaw P)
          (fun s => k * (armMeanSize P a s - (populationSize P : ℝ) / P.M)) =
        k * expectation (clusterLaw P)
          (fun s => armMeanSize P a s - (populationSize P : ℝ) / P.M) :=
      AronowAudit.P020.expectation_const_mul (toLaw (clusterLaw P)) _ k
    exact ⟨hm, hsize P a, by rw [hm, hsize, mul_zero]⟩
  · intro P A X ks ka a
    have hadd : expectation (clusterLaw P) (fun s =>
          ks * centeredArmMeanW3 P a (fun j => (P.n j : ℝ)) s +
            ∑ cov, ka cov * centeredArmMeanW3 P a (X cov) s) =
        expectation (clusterLaw P)
          (fun s => ks * centeredArmMeanW3 P a (fun j => (P.n j : ℝ)) s) +
        expectation (clusterLaw P)
          (fun s => ∑ cov, ka cov * centeredArmMeanW3 P a (X cov) s) :=
      AronowAudit.P020.expectation_add (toLaw (clusterLaw P)) _ _
    rw [hadd, hmultiple, zero_add]
    have hsum : expectation (clusterLaw P)
          (fun s => ∑ cov, ka cov * centeredArmMeanW3 P a (X cov) s) =
        ∑ cov, expectation (clusterLaw P)
          (fun s => ka cov * centeredArmMeanW3 P a (X cov) s) := by
      unfold expectation
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hsum]
    simp only [hmultiple, Finset.sum_const_zero]
  · intro P a k
    exact (AronowAudit.P020.raj_total_unbiased (toPopulation P) a k).trans
      (AronowAudit.P020.ht_total_unbiased (toPopulation P) a).symm
  · intro P A X ks ka a
    exact (AronowAudit.P020.raj_covariate_total_unbiased (toPopulation P) X ks ka a).trans
      (AronowAudit.P020.ht_total_unbiased (toPopulation P) a).symm

end

end SAP.P020.WH.W3
