import SAP.P020.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P020.WH.W1.P.T5_L1
open scoped BigOperators
open SAP.P020 SAP.P020.Bridge
noncomputable section
private theorem expectation_congr_support {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) (h : ∀ s ∈ L.support, T s = U s) : expectation L T = expectation L U := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s hs]
private theorem expectation_mul_const_local {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (c : ℝ) : expectation L (fun s => T s * c) = expectation L T * c := by
  simp [expectation, ← Finset.sum_mul, ← mul_assoc]
private theorem expectation_const_mul_local {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (c : ℝ) : expectation L (fun s => c * T s) = c * expectation L T := by
  simpa [mul_comm c] using expectation_mul_const_local L T c
private theorem design_covariance_product_local {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) : designCovariance L T U = expectation L (fun s => T s * U s) - expectation L T * expectation L U := by
  unfold designCovariance
  have hfun : (fun s => (T s - expectation L T) * (U s - expectation L U)) =
      (fun s => T s * U s - T s * expectation L U - U s * expectation L T +
        expectation L T * expectation L U) := by
    funext s
    ring
  rw [hfun]
  unfold expectation
  simp [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← mul_assoc, L.total]
  ring
private theorem armCount_ne (P : ClusterPopulation) (a : Bool) : W1ArmCount P a ≠ 0 := by
  cases a
  · simp only [W1ArmCount, Bool.false_eq_true, ↓reduceIte]
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  · simp only [W1ArmCount, if_true]
    exact_mod_cast (Nat.ne_of_gt P.mt_pos)
private theorem observed_mean_count (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M)) : W1ArmCount P a * W1ObservedArmMean P a s = ∑ j ∈ W1ArmSet a s, observedTotal P s j := by
  unfold W1ObservedArmMean
  field_simp [armCount_ne P a]
private theorem observed_selected_eq (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M)) (j : Fin P.M) (hj : j ∈ W1ArmSet a s) : observedTotal P s j = (if a then P.y1 else P.y0) j := by
  cases a with
  | false =>
      have hj' : j ∉ s := by simpa [W1ArmSet, controls] using hj
      simp [observedTotal, hj']
  | true =>
      have hj' : j ∈ s := by simpa [W1ArmSet] using hj
      simp [observedTotal, hj']
private theorem observed_arm_sum (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M)) : (∑ j ∈ W1ArmSet a s, observedTotal P s j) = armSum P a (if a then P.y1 else P.y0) s := by
  unfold armSum
  apply Finset.sum_congr rfl
  intro j hj
  exact observed_selected_eq P a s j hj
private theorem observed_raj_sum (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) (s : Finset (Fin P.M)) : (∑ j ∈ W1ArmSet a s, (observedTotal P s j - khat s * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M))) = armSum P a (rajPotential P a (khat s)) s := by
  unfold armSum
  apply Finset.sum_congr rfl
  intro j hj
  rw [observed_selected_eq P a s j hj]
  have hsize : clusterMean (fun j : Fin P.M => (P.n j : ℝ)) =
      (populationSize P : ℝ) / P.M := by
    unfold clusterMean
    simp [populationSize, Nat.cast_sum]
  simp only [rajPotential, differenced]
  rw [hsize]
private theorem observed_raj_total (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) (s : Finset (Fin P.M)) (hs : s ∈ assignments P) : rajTotal P a (khat s) s = W1ObservedRajTotal P a khat s := by
  unfold rajTotal W1ObservedRajTotal
  rw [observed_raj_sum]
  simp [W1ArmCount]
private theorem armSum_bridge (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) : SAP.P020.armSum P a v = AronowAudit.P020.armSum (toPopulation P) a v := by
  funext s
  cases a <;> rfl
private theorem armSize_bridge (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M)) : SAP.P020.armSize P a s = AronowAudit.P020.armSize (toPopulation P) a s := by
  rfl
private theorem armMeanSize_bridge (P : ClusterPopulation) (a : Bool) : SAP.P020.armMeanSize P a = AronowAudit.P020.armMeanSize (toPopulation P) a := by
  rfl
private theorem rajPotential_bridge (P : ClusterPopulation) (a : Bool) (k : ℝ) : SAP.P020.rajPotential P a k = AronowAudit.P020.rajPotential (toPopulation P) a k := by
  rfl
private theorem rajTotal_bridge (P : ClusterPopulation) (a : Bool) (k : ℝ) : SAP.P020.rajTotal P a k = AronowAudit.P020.rajTotal (toPopulation P) a k := by
  rfl
private theorem expectation_bridge (P : ClusterPopulation) (T : Finset (Fin P.M) → ℝ) : expectation (clusterLaw P) T = AronowAudit.P020.expectation (AronowAudit.P020.clusterLaw (toPopulation P)) T := by
  rw [← Bridge.expectation_eq (clusterLaw P) T]
  rw [← Bridge.clusterLaw_eq P]
  rfl
private theorem design_covariance_bridge (P : ClusterPopulation) (T U : Finset (Fin P.M) → ℝ) : designCovariance (clusterLaw P) T U = AronowAudit.P020.designCovariance (AronowAudit.P020.clusterLaw (toPopulation P)) T U := by
  rfl
private theorem estimated_raj_total_mean_local (P : ClusterPopulation) (a : Bool) (khat : Finset (Fin P.M) → ℝ) : expectation (clusterLaw P) (fun s => rajTotal P a (khat s) s) = (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) * designCovariance (clusterLaw P) khat (armMeanSize P a) := by
  have hcov : designCovariance (clusterLaw P) khat (armMeanSize P a) =
      AronowAudit.P020.designCovariance
        (AronowAudit.P020.clusterLaw (toPopulation P)) khat
        (AronowAudit.P020.armMeanSize (toPopulation P) a) := by
    rfl
  calc
    expectation (clusterLaw P) (fun s => rajTotal P a (khat s) s) =
        AronowAudit.P020.expectation
          (AronowAudit.P020.clusterLaw (toPopulation P))
          (fun s => AronowAudit.P020.rajTotal (toPopulation P) a (khat s) s) := by
            rfl
    _ = (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
          AronowAudit.P020.designCovariance
            (AronowAudit.P020.clusterLaw (toPopulation P)) khat
            (AronowAudit.P020.armMeanSize (toPopulation P) a) := by
          exact AronowAudit.P020.estimated_raj_total_mean (toPopulation P) a khat
    _ = (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
          designCovariance (clusterLaw P) khat (armMeanSize P a) := by
          rw [← hcov]
private theorem expected_arm_sum_local (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) : expectation (clusterLaw P) (armSum P a v) = ((if a then P.mt else controlCount P : ℕ) : ℝ) / P.M * ∑ j, v j := by
  rw [← Bridge.expectation_eq (clusterLaw P) (armSum P a v)]
  rw [← Bridge.clusterLaw_eq P]
  rw [armSum_bridge]
  calc
    AronowAudit.P020.expectation
        (AronowAudit.P020.clusterLaw (toPopulation P))
        (AronowAudit.P020.armSum (toPopulation P) a v) =
      (if a then ((toPopulation P).mt : ℝ) else
        (AronowAudit.P020.controlCount (toPopulation P) : ℝ)) /
          (toPopulation P).M * ∑ j, v j :=
        AronowAudit.P020.expected_arm_sum (toPopulation P) a v
    _ = ((if a then P.mt else controlCount P : ℕ) : ℝ) / P.M *
          ∑ j, v j := by
        simp [Bridge.toPopulation, SAP.P020.controlCount,
          AronowAudit.P020.controlCount, Nat.cast_ite]
private theorem expected_arm_mean_size_local (P : ClusterPopulation) (a : Bool) : expectation (clusterLaw P) (armMeanSize P a) = (populationSize P : ℝ) / P.M := by
  rw [← Bridge.expectation_eq (clusterLaw P) (armMeanSize P a)]
  rw [← Bridge.clusterLaw_eq P]
  rw [armMeanSize_bridge]
  exact AronowAudit.P020.expected_arm_mean_size (toPopulation P) a
private theorem expected_observed_arm_mean_count (P : ClusterPopulation) (a : Bool) : expectation (clusterLaw P) (fun s => W1ArmCount P a * W1ObservedArmMean P a s) = W1ArmCount P a / P.M * ∑ j, (if a then P.y1 else P.y0) j := by
  calc
    expectation (clusterLaw P)
        (fun s => W1ArmCount P a * W1ObservedArmMean P a s) =
      expectation (clusterLaw P)
        (fun s => armSum P a (if a then P.y1 else P.y0) s) := by
          apply expectation_congr_support
          intro s hs
          rw [observed_mean_count, observed_arm_sum]
    _ = W1ArmCount P a / P.M * ∑ j, (if a then P.y1 else P.y0) j := by
        simpa [W1ArmCount] using
          expected_arm_sum_local P a (if a then P.y1 else P.y0)
private theorem expectation_observed_equals_raj (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : expectation (clusterLaw P) (fun s => rajTotal P a (khat s) s) = expectation (clusterLaw P) (W1ObservedRajTotal P a khat) := by
  apply expectation_congr_support
  intro s hs
  have hs' : s ∈ assignments P := by simpa [clusterLaw, uniformLaw] using hs
  exact observed_raj_total P khat a s hs'
private theorem first_sum_eq_second_sum (P : ClusterPopulation) (a : Bool) : expectation (clusterLaw P) (fun s => ∑ j ∈ W1ArmSet a s, observedTotal P s j) = expectation (clusterLaw P) (fun s => W1ArmCount P a * W1ObservedArmMean P a s) := by
  apply expectation_congr_support
  intro s hs
  rw [observed_mean_count]
private theorem adjusted_size_sum_eq (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) (s : Finset (Fin P.M)) : khat s * W1ArmCount P a * armMeanSize P a s = ∑ j ∈ W1ArmSet a s, khat s * (P.n j : ℝ) := by
  calc
    khat s * W1ArmCount P a * armMeanSize P a s =
        khat s * armSize P a s := by
          have hm : ((if a then P.mt else controlCount P : ℕ) : ℝ) ≠ 0 := by
            cases a
            · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
            · exact_mod_cast (Nat.ne_of_gt P.mt_pos)
          simp only [W1ArmCount]
          unfold armMeanSize
          field_simp [hm]
          push_cast
          ring
    _ = ∑ j ∈ W1ArmSet a s, khat s * (P.n j : ℝ) := by
          unfold armSize armSum W1ArmSet
          rw [← Finset.mul_sum]
private theorem adjusted_size_expectation_eq (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * armMeanSize P a s) = expectation (clusterLaw P) (fun s => ∑ j ∈ W1ArmSet a s, khat s * (P.n j : ℝ)) := by
  apply expectation_congr_support
  intro s hs
  exact adjusted_size_sum_eq P khat a s
private theorem adjusted_constant_sum_expectation_eq (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : expectation (clusterLaw P) (fun s => ∑ _j ∈ W1ArmSet a s, khat s * (populationSize P : ℝ) / P.M) = expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * (populationSize P : ℝ) / P.M) := by
  apply expectation_congr_support
  intro s hs
  have hs' : s ∈ assignments P := by simpa [clusterLaw, uniformLaw] using hs
  have hcard : (W1ArmSet a s).card =
      (if a then P.mt else controlCount P) := by
    cases a
    · simp only [W1ArmSet, Bool.false_eq_true, ↓reduceIte]
      exact (AronowAudit.P020.assignment_arm_counts (toPopulation P) s hs').2
    · simp only [W1ArmSet, if_true]
      exact (AronowAudit.P020.assignment_arm_counts (toPopulation P) s hs').1
  cases a <;> simp [Finset.sum_const, nsmul_eq_mul, hcard, W1ArmCount] <;>
    push_cast <;> ring
private theorem observed_adjusted_B_eq_C (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : (P.M : ℝ) / W1ArmCount P a * (expectation (clusterLaw P) (fun s => ∑ j ∈ W1ArmSet a s, observedTotal P s j) - expectation (clusterLaw P) (fun s => ∑ j ∈ W1ArmSet a s, khat s * (P.n j : ℝ)) + expectation (clusterLaw P) (fun s => ∑ _j ∈ W1ArmSet a s, khat s * (populationSize P : ℝ) / P.M)) = (P.M : ℝ) / W1ArmCount P a * (expectation (clusterLaw P) (fun s => W1ArmCount P a * W1ObservedArmMean P a s) - expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * armMeanSize P a s) + expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * (populationSize P : ℝ) / P.M)) := by
  rw [first_sum_eq_second_sum, adjusted_size_expectation_eq,
    adjusted_constant_sum_expectation_eq]
private theorem adjusted_mean_expectation_eq (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * armMeanSize P a s) = W1ArmCount P a * expectation (clusterLaw P) (fun s => khat s * armMeanSize P a s) := by
  calc
    expectation (clusterLaw P)
        (fun s => khat s * W1ArmCount P a * armMeanSize P a s) =
      expectation (clusterLaw P)
        (fun s => (khat s * armMeanSize P a s) * W1ArmCount P a) := by
          apply expectation_congr_support
          intro s hs
          ring
    _ = expectation (clusterLaw P)
          (fun s => khat s * armMeanSize P a s) * W1ArmCount P a := by
          exact expectation_mul_const_local
            (clusterLaw P) _ (W1ArmCount P a)
    _ = W1ArmCount P a * expectation (clusterLaw P)
          (fun s => khat s * armMeanSize P a s) := by ring
private theorem adjusted_constant_expectation_eq (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * (populationSize P : ℝ) / P.M) = W1ArmCount P a * ((populationSize P : ℝ) / P.M) * expectation (clusterLaw P) khat := by
  calc
    expectation (clusterLaw P)
        (fun s => khat s * W1ArmCount P a * (populationSize P : ℝ) / P.M) =
      expectation (clusterLaw P)
        (fun s => khat s * (W1ArmCount P a * ((populationSize P : ℝ) / P.M))) := by
          apply expectation_congr_support
          intro s hs
          ring
    _ = expectation (clusterLaw P) khat *
          (W1ArmCount P a * ((populationSize P : ℝ) / P.M)) := by
          exact expectation_mul_const_local
            (clusterLaw P) khat
            (W1ArmCount P a * ((populationSize P : ℝ) / P.M))
    _ = W1ArmCount P a * ((populationSize P : ℝ) / P.M) *
          expectation (clusterLaw P) khat := by ring
private theorem adjusted_C_eq_D (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : (P.M : ℝ) / W1ArmCount P a * (expectation (clusterLaw P) (fun s => W1ArmCount P a * W1ObservedArmMean P a s) - expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * armMeanSize P a s) + expectation (clusterLaw P) (fun s => khat s * W1ArmCount P a * (populationSize P : ℝ) / P.M)) = (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) * (expectation (clusterLaw P) (fun s => khat s * armMeanSize P a s) - expectation (clusterLaw P) khat * expectation (clusterLaw P) (armMeanSize P a)) := by
  have hEmean := expected_arm_mean_size_local P a
  have hEy := expected_observed_arm_mean_count P a
  have hEy' : expectation (clusterLaw P)
      (fun s => W1ArmCount P a * W1ObservedArmMean P a s) =
      W1ArmCount P a / P.M * ∑ j, (if a then P.y1 else P.y0) j := by
    simpa [W1ArmCount] using hEy
  rw [adjusted_mean_expectation_eq, adjusted_constant_expectation_eq,
    hEy', hEmean]
  have hm : W1ArmCount P a ≠ 0 := armCount_ne P a
  have hM : (P.M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  field_simp [hm, hM]
  <;> ring
end
end SAP.P020.WH.W1.P.T5_L1
namespace SAP.P020.WH.W1
open SAP.P020 SAP.P020.Bridge SAP.P020.WH.W1.P.T5_L1
theorem T5_L1_proof : SAP.P020.WH.W1.T5_L1 := by
  intro P khat a
  dsimp only [W1RajExpectationChain]
  -- The remaining goal is the seven-link expectation chain.
  constructor
  · intro s hs
    have hs' : s ∈ assignments P := by simpa [clusterLaw, uniformLaw] using hs
    exact observed_raj_total P khat a s hs'
  constructor
  · exact expected_arm_mean_size_local P a
  constructor
  · exact expected_observed_arm_mean_count P a
  constructor
  · exact expectation_observed_equals_raj P khat a
  constructor
  · have hOD : expectation (clusterLaw P) (W1ObservedRajTotal P a khat) =
        (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
          designCovariance (clusterLaw P) khat (armMeanSize P a) := by
      calc
        expectation (clusterLaw P) (W1ObservedRajTotal P a khat) =
            expectation (clusterLaw P) (fun s => rajTotal P a (khat s) s) :=
              (expectation_observed_equals_raj P khat a).symm
        _ = (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
              designCovariance (clusterLaw P) khat (armMeanSize P a) :=
              estimated_raj_total_mean_local P a khat
    have hODD : expectation (clusterLaw P) (W1ObservedRajTotal P a khat) =
        (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
          (expectation (clusterLaw P)
              (fun s => khat s * armMeanSize P a s) -
           expectation (clusterLaw P) khat *
              expectation (clusterLaw P) (armMeanSize P a)) := by
      rw [hOD, design_covariance_product_local, expected_arm_mean_size_local]
    calc
      expectation (clusterLaw P) (W1ObservedRajTotal P a khat) =
          (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
            (expectation (clusterLaw P)
                (fun s => khat s * armMeanSize P a s) -
             expectation (clusterLaw P) khat *
                expectation (clusterLaw P) (armMeanSize P a)) := hODD
      _ = (P.M : ℝ) / W1ArmCount P a *
          (expectation (clusterLaw P)
              (fun s => W1ArmCount P a * W1ObservedArmMean P a s) -
           expectation (clusterLaw P)
              (fun s => khat s * W1ArmCount P a * armMeanSize P a s) +
           expectation (clusterLaw P)
              (fun s => khat s * W1ArmCount P a * (populationSize P : ℝ) / P.M)) :=
            (adjusted_C_eq_D P khat a).symm
      _ = (P.M : ℝ) / W1ArmCount P a *
          (expectation (clusterLaw P)
              (fun s => ∑ j ∈ W1ArmSet a s, observedTotal P s j) -
           expectation (clusterLaw P)
              (fun s => ∑ j ∈ W1ArmSet a s, khat s * (P.n j : ℝ)) +
           expectation (clusterLaw P)
              (fun s => ∑ _j ∈ W1ArmSet a s,
                khat s * (populationSize P : ℝ) / P.M)) :=
            (observed_adjusted_B_eq_C P khat a).symm
  constructor
  · exact observed_adjusted_B_eq_C P khat a
  constructor
  · exact adjusted_C_eq_D P khat a
  · rw [design_covariance_product_local, expected_arm_mean_size_local]
end SAP.P020.WH.W1
