import SAP.P033.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P033.WH.W1.P.T4_L1

open SAP.P033.WH.W1
open scoped BigOperators

lemma active_val (n : ℕ) (i : Fin n) :
    (wholeActiveIndex n i).val = i.val := by
  simp [wholeActiveIndex]

lemma physical_ratio (n : ℕ) (hn : 0 < n) (j : Fin (n*(n+1))) :
    wholePhysicalDistance n j / wholeBandwidth n =
      ((j : ℝ)+1)/((n : ℝ)+1) := by
  unfold wholePhysicalDistance wholeBandwidth
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn1R : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hnR, hn1R]

lemma physical_kernel_pos_iff (n : ℕ) (hn : 0 < n)
    (j : Fin (n*(n+1))) :
    0 < wholePhysicalKernel n j ↔ j.val < n := by
  unfold wholePhysicalKernel
  rw [physical_ratio n hn j]
  have hnonneg : 0 ≤ ((j : ℝ)+1)/((n : ℝ)+1) := by positivity
  rw [abs_of_nonneg hnonneg, lt_max_iff]
  simp only [lt_self_iff_false, false_or, sub_pos]
  rw [div_lt_one (by positivity : 0 < (n : ℝ)+1)]
  have hnat : j.val + 1 < n + 1 ↔ j.val < n := by omega
  exact_mod_cast hnat

lemma physical_kernel_zero_of_not_lt (n : ℕ) (hn : 0 < n)
    (j : Fin (n*(n+1))) (hj : ¬ j.val < n) :
    wholePhysicalKernel n j = 0 := by
  have hnot : ¬ 0 < wholePhysicalKernel n j := by
    intro h
    exact hj ((physical_kernel_pos_iff n hn j).mp h)
  apply le_antisymm
  · exact le_of_not_gt hnot
  · exact le_max_left _ _

lemma active_kernel_eq (n : ℕ) (hn : 0 < n) (i : Fin n) :
    wholePhysicalKernel n (wholeActiveIndex n i) = shrinkingKernel n i := by
  rw [wholePhysicalKernel, physical_ratio n hn (wholeActiveIndex n i), active_val]
  have hx : 0 ≤ ((i : ℝ)+1)/((n : ℝ)+1) := by positivity
  have hnat : i.val + 1 < n + 1 := Nat.add_lt_add_right i.isLt 1
  have hreal : (i.val : ℝ) + 1 < (n : ℝ) + 1 := by exact_mod_cast hnat
  have hlt : ((i : ℝ)+1)/((n : ℝ)+1) < 1 :=
    (div_lt_one (by positivity : 0 < (n : ℝ)+1)).2 hreal
  rw [abs_of_nonneg hx, max_eq_right (le_of_lt (sub_pos.mpr hlt))]
  rw [shrinkingKernel, shrinkingDistance]

lemma sum_lt_reindex (n : ℕ) (g : Fin (n*(n+1)) → ℝ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (n*(n+1)) => j.val < n), g j) =
      ∑ i : Fin n, g (wholeActiveIndex n i) := by
  symm
  refine Finset.sum_bij (fun i _ => wholeActiveIndex n i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [active_val]
    exact i.isLt
  · intro i hi i' hi' heq
    apply Fin.ext
    simpa only [active_val] using congrArg Fin.val heq
  · intro j hj
    have hjval : j.val < n := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val, hjval⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro i hi
    rfl

lemma kernel_sum_reduction (n : ℕ) (hn : 0 < n)
    (F : Fin (n*(n+1)) → ℝ) :
    (∑ j, wholePhysicalKernel n j * F j) =
      ∑ i : Fin n, shrinkingKernel n i * F (wholeActiveIndex n i) := by
  have hzero : ∀ j : Fin (n*(n+1)), ¬ j.val < n →
      wholePhysicalKernel n j * F j = 0 := by
    intro j hj
    rw [physical_kernel_zero_of_not_lt n hn j hj]
    ring
  calc
    (∑ j, wholePhysicalKernel n j * F j) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin (n*(n+1)) => j.val < n),
          wholePhysicalKernel n j * F j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjnot
      have hjlt : ¬ j.val < n := by
        intro h
        exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact hzero j hjlt
    _ = ∑ i : Fin n,
        wholePhysicalKernel n (wholeActiveIndex n i) * F (wholeActiveIndex n i) :=
      sum_lt_reindex n (fun j => wholePhysicalKernel n j * F j)
    _ = ∑ i : Fin n, shrinkingKernel n i * F (wholeActiveIndex n i) := by
      congr 1
      funext i
      rw [active_kernel_eq n hn i]

lemma padded_active_eq (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    wholePaddedWeight n a (wholeActiveIndex n i) = a i := by
  unfold wholePaddedWeight
  simp [active_val]

lemma padded_sum_reduction (n : ℕ) (a : Fin n → ℝ)
    (F : Fin (n*(n+1)) → ℝ) :
    (∑ j, wholePaddedWeight n a j * F j) =
      ∑ i : Fin n, a i * F (wholeActiveIndex n i) := by
  have hzero : ∀ j : Fin (n*(n+1)), ¬ j.val < n →
      wholePaddedWeight n a j * F j = 0 := by
    intro j hj
    rw [wholePaddedWeight]
    simp [hj]
  calc
    (∑ j, wholePaddedWeight n a j * F j) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin (n*(n+1)) => j.val < n),
          wholePaddedWeight n a j * F j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjnot
      have hjlt : ¬ j.val < n := by
        intro h
        exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact hzero j hjlt
    _ = ∑ i : Fin n,
        wholePaddedWeight n a (wholeActiveIndex n i) * F (wholeActiveIndex n i) :=
      sum_lt_reindex n (fun j => wholePaddedWeight n a j * F j)
    _ = ∑ i : Fin n, a i * F (wholeActiveIndex n i) := by
      congr 1
      funext i
      rw [padded_active_eq]

end SAP.P033.WH.W1.P.T4_L1

theorem SAP.P033.WH.W1.T4_L1_proof : SAP.P033.WH.W1.T4_L1 := by
  intro n hnNat
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnorm (j : Fin (n*(n+1))) :
      wholePhysicalDistance n j / wholeBandwidth n = ((j : ℝ)+1)/((n : ℝ)+1) :=
    SAP.P033.WH.W1.P.T4_L1.physical_ratio n hn j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold wholeBandwidth
    exact one_div_pos.mpr hnR
  · exact hnorm
  · intro j
    exact SAP.P033.WH.W1.P.T4_L1.physical_kernel_pos_iff n hn j
  · have hfilter :
        Finset.univ.filter (fun j : Fin (n*(n+1)) => 0 < wholePhysicalKernel n j) =
          Finset.univ.filter (fun j : Fin (n*(n+1)) => j.val < n) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact SAP.P033.WH.W1.P.T4_L1.physical_kernel_pos_iff n hn j
    rw [hfilter, Fin.card_filter_val_lt,
      Nat.min_eq_right (Nat.le_mul_of_pos_right n (Nat.succ_pos n))]
  · intro j
    exact SAP.P033.WH.W1.P.T4_L1.active_kernel_eq n hn j
  · intro F
    exact SAP.P033.WH.W1.P.T4_L1.kernel_sum_reduction n hn F
  · intro a F
    exact SAP.P033.WH.W1.P.T4_L1.padded_sum_reduction n a F
