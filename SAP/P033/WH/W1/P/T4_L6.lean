import SAP.P033.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P033.WH.W1.P.T4_L6

open SAP.P033.WH.W1
open scoped BigOperators

noncomputable section

def sideCoefficient (n : ℕ) (a : Fin n → ℝ)
    (g : Fin 2 × Fin (n*(n+1))) : ℝ :=
  if g.1 = 0 then -wholePaddedWeight n a g.2 else wholePaddedWeight n a g.2

def noisyCoefficient (n : ℕ) (a : Fin n → ℝ)
    (g : (Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5)) : ℝ :=
  Sum.elim (sideCoefficient n a) (fun gi => sideCoefficient n a gi.1 / 5) g

theorem sum_positions {N n : ℕ} (h : n ≤ N) (f : Fin N → ℝ) :
    (∑ j : Fin N, if j.val < n then f j else 0) =
      ∑ i : Fin n, f ⟨i.val, by omega⟩ := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun i _ => (⟨i.val, by omega⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact i.isLt
  · intro i hi j hj hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    exact hv
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.val, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro i hi
    rfl

theorem padded_weight_sq_sum (n : ℕ) (hn : 3 ≤ n) (a : Fin n → ℝ) :
    (∑ j : Fin (n*(n+1)), wholePaddedWeight n a j ^ 2) = ∑ j : Fin n, a j ^ 2 := by
  have hsum := sum_positions (N := n*(n+1)) (n := n)
    (Nat.le_mul_of_pos_right n (Nat.succ_pos n))
    (fun j => a ⟨j.val % n, Nat.mod_lt _ (by omega)⟩ ^ 2)
  have hpad :
      (∑ j : Fin (n*(n+1)), wholePaddedWeight n a j ^ 2) =
        ∑ j : Fin (n*(n+1)), if h : j.val < n then
          a ⟨j.val % n, Nat.mod_lt _ (by omega)⟩ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j.val < n
    · simp [wholePaddedWeight, h, Nat.mod_eq_of_lt h]
    · simp [wholePaddedWeight, h]
  calc
    (∑ j : Fin (n*(n+1)), wholePaddedWeight n a j ^ 2) =
        ∑ j : Fin (n*(n+1)), if h : j.val < n then
          a ⟨j.val % n, Nat.mod_lt _ (by omega)⟩ ^ 2 else 0 := hpad
    _ = ∑ i : Fin n, a ⟨i.val % n, Nat.mod_lt _ (by omega)⟩ ^ 2 := hsum
    _ = ∑ i : Fin n, a i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]

theorem side_linear_identity {n : ℕ} (a : Fin n → ℝ)
    (x : Fin 2 × Fin (n*(n+1)) → ℝ) :
    (∑ j : Fin (n*(n+1)), wholePaddedWeight n a j *
      (x (1,j) - x (0,j))) =
        ∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g * x g := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [sideCoefficient]
  rw [Fin.sum_univ_succ]
  simp
  ring

theorem sign_estimator_sum (n : ℕ) (a : Fin n → ℝ) :
    wholePaddedSignEstimator n a = fun data =>
      ∑ g : Fin 2 × Fin (n*(n+1)),
        sideCoefficient n a g * signShock (data g) := by
  funext data
  have hmean (s : Fin 2) (j : Fin (n*(n+1))) :
      wholeClusterMean n (fun k (_ : Fin 5) => signShock (data (s,k))) j =
        signShock (data (s,j)) := by
    unfold wholeClusterMean
    simp [Finset.sum_const, Finset.card_univ]
  rw [wholePaddedSignEstimator, wholePaddedEstimator]
  change (∑ j : Fin (n*(n+1)), wholePaddedWeight n a j *
      (wholeClusterMean n (fun k (_ : Fin 5) => signShock (data (1,k))) j -
       wholeClusterMean n (fun k (_ : Fin 5) => signShock (data (0,k))) j)) = _
  simp_rw [hmean]
  exact side_linear_identity a (fun g => signShock (data g))

theorem noisy_cluster_mean (n : ℕ)
    (data : ((Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5)) → Bool)
    (s : Fin 2) (j : Fin (n*(n+1))) :
    wholeClusterMean n
      (fun k (i : Fin 5) => signShock (data (.inl (s,k))) + signShock (data (.inr ((s,k),i)))) j =
      signShock (data (.inl (s,j))) + (∑ i : Fin 5, signShock (data (.inr ((s,j),i)))) / 5 := by
  unfold wholeClusterMean
  rw [Finset.sum_add_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem noisy_estimator_sum (n : ℕ) (a : Fin n → ℝ) :
    wholePaddedNoisyEstimator n a = fun data =>
      ∑ g : (Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5),
        noisyCoefficient n a g * signShock (data g) := by
  funext data
  let x : Fin 2 × Fin (n*(n+1)) → ℝ := fun g =>
    signShock (data (.inl g)) + (∑ i : Fin 5, signShock (data (.inr (g,i)))) / 5
  have hmean (s : Fin 2) (j : Fin (n*(n+1))) :
      wholeClusterMean n
        (fun k (i : Fin 5) => signShock (data (.inl (s,k))) + signShock (data (.inr ((s,k),i)))) j =
          signShock (data (.inl (s,j))) + (∑ i : Fin 5, signShock (data (.inr ((s,j),i)))) / 5 := by
    exact noisy_cluster_mean n data s j
  have hsum := side_linear_identity a x
  rw [wholePaddedNoisyEstimator, wholePaddedEstimator]
  change (∑ j : Fin (n*(n+1)), wholePaddedWeight n a j *
      (wholeClusterMean n (fun k (i : Fin 5) => signShock (data (.inl (1,k))) +
          signShock (data (.inr ((1,k),i)))) j -
       wholeClusterMean n (fun k (i : Fin 5) => signShock (data (.inl (0,k))) +
          signShock (data (.inr ((0,k),i)))) j)) = _
  simp_rw [hmean]
  rw [hsum]
  let cluster : Fin 2 × Fin (n*(n+1)) → ℝ := fun g => signShock (data (.inl g))
  let recordMean : Fin 2 × Fin (n*(n+1)) → ℝ := fun g =>
    (∑ i : Fin 5, signShock (data (.inr (g,i)))) / 5
  have hsplit :
      (∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g * x g) =
        (∑ g, sideCoefficient n a g * cluster g) +
          ∑ g, sideCoefficient n a g * recordMean g := by
    calc
      _ = ∑ g, (sideCoefficient n a g * cluster g +
          sideCoefficient n a g * recordMean g) := by
        apply Finset.sum_congr rfl
        intro g hg
        dsimp [x, cluster, recordMean]
        ring
      _ = _ := Finset.sum_add_distrib
  have hrecord :
      (∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g * recordMean g) =
        ∑ gi : (Fin 2 × Fin (n*(n+1))) × Fin 5,
          sideCoefficient n a gi.1 / 5 * signShock (data (.inr gi)) := by
    calc
      _ = ∑ g : Fin 2 × Fin (n*(n+1)), ∑ i : Fin 5,
          sideCoefficient n a g / 5 * signShock (data (.inr (g,i))) := by
        apply Finset.sum_congr rfl
        intro g hg
        dsimp [recordMean]
        calc
          sideCoefficient n a g * ((∑ i : Fin 5, signShock (data (.inr (g,i)))) / 5) =
              (sideCoefficient n a g / 5) * ∑ i : Fin 5, signShock (data (.inr (g,i))) := by ring
          _ = ∑ i : Fin 5, sideCoefficient n a g / 5 * signShock (data (.inr (g,i))) := by
            rw [Finset.mul_sum]
      _ = _ := by
        symm
        rw [Fintype.sum_prod_type]
  have hnoise :
      (∑ g : (Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5),
        noisyCoefficient n a g * signShock (data g)) =
        (∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g * cluster g) +
          ∑ gi : (Fin 2 × Fin (n*(n+1))) × Fin 5,
            sideCoefficient n a gi.1 / 5 * signShock (data (.inr gi)) := by
    rw [Fintype.sum_sum_type]
    simp only [noisyCoefficient, Sum.elim_inl, Sum.elim_inr, cluster]
  calc
    (∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g * x g) =
        (∑ g, sideCoefficient n a g * cluster g) +
          ∑ g, sideCoefficient n a g * recordMean g := hsplit
    _ = (∑ g, sideCoefficient n a g * cluster g) +
          ∑ gi : (Fin 2 × Fin (n*(n+1))) × Fin 5,
            sideCoefficient n a gi.1 / 5 * signShock (data (.inr gi)) := by rw [hrecord]
    _ = ∑ g : (Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5),
          noisyCoefficient n a g * signShock (data g) := hnoise.symm

theorem side_coefficient_sq_sum (n : ℕ) (hn : 3 ≤ n) (a : Fin n → ℝ) :
    (∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g ^ 2) =
      2 * ∑ j : Fin n, a j ^ 2 := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ j : Fin (n*(n+1)), ∑ s : Fin 2, sideCoefficient n a (s,j) ^ 2) =
        ∑ j : Fin (n*(n+1)), 2 * wholePaddedWeight n a j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [sideCoefficient]
      rw [Fin.sum_univ_succ]
      simp
      ring
    _ = 2 * ∑ j : Fin (n*(n+1)), wholePaddedWeight n a j ^ 2 := by
      rw [Finset.mul_sum]
    _ = 2 * ∑ j : Fin n, a j ^ 2 := by rw [padded_weight_sq_sum n hn a]

theorem noisy_coefficient_sq_sum (n : ℕ) (hn : 3 ≤ n) (a : Fin n → ℝ) :
    (∑ g : (Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5),
      noisyCoefficient n a g ^ 2) =
        (6/5:ℝ) * (2 * ∑ j : Fin n, a j ^ 2) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [noisyCoefficient, Sum.elim_inl, Sum.elim_inr]
  have hs := side_coefficient_sq_sum n hn a
  have hrec :
      (∑ gi : (Fin 2 × Fin (n*(n+1))) × Fin 5,
        (sideCoefficient n a gi.1 / 5) ^ 2) =
        (1/5:ℝ) * ∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g ^ 2 := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ g : Fin 2 × Fin (n*(n+1)), 5 * (sideCoefficient n a g / 5) ^ 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        simp [Finset.sum_const, Finset.card_univ]
      _ = ∑ g : Fin 2 × Fin (n*(n+1)), (1/5:ℝ) * sideCoefficient n a g ^ 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        ring
      _ = (1/5:ℝ) * ∑ g : Fin 2 × Fin (n*(n+1)), sideCoefficient n a g ^ 2 := by
        rw [← Finset.mul_sum]
  rw [hrec, hs]
  ring

end
end SAP.P033.WH.W1.P.T4_L6

open SAP.P033.WH.W1 SAP.P033

theorem SAP.P033.WH.W1.T4_L6_proof : SAP.P033.WH.W1.T4_L6 := by
  intro n hn a
  let c : Fin 2 × Fin (n*(n+1)) → ℝ := SAP.P033.WH.W1.P.T4_L6.sideCoefficient n a
  let d : (Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5) → ℝ :=
    SAP.P033.WH.W1.P.T4_L6.noisyCoefficient n a
  have hc := AronowAudit.P033.weighted_sign_moments c
  have hd := AronowAudit.P033.weighted_sign_moments d
  have hce : wholePaddedSignEstimator n a = fun data =>
      ∑ g, c g * signShock (data g) := by
    simpa [c] using SAP.P033.WH.W1.P.T4_L6.sign_estimator_sum n a
  have hde : wholePaddedNoisyEstimator n a = fun data =>
      ∑ g, d g * signShock (data g) := by
    simpa [d] using SAP.P033.WH.W1.P.T4_L6.noisy_estimator_sum n a
  constructor
  · rw [hce]
    exact hc.1
  constructor
  · rw [hce]
    exact hc.2.trans (SAP.P033.WH.W1.P.T4_L6.side_coefficient_sq_sum n hn a)
  constructor
  · rw [hde]
    exact hd.1
  · rw [hde]
    exact hd.2.trans (SAP.P033.WH.W1.P.T4_L6.noisy_coefficient_sq_sum n hn a)
