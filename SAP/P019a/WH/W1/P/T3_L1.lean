import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T3_L1

open SAP.P019a SAP.P019a.Bridge
open scoped BigOperators
open Classical

lemma negativeCount_eq_falseY {Ω : Type*} [Fintype Ω] (S : Study Ω)
    {n : ℕ} (s : Fin n → Ω) :
    S.negativeCount s = ∑ j, if S.Y (s j) = false then (1 : ℕ) else 0 := by
  classical
  unfold Study.negativeCount Study.cellCount Study.cell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  cases hy : S.Y (s j) <;> cases hz : S.Z (s j) <;> simp [hy, hz]

lemma falsePrefixCount (n k : ℕ) (hk : k ≤ n) :
    (∑ j : Fin n, if j.val < k then (1 : ℕ) else 0) = k := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k)
  let e : {j : Fin n // j.val < k} ≃ Fin k :=
    { toFun := fun j => ⟨j.1.val, j.2⟩
      invFun := fun j => ⟨⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩, j.isLt⟩
      left_inv := by intro j; cases j; rfl
      right_inv := by intro j; rfl }
  have hcard : A.card = Fintype.card {j : Fin n // j.val < k} := by
    let eA : {j : Fin n // j ∈ A} ≃ {j : Fin n // j.val < k} :=
      { toFun := fun j => ⟨j.1, by
          have hj := j.2
          change j.1 ∈ Finset.univ.filter (fun x : Fin n => x.val < k) at hj
          exact (Finset.mem_filter.mp hj).2⟩
        invFun := fun j => ⟨j.1, by
          change j.1 ∈ A
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          exact j.2⟩
        left_inv := by intro j; apply Subtype.ext; rfl
        right_inv := by intro j; cases j; rfl }
    calc
      A.card = Fintype.card {j : Fin n // j ∈ A} := (Fintype.card_coe A).symm
      _ = Fintype.card {j : Fin n // j.val < k} := Fintype.card_congr eA
  calc
    (∑ j : Fin n, if j.val < k then (1 : ℕ) else 0) = A.card := by
      simpa [A] using (Finset.card_filter (fun j : Fin n => j.val < k) Finset.univ).symm
    _ = Fintype.card {j : Fin n // j.val < k} := hcard
    _ = Fintype.card (Fin k) := Fintype.card_congr e
    _ = k := by simp

lemma negative_count_prob_pos (n k : ℕ) (hk : k ≤ n) :
    0 < (finiteSampleWitness.law.iid n).prob
      (fun s => finiteSampleWitness.negativeCount s = k) := by
  let S := finiteSampleWitness
  let P := S.law.iid n
  let s : Fin n → Fin 16 := fun j => if j.val < k then 0 else 3
  have hcount : S.negativeCount s = k := by
    rw [negativeCount_eq_falseY]
    have hfun : (fun j : Fin n => if S.Y (s j) = false then (1 : ℕ) else 0) =
        fun j => if j.val < k then 1 else 0 := by
      funext j
      by_cases hj : j.val < k
      · simp only [s, if_pos hj]
        change (if (finiteSampleWitness.Y 0) = false then 1 else 0) = 1
        simp [finiteSampleWitness, fairBit]
      · simp only [s, if_neg hj]
        change (if (finiteSampleWitness.Y 3) = false then 1 else 0) = 0
        simp [finiteSampleWitness, fairBit]
    rw [hfun]
    exact falsePrefixCount n k hk
  have hmass : 0 < P.mass s := by
    simp [P, S, FiniteLaw.iid, finiteSampleWitness, uniformFin]
  have hle : P.mass s ≤ P.prob (fun t => S.negativeCount t = k) := by
    unfold FiniteLaw.prob FiniteLaw.mean
    calc
      P.mass s = P.mass s * (if S.negativeCount s = k then (1 : ℝ) else 0) := by simp [hcount]
      _ ≤ ∑ t : Fin n → Fin 16,
          P.mass t * (if S.negativeCount t = k then 1 else 0) :=
        Finset.single_le_sum (f := fun t : Fin n → Fin 16 =>
          P.mass t * (if S.negativeCount t = k then (1 : ℝ) else 0))
          (fun t ht => mul_nonneg (P.nonneg t) (by split_ifs <;> norm_num))
          (Finset.mem_univ s)
      _ = _ := rfl
  exact lt_of_lt_of_le hmass hle

lemma binomial_positive_sum (k : ℕ) :
    (∑ i ∈ Finset.Icc 1 k, (Nat.choose k i : ℝ) * (1/2 : ℝ)^k) =
      1 - (1/2 : ℝ)^k := by
  have hset : Finset.range (k+1) = insert 0 (Finset.Icc 1 k) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsplit :
      (∑ i ∈ Finset.range (k+1), (Nat.choose k i : ℝ)) =
        1 + ∑ i ∈ Finset.Icc 1 k, (Nat.choose k i : ℝ) := by
    rw [hset, Finset.sum_insert (by simp)]
    simp
  have htotal :
      (∑ i ∈ Finset.range (k+1), (Nat.choose k i : ℝ)) = (2 : ℝ)^k := by
    exact_mod_cast Nat.sum_range_choose k
  have hcoeff :
      (∑ i ∈ Finset.Icc 1 k, (Nat.choose k i : ℝ)) = (2 : ℝ)^k - 1 := by
    nlinarith [hsplit, htotal]
  have hp : (2 : ℝ)^k * (1/2 : ℝ)^k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← Finset.sum_mul, hcoeff]
  nlinarith [hp]

lemma iid_one_ce_coordinate {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    (P.iid 1).ce (fun s => f (s 0)) (fun s => D (s 0)) = P.ce f D := by
  have hmean (g : Ω → ℝ) : (P.iid 1).mean (fun s => g (s 0)) = P.mean g :=
    AronowAudit.P019.iid_mean_coordinate (toLaw P) 1 0 g
  unfold FiniteLaw.ce FiniteLaw.prob
  rw [hmean (fun ω => if D ω then f ω else 0), hmean (fun ω => if D ω then 1 else 0)]

lemma cellCount_one {Ω : Type*} [Fintype Ω] (S : Study Ω) (s : Fin 1 → Ω) (z : Bool) :
    S.cellCount s z false = if S.cell z false (s 0) then 1 else 0 := by
  unfold Study.cellCount
  rw [Fin.sum_univ_one]

lemma negativeCount_one {Ω : Type*} [Fintype Ω] (S : Study Ω) (s : Fin 1 → Ω) :
    S.negativeCount s = if S.Y (s 0) = false then 1 else 0 := by
  rw [negativeCount_eq_falseY]
  rw [Fin.sum_univ_one]

lemma singleton_count_ce (z : Bool) (i k : ℕ) :
    (finiteSampleWitness.law.iid 1).ce
        (fun s => if finiteSampleWitness.cellCount s z false = i then 1 else 0)
        (fun s => finiteSampleWitness.negativeCount s = k) =
      finiteSampleWitness.law.ce
        (fun ω => if (if finiteSampleWitness.cell z false ω then 1 else 0) = i then 1 else 0)
        (fun ω => (if finiteSampleWitness.Y ω = false then 1 else 0) = k) := by
  have hobs : (fun s : Fin 1 → Fin 16 =>
      if finiteSampleWitness.cellCount s z false = i then (1 : ℝ) else 0) =
      fun s => if (if finiteSampleWitness.cell z false (s 0) then 1 else 0) = i then 1 else 0 := by
    funext s
    rw [cellCount_one]
  have hK : (fun s : Fin 1 → Fin 16 => finiteSampleWitness.negativeCount s = k) =
      fun s => (if finiteSampleWitness.Y (s 0) = false then 1 else 0) = k := by
    funext s
    rw [negativeCount_one]
  simpa only [← hobs, ← hK] using
    (iid_one_ce_coordinate finiteSampleWitness.law
      (fun ω => if (if finiteSampleWitness.cell z false ω then 1 else 0) = i then 1 else 0)
      (fun ω => (if finiteSampleWitness.Y ω = false then 1 else 0) = k))

lemma conditional_count_formula (n k : ℕ) (hk : k ≤ n)
    (hK : (finiteSampleWitness.law.iid n).prob
      (fun s => finiteSampleWitness.negativeCount s = k) ≠ 0)
    (z : Bool) (i : ℕ) (hi : i ≤ k) :
    (finiteSampleWitness.law.iid n).ce
        (fun s => if finiteSampleWitness.cellCount s z false = i then 1 else 0)
        (fun s => finiteSampleWitness.negativeCount s = k) =
      (Nat.choose k i : ℝ) * (1/2 : ℝ)^k := by
  let S := finiteSampleWitness
  let P := S.law.iid n
  let K := fun (s : Fin n → Fin 16) => S.negativeCount s = k
  have hstand : S.standing := AronowAudit.P019.lemma_two_counterexample.1
  have hgamma : S.gamma = 1/2 := by
    norm_num [S, finiteSampleWitness, Study.gamma, FiniteLaw.prob, FiniteLaw.mean,
      uniformFin, fairBit, Fin.sum_univ_succ]
  change P.ce (fun s => if S.cellCount s z false = i then 1 else 0) K = _
  by_cases hn : 2 ≤ n
  · have hcore := AronowAudit.P019.Wave1.corrected_cell_lemmas_proof
      (toStudy S) hstand n hn 0 0
    obtain ⟨_, _, hbin, _, _, _⟩ := hcore
    have hK' : ((toStudy S).law.iid n).prob
        (fun s => (toStudy S).negativeCount s = k) ≠ 0 := by
      change P.prob K ≠ 0
      exact hK
    have ht (j : ℕ) (hj : j ≤ k) :
        P.ce (fun s => if S.cellCount s true false = j then 1 else 0) K =
          (Nat.choose k j : ℝ) * S.gamma^j * (1-S.gamma)^(k-j) := by
      have h := hbin k hk hK' j hj
      change P.ce (fun s => if S.cellCount s true false = j then 1 else 0) K = _ at h
      exact h
    have ht' (j : ℕ) (hj : j ≤ k) :
        P.ce (fun s => if S.cellCount s true false = j then 1 else 0) K =
          (Nat.choose k j : ℝ) * (1/2 : ℝ)^k := by
      rw [ht j hj, hgamma]
      rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num]
      calc
        (Nat.choose k j : ℝ) * (1/2 : ℝ)^j * (1/2)^(k-j) =
            (Nat.choose k j : ℝ) * ((1/2 : ℝ)^j * (1/2)^(k-j)) := by ring
        _ = (Nat.choose k j : ℝ) * (1/2 : ℝ)^(j+(k-j)) := by rw [← pow_add]
        _ = (Nat.choose k j : ℝ) * (1/2 : ℝ)^k := by rw [Nat.add_sub_of_le hj]
    cases z with
    | true => exact ht' i hi
    | false =>
      have hnum :
          P.mean (fun s => if K s then
            (if S.cellCount s false false = i then (1 : ℝ) else 0) else 0) =
          P.mean (fun s => if K s then
            (if S.cellCount s true false = k-i then (1 : ℝ) else 0) else 0) := by
        apply congrArg P.mean
        funext (s : Fin n → Fin 16)
        by_cases hks : K s
        · have hs : S.cellCount s true false + S.cellCount s false false = k := hks
          have heq : S.cellCount s false false = i ↔
              S.cellCount s true false = k-i := by omega
          simp [hks, heq]
        · simp [hks]
      have hce :
          P.ce (fun s => if S.cellCount s false false = i then 1 else 0) K =
          P.ce (fun s => if S.cellCount s true false = k-i then 1 else 0) K := by
        unfold FiniteLaw.ce
        rw [hnum]
      rw [hce, ht' (k-i) (Nat.sub_le k i), Nat.choose_symm hi]
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · have hk0 : k = 0 := by omega
      subst k
      have hi0 : i = 0 := by omega
      subst i
      cases z <;> norm_num [P, S, K, FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean,
        FiniteLaw.iid, finiteSampleWitness, uniformFin, fairBit,
        Study.negativeCount, Study.cellCount, Study.cell, Fin.sum_univ_succ]
    · have hk0 : k = 0 ∨ k = 1 := by omega
      rcases hk0 with rfl | rfl
      · have hi0 : i = 0 := by omega
        subst i
        cases z <;> rw [singleton_count_ce] <;>
          norm_num [S, finiteSampleWitness, uniformFin, fairBit, Study.cell,
            FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]
      · have hi0 : i = 0 ∨ i = 1 := by omega
        rcases hi0 with rfl | rfl
        · cases z <;> rw [singleton_count_ce] <;>
            norm_num [S, finiteSampleWitness, uniformFin, fairBit, Study.cell,
              FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]
        · cases z <;> rw [singleton_count_ce] <;>
            norm_num [S, finiteSampleWitness, uniformFin, fairBit, Study.cell,
              FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]

end SAP.P019a.WH.W1.P.T3_L1

open SAP.P019a.WH.W1.P.T3_L1

theorem SAP.P019a.WH.W1.T3_L1_proof : SAP.P019a.WH.W1.T3_L1 := by
  change wholeT3Counts
  dsimp only [wholeT3Counts]
  intro n k hk
  let S := finiteSampleWitness
  let P := S.law.iid n
  let K := fun (s : Fin n → Fin 16) => S.negativeCount s = k
  change 0 < P.prob K ∧
    (∀ z : Bool, ∀ i : ℕ, i ≤ k →
      P.ce (fun s => if S.cellCount s z false = i then 1 else 0) K =
        (Nat.choose k i : ℝ)*(1/2 : ℝ)^k) ∧
    (∀ z : Bool, (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s z false = i then 1 else 0) K) =
        1-(1/2 : ℝ)^k) ∧ 1-(1/2 : ℝ)^k < 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [P, S, K] using negative_count_prob_pos n k hk
  · intro z i hi
    simpa [P, S, K] using conditional_count_formula n k hk
      (ne_of_gt (negative_count_prob_pos n k hk)) z i hi
  · intro z
    calc
      (∑ i ∈ Finset.Icc 1 k,
          P.ce (fun s => if S.cellCount s z false = i then 1 else 0) K) =
        ∑ i ∈ Finset.Icc 1 k, (Nat.choose k i : ℝ)*(1/2 : ℝ)^k := by
          apply Finset.sum_congr rfl
          intro i hi
          exact conditional_count_formula n k hk
            (ne_of_gt (negative_count_prob_pos n k hk)) z i
            (Finset.mem_Icc.mp hi).2
      _ = 1-(1/2 : ℝ)^k := binomial_positive_sum k
  · have hp : 0 < (1/2 : ℝ)^k := pow_pos (by norm_num) k
    linarith

