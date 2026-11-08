import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace SAP.P019a.WH.W1.P.T4_L1

open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical

variable {E : Type u} [Fintype E] {n : ℕ}

lemma positive_atom (P : AronowAudit.P019.FiniteLaw E) (D : E → Prop)
    [DecidablePred D] (hD : 0 < P.prob D) : ∃ ω, D ω ∧ 0 < P.mass ω := by
  classical
  unfold AronowAudit.P019.FiniteLaw.prob AronowAudit.P019.FiniteLaw.mean at hD
  have hne : (∑ ω, P.mass ω * if D ω then (1 : ℝ) else 0) ≠ 0 := ne_of_gt hD
  obtain ⟨ω, -, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨ω, ?_, ?_⟩
  · by_contra h
    simp [h] at hterm
  · have hmass : P.mass ω ≠ 0 := by
      intro hz
      simp [hz] at hterm
    exact lt_of_le_of_ne (P.nonneg ω) (Ne.symm hmass)

lemma positive_sample_with_k_negatives (S : SAP.P019a.Study E)
    (hs : S.standing) (n k : ℕ) (hk : k ≤ n) :
    ∃ s : Fin n → E, S.negativeCount s = k ∧ 0 < (S.law.iid n).mass s := by
  let T := Bridge.toStudy S
  have hnegprob : 0 < T.law.prob (T.cell true false) := hs.2.2.2.1 true false |>.1
  have hposprob : 0 < T.law.prob (fun ω => T.Y ω = true) :=
    (AronowAudit.P019.regularity_probabilities T hs.2.2.2).2 true
  obtain ⟨ω₀, hω₀, hω₀mass⟩ := positive_atom T.law (T.cell true false) hnegprob
  obtain ⟨ω₁, hω₁, hω₁mass⟩ := positive_atom T.law (fun ω => T.Y ω = true) hposprob
  have hω₀' : S.cell true false ω₀ := hω₀
  have hω₁' : S.Y ω₁ = true := hω₁
  rcases hω₀' with ⟨hz₀, hy₀⟩
  let A : Finset (Fin n) := Finset.univ.image (Fin.castLE hk)
  have hcardA : A.card = k := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
    simp
  let s : Fin n → E := fun i => if i ∈ A then ω₀ else ω₁
  have hcount : S.negativeCount s = k := by
    have ht : S.cellCount s true false = k := by
      unfold Study.cellCount
      calc
        _ = ∑ i : Fin n, if i ∈ A then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ A
          · simp [s, hi, Study.cell, hz₀, hy₀]
          · simp [s, hi, Study.cell, hω₁']
        _ = A.card := by simp [Finset.card_filter]
        _ = k := hcardA
    have hc : S.cellCount s false false = 0 := by
      unfold Study.cellCount
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i ∈ A
      · simp [s, hi, Study.cell, hz₀, hy₀]
      · simp [s, hi, Study.cell, hω₁']
    unfold Study.negativeCount
    omega
  have hmass : 0 < (S.law.iid n).mass s := by
    change 0 < ∏ i, S.law.mass (s i)
    apply Finset.prod_pos
    intro i _
    by_cases hi : i ∈ A
    · simpa [T, s, hi, Bridge.toStudy, Bridge.toLaw] using hω₀mass
    · simpa [T, s, hi, Bridge.toStudy, Bridge.toLaw] using hω₁mass
  exact ⟨s, hcount, hmass⟩

lemma iid_event_positive (S : SAP.P019a.Study E)
    (P : AronowAudit.P019.FiniteLaw (Fin n → E)) (k : ℕ)
    (s : Fin n → E) (hs : S.negativeCount s = k)
    (hm : 0 < P.mass s) :
    0 < P.prob (fun t => S.negativeCount t = k) := by
  let f : (Fin n → E) → ℝ := fun t => P.mass t *
    (if S.negativeCount t = k then (1 : ℝ) else 0)
  have hnonneg : ∀ t ∈ (Finset.univ : Finset (Fin n → E)), 0 ≤ f t := by
    intro t _
    dsimp [f]
    by_cases ht : S.negativeCount t = k <;>
      simp [ht, mul_nonneg, P.nonneg]
  have hle : f s ≤ ∑ t ∈ (Finset.univ : Finset (Fin n → E)), f t :=
    Finset.single_le_sum hnonneg (Finset.mem_univ s)
  have hterm : f s = P.mass s := by simp [f, hs]
  have hprob : P.prob (fun t => S.negativeCount t = k) =
      ∑ t ∈ (Finset.univ : Finset (Fin n → E)), f t := by
    unfold AronowAudit.P019.FiniteLaw.prob AronowAudit.P019.FiniteLaw.mean
    simp [f]
  rw [hprob]
  linarith [hm]

lemma ce_sum_finset {α : Type*}
    (P : AronowAudit.P019.FiniteLaw (Fin n → E)) (S : SAP.P019a.Study E)
    (k : ℕ) (s : Finset α) (f : α → (Fin n → E) → ℝ) :
    P.ce (fun ω => ∑ i ∈ s, f i ω)
        (fun ω : Fin n → E => S.negativeCount ω = k) =
      ∑ i ∈ s, P.ce (f i) (fun ω : Fin n → E => S.negativeCount ω = k) := by
  classical
  have hmask : (fun ω : Fin n → E =>
      if S.negativeCount ω = k then ∑ i ∈ s, f i ω else 0) =
      (fun ω => ∑ i ∈ s, if S.negativeCount ω = k then f i ω else 0) := by
    funext ω
    by_cases hd : S.negativeCount ω = k <;> simp [hd]
  unfold AronowAudit.P019.FiniteLaw.ce
  rw [hmask]
  have hmean : P.mean (fun ω : Fin n → E =>
      ∑ i ∈ s, if S.negativeCount ω = k then f i ω else 0) =
      ∑ i ∈ s, P.mean (fun ω : Fin n → E =>
        if S.negativeCount ω = k then f i ω else 0) := by
    unfold AronowAudit.P019.FiniteLaw.mean
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hmean, Finset.sum_div]

lemma positive_count_sum_eq_ce
    (P : AronowAudit.P019.FiniteLaw (Fin n → E)) (S : SAP.P019a.Study E)
    (c : (Fin n → E) → ℕ) (k : ℕ)
    (hD : P.prob (fun s : Fin n → E => S.negativeCount s = k) ≠ 0)
    (hbound : ∀ s, S.negativeCount s = k → c s ≤ k) :
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if c s = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) =
      P.ce (fun s => if 0 < c s then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) := by
  classical
  let F : Finset ℕ := Finset.Icc 1 k
  have hpt : ∀ s, S.negativeCount s = k →
      (∑ i ∈ F, if c s = i then (1 : ℝ) else 0) =
        (if 0 < c s then 1 else 0) := by
    intro s hs
    by_cases hc0 : c s = 0
    · have hz : (∑ i ∈ F, if c s = i then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi1 := (Finset.mem_Icc.mp hi).1
        have hne : c s ≠ i := by omega
        simp [hne]
      rw [hz]
      simp [hc0]
    · have hcpos : 0 < c s := Nat.pos_of_ne_zero hc0
      have hmem : c s ∈ F := by
        exact Finset.mem_Icc.mpr ⟨by omega, hbound s hs⟩
      rw [Finset.sum_eq_single (c s)]
      · simp [hcpos]
      · intro i hi hne
        simp [ne_comm.mp hne]
      · intro hnot
        exact (hnot hmem).elim
  have hce : P.ce (fun s => if 0 < c s then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k) =
      P.ce (fun s => ∑ i ∈ F, if c s = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) := by
    apply AronowAudit.P019.ce_congr_support
    intro s _ hs
    exact (hpt s hs).symm
  change (∑ i ∈ F, P.ce (fun s => if c s = i then (1 : ℝ) else 0)
    (fun s : Fin n → E => S.negativeCount s = k)) = _
  calc
    _ = P.ce (fun s => ∑ i ∈ F, if c s = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) :=
      (ce_sum_finset P S k F (fun i s => if c s = i then (1 : ℝ) else 0)).symm
    _ = P.ce (fun s => if 0 < c s then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) := hce.symm

lemma ce_sub_local (P : AronowAudit.P019.FiniteLaw (Fin n → E))
    (S : SAP.P019a.Study E) (k : ℕ)
    (f g : (Fin n → E) → ℝ) :
    P.ce (fun s => f s - g s) (fun s : Fin n → E => S.negativeCount s = k) =
      P.ce f (fun s : Fin n → E => S.negativeCount s = k) -
        P.ce g (fun s : Fin n → E => S.negativeCount s = k) := by
  have hfun : (fun s => f s - g s) = (fun s => f s + g s * (-1)) := by
    funext s
    ring
  rw [hfun, AronowAudit.P019.ce_add, AronowAudit.P019.ce_mul_const]
  ring

lemma ce_positive_is_complement
    (P : AronowAudit.P019.FiniteLaw (Fin n → E)) (S : SAP.P019a.Study E)
    (k : ℕ) (c : (Fin n → E) → ℕ)
    (hD : P.prob (fun s : Fin n → E => S.negativeCount s = k) ≠ 0) :
    P.ce (fun s => if 0 < c s then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) =
      1 - P.ce (fun s => if c s = 0 then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) := by
  have hfun : ∀ s : Fin n → E, S.negativeCount s = k →
      (if 0 < c s then (1 : ℝ) else 0) =
      1 - (if c s = 0 then (1 : ℝ) else 0) := by
    intro s _
    by_cases hc : c s = 0 <;> simp [hc]
  have hce := AronowAudit.P019.ce_congr_support P
    (fun s => if 0 < c s then (1 : ℝ) else 0)
    (fun s => 1 - (if c s = 0 then (1 : ℝ) else 0))
    (fun s : Fin n → E => S.negativeCount s = k)
    (by intro s _ hs; exact hfun s hs)
  calc
    _ = P.ce (fun s => 1 - (if c s = 0 then (1 : ℝ) else 0))
        (fun s : Fin n → E => S.negativeCount s = k) := hce
    _ = P.ce (fun _ => (1 : ℝ))
          (fun s : Fin n → E => S.negativeCount s = k) -
        P.ce (fun s => if c s = 0 then (1 : ℝ) else 0)
          (fun s : Fin n → E => S.negativeCount s = k) :=
      ce_sub_local P S k (fun _ => 1) (fun s => if c s = 0 then 1 else 0)
    _ = 1 - P.ce (fun s => if c s = 0 then (1 : ℝ) else 0)
          (fun s : Fin n → E => S.negativeCount s = k) := by
      rw [AronowAudit.P019.ce_const P 1
        (fun s : Fin n → E => S.negativeCount s = k) hD]

lemma assemble_sums
    (S : SAP.P019a.Study E) (n k : ℕ) (P : AronowAudit.P019.FiniteLaw (Fin n → E))
    (hK : P.prob (fun s : Fin n → E => S.negativeCount s = k) ≠ 0)
    (hbin : ∀ i, i ≤ k →
      P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) =
          (Nat.choose k i : ℝ) * S.gamma^i * (1-S.gamma)^(k-i)) :
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-(1-S.gamma)^k ∧
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s false false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-S.gamma^k := by
  have htbound : ∀ s : Fin n → E, S.negativeCount s = k → S.cellCount s true false ≤ k := by
    intro s hs
    unfold Study.negativeCount at hs
    omega
  have hcbound : ∀ s : Fin n → E, S.negativeCount s = k → S.cellCount s false false ≤ k := by
    intro s hs
    unfold Study.negativeCount at hs
    omega
  have htreatedsum := positive_count_sum_eq_ce P S
    (fun s => S.cellCount s true false) k hK htbound
  have hcontrolsum := positive_count_sum_eq_ce P S
    (fun s => S.cellCount s false false) k hK hcbound
  have htzero := hbin 0 (by omega)
  have htzero' : P.ce (fun s => if S.cellCount s true false = 0 then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k) = (1-S.gamma)^k := by simpa using htzero
  have htk : P.ce (fun s => if S.cellCount s true false = k then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k) = S.gamma^k := by
    simpa using hbin k (by omega)
  have hczero : P.ce (fun s => if S.cellCount s false false = 0 then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k) = S.gamma^k := by
    have hce := AronowAudit.P019.ce_congr_support P
      (fun s => if S.cellCount s false false = 0 then (1 : ℝ) else 0)
      (fun s => if S.cellCount s true false = k then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k)
      (by
        intro s _ hs
        have hsum := hs
        unfold Study.negativeCount at hsum
        by_cases hz : S.cellCount s false false = 0
        · have ht : S.cellCount s true false = k := by omega
          simp [hz, ht]
        · have ht : S.cellCount s true false ≠ k := by omega
          simp [hz, ht])
    exact hce.trans htk
  constructor
  · calc
      _ = P.ce (fun s => if 0 < S.cellCount s true false then (1 : ℝ) else 0)
          (fun s : Fin n → E => S.negativeCount s = k) := htreatedsum
      _ = 1-(1-S.gamma)^k := by
        rw [ce_positive_is_complement P S k
          (fun s => S.cellCount s true false) hK, htzero']
  · calc
      _ = P.ce (fun s => if 0 < S.cellCount s false false then (1 : ℝ) else 0)
          (fun s : Fin n → E => S.negativeCount s = k) := hcontrolsum
      _ = 1-S.gamma^k := by
        rw [ce_positive_is_complement P S k
          (fun s => S.cellCount s false false) hK, hczero]

lemma bridge_count_conclusions (S : SAP.P019a.Study E) (n k : ℕ)
    (P : AronowAudit.P019.FiniteLaw (Fin n → E))
    (P₀ : SAP.P019a.FiniteLaw (Fin n → E))
    (hP : P = Bridge.toLaw P₀)
    (hpos : 0 < P.prob (fun s : Fin n → E => S.negativeCount s = k))
    (hbin : ∀ i, i ≤ k →
      P.ce
        (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) =
          (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i))
    (hsumT : (∑ i ∈ Finset.Icc 1 k,
      P.ce
        (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-(1-S.gamma)^k)
    (hsumC : (∑ i ∈ Finset.Icc 1 k,
      P.ce
        (fun s => if S.cellCount s false false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-S.gamma^k) :
    0 < P₀.prob (fun s : Fin n → E => S.negativeCount s = k) ∧
    (∀ i : ℕ, i ≤ k → P₀.ce
      (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k) =
        (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i)) ∧
    (∑ i ∈ Finset.Icc 1 k,
      P₀.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-(1-S.gamma)^k ∧
    (∑ i ∈ Finset.Icc 1 k,
      P₀.ce (fun s => if S.cellCount s false false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-S.gamma^k := by
  have hpos' : 0 < (Bridge.toLaw P₀).prob
      (fun s : Fin n → E => S.negativeCount s = k) := by
    rw [← hP]
    exact hpos
  have hbin' : ∀ i, i ≤ k → (Bridge.toLaw P₀).ce
      (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
      (fun s : Fin n → E => S.negativeCount s = k) =
        (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i) := by
    intro i hi
    rw [← hP]
    exact hbin i hi
  have hsumT' : (∑ i ∈ Finset.Icc 1 k,
      (Bridge.toLaw P₀).ce
        (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-(1-S.gamma)^k := by
    rw [← hP]
    exact hsumT
  have hsumC' : (∑ i ∈ Finset.Icc 1 k,
      (Bridge.toLaw P₀).ce
        (fun s => if S.cellCount s false false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k)) = 1-S.gamma^k := by
    rw [← hP]
    exact hsumC
  have hprob := Bridge.prob_eq P₀ (fun s : Fin n → E => S.negativeCount s = k)
  have hce (f : (Fin n → E) → ℝ) :
      (Bridge.toLaw P₀).ce f (fun s : Fin n → E => S.negativeCount s = k) =
        P₀.ce f (fun s : Fin n → E => S.negativeCount s = k) :=
    Bridge.ce_eq P₀ f (fun s : Fin n → E => S.negativeCount s = k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hprob]
    exact hpos'
  · intro i hi
    rw [← hce]
    exact hbin' i hi
  · calc
      _ = ∑ i ∈ Finset.Icc 1 k,
          (Bridge.toLaw P₀).ce
            (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
            (fun s : Fin n → E => S.negativeCount s = k) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← hce]
      _ = _ := hsumT'
  · calc
      _ = ∑ i ∈ Finset.Icc 1 k,
          (Bridge.toLaw P₀).ce
            (fun s => if S.cellCount s false false = i then (1 : ℝ) else 0)
            (fun s : Fin n → E => S.negativeCount s = k) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← hce]
      _ = _ := hsumC'

lemma one_sample_coordinate_ce (S : SAP.P019a.Study E)
    (P : AronowAudit.P019.FiniteLaw (Fin 1 → E))
    (Q : AronowAudit.P019.FiniteLaw E)
    (hD : ∀ s : Fin 1 → E, S.negativeCount s = 1 ↔ S.Y (s 0) = false)
    (hP1 : P = Q.iid 1)
    (hKprob : P.prob (fun s : Fin 1 → E => S.negativeCount s = 1) =
      Q.prob (fun ω => S.Y ω = false)) :
    ∀ f : E → ℝ,
      P.ce (fun s : Fin 1 → E => f (s 0))
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
          Q.ce f (fun ω => S.Y ω = false) := by
  intro f
  have hmask : (fun s : Fin 1 → E =>
      if S.negativeCount s = 1 then f (s 0) else 0) =
      (fun s => if S.Y (s 0) = false then f (s 0) else 0) := by
    funext s
    by_cases hy : S.Y (s 0) = false
    · have hval := (hD s).mpr hy
      simp [hval, hy]
    · have hneq : S.negativeCount s ≠ 1 := fun h => hy ((hD s).mp h)
      simp [hneq, hy]
  have hnum : P.mean (fun s : Fin 1 → E =>
      if S.negativeCount s = 1 then f (s 0) else 0) =
      Q.mean (fun ω => if S.Y ω = false then f ω else 0) := by
    rw [hP1, hmask]
    exact AronowAudit.P019.iid_mean_coordinate Q 1 0
      (fun ω => if S.Y ω = false then f ω else 0)
  unfold AronowAudit.P019.FiniteLaw.ce
  rw [hnum, hKprob]

lemma one_sample_k1_binomial (S : SAP.P019a.Study E)
    (P : AronowAudit.P019.FiniteLaw (Fin 1 → E))
    (Q : AronowAudit.P019.FiniteLaw E)
    (hcount_zero : P.ce
      (fun s => if S.cellCount s true false = 0 then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
      P.ce (fun s : Fin 1 → E => if S.Z (s 0) = false then (1 : ℝ) else 0)
        (fun s => S.negativeCount s = 1))
    (hcount_one : P.ce
      (fun s => if S.cellCount s true false = 1 then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
      P.ce (fun s : Fin 1 → E => if S.Z (s 0) = true then (1 : ℝ) else 0)
        (fun s => S.negativeCount s = 1))
    (hcoord_ce : ∀ f : E → ℝ,
      P.ce (fun s : Fin 1 → E => f (s 0))
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
          Q.ce f (fun ω => S.Y ω = false))
    (hceZ : ∀ z : Bool,
      Q.ce (fun ω => if S.Z ω = z then (1 : ℝ) else 0)
        (fun ω => S.Y ω = false) = Q.prob (fun ω => S.Z ω = z))
    (hQcontrol : Q.prob (fun ω => S.Z ω = false) = 1-S.gamma)
    (hQgamma : Q.prob (fun ω => S.Z ω = true) = S.gamma) :
    ∀ i, i ≤ 1 →
      P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
        (Nat.choose 1 i : ℝ) * S.gamma^i * (1-S.gamma)^(1-i) := by
  intro i hi
  have hi_cases : i = 0 ∨ i = 1 := by omega
  rcases hi_cases with rfl | rfl
  · calc
      _ = P.ce (fun s : Fin 1 → E => if S.Z (s 0) = false then (1 : ℝ) else 0)
          (fun s => S.negativeCount s = 1) := hcount_zero
      _ = Q.ce (fun ω => if S.Z ω = false then (1 : ℝ) else 0)
          (fun ω => S.Y ω = false) :=
            hcoord_ce (fun ω => if S.Z ω = false then (1 : ℝ) else 0)
      _ = Q.prob (fun ω => S.Z ω = false) := hceZ false
      _ = 1-S.gamma := hQcontrol
      _ = (Nat.choose 1 0 : ℝ) * S.gamma^0 * (1-S.gamma)^(1-0) := by norm_num
  · calc
      _ = P.ce (fun s : Fin 1 → E => if S.Z (s 0) = true then (1 : ℝ) else 0)
          (fun s => S.negativeCount s = 1) := hcount_one
      _ = Q.ce (fun ω => if S.Z ω = true then (1 : ℝ) else 0)
          (fun ω => S.Y ω = false) :=
            hcoord_ce (fun ω => if S.Z ω = true then (1 : ℝ) else 0)
      _ = Q.prob (fun ω => S.Z ω = true) := hceZ true
      _ = S.gamma := hQgamma
      _ = (Nat.choose 1 1 : ℝ) * S.gamma^1 * (1-S.gamma)^(1-1) := by norm_num

lemma one_sample_k1_counts (S : SAP.P019a.Study E) (hs : S.standing)
    (P₀ : SAP.P019a.FiniteLaw (Fin 1 → E))
    (P : AronowAudit.P019.FiniteLaw (Fin 1 → E))
    (hPbridge : P = Bridge.toLaw P₀)
    (hP1 : P = (Bridge.toStudy S).law.iid 1)
    (hKpos : 0 < P.prob (fun s : Fin 1 → E => S.negativeCount s = 1)) :
    0 < P₀.prob (fun s : Fin 1 → E => S.negativeCount s = 1) ∧
    (∀ i : ℕ, i ≤ 1 → P₀.ce
      (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
      (fun s : Fin 1 → E => S.negativeCount s = 1) =
        (Nat.choose 1 i : ℝ)*S.gamma^i*(1-S.gamma)^(1-i)) ∧
    (∑ i ∈ Finset.Icc 1 1,
      P₀.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1)) = 1-(1-S.gamma)^1 ∧
    (∑ i ∈ Finset.Icc 1 1,
      P₀.ce (fun s => if S.cellCount s false false = i then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1)) = 1-S.gamma^1 := by
  let T := Bridge.toStudy S
  let Q := T.law
  have hK1 : P.prob (fun s : Fin 1 → E => S.negativeCount s = 1) ≠ 0 := ne_of_gt hKpos
  have hD : ∀ s : Fin 1 → E,
      S.negativeCount s = 1 ↔ S.Y (s 0) = false := by
    intro s
    cases hy : S.Y (s 0) <;> cases hz : S.Z (s 0) <;>
      simp [Study.negativeCount, Study.cellCount, Study.cell, hy, hz]
  have hKmask : (fun s : Fin 1 → E =>
      if S.negativeCount s = 1 then (1 : ℝ) else 0) =
      (fun s => if S.Y (s 0) = false then (1 : ℝ) else 0) := by
    funext s
    by_cases hy : S.Y (s 0) = false
    · have hval := (hD s).mpr hy
      simp [hval, hy]
    · have hneq : S.negativeCount s ≠ 1 := fun h => hy ((hD s).mp h)
      simp [hneq, hy]
  have hKprob : P.prob (fun s : Fin 1 → E => S.negativeCount s = 1) =
      Q.prob (fun ω => S.Y ω = false) := by
    rw [hP1]
    unfold AronowAudit.P019.FiniteLaw.prob
    rw [hKmask]
    exact AronowAudit.P019.iid_mean_coordinate Q 1 0
      (fun ω => if S.Y ω = false then 1 else 0)
  have hYpos : 0 < Q.prob (fun ω => S.Y ω = false) := by
    rw [← hKprob]
    exact hKpos
  have hcell (z : Bool) : Q.prob (S.cell z false) =
      Q.prob (fun ω => S.Z ω = z) * Q.prob (fun ω => S.Y ω = false) := by
    change T.law.prob (T.cell z false) =
      T.law.prob (fun ω => T.Z ω = z) * T.law.prob (fun ω => T.Y ω = false)
    exact AronowAudit.P019.cell_probability T hs.2.2.1 z false
  have hceZ (z : Bool) : Q.ce (fun ω => if S.Z ω = z then (1 : ℝ) else 0)
      (fun ω => S.Y ω = false) = Q.prob (fun ω => S.Z ω = z) := by
    have hmask : (fun ω => if S.Y ω = false then
        (if S.Z ω = z then (1 : ℝ) else 0) else 0) =
        (fun ω => if S.cell z false ω then (1 : ℝ) else 0) := by
      funext ω
      by_cases hz : S.Z ω = z <;> by_cases hy : S.Y ω = false <;>
        simp [Study.cell, hz, hy]
    calc
      _ = Q.prob (S.cell z false) / Q.prob (fun ω => S.Y ω = false) := by
        unfold AronowAudit.P019.FiniteLaw.ce
        rw [hmask]
        rfl
      _ = Q.prob (fun ω => S.Z ω = z) := by
        rw [hcell z]
        field_simp [ne_of_gt hYpos]
  have hQgamma : Q.prob (fun ω => S.Z ω = true) = S.gamma := rfl
  have hQcontrol : Q.prob (fun ω => S.Z ω = false) = 1-S.gamma := by
    rw [AronowAudit.P019.prob_false, hQgamma]
  have hcoord_ce := one_sample_coordinate_ce S P Q hD hP1 hKprob
  have hcount_zero : P.ce
      (fun s => if S.cellCount s true false = 0 then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
      P.ce (fun s : Fin 1 → E => if S.Z (s 0) = false then (1 : ℝ) else 0)
        (fun s => S.negativeCount s = 1) := by
    apply AronowAudit.P019.ce_congr_support P
    intro s _ hsK
    have hy := (hD s).mp hsK
    cases hz : S.Z (s 0) <;> simp [Study.cellCount, Study.cell, hy, hz]
  have hcount_one : P.ce
      (fun s => if S.cellCount s true false = 1 then (1 : ℝ) else 0)
        (fun s : Fin 1 → E => S.negativeCount s = 1) =
      P.ce (fun s : Fin 1 → E => if S.Z (s 0) = true then (1 : ℝ) else 0)
        (fun s => S.negativeCount s = 1) := by
    apply AronowAudit.P019.ce_congr_support P
    intro s _ hsK
    have hy := (hD s).mp hsK
    cases hz : S.Z (s 0) <;> simp [Study.cellCount, Study.cell, hy, hz]
  have hbin := one_sample_k1_binomial S P Q hcount_zero hcount_one
    hcoord_ce hceZ hQcontrol hQgamma
  have hsum := assemble_sums S 1 1 P hK1 hbin
  exact bridge_count_conclusions S 1 1 P P₀ hPbridge hKpos hbin hsum.1 hsum.2

end

end SAP.P019a.WH.W1.P.T4_L1

theorem SAP.P019a.WH.W1.T4_L1_proof : SAP.P019a.WH.W1.T4_L1 := by
  classical
  intro E _ S hs n k hk
  let P₀ := S.law.iid n
  let T := Bridge.toStudy S
  let Q := T.law
  let P := Q.iid n
  have hPbridge : P = Bridge.toLaw P₀ := by
    change (Bridge.toLaw S.law).iid n = Bridge.toLaw (S.law.iid n)
    exact (Bridge.iid_eq S.law n).symm
  have hsample := SAP.P019a.WH.W1.P.T4_L1.positive_sample_with_k_negatives S hs n k hk
  obtain ⟨s₀, hs₀, hm₀⟩ := hsample
  have hm₀' : 0 < P.mass s₀ := by
    change 0 < ((Bridge.toLaw S.law).iid n).mass s₀
    rw [Bridge.iid_eq S.law n]
    simpa [Bridge.toLaw] using hm₀
  have hKpos : 0 < P.prob (fun s : Fin n → E => S.negativeCount s = k) :=
    SAP.P019a.WH.W1.P.T4_L1.iid_event_positive S P k s₀ hs₀ hm₀'
  have hK : P.prob (fun s : Fin n → E => S.negativeCount s = k) ≠ 0 := ne_of_gt hKpos
  by_cases hn : 2 ≤ n
  · have hdonor := AronowAudit.P019.Wave1.corrected_cell_lemmas_proof
      T hs n hn 0 0
    have hbin : ∀ i, i ≤ k →
        P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
          (fun s : Fin n → E => S.negativeCount s = k) =
          (Nat.choose k i : ℝ) * S.gamma^i * (1-S.gamma)^(k-i) := by
      intro i hi
      have hb := hdonor.2.2.1 k hk hK i hi
      change P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
        (fun s : Fin n → E => S.negativeCount s = k) =
          (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i) at hb
      exact hb
    have hsum := SAP.P019a.WH.W1.P.T4_L1.assemble_sums S n k P hK hbin
    exact SAP.P019a.WH.W1.P.T4_L1.bridge_count_conclusions S n k P P₀ hPbridge
      hKpos hbin hsum.1 hsum.2
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · cases k with
      | zero =>
        have hK0 : P.prob (fun s : Fin 0 → E => S.negativeCount s = 0) ≠ 0 :=
          ne_of_gt hKpos
        have hbin : ∀ i, i ≤ 0 →
            P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
              (fun s : Fin 0 → E => S.negativeCount s = 0) =
                (Nat.choose 0 i : ℝ)*S.gamma^i*(1-S.gamma)^(0-i) := by
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          have hfun : (fun s : Fin 0 → E =>
              if S.cellCount s true false = 0 then (1 : ℝ) else 0) = fun _ => 1 := by
            funext s
            simp [Study.cellCount]
          rw [hfun, AronowAudit.P019.ce_const P 1 _ hK0]
          norm_num
        have hsum := SAP.P019a.WH.W1.P.T4_L1.assemble_sums S 0 0 P hK0 hbin
        exact SAP.P019a.WH.W1.P.T4_L1.bridge_count_conclusions S 0 0 P P₀ hPbridge
          hKpos hbin hsum.1 hsum.2
      | succ k => omega
    · cases k with
      | zero =>
        have hK0 : P.prob (fun s : Fin 1 → E => S.negativeCount s = 0) ≠ 0 :=
          ne_of_gt hKpos
        have hzero : ∀ s : Fin 1 → E,
            S.negativeCount s = 0 → S.cellCount s true false = 0 := by
          intro s hsK
          unfold Study.negativeCount at hsK
          omega
        have hbin : ∀ i, i ≤ 0 →
            P.ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
              (fun s : Fin 1 → E => S.negativeCount s = 0) =
                (Nat.choose 0 i : ℝ)*S.gamma^i*(1-S.gamma)^(0-i) := by
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          have hce := AronowAudit.P019.ce_congr_support P
            (fun s => if S.cellCount s true false = 0 then (1 : ℝ) else 0)
            (fun _ => (1 : ℝ)) (fun s : Fin 1 → E => S.negativeCount s = 0)
            (by intro s _ hsK; simp [hzero s hsK])
          rw [hce, AronowAudit.P019.ce_const P 1 _ hK0]
          norm_num
        have hsum := SAP.P019a.WH.W1.P.T4_L1.assemble_sums S 1 0 P hK0 hbin
        exact SAP.P019a.WH.W1.P.T4_L1.bridge_count_conclusions S 1 0 P P₀ hPbridge
          hKpos hbin hsum.1 hsum.2
      | succ k' =>
        cases k' with
        | zero =>
          have hP1 : P = (Bridge.toStudy S).law.iid 1 := by
            rfl
          exact SAP.P019a.WH.W1.P.T4_L1.one_sample_k1_counts S hs P₀ P
            hPbridge hP1 hKpos
        | succ k'' => omega
