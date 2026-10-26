import AronowAudit.P037.P037_Design
import AronowAudit.P037.P037_Network

namespace AronowAudit.P037.Wave1
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private def school_section {B : ℕ} (s : Finset (Fin B × Fin 4)) (b : Fin B) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => (b,j) ∈ s)

private theorem school_section_filter {B : ℕ} (s : Finset (Fin B × Fin 4)) (b : Fin B) :
    s.filter (fun i => i.1=b) = {b} ×ˢ school_section s b := by
  ext ⟨c,j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, school_section,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h,rfl⟩; exact ⟨rfl,h⟩
  · rintro ⟨rfl,h⟩; exact ⟨h,rfl⟩

/-- A blocked assignment is one two-element subset of `Fin 4` per block. -/
private noncomputable def school_block_equiv (B : ℕ) :
    {s // s ∈ blockedSchoolSupport B} ≃
      (Fin B → {a : Finset (Fin 4) // a ∈ Finset.univ.powersetCard 2}) := by
  classical
  refine { toFun := fun s b => ⟨school_section s.val b, ?_⟩
           invFun := fun f => ⟨Finset.univ.filter (fun i => i.2 ∈ (f i.1).val), ?_⟩
           left_inv := ?_, right_inv := ?_ }
  · have h := (Finset.mem_filter.mp s.property).2 b
    rw [school_section_filter, Finset.card_product] at h
    simpa using h
  · simp only [blockedSchoolSupport, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    intro b
    rw [school_section_filter, Finset.card_product]
    have he : school_section (Finset.univ.filter (fun i => i.2 ∈ (f i.1).val)) b = (f b).val := by
      ext j; simp [school_section]
    rw [he]
    simpa using (Finset.mem_powersetCard.mp (f b).property).2
  · intro s
    apply Subtype.ext
    ext ⟨b,j⟩; simp [school_section]
  · intro f
    funext b
    apply Subtype.ext
    ext j; simp [school_section]

private theorem school_block_card (B : ℕ) : (blockedSchoolSupport B).card = 6^B := by
  classical
  have h := Fintype.card_congr (school_block_equiv B)
  simpa [Fintype.card_fun, Finset.card_powersetCard, Nat.choose] using h

private theorem school_choose_one (n m : ℕ) (hn : 0<n) (hm : 0<m) :
    n * Nat.choose (n-1) (m-1) = Nat.choose n m * m := by
  have h := Nat.add_one_mul_choose_eq (n-1) (m-1)
  simpa [Nat.sub_add_cancel (by omega : 1≤n), Nat.sub_add_cancel (by omega : 1≤m)] using h

private theorem school_required_count (n m : ℕ) (a : Finset (Fin n)) (ha : a.card ≤ m) :
    ((unblockedSchoolSupport n m).filter (a ⊆ ·)).card = Nat.choose (n-a.card) (m-a.card) := by
  simpa [unblockedSchoolSupport] using
    Finset.card_filter_powersetCard_subset a Finset.univ m (Finset.subset_univ _) ha

/-- Exact blocked-support normalization and unblocked inclusion probabilities. -/
theorem school_randomization_laws_proof (B n m : ℕ) (hn : 2≤n) (hm : m≤n) :
    (blockedSchoolSupport B).card=6^B ∧
    (∑ s ∈ blockedSchoolSupport B, blockedSchoolMass s)=1 ∧
    (unblockedSchoolSupport n m).card=Nat.choose n m ∧
    (∀ h : Fin n, uniformSchoolProbability n m (fun s => h∈s)=(m:ℝ)/n) ∧
    (∀ h j : Fin n, h≠j →
      uniformSchoolProbability n m (fun s => h∈s ∧ j∈s)=
        ((m:ℝ)*(m-1))/(n*(n-1))) := by
  classical
  have hc : (Nat.choose n m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  refine ⟨school_block_card B, ?_, by simp [unblockedSchoolSupport], ?_, ?_⟩
  · have he : ∀ s ∈ blockedSchoolSupport B, blockedSchoolMass s = (6:ℝ)^(-(B:ℤ)) := by
      intro s hs; simp [blockedSchoolMass, hs]
    rw [Finset.sum_congr rfl he]
    rw [Finset.sum_const, school_block_card]
    simp [zpow_neg, zpow_natCast, nsmul_eq_mul]
  · intro h
    cases m with
    | zero => simp [uniformSchoolProbability, unblockedSchoolSupport]
    | succ k =>
      have hcount := school_required_count n (k+1) {h} (by simp)
      simp only [Finset.card_singleton, Nat.add_sub_cancel, Finset.singleton_subset_iff] at hcount
      unfold uniformSchoolProbability
      trans (Nat.choose (n-1) k:ℝ) / (Nat.choose n (k+1):ℝ)
      · congr 1
        apply congrArg (fun a : ℕ => (a:ℝ))
        convert hcount using 1 <;> congr!
      have hid := school_choose_one n (k+1) (by omega) (by omega)
      have hidr : (n:ℝ) * (Nat.choose (n-1) k:ℝ) = (Nat.choose n (k+1):ℝ) * (k+1) := by
        exact_mod_cast hid
      apply (div_eq_div_iff hc hn0).mpr
      push_cast
      nlinarith
  · intro h j hj
    by_cases hm2 : 2≤m
    · have hcount := school_required_count n m {h,j} (by simpa [hj] using hm2)
      simp only [Finset.card_pair hj, Finset.insert_subset_iff, Finset.singleton_subset_iff] at hcount
      unfold uniformSchoolProbability
      trans (Nat.choose (n-2) (m-2):ℝ) / (Nat.choose n m:ℝ)
      · congr 1
        apply congrArg (fun a : ℕ => (a:ℝ))
        convert hcount using 1 <;> congr!
      have h1 := school_choose_one n m (by omega) (by omega)
      have h2 := school_choose_one (n-1) (m-1) (by omega) (by omega)
      have hsubn : n-1-1=n-2 := by omega
      have hsubm : m-1-1=m-2 := by omega
      rw [hsubn,hsubm] at h2
      have h1r : (n:ℝ)*(Nat.choose (n-1) (m-1):ℝ) = (Nat.choose n m:ℝ)*(m:ℝ) := by exact_mod_cast h1
      have h2r : ((n:ℝ)-1)*(Nat.choose (n-2) (m-2):ℝ) = (Nat.choose (n-1) (m-1):ℝ)*((m:ℝ)-1) := by
        simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1≤n),
          Nat.cast_sub (by omega : 1≤m), Nat.cast_one] using
          congrArg (fun a : ℕ => (a:ℝ)) h2
      apply (div_eq_div_iff hc (mul_ne_zero hn0 hn1)).mpr
      nlinarith [congrArg (fun x : ℝ => x*((m:ℝ)-1)) h1r,
        congrArg (fun x : ℝ => (n:ℝ)*x) h2r]
    · have hempty : (unblockedSchoolSupport n m).filter (fun s => h∈s ∧ j∈s) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        rcases Finset.mem_filter.mp hs with ⟨hs,hh,hj'⟩
        have hcard := (Finset.mem_powersetCard.mp hs).2
        have : ({h,j}:Finset (Fin n)) ⊆ s := by exact Finset.insert_subset hh (Finset.singleton_subset_iff.mpr hj')
        have := Finset.card_le_card this
        simp [hj,hcard] at this
        omega
      have hm01 : m=0 ∨ m=1 := by omega
      unfold uniformSchoolProbability
      have he : (((unblockedSchoolSupport n m).filter (fun s => h∈s ∧ j∈s)).card:ℝ) = 0 := by
        convert (congrArg (fun s : Finset (Finset (Fin n)) => (s.card:ℝ)) hempty) using 1 <;> simp
      trans 0 / (Nat.choose n m:ℝ)
      · congr 1
        convert he using 1 <;> congr!
      rcases hm01 with rfl | rfl <;> simp

/-- Rejected states lie in the upper tail of a rejected state of minimum score. -/
private theorem sharp_tail {Ω : Type*} [Fintype Ω] (p t : Ω → ℝ)
    (hp : ∀ z, 0≤p z) (α : ℝ) (hα : 0≤α) :
    let q := fun z => ∑ u, p u * (if t z ≤ t u then (1:ℝ) else 0)
    (∑ z, p z * (if q z ≤ α then (1:ℝ) else 0)) ≤ α := by
  classical
  dsimp only
  let q := fun z => ∑ u, p u * (if t z ≤ t u then (1:ℝ) else 0)
  change (∑ z, p z * (if q z ≤ α then (1:ℝ) else 0)) ≤ α
  let R := Finset.univ.filter (fun z => q z ≤ α)
  by_cases hR : R.Nonempty
  · obtain ⟨z,hz,hmin⟩ := R.exists_min_image t hR
    have hzα : q z ≤ α := (Finset.mem_filter.mp hz).2
    apply le_trans (b := q z) ?_ hzα
    apply Finset.sum_le_sum
    intro u _
    by_cases hu : q u ≤ α
    · have htu : t z ≤ t u := hmin u (by simp [R,hu])
      simp only [hu,htu,if_true,mul_one,le_refl]
    · simp only [hu, if_false, mul_zero]
      exact mul_nonneg (hp u) (by split_ifs <;> norm_num)
  · have hnone : ∀ z, ¬q z ≤ α := by
      intro z hz
      exact hR ⟨z, by simp [R,hz]⟩
    simpa only [hnone, if_false, mul_zero, Finset.sum_const_zero] using hα

/-- Weighted permutation validity with an assignment-invariant outcome vector. -/
theorem sharp_null_permutation_valid_proof {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : Ω → ℝ) (hp : ∀ z, 0<p z) (htotal : ∑ z, p z=1)
    (T : Ω → (I → ℝ) → ℝ) (Y : Ω → I → ℝ)
    (hsharp : ∀ z z' i, Y z i=Y z' i) (z0 : Ω) (α : ℝ)
    (hα : 0≤α ∧ α≤1) :
    let pval := fun z => ∑ z', p z'*(if |T z' (Y z0)| ≥ |T z (Y z0)| then (1:ℝ) else 0)
    (∑ z, p z*(if pval z≤α then (1:ℝ) else 0))≤α := by
  exact sharp_tail p (fun z => |T z (Y z0)|) (fun z => (hp z).le) α hα.1

end AronowAudit.P037.Wave1
