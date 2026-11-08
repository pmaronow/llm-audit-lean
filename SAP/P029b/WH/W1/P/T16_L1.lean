import SAP.P029b.WH.W1.Leaves
import Mathlib.Data.Finset.Max
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W1.P.T16_L1

open Classical Set

private noncomputable def qualifyingValues {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ) : Finset ℝ :=
  (Finset.univ.image s).filter (fun x => level ≤ EmpiricalCDFW1 s x)

private lemma cdf_level_iff {n : ℕ} (s : Fin (n+1) → ℝ) (level t : ℝ) :
    level ≤ EmpiricalCDFW1 s t ↔
      ((n+1 : ℕ) : ℝ) * level ≤
        (Finset.univ.filter (fun i : Fin (n+1) => s i ≤ t)).card := by
  unfold EmpiricalCDFW1
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hDen : ((n+1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [← hDen]
  rw [le_div_iff₀ hN]
  constructor <;> intro h <;> nlinarith [h]

private lemma qualifyingValues_nonempty {n : ℕ} (s : Fin (n+1) → ℝ)
    (level : ℝ) (hlevel : level ∈ Ioc (0 : ℝ) 1) :
    (qualifyingValues s level).Nonempty := by
  let vals := Finset.univ.image s
  have hvals : vals.Nonempty := by
    refine ⟨s 0, ?_⟩
    simp [vals]
  let m := vals.max' hvals
  have hle (i : Fin (n+1)) : s i ≤ m := by
    apply Finset.le_max' vals (s i)
    simp [vals]
  have hfilter : Finset.univ.filter (fun i : Fin (n+1) => s i ≤ m) = Finset.univ := by
    ext i
    simp [hle i]
  have hm : level ≤ EmpiricalCDFW1 s m := by
    apply (cdf_level_iff s level m).2
    rw [hfilter]
    have hcard : ((Finset.univ : Finset (Fin (n+1))).card : ℝ) = ((n+1 : ℕ) : ℝ) := by simp
    rw [hcard]
    exact mul_le_of_le_one_right (by positivity) hlevel.2
  refine ⟨m, Finset.mem_filter.mpr ⟨?_, hm⟩⟩
  · exact Finset.max'_mem vals hvals

private noncomputable def cutoff {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ)
    (hlevel : level ∈ Ioc (0 : ℝ) 1) : ℝ :=
  (qualifyingValues s level).min' (qualifyingValues_nonempty s level hlevel)

private lemma cutoff_mem {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ)
    (hlevel : level ∈ Ioc (0 : ℝ) 1) :
    cutoff s level hlevel ∈ qualifyingValues s level := by
  exact Finset.min'_mem _ _

private lemma cutoff_is_entry {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ)
    (hlevel : level ∈ Ioc (0 : ℝ) 1) :
    ∃ i : Fin (n+1), cutoff s level hlevel = s i := by
  have hm := (Finset.mem_filter.mp (cutoff_mem s level hlevel)).1
  rcases Finset.mem_image.mp hm with ⟨i, hi, hval⟩
  exact ⟨i, hval.symm⟩

private lemma empiricalCDF_mono {n : ℕ} (s : Fin (n+1) → ℝ) {a b : ℝ}
    (hab : a ≤ b) : EmpiricalCDFW1 s a ≤ EmpiricalCDFW1 s b := by
  unfold EmpiricalCDFW1
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact le_trans hi hab

private lemma superlevel_eq_Ici {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ)
    (hlevel : level ∈ Ioc (0 : ℝ) 1) :
    {t | level ≤ EmpiricalCDFW1 s t} = Ici (cutoff s level hlevel) := by
  ext t
  change (level ≤ EmpiricalCDFW1 s t) ↔ cutoff s level hlevel ≤ t
  constructor
  · intro ht
    let inds := Finset.univ.filter (fun i : Fin (n+1) => s i ≤ t)
    have hcard : ((inds.card : ℕ) : ℝ) > 0 := by
      have hpos : 0 < ((n+1 : ℕ) : ℝ) * level := mul_pos (by positivity) hlevel.1
      have hle := (cdf_level_iff s level t).mp ht
      exact lt_of_lt_of_le hpos hle
    have hinds : inds.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
    obtain ⟨i₀, hi₀⟩ := hinds
    let vals := inds.image s
    have hvals : vals.Nonempty := ⟨s i₀, Finset.mem_image.mpr ⟨i₀, hi₀, rfl⟩⟩
    let m := vals.max' hvals
    have hmval : m ∈ vals := Finset.max'_mem vals hvals
    obtain ⟨im, him, hsm⟩ := Finset.mem_image.mp hmval
    have hmt : m ≤ t := by
      rw [← hsm]
      exact (Finset.mem_filter.mp him).2
    have hfilter :
        Finset.univ.filter (fun i : Fin (n+1) => s i ≤ m) = inds := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, inds]
      constructor
      · intro him
        exact le_trans him hmt
      · intro hit
        exact Finset.le_max' vals (s i)
          (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, rfl⟩)
    have hcdf : EmpiricalCDFW1 s m = EmpiricalCDFW1 s t := by
      unfold EmpiricalCDFW1
      rw [hfilter]
    have hmqual : level ≤ EmpiricalCDFW1 s m := by rw [hcdf]; exact ht
    have hmin : cutoff s level hlevel ≤ m := by
      change (qualifyingValues s level).min'
        (qualifyingValues_nonempty s level hlevel) ≤ m
      apply Finset.min'_le
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨im, Finset.mem_univ _, hsm⟩, hmqual⟩
    exact hmin.trans hmt
  · intro hqt
    exact (Finset.mem_filter.mp (cutoff_mem s level hlevel)).2 |>.trans
      (empiricalCDF_mono s hqt)

private lemma below_count_lt {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ)
    (hlevel : level ∈ Ioc (0 : ℝ) 1) :
    ((belowCount s (cutoff s level hlevel) : ℕ) : ℝ) < ((n+1 : ℕ) : ℝ) * level := by
  let q := cutoff s level hlevel
  let inds := Finset.univ.filter (fun i : Fin (n+1) => s i < q)
  change ((inds.card : ℕ) : ℝ) < ((n+1 : ℕ) : ℝ) * level
  by_contra hnot
  have hle : ((n+1 : ℕ) : ℝ) * level ≤ (inds.card : ℝ) := le_of_not_gt hnot
  have hpos : 0 < (inds.card : ℝ) := lt_of_lt_of_le
    (mul_pos (by positivity) hlevel.1) hle
  have hinds : inds.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨i₀, hi₀⟩ := hinds
  let vals := inds.image s
  have hvals : vals.Nonempty := ⟨s i₀, Finset.mem_image.mpr ⟨i₀, hi₀, rfl⟩⟩
  let m := vals.max' hvals
  have hmval : m ∈ vals := Finset.max'_mem vals hvals
  obtain ⟨im, him, hsm⟩ := Finset.mem_image.mp hmval
  have hmq : m < q := by
    rw [← hsm]
    exact (Finset.mem_filter.mp him).2
  have hfilter :
      Finset.univ.filter (fun i : Fin (n+1) => s i ≤ m) = inds := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inds]
    constructor
    · intro him
      exact lt_of_le_of_lt him hmq
    · intro hit
      exact Finset.le_max' vals (s i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, rfl⟩)
  have hmqual : level ≤ EmpiricalCDFW1 s m := by
    apply (cdf_level_iff s level m).2
    rw [hfilter]
    exact hle
  have hmin : q ≤ m := by
    change (qualifyingValues s level).min'
      (qualifyingValues_nonempty s level hlevel) ≤ m
    apply Finset.min'_le
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨im, Finset.mem_univ _, hsm⟩, hmqual⟩
  exact (not_lt_of_ge hmin) hmq

theorem proof : SAP.P029b.WH.W1.T16_L1 := by
  intro n s level hlevel
  let q := cutoff s level hlevel
  have hset : {t | level ≤ EmpiricalCDFW1 s t} = Ici q := by
    simpa [q] using superlevel_eq_Ici s level hlevel
  constructor
  · refine ⟨q, ?_⟩
    unfold InverseEmpiricalQuantileW1
    refine ⟨?_, ?_, ?_⟩
    · rw [hset]
      exact ⟨q, by simp⟩
    · rw [hset]
      exact ⟨q, fun y hy => by simpa using hy⟩
    · rw [hset]
      simp
  · intro c hc
    unfold InverseEmpiricalQuantileW1 at hc
    have hceq : c = q := by
      rw [hset] at hc
      simpa using hc.2.2
    constructor
    · obtain ⟨i, hi⟩ := cutoff_is_entry s level hlevel
      exact ⟨i, hceq.trans hi⟩
    · rw [hceq]
      have hstrict := below_count_lt s level hlevel
      change (belowCount s (cutoff s level hlevel) : ℝ) /
          ((n : ℝ) + 1) < level
      have hDen : ((n+1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      rw [← hDen]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ))).2
      nlinarith

end SAP.P029b.WH.W1.P.T16_L1

theorem SAP.P029b.WH.W1.T16_L1_proof : SAP.P029b.WH.W1.T16_L1 :=
  SAP.P029b.WH.W1.P.T16_L1.proof
