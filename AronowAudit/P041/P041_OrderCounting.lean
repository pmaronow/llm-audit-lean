import Mathlib

/-! Exact balanced-subset leading-run counts for P041-T5,
expressed through binomial coefficients. -/

noncomputable section
open scoped BigOperators
namespace AronowAudit.P041.OrderCompletion

def leadingRun {N : ℕ} (z : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter (fun r => ∀ s : Fin N, s ≤ r → s ∈ z)).card

def initialSegment (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun r => r.val < k)

lemma initialSegment_eq_Iio {N k : ℕ} (hk : k < N) : initialSegment N k = Finset.Iio ⟨k,hk⟩ := by
  ext r
  simp [initialSegment,Fin.lt_iff_val_lt_val]

lemma initialSegment_card {N k : ℕ} (hk : k < N) : (initialSegment N k).card = k := by
  rw [initialSegment_eq_Iio hk,Fin.card_Iio]

lemma leading_run_first_missing {N : ℕ} (z : Finset (Fin N)) (q : Fin N)
    (hq : q ∉ z) (hmin : ∀ r, r ∉ z → q ≤ r) : leadingRun z = q.val := by
  have he : Finset.univ.filter (fun r => ∀ s : Fin N, s ≤ r → s ∈ z) = Finset.Iio q := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    constructor
    · intro h
      by_contra hn
      exact hq (h q (le_of_not_gt hn))
    · intro h s hs
      by_contra hn
      exact (not_lt_of_ge (hmin s hn)) (hs.trans_lt h)
  rw [leadingRun,he,Fin.card_Iio]

lemma first_missing_exists {N : ℕ} (z : Finset (Fin N)) (hz : z ≠ Finset.univ) :
    ∃ q : Fin N, q ∉ z ∧ (∀ r, r ∉ z → q ≤ r) ∧ leadingRun z = q.val := by
  have hc : (zᶜ).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hz)
  let q := (zᶜ).min' hc
  have hq : q ∉ z := Finset.mem_compl.mp (Finset.min'_mem _ _)
  have hm (r : Fin N) (hr : r ∉ z) : q ≤ r := Finset.min'_le _ _ (Finset.mem_compl.mpr hr)
  exact ⟨q,hq,hm,leading_run_first_missing z q hq hm⟩

lemma leading_run_eq_iff {N k : ℕ} (hk : k < N) (z : Finset (Fin N))
    (hz : z ≠ Finset.univ) :
    leadingRun z = k ↔ initialSegment N k ⊆ z ∧ (⟨k,hk⟩ : Fin N) ∉ z := by
  obtain ⟨q,hq,hmin,he⟩ := first_missing_exists z hz
  constructor
  · intro h
    have hqk : q = ⟨k,hk⟩ := Fin.ext (he.symm.trans h)
    refine ⟨?_,by simpa only [← hqk] using hq⟩
    intro r hr
    have hrk : r.val < k := (Finset.mem_filter.mp hr).2
    by_contra hn
    have hm := hmin r hn
    rw [hqk] at hm
    have := hm
    change k ≤ r.val at this
    omega
  · rintro ⟨hp,hkz⟩
    apply leading_run_first_missing z ⟨k,hk⟩ hkz
    intro r hr
    by_contra hn
    apply hr
    apply hp
    simp only [initialSegment,Finset.mem_filter,Finset.mem_univ,true_and]
    exact not_le.mp hn

lemma leading_run_ge_iff {N k : ℕ} (z : Finset (Fin N)) (hz : z ≠ Finset.univ) :
    k ≤ leadingRun z ↔ initialSegment N k ⊆ z := by
  obtain ⟨q,hq,hmin,he⟩ := first_missing_exists z hz
  rw [he]
  constructor
  · intro hk r hr
    have hrk : r.val < k := (Finset.mem_filter.mp hr).2
    by_contra hn
    have hm := hmin r hn
    change q.val ≤ r.val at hm
    omega
  · intro hp
    by_contra hn
    apply hq
    apply hp
    simp only [initialSegment,Finset.mem_filter,Finset.mem_univ,true_and]
    omega


lemma balanced_proper {m : ℕ} (hm : 1 ≤ m) (z : Finset (Fin (2*m))) (hz : z.card = m) :
    z ≠ Finset.univ := by
  intro he
  have hc := congrArg Finset.card he
  simp only [Finset.card_univ,Fintype.card_fin,hz] at hc
  omega

lemma balanced_leading_count {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m) :
    ((Finset.univ.powersetCard m).filter
      (fun z : Finset (Fin (2*m)) => leadingRun z = k)).card =
      (2*m-k-1).choose (m-1) := by
  classical
  have hkN : k < 2*m := by omega
  let q : Fin (2*m) := ⟨k,hkN⟩
  let A := initialSegment (2*m) k
  let U : Finset (Fin (2*m)) := Finset.univ.erase q
  have hA : A ⊆ U := by
    intro r hr
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro he
    have hrk : r.val < k := (Finset.mem_filter.mp hr).2
    have her := congrArg Fin.val he
    change r.val = k at her
    omega
  have he : (Finset.univ.powersetCard m).filter
      (fun z : Finset (Fin (2*m)) => leadingRun z = k) =
      (U.powersetCard m).filter (fun z => A ⊆ z) := by
    ext z
    constructor
    · intro h
      obtain ⟨hz,hL⟩ := Finset.mem_filter.mp h
      have hcard := (Finset.mem_powersetCard.mp hz).2
      obtain ⟨hp,hn⟩ := (leading_run_eq_iff hkN z (balanced_proper hm z hcard)).mp hL
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨?_,hcard⟩,hp⟩
      intro r hr
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      intro hrq
      apply hn
      simpa only [hrq,q] using hr
    · intro h
      obtain ⟨hz,hp⟩ := Finset.mem_filter.mp h
      obtain ⟨hU,hcard⟩ := Finset.mem_powersetCard.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩,?_⟩
      apply (leading_run_eq_iff hkN z (balanced_proper hm z hcard)).mpr
      refine ⟨hp,?_⟩
      intro hq
      exact (Finset.mem_erase.mp (hU hq)).1 rfl
  rw [he,Finset.card_filter_powersetCard_subset A U m hA]
  · have ha : A.card = k := initialSegment_card hkN
    have hu : U.card = 2*m-1 := by simp [U]
    rw [ha,hu]
    have hb : m-k ≤ 2*m-1-k := by omega
    rw [← Nat.choose_symm hb]
    congr 1 <;> omega
  · rw [initialSegment_card hkN]
    exact hk

end AronowAudit.P041.OrderCompletion
